#!/usr/bin/env python3
"""Compare C export-syntax macro trace results with the Lean reference model.

The generated Lean file contains only data decoded from C JSON; no syntax tree
or expected result is hand-transcribed.  This is intentionally a small bridge
for the reference-model experiment, not a replacement for the C parser.
"""

import argparse
import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile


def lean_string(value):
    return json.dumps(value, ensure_ascii=False)


def tree_term(value):
    if isinstance(value, list):
        return ".list [" + ", ".join(tree_term(item) for item in value) + "]"
    if not isinstance(value, dict) or set(value) < {"atom", "origin", "token_identity"}:
        raise ValueError(f"unexpected C syntax node: {value!r}")
    origin = "none" if value["origin"] is None else f"some {value['origin']}"
    return f".atom ⟨{lean_string(value['atom'])}, {origin}, {value['token_identity']}⟩"


def syntax_key(value):
    if isinstance(value, list):
        return "L" + "".join(syntax_key(item) for item in value) + "E"
    return "A" + value["atom"] + ";"


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def run_lean(lake, source, fuel, input_term, rules_term, expected,
             graph_fuel, edges_term, ranks_term, trace_term):
    program = f'''import NLisp.MacroReferenceModel
 open NLisp.CMacroCopy NLisp.CExpansion NLisp.MacroTermination NLisp.MacroReferenceModel
private def rules : List (Nat × Tree) := {rules_term}
private def input : Tree := {input_term}
private def edges : List Edge := {edges_term}
private def ranks : List Nat := {ranks_term}
private def trace : List Nat := {trace_term}
#eval "MRM:" ++ resultKey (run rules {fuel} 0 input) ++
  "|rank=" ++ rankStatusName (rankTraceStatus edges ranks trace) ++
  "|graph=" ++ (if graph {graph_fuel} rules == some edges then "proven" else "mismatch") ++
  "|ranks=" ++ (if checkRanks edges ranks then "proven" else "unproved")
'''
    with tempfile.TemporaryDirectory() as directory:
        path = pathlib.Path(directory) / "MacroReferenceBridge.lean"
        path.write_text(program, encoding="utf-8")
        result = subprocess.run([lake, "env", "lean", str(path)],
                                cwd=pathlib.Path(__file__).resolve().parents[1],
                                capture_output=True, text=True, timeout=120)
    if result.returncode != 0:
        raise RuntimeError(result.stdout + result.stderr)
    lines = []
    for line in result.stdout.splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, str) and value.startswith("MRM:"):
            lines.append(value)
    if len(lines) != 1:
        raise RuntimeError("Lean did not emit exactly one MRM result:\n" + result.stdout)
    actual = lines[0][4:]
    return actual, expected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("nlisp", type=pathlib.Path)
    parser.add_argument("source", type=pathlib.Path)
    parser.add_argument("--lake", required=True, type=pathlib.Path)
    parser.add_argument("--fuel", type=int, default=64)
    parser.add_argument("--c-max-expansions", type=int)
    parser.add_argument("--tamper-result", action="store_true")
    args = parser.parse_args()

    command = [str(args.nlisp), "export-core", str(args.source)]
    if args.c_max_expansions is not None:
        command += ["--max-expansions", str(args.c_max_expansions)]
    process = subprocess.run(command,
                             capture_output=True, text=True)
    if process.returncode != 0:
        category = "fuel-exhausted" if "Unknown:" in process.stderr else "failed"
        syntax = subprocess.run([str(args.nlisp), "export-syntax", str(args.source)],
                                capture_output=True, text=True)
        if syntax.returncode != 0:
            print(json.dumps({"c_status": category, "lean_status": "not-run"}, ensure_ascii=False))
            return 0
        spec = importlib.util.spec_from_file_location("verify_lean", pathlib.Path(__file__).with_name("verify_lean.py"))
        verify_lean = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = verify_lean
        spec.loader.exec_module(verify_lean)
        plan = verify_lean.termination_plan(json.loads(syntax.stdout))
        print(json.dumps({"c_status": category,
                          "lean_status": "fuel-exhausted" if category == "fuel-exhausted" else "failed",
                          "rank_status": "proven" if plan.get("status") == "proved" else "unproved"},
                         ensure_ascii=False))
        return 0
    document = json.loads(process.stdout)
    traces = document.get("macro_trace", [])
    if not traces:
        print(json.dumps({"traces": 0, "message": "no macro trace"}, ensure_ascii=False))
        return 0

    spec = importlib.util.spec_from_file_location("verify_lean", pathlib.Path(__file__).with_name("verify_lean.py"))
    verify_lean = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = verify_lean
    spec.loader.exec_module(verify_lean)
    plan = verify_lean.termination_plan(document)
    if plan.get("status") != "proved":
        print(json.dumps({"traces": len(traces), "rank_status": "unproved",
                          "reason": plan.get("reason", "no decreasing rank found")},
                         ensure_ascii=False))
        return 0

    rules = []
    rule_indices = {}
    declaration_index = 0
    for form in document["normalized_ast"]:
        head = form[0].get("atom") if isinstance(form, list) and form else None
        if head == "define-macro":
            for rule in form[2][1:]:
                index = len(rules)
                entry = (declaration_index, rule)
                rules.append(entry)
                rule_indices[(declaration_index, canonical(rule))] = index
        else:
            declaration_index += 1
    rules_term = "[" + ", ".join(f"({origin}, {tree_term(rule)})" for origin, rule in rules) + "]"
    edges_term = "[" + ", ".join(f"({child}, {parent})" for child, parent in plan["edges"]) + "]"
    ranks_term = "[" + ", ".join(str(rank) for rank in plan["ranks"]) + "]"
    graph_fuel = 4 * verify_lean.syntax_nodes(document["normalized_ast"]) + 4
    trace_indices = [rule_indices[(trace["definition_index"], canonical(trace["rule"]))]
                     for trace in reversed(traces)]
    trace_term = "[" + ", ".join(str(index) for index in trace_indices) + "]"

    results = []
    for trace in traces:
        expected = "completed|" + syntax_key(trace["result"])
        if args.tamper_result:
            expected += "-tampered"
        actual, _ = run_lean(args.lake, args.source, args.fuel,
                             tree_term(trace["input"]), rules_term, expected,
                             graph_fuel, edges_term, ranks_term, trace_term)
        result, rank_info = actual.split("|rank=", 1)
        rank_status, graph_info, ranks_info = rank_info.split("|graph=", 1)[0], "", ""
        rank_status, rest = rank_info.split("|graph=", 1)
        graph_info, ranks_info = rest.split("|ranks=", 1)
        results.append({"sequence": trace["sequence"], "equal": result == expected,
                        "c": expected, "lean": result})
    all_equal = all(item["equal"] for item in results)
    output = {"traces": len(results), "all_equal": all_equal,
              "rank_status": rank_status, "graph_status": graph_info,
              "rank_check": ranks_info, "trace_rule_indices": trace_indices,
              "results": results}
    print(json.dumps(output, ensure_ascii=False, indent=2))
    return 0 if all_equal and rank_status == "proven" and graph_info == "proven" and ranks_info == "proven" else 1


if __name__ == "__main__":
    raise SystemExit(main())
