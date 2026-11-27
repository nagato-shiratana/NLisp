import NLisp.CExpansion
import NLisp.ExpansionCertificate

namespace NLisp.MacroTermination
open CMacroCopy CExpansion

private theorem option_bind_some {α β : Type} {source : Option α}
    {continuation : α → Option β} {value : β}
    (accepted : source.bind continuation = some value) :
    ∃ intermediate, source = some intermediate ∧ continuation intermediate = some value := by
  cases source with
  | none => simp at accepted
  | some intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mem_append_left {α : Type} (left right : List α) {item : α}
    (member : item ∈ left) : item ∈ left ++ right := by
  induction left with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.cons_append, List.mem_cons] at member ⊢
      rcases member with same | member
      · subst item
        exact Or.inl rfl
      · exact Or.inr (ih member)

private theorem mem_append_right {α : Type} (left right : List α) {item : α}
    (member : item ∈ right) : item ∈ left ++ right := by
  have each (pre : List α) : item ∈ right → item ∈ pre ++ right := by
    induction pre with
    | nil => simp
    | cons head tail ih =>
        intro member
        simp only [List.cons_append, List.mem_cons]
        exact Or.inr (ih member)
  exact each left member

private theorem mem_map_counter (values : List Nat) (target index : Nat)
    (member : target ∈ values) :
    (target, index) ∈ values.map (fun child => (child, index)) := by
  induction values with
  | nil => simp at member
  | cons child tail ih =>
      rcases List.mem_cons.mp member with same | rest
      · subst target
        simp [List.map_cons]
      · exact List.mem_cons_of_mem _ (ih rest)

abbrev Edge := Nat × Nat -- child, parent

def signature : Tree → Option (String × Nat)
  | .list [.list (.atom head :: parameters), _, _, _] => some (head.name, parameters.length)
  | _ => none

theorem holeEntries_success_lengths (parameters arguments : List Tree) (holes : Holes)
    (accepted : holeEntries parameters arguments = some holes) :
    parameters.length = arguments.length := by
  induction parameters generalizing arguments holes with
  | nil => cases arguments <;> simp [holeEntries] at accepted ⊢
  | cons parameter parameters ih =>
      cases parameter with
      | list items => simp [holeEntries] at accepted
      | atom parameter =>
          cases arguments with
          | nil => simp [holeEntries] at accepted
          | cons argument arguments =>
              cases tailResult : holeEntries parameters arguments with
              | none => simp [holeEntries, tailResult] at accepted
              | some tailHoles =>
                  have tailLengths := ih arguments tailHoles tailResult
                  simp [holeEntries, tailResult, tailLengths]

theorem successful_match_has_signature (rule input : Tree) (holes : Holes) (template : Tree)
    (matched : matchRule rule input = some (holes, template)) :
    ∃ ruleHead arity callHead arguments,
      signature rule = some (ruleHead, arity) ∧
      input = .list (.atom callHead :: arguments) ∧
      callHead.name = ruleHead ∧ arity = arguments.length := by
  unfold matchRule at matched
  split at matched
  all_goals try split at matched
  case h_1.inl =>
    rename_i _ _ pattern parameters _ _ _ called arguments nameEq
    have arityMatch : parameters.length = arguments.length := by
      rcases Option.map_eq_some'.mp matched with ⟨generatedHoles, holesMatch, _⟩
      exact holeEntries_success_lengths _ _ _ holesMatch
    refine ⟨pattern.name, parameters.length, called, arguments, ?_⟩
    exact ⟨rfl, ⟨rfl, ⟨nameEq.symm, arityMatch⟩⟩⟩
  all_goals simp_all [signature]

def findRule (name : String) (arity : Nat) : Nat → List (Nat × Tree) → Option Nat
  | _, [] => none
  | index, (_, rule) :: tail =>
      if signature rule = some (name, arity) then some index else findRule name arity (index + 1) tail

def targetsOfSignature (name : String) (arity : Nat) : Nat → List (Nat × Tree) → List Nat
  | _, [] => []
  | index, (_, rule) :: tail =>
      if signature rule = some (name, arity) then
        index :: targetsOfSignature name arity (index + 1) tail
      else targetsOfSignature name arity (index + 1) tail

theorem findRule_of_member_signature (name : String) (arity start : Nat)
    (rules : List (Nat × Tree)) (owner : Nat) (rule : Tree)
    (member : (owner, rule) ∈ rules) (sigMatch : signature rule = some (name, arity)) :
    ∃ target, findRule name arity start rules = some target := by
  induction rules generalizing start owner rule with
  | nil => simp at member
  | cons entry tail ih =>
      rcases entry with ⟨headOwner, headRule⟩
      simp only [List.mem_cons] at member
      rcases member with same | rest
      · cases same
        exact ⟨start, by simp [findRule, sigMatch]⟩
      · by_cases headMatches : signature headRule = some (name, arity)
        · exact ⟨start, by simp [findRule, headMatches]⟩
        · obtain ⟨target, found⟩ := ih (start := start + 1) (owner := owner)
            (rule := rule) rest sigMatch
          exact ⟨target, by simp [findRule, headMatches, found]⟩

theorem findRule_mem_targetsOfSignature (name : String) (arity start : Nat)
    (rules : List (Nat × Tree)) (target : Nat)
    (found : findRule name arity start rules = some target) :
    target ∈ targetsOfSignature name arity start rules := by
  induction rules generalizing start with
  | nil => simp [findRule] at found
  | cons entry tail ih =>
      rcases entry with ⟨owner, rule⟩
      change (if signature rule = some (name, arity) then some start
        else findRule name arity (start + 1) tail) = some target at found
      change target ∈ (if signature rule = some (name, arity) then
        start :: targetsOfSignature name arity (start + 1) tail
        else targetsOfSignature name arity (start + 1) tail)
      by_cases signatureMatches : signature rule = some (name, arity)
      · simp [signatureMatches] at found
        subst target
        simp [signatureMatches]
      · simp [signatureMatches] at found
        have rest := ih (start + 1) found
        simp [signatureMatches]
        exact rest

def parameters : Tree → Option (List String × Tree)
  | .list [.list (_ :: names), _, _, template] => do
      let holes ← names.mapM (fun tree => match tree with
        | .atom a => some a.name
        | _ => none)
      pure (holes, template)
  | _ => none

/- A syntax hole in call-head position can be substituted by any macro name.
Include every rule of the same arity as a conservative target candidate. -/
def targetsOfArity (arity : Nat) : Nat → List (Nat × Tree) → List Nat
  | _, [] => []
  | index, (_, rule) :: tail =>
      if (signature rule).map Prod.snd = some arity then
        index :: targetsOfArity arity (index + 1) tail
      else targetsOfArity arity (index + 1) tail

theorem findRule_mem_targetsOfArity (name : String) (arity start : Nat)
    (rules : List (Nat × Tree)) (target : Nat)
    (found : findRule name arity start rules = some target) :
    target ∈ targetsOfArity arity start rules := by
  induction rules generalizing start with
  | nil => simp [findRule] at found
  | cons entry tail ih =>
      rcases entry with ⟨owner, rule⟩
      change (if signature rule = some (name, arity) then some start
        else findRule name arity (start + 1) tail) = some target at found
      change target ∈ (if (signature rule).map Prod.snd = some arity then
        start :: targetsOfArity arity (start + 1) tail
        else targetsOfArity arity (start + 1) tail)
      by_cases signatureMatches : signature rule = some (name, arity)
      · simp [signatureMatches] at found
        subst target
        simp [signatureMatches]
      · simp [signatureMatches] at found
        have rest := ih (start + 1) found
        by_cases sameArity : (signature rule).map Prod.snd = some arity
        · simp [sameArity]
          exact Or.inr rest
        · simp [sameArity]
          exact rest

/- Conservative call extraction. A hole in head position can manufacture a
new call, so every rule of the same arity is a possible target. A named call
includes every rule with that exact signature. Scanning annotations too only
adds edges and may reduce completeness. -/
structure CallOperations where
  calls : List (Nat × Tree) → List String → Tree → Option (List Nat)
  callsMany : List (Nat × Tree) → List String → List Tree → Option (List Nat)

def callOperations : Nat → CallOperations
  | 0 => ⟨fun _ _ _ => none, fun _ _ _ => none⟩
  | fuel + 1 =>
      let previous := callOperations fuel
      { calls := fun rules holes tree =>
          match tree with
          | .atom _ => some []
          | .list items =>
              match previous.callsMany rules holes items with
              | none => none
              | some nested =>
                match items with
                | .atom head :: arguments =>
                    if head.name ∈ holes then
                      some (targetsOfArity arguments.length 0 rules ++ nested)
                    else
                      some (targetsOfSignature head.name arguments.length 0 rules ++ nested)
                | _ => some nested
        callsMany := fun rules holes trees =>
          match trees with
          | [] => some []
          | head :: tail =>
              match previous.calls rules holes head with
              | none => none
              | some headCalls =>
                match previous.callsMany rules holes tail with
                | none => none
                | some tailCalls => some (headCalls ++ tailCalls) }

def calls (fuel : Nat) := (callOperations fuel).calls
def callsMany (fuel : Nat) := (callOperations fuel).callsMany

theorem calls_direct_macro_complete (fuel : Nat) (rules : List (Nat × Tree))
    (holes : List String) (head : Atom) (arguments : List Tree) (target : Nat)
    (targets : List Nat) (notHole : head.name ∉ holes)
    (found : findRule head.name arguments.length 0 rules = some target)
    (checked : calls (fuel + 1) rules holes (.list (.atom head :: arguments)) = some targets) :
    target ∈ targets := by
  simp only [calls, callOperations, notHole] at checked
  generalize nestedResult : (callOperations fuel).callsMany rules holes
      (.atom head :: arguments) = nestedOption at checked
  cases nestedOption with
  | none => simp [nestedResult] at checked
  | some nested =>
      simp [nestedResult] at checked
      subst targets
      exact mem_append_left _ _
        (findRule_mem_targetsOfSignature head.name arguments.length 0 rules target found)

inductive StaticCall (rules : List (Nat × Tree)) (holes : List String) : Tree → Nat → Prop where
  | direct {head : Atom} {arguments : List Tree} {target : Nat} :
      head.name ∉ holes → target ∈ targetsOfSignature head.name arguments.length 0 rules →
      StaticCall rules holes (.list (.atom head :: arguments)) target
  | substitutedHead {head : Atom} {arguments : List Tree} {target : Nat} :
      head.name ∈ holes → target ∈ targetsOfArity arguments.length 0 rules →
      StaticCall rules holes (.list (.atom head :: arguments)) target
  | nested {items : List Tree} {child : Tree} {target : Nat} :
      child ∈ items → StaticCall rules holes child target →
      StaticCall rules holes (.list items) target

theorem macro_step_input_is_static_candidate (rules : List (Nat × Tree)) (origin : Nat)
    (rule input template : Tree) (holes : Holes)
    (member : (origin, rule) ∈ rules)
    (matched : matchRule rule input = some (holes, template)) :
    ∃ target, StaticCall rules [] input target := by
  obtain ⟨ruleName, arity, callHead, arguments, signatureMatch, inputShape, nameMatch, arityMatch⟩ :=
    successful_match_has_signature rule input holes template matched
  obtain ⟨target, found⟩ :=
    findRule_of_member_signature ruleName arity 0 rules origin rule member signatureMatch
  have candidate := findRule_mem_targetsOfSignature ruleName arity 0 rules target found
  refine ⟨target, ?_⟩
  rw [inputShape]
  apply StaticCall.direct
  · simp
  · rw [nameMatch, ← arityMatch]
    exact candidate

/-- A successful macro match identifies the redex as a static candidate call.
This is only a redex-to-candidate fact; it does not connect the redex to the
parent rule whose template produced it. -/
theorem macroStep_has_static_call (rules : List (Nat × Tree))
    (origin fuel fresh final : Nat) (rule input template output : Tree) (holes : Holes)
    (member : (origin, rule) ∈ rules)
    (matched : matchRule rule input = some (holes, template))
    (_copied : copyWithMacros (macroNames rules) fuel origin holes [] fresh template =
      some (output, final)) :
    ∃ target, StaticCall rules [] input target := by
  exact macro_step_input_is_static_candidate rules origin rule input template holes
    member matched

/-- Acceptance by the independent local expansion checker exposes both the
exact copy derivation and a static candidate for the redex. This is the
checker-to-call-graph boundary for an individual runtime macro step; relating
the candidate to the enclosing template rank still requires the traversal
simulation lemmas below. -/
theorem certified_macroStep_has_static_call (rules : List (Nat × Tree))
    (origin fuel fresh final : Nat) (rule input output : Tree)
    (accepted : NLisp.ExpansionCertificate.checkStep rules origin fuel fresh final
      rule input output = true) :
    ∃ holes template target,
      (origin, rule) ∈ rules ∧
      matchRule rule input = some (holes, template) ∧
      copyWithMacros (macroNames rules) fuel origin holes [] fresh template =
        some (output, final) ∧
      StaticCall rules [] input target := by
  obtain ⟨holes, template, member, matched, copied⟩ :=
    NLisp.ExpansionCertificate.checkStep_sound accepted
  obtain ⟨target, candidate⟩ := macro_step_input_is_static_candidate rules origin
    rule input template holes member matched
  exact ⟨holes, template, target, member, matched, copied, candidate⟩

/-- Expose the binder, initializer, and tail operations of a successful
single-head `copyBindings` scan. -/
theorem copyBindingsWithMacros_cons_parts (macros : List String) (fuel origin : Nat)
    (holes : Holes) (outside names finalNames : Renames) (fresh final : Nat)
    (name typ value : Tree) (tail copied : List Tree)
    (accepted : copyBindingsWithMacros macros (fuel + 1) origin holes outside names fresh
      (.list [.list [name, typ], value] :: tail) = some (copied, finalNames, final)) :
    ∃ copiedName names' next copiedValue afterValue copiedTail finalNames',
      binder holes names fresh name = some (copiedName, names', next) ∧
        (operations macros fuel).copy origin holes outside next value =
          some (copiedValue, afterValue) ∧
        (operations macros fuel).copyBindings origin holes outside names' afterValue tail =
          some (copiedTail, finalNames', final) ∧
        copied = .list [.list [copiedName, typ], copiedValue] :: copiedTail := by
  simp [copyBindingsWithMacros, operations] at accepted
  rcases accepted with ⟨⟨copiedName, names', next⟩, binderAccepted,
    ⟨copiedValue, afterValue⟩, valueAccepted, ⟨copiedTail, finalNames', final'⟩,
    tailAccepted, copiedEq, finalEq⟩
  simp only [Prod.fst, Prod.snd] at finalEq copiedEq binderAccepted valueAccepted tailAccepted
  rcases finalEq with ⟨rfl, rfl⟩
  exact ⟨copiedName, names', next, copiedValue, afterValue, copiedTail, finalNames',
    binderAccepted, valueAccepted, tailAccepted, copiedEq.symm⟩

/-- Split a successful `copyCases` scan at a default case with an empty
pattern. Its body uses the current rename environment directly. -/
theorem copyCasesWithMacros_default_parts (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (body : Tree) (tail copiedCases : List Tree)
    (accepted : copyCasesWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.list [], body] :: tail) = some (copiedCases, final)) :
    ∃ copiedBody afterBody copiedTail,
      (operations macros fuel).copy origin holes renames fresh body =
        some (copiedBody, afterBody) ∧
      (operations macros fuel).copyCases origin holes renames afterBody tail =
        some (copiedTail, final) ∧
      copiedCases = .list [.list [], copiedBody] :: copiedTail := by
  simp [copyCasesWithMacros, operations] at accepted
  rcases accepted with ⟨⟨copiedBody, afterBody⟩, bodyAccepted,
    ⟨copiedTail, final'⟩, tailAccepted, copiedEq, finalEq⟩
  simp only [Prod.fst, Prod.snd] at copiedEq finalEq
  subst final'
  exact ⟨copiedBody, afterBody, copiedTail, bodyAccepted, tailAccepted, copiedEq.symm⟩

/-- Split a successful nonempty-pattern case scan into pattern freshening,
case-body copying under the freshened names, and the remaining cases. -/
theorem copyCasesWithMacros_pattern_parts (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (names : Renames) (constructor : Tree) (patternParameters : List Tree)
    (body : Tree) (tail copiedCases : List Tree) (originalNames : List String)
    (patternNamesMatch : patternNames patternParameters = some originalNames)
    (patternNamesDistinct : Lexical.distinctNames originalNames = true)
    (accepted : copyCasesWithMacros macros (fuel + 1) origin holes names fresh
      (.list [.list (constructor :: patternParameters), body] :: tail) =
        some (copiedCases, final)) :
    ∃ copiedParameters localNames afterPattern copiedBody afterBody copiedTail,
      (operations macros fuel).copyPattern holes names fresh patternParameters =
        some (copiedParameters, localNames, afterPattern) ∧
      (operations macros fuel).copy origin holes localNames afterPattern body =
        some (copiedBody, afterBody) ∧
      (operations macros fuel).copyCases origin holes names afterBody tail =
        some (copiedTail, final) ∧
      copiedCases = .list [.list (constructor :: copiedParameters), copiedBody] :: copiedTail := by
  simp [copyCasesWithMacros, operations, patternNamesMatch, patternNamesDistinct] at accepted
  rcases accepted with ⟨⟨copiedParameters, localNames, afterPattern⟩, patternAccepted,
    ⟨copiedBody, afterBody⟩, bodyAccepted, ⟨copiedTail, final'⟩,
    tailAccepted, copiedEq, finalEq⟩
  simp only [Prod.fst, Prod.snd] at copiedEq finalEq patternAccepted bodyAccepted tailAccepted
  rcases finalEq with ⟨rfl, rfl⟩
  exact ⟨copiedParameters, localNames, afterPattern, copiedBody, afterBody, copiedTail,
    patternAccepted, bodyAccepted, tailAccepted, copiedEq.symm⟩

inductive CaseRows : List Tree → Prop where
  | nil : CaseRows []
  | default (body : Tree) (tail : List Tree) :
      CaseRows tail → CaseRows (.list [.list [], body] :: tail)
  | pattern (constructor : Tree) (parameters : List Tree) (body : Tree)
      (tail : List Tree) (names : List String) :
      patternNames parameters = some names → Lexical.distinctNames names = true →
      CaseRows tail →
      CaseRows (.list [.list (constructor :: parameters), body] :: tail)

/-- Extract the body copy at any case index from a successful case scan.
The prefix condition records exactly the case shapes and distinct binders
accepted by the dispatcher. -/
theorem copyCasesWithMacros_extract_default (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (names : Renames) (before : List Tree) (body : Tree)
    (suffix copiedCases : List Tree) (beforeValid : CaseRows before)
    (accepted : copyCasesWithMacros macros (fuel + before.length + 1) origin holes names fresh
      (before ++ .list [.list [], body] :: suffix) = some (copiedCases, final)) :
    ∃ freshBefore copiedBody afterBody,
      (operations macros fuel).copy origin holes names freshBefore body =
        some (copiedBody, afterBody) := by
  induction beforeValid generalizing fuel fresh copiedCases final with
  | nil =>
      have accepted' : copyCasesWithMacros macros (fuel + 1) origin holes names fresh
          (.list [.list [], body] :: suffix) = some (copiedCases, final) := by
        simpa using accepted
      obtain ⟨copiedBody, afterBody, _copiedTail, bodyAccepted, _tailAccepted, _shape⟩ :=
        copyCasesWithMacros_default_parts macros fuel origin fresh final holes names body suffix
          copiedCases accepted'
      exact ⟨fresh, copiedBody, afterBody, bodyAccepted⟩
  | @default previousBody tail _tailValid ih =>
      have accepted' : copyCasesWithMacros macros (fuel + tail.length + 1 + 1) origin holes names
          fresh (.list [.list [], previousBody] :: (tail ++ .list [.list [], body] :: suffix)) =
            some (copiedCases, final) := by
        simpa [List.length, Nat.add_assoc] using accepted
      obtain ⟨_copiedPrefixBody, afterPrefixBody, copiedTail, _prefixBody, tailAccepted,
        _prefixShape⟩ := copyCasesWithMacros_default_parts macros (fuel + tail.length + 1) origin
          fresh final holes names previousBody (tail ++ .list [.list [], body] :: suffix)
          copiedCases accepted'
      have tailAccepted' : copyCasesWithMacros macros (fuel + tail.length + 1) origin holes names
          afterPrefixBody (tail ++ .list [.list [], body] :: suffix) =
            some (copiedTail, final) := by
        simpa [copyCasesWithMacros] using tailAccepted
      exact ih (fuel := fuel) (fresh := afterPrefixBody) (copiedCases := copiedTail)
        (final := final) tailAccepted'
  | @pattern constructor parameters previousBody tail originalNames namesMatch namesDistinct
      _tailValid ih =>
      have accepted' : copyCasesWithMacros macros (fuel + tail.length + 1 + 1) origin holes names
          fresh (.list [.list (constructor :: parameters), previousBody] ::
            (tail ++ .list [.list [], body] :: suffix)) = some (copiedCases, final) := by
        simpa [List.length, Nat.add_assoc] using accepted
      obtain ⟨_copiedParameters, _localNames, _afterPattern, _copiedPrefixBody,
        afterPrefixBody, copiedTail, _patternCopy, _bodyCopy, tailAccepted, _prefixShape⟩ :=
        copyCasesWithMacros_pattern_parts macros (fuel + tail.length + 1) origin fresh final
          holes names constructor parameters previousBody
          (tail ++ .list [.list [], body] :: suffix) copiedCases originalNames
          namesMatch namesDistinct accepted'
      have tailAccepted' : copyCasesWithMacros macros (fuel + tail.length + 1) origin holes names
          afterPrefixBody (tail ++ .list [.list [], body] :: suffix) =
            some (copiedTail, final) := by
        simpa [copyCasesWithMacros] using tailAccepted
      exact ih (fuel := fuel) (fresh := afterPrefixBody) (copiedCases := copiedTail)
        (final := final) tailAccepted'

/-- Extract pattern freshening and body copying at any case index from a
successful case scan. -/
theorem copyCasesWithMacros_extract_pattern (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (names : Renames) (before : List Tree) (constructor : Tree)
    (parameters : List Tree) (body : Tree) (suffix copiedCases : List Tree)
    (beforeValid : CaseRows before) (originalNames : List String)
    (namesMatch : patternNames parameters = some originalNames)
    (namesDistinct : Lexical.distinctNames originalNames = true)
    (accepted : copyCasesWithMacros macros (fuel + before.length + 1) origin holes names fresh
      (before ++ .list [.list (constructor :: parameters), body] :: suffix) =
        some (copiedCases, final)) :
    ∃ freshAt copiedParameters localNames afterPattern copiedBody afterBody,
      (operations macros fuel).copyPattern holes names freshAt parameters =
        some (copiedParameters, localNames, afterPattern) ∧
      (operations macros fuel).copy origin holes localNames afterPattern body =
        some (copiedBody, afterBody) := by
  induction beforeValid generalizing fuel fresh copiedCases final with
  | nil =>
      have accepted' : copyCasesWithMacros macros (fuel + 1) origin holes names fresh
          (.list [.list (constructor :: parameters), body] :: suffix) =
            some (copiedCases, final) := by
        simpa using accepted
      obtain ⟨copiedParameters, localNames, afterPattern, copiedBody, afterBody,
        _copiedTail, patternAccepted, bodyAccepted, _tailAccepted, _shape⟩ :=
        copyCasesWithMacros_pattern_parts macros fuel origin fresh final holes names constructor
          parameters body suffix copiedCases originalNames namesMatch namesDistinct accepted'
      exact ⟨fresh, copiedParameters, localNames, afterPattern, copiedBody, afterBody,
        patternAccepted, bodyAccepted⟩
  | @default previousBody tail _tailValid ih =>
      have accepted' : copyCasesWithMacros macros (fuel + tail.length + 1 + 1) origin holes names
          fresh (.list [.list [], previousBody] ::
            (tail ++ .list [.list (constructor :: parameters), body] :: suffix)) =
              some (copiedCases, final) := by
        simpa [List.length, Nat.add_assoc] using accepted
      obtain ⟨_copiedPrefixBody, afterPrefixBody, copiedTail, _prefixBody, tailAccepted,
        _prefixShape⟩ := copyCasesWithMacros_default_parts macros (fuel + tail.length + 1) origin
          fresh final holes names previousBody
          (tail ++ .list [.list (constructor :: parameters), body] :: suffix) copiedCases accepted'
      have tailAccepted' : copyCasesWithMacros macros (fuel + tail.length + 1) origin holes names
          afterPrefixBody (tail ++ .list [.list (constructor :: parameters), body] :: suffix) =
            some (copiedTail, final) := by
        simpa [copyCasesWithMacros] using tailAccepted
      obtain ⟨freshAt, copiedParameters, localNames, afterPattern, copiedBody, afterBody,
        patternAccepted, bodyAccepted⟩ :=
        ih (fuel := fuel) (fresh := afterPrefixBody) (copiedCases := copiedTail)
          (final := final) tailAccepted'
      exact ⟨freshAt, copiedParameters, localNames, afterPattern, copiedBody, afterBody,
        patternAccepted, bodyAccepted⟩
  | @pattern prefixConstructor prefixParameters prefixBody tail originalNames'
      namesMatch' namesDistinct' _tailValid ih =>
      have accepted' : copyCasesWithMacros macros (fuel + tail.length + 1 + 1) origin holes names
          fresh (.list [.list (prefixConstructor :: prefixParameters), prefixBody] ::
            (tail ++ .list [.list (constructor :: parameters), body] :: suffix)) =
              some (copiedCases, final) := by
        simpa [List.length, Nat.add_assoc] using accepted
      obtain ⟨_copiedParameters, _localNames, _afterPattern, _copiedPrefixBody,
        afterPrefixBody, copiedTail, _patternCopy, _bodyCopy, tailAccepted, _shape⟩ :=
        copyCasesWithMacros_pattern_parts macros (fuel + tail.length + 1) origin fresh final
          holes names prefixConstructor prefixParameters prefixBody
          (tail ++ .list [.list (constructor :: parameters), body] :: suffix) copiedCases
          originalNames' namesMatch' namesDistinct' accepted'
      have tailAccepted' : copyCasesWithMacros macros (fuel + tail.length + 1) origin holes names
          afterPrefixBody (tail ++ .list [.list (constructor :: parameters), body] :: suffix) =
            some (copiedTail, final) := by
        simpa [copyCasesWithMacros] using tailAccepted
      obtain ⟨freshAt, copiedParameters, localNames, afterPattern, copiedBody, afterBody,
        patternAccepted, bodyAccepted⟩ :=
        ih (fuel := fuel) (fresh := afterPrefixBody) (copiedCases := copiedTail)
          (final := final) tailAccepted'
      exact ⟨freshAt, copiedParameters, localNames, afterPattern, copiedBody, afterBody,
        patternAccepted, bodyAccepted⟩

/-- Decompose a successful ordinary three-element `match` copy around its
scrutinee and case scan. -/
theorem copyWithMacros_match_default_parts (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (matchHead : Atom) (scrutineeItems : List Tree)
    (caseBody copied : Tree)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : macros.contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name holes).isNone = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom matchHead, .list scrutineeItems, caseBody]) = some (copied, final)) :
    ∃ copiedScrutinee afterScrutinee copiedCases,
      (operations macros fuel).copy origin holes renames fresh (.list scrutineeItems) =
        some (copiedScrutinee, afterScrutinee) ∧
      (operations macros fuel).copyCases origin holes renames afterScrutinee [caseBody] =
        some (copiedCases, final) ∧
      copied = .list (.atom matchHead :: copiedScrutinee :: copiedCases) := by
  have matchNotMacro' : macros.contains "match" = false := by
    simpa [matchForm] using matchNotMacro
  have matchNotHole' : (lookup "match" holes).isNone = true := by
    simpa [matchForm] using matchNotHole
  have isMatch : named (.atom matchHead) "match" = true := by
    change (matchHead.name == "match") = true
    rw [matchForm]
    decide
  have notLet : named (.atom matchHead) "let" = false := by
    change (matchHead.name == "let") = false
    rw [matchForm]
    decide
  have raw : (do
      let (copiedScrutinee, afterScrutinee) ←
        (operations macros fuel).copy origin holes renames fresh (.list scrutineeItems)
      let (copiedCases, afterCases) ←
        (operations macros fuel).copyCases origin holes renames afterScrutinee [caseBody]
      pure (Tree.list (Tree.atom matchHead :: copiedScrutinee :: copiedCases),
        afterCases)) = some (copied, final) := by
    simpa [copyWithMacros, operations, matchForm, matchNotMacro', matchNotHole', isMatch,
      notLet] using accepted
  obtain ⟨scrutineePair, scrutineeAccepted, afterScrutineeAccepted⟩ := option_bind_some raw
  rcases scrutineePair with ⟨copiedScrutinee, afterScrutinee⟩
  obtain ⟨casesPair, casesAccepted, outputAccepted⟩ := option_bind_some afterScrutineeAccepted
  rcases casesPair with ⟨copiedCases, afterCases⟩
  have outputEq : (Tree.list (Tree.atom matchHead :: copiedScrutinee :: copiedCases),
      afterCases) = (copied, final) := by simpa using outputAccepted
  rcases Prod.mk.inj outputEq with ⟨copiedEq, finalEq⟩
  subst finalEq
  exact ⟨copiedScrutinee, afterScrutinee, copiedCases, scrutineeAccepted, casesAccepted,
    copiedEq.symm⟩

/-- If the `match` head is also a substitution hole, the dispatcher still
selects the special form and preserves that literal head. This rules out a
spurious dynamic macro step at this one-case match callsite. -/
theorem copyWithMacros_match_hole_head_default_parts (macros : List String)
    (fuel origin fresh final : Nat) (holes : Holes) (renames : Renames)
    (matchHead : Atom) (scrutineeItems : List Tree) (caseBody copied : Tree)
    (substitutedHead : Tree) (matchForm : matchHead.name = "match")
    (matchHole : lookup matchHead.name holes = some substitutedHead)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom matchHead, .list scrutineeItems, caseBody]) = some (copied, final)) :
    ∃ copiedScrutinee afterScrutinee copiedCases,
      (operations macros fuel).copy origin holes renames fresh (.list scrutineeItems) =
        some (copiedScrutinee, afterScrutinee) ∧
      (operations macros fuel).copyCases origin holes renames afterScrutinee [caseBody] =
        some (copiedCases, final) ∧
      copied = .list (.atom matchHead :: copiedScrutinee :: copiedCases) := by
  have matchHole' : lookup "match" holes = some substitutedHead := by
    simpa [matchForm] using matchHole
  have matchNotHole : (lookup "match" holes).isNone = false := by simp [matchHole']
  have isMatch : named (.atom matchHead) "match" = true := by
    change (matchHead.name == "match") = true
    rw [matchForm]
    decide
  have notLet : named (.atom matchHead) "let" = false := by
    change (matchHead.name == "let") = false
    rw [matchForm]
    decide
  have raw : (do
      let (copiedScrutinee, afterScrutinee) ←
        (operations macros fuel).copy origin holes renames fresh (.list scrutineeItems)
      let (copiedCases, afterCases) ←
        (operations macros fuel).copyCases origin holes renames afterScrutinee [caseBody]
      pure (Tree.list (Tree.atom matchHead :: copiedScrutinee :: copiedCases), afterCases)) =
        some (copied, final) := by
    simpa [copyWithMacros, operations, matchForm, matchNotHole, isMatch, notLet] using accepted
  obtain ⟨scrutineePair, scrutineeAccepted, afterScrutineeAccepted⟩ := option_bind_some raw
  rcases scrutineePair with ⟨copiedScrutinee, afterScrutinee⟩
  obtain ⟨casesPair, casesAccepted, outputAccepted⟩ := option_bind_some afterScrutineeAccepted
  rcases casesPair with ⟨copiedCases, afterCases⟩
  have outputEq : (Tree.list (Tree.atom matchHead :: copiedScrutinee :: copiedCases),
      afterCases) = (copied, final) := by simpa using outputAccepted
  rcases Prod.mk.inj outputEq with ⟨copiedEq, finalEq⟩
  subst finalEq
  exact ⟨copiedScrutinee, afterScrutinee, copiedCases, scrutineeAccepted, casesAccepted,
    copiedEq.symm⟩

/-- Decompose a successful match copy with at least two case rows. This is the
dispatcher path used by both the four-element form and longer match lists. -/
theorem copyWithMacros_match_cases_parts (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (matchHead : Atom) (scrutineeItems : List Tree)
    (firstCase secondCase : Tree) (tail : List Tree) (copied : Tree)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : macros.contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name holes).isNone = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: tail)) =
        some (copied, final)) :
    ∃ copiedScrutinee afterScrutinee copiedCases,
      (operations macros fuel).copy origin holes renames fresh (.list scrutineeItems) =
        some (copiedScrutinee, afterScrutinee) ∧
      (operations macros fuel).copyCases origin holes renames afterScrutinee
        (firstCase :: secondCase :: tail) = some (copiedCases, final) ∧
      copied = .list (.atom matchHead :: copiedScrutinee :: copiedCases) := by
  have matchNotMacro' : macros.contains "match" = false := by
    simpa [matchForm] using matchNotMacro
  have matchNotHole' : (lookup "match" holes).isNone = true := by
    simpa [matchForm] using matchNotHole
  have isMatch : named (.atom matchHead) "match" = true := by
    change (matchHead.name == "match") = true
    rw [matchForm]
    decide
  have notLet : named (.atom matchHead) "let" = false := by
    change (matchHead.name == "let") = false
    rw [matchForm]
    decide
  have notLambda : named (.atom matchHead) "lambda" = false := by
    change (matchHead.name == "lambda") = false
    rw [matchForm]
    decide
  have raw : (do
      let (copiedScrutinee, afterScrutinee) ←
        (operations macros fuel).copy origin holes renames fresh (.list scrutineeItems)
      let (copiedCases, afterCases) ←
        (operations macros fuel).copyCases origin holes renames afterScrutinee
          (firstCase :: secondCase :: tail)
      pure (Tree.list (Tree.atom matchHead :: copiedScrutinee :: copiedCases), afterCases)) =
        some (copied, final) := by
    cases tail with
    | nil =>
        simpa [copyWithMacros, operations, matchForm, matchNotMacro', matchNotHole', isMatch,
          notLet, notLambda] using accepted
    | cons second rest =>
        cases rest with
        | nil =>
            simpa [copyWithMacros, operations, matchForm, matchNotMacro', matchNotHole', isMatch,
              notLet, notLambda] using accepted
        | cons third rest =>
            simpa [copyWithMacros, operations, matchForm, matchNotMacro', matchNotHole', isMatch,
              notLet, notLambda] using accepted
  obtain ⟨scrutineePair, scrutineeAccepted, casesResult⟩ := option_bind_some raw
  rcases scrutineePair with ⟨copiedScrutinee, afterScrutinee⟩
  obtain ⟨casesPair, casesAccepted, outputAccepted⟩ := option_bind_some casesResult
  rcases casesPair with ⟨copiedCases, afterCases⟩
  have outputEq : (Tree.list (Tree.atom matchHead :: copiedScrutinee :: copiedCases), afterCases) =
      (copied, final) := by simpa using Option.some.inj outputAccepted
  rcases Prod.mk.inj outputEq with ⟨copiedEq, finalEq⟩
  subst afterCases
  exact ⟨copiedScrutinee, afterScrutinee, copiedCases, scrutineeAccepted, casesAccepted,
    copiedEq.symm⟩

/-- Freshness of match case binders is derived from a successful full match
dispatcher copy. The accepted match is first decomposed into its scrutinee
and case phases; the latter's token sequence then gives uniqueness, source
disjointness, and a bound by the final match counter. -/
theorem copyWithMacros_match_case_tokens_fresh
    (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (matchHead : Atom)
    (scrutineeItems : List Tree) (firstCase secondCase : Tree) (tail : List Tree)
    (copied : Tree) (matchForm : matchHead.name = "match")
    (matchNotMacro : macros.contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name holes).isNone = true)
    (safe : MacroCounterSafeCases macros (firstCase :: secondCase :: tail))
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: tail)) =
        some (copied, final)) :
    ∃ copiedScrutinee afterScrutinee copiedCases,
      (operations macros fuel).copy origin holes renames fresh (.list scrutineeItems) =
        some (copiedScrutinee, afterScrutinee) ∧
      copyCasesWithMacros macros fuel origin holes renames afterScrutinee
        (firstCase :: secondCase :: tail) = some (copiedCases, final) ∧
      copied = .list (.atom matchHead :: copiedScrutinee :: copiedCases) ∧
      Unique (counterPreservingCaseTokens copiedCases) ∧
      (∀ sourceToken, sourceToken % 3 = 1 →
        sourceToken ∉ counterPreservingCaseTokens copiedCases) ∧
      (∀ token, token ∈ counterPreservingCaseTokens copiedCases →
        ∃ counter, afterScrutinee < counter ∧ counter ≤ final ∧ token = 3 * counter + 2) := by
  obtain ⟨copiedScrutinee, afterScrutinee, copiedCases, scrutineeCopy, casesCopy, shape⟩ :=
    copyWithMacros_match_cases_parts macros fuel origin fresh final holes renames matchHead
      scrutineeItems firstCase secondCase tail copied matchForm matchNotMacro matchNotHole accepted
  have casesCopy' : copyCasesWithMacros macros fuel origin holes renames afterScrutinee
      (firstCase :: secondCase :: tail) = some (copiedCases, final) := by
    simpa [copyCasesWithMacros] using casesCopy
  have preserving := macroCounterSafeCases_preserving macros
    (firstCase :: secondCase :: tail) safe
  refine ⟨copiedScrutinee, afterScrutinee, copiedCases, scrutineeCopy, casesCopy', shape, ?_, ?_, ?_⟩
  · exact copyCasesWithMacros_preserving_tokens_unique macros fuel origin holes renames
      afterScrutinee (firstCase :: secondCase :: tail) copiedCases final preserving casesCopy'
  · intro sourceToken sourceClass
    exact copyCasesWithMacros_preserving_tokens_avoid_source macros fuel origin holes renames
      afterScrutinee sourceToken (firstCase :: secondCase :: tail) copiedCases final preserving
      casesCopy' sourceClass
  · intro token member
    exact copyCasesWithMacros_preserving_tokens_within_interval macros fuel origin holes renames
      afterScrutinee (firstCase :: secondCase :: tail) copiedCases final preserving casesCopy' token member

/-- The multi-case match dispatcher also takes precedence when `match` is a
hole name. The head remains literal and the complete case list is passed to
`copyCases`, including the four-element/two-case syntax. -/
theorem copyWithMacros_match_hole_head_cases_parts (macros : List String)
    (fuel origin fresh final : Nat) (holes : Holes) (renames : Renames)
    (matchHead : Atom) (scrutineeItems : List Tree) (firstCase secondCase : Tree)
    (tail : List Tree) (copied : Tree) (substitutedHead : Tree)
    (matchForm : matchHead.name = "match")
    (matchHole : lookup matchHead.name holes = some substitutedHead)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: tail)) =
        some (copied, final)) :
    ∃ copiedScrutinee afterScrutinee copiedCases,
      (operations macros fuel).copy origin holes renames fresh (.list scrutineeItems) =
        some (copiedScrutinee, afterScrutinee) ∧
      (operations macros fuel).copyCases origin holes renames afterScrutinee
        (firstCase :: secondCase :: tail) = some (copiedCases, final) ∧
      copied = .list (.atom matchHead :: copiedScrutinee :: copiedCases) := by
  have matchHole' : lookup "match" holes = some substitutedHead := by
    simpa [matchForm] using matchHole
  have matchNotHole : (lookup "match" holes).isNone = false := by simp [matchHole']
  have isMatch : named (.atom matchHead) "match" = true := by
    change (matchHead.name == "match") = true
    rw [matchForm]
    decide
  have notLet : named (.atom matchHead) "let" = false := by
    change (matchHead.name == "let") = false
    rw [matchForm]
    decide
  have notLambda : named (.atom matchHead) "lambda" = false := by
    change (matchHead.name == "lambda") = false
    rw [matchForm]
    decide
  have raw : (do
      let (copiedScrutinee, afterScrutinee) ←
        (operations macros fuel).copy origin holes renames fresh (.list scrutineeItems)
      let (copiedCases, afterCases) ←
        (operations macros fuel).copyCases origin holes renames afterScrutinee
          (firstCase :: secondCase :: tail)
      pure (Tree.list (Tree.atom matchHead :: copiedScrutinee :: copiedCases), afterCases)) =
        some (copied, final) := by
    cases tail with
    | nil =>
        simpa [copyWithMacros, operations, matchForm, matchNotHole, isMatch, notLet,
          notLambda] using accepted
    | cons third rest =>
        simpa [copyWithMacros, operations, matchForm, matchNotHole, isMatch, notLet,
          notLambda] using accepted
  obtain ⟨scrutineePair, scrutineeAccepted, casesResult⟩ := option_bind_some raw
  rcases scrutineePair with ⟨copiedScrutinee, afterScrutinee⟩
  obtain ⟨casesPair, casesAccepted, outputAccepted⟩ := option_bind_some casesResult
  rcases casesPair with ⟨copiedCases, afterCases⟩
  have outputEq : (Tree.list (Tree.atom matchHead :: copiedScrutinee :: copiedCases), afterCases) =
      (copied, final) := by simpa using Option.some.inj outputAccepted
  rcases Prod.mk.inj outputEq with ⟨copiedEq, finalEq⟩
  subst afterCases
  exact ⟨copiedScrutinee, afterScrutinee, copiedCases, scrutineeAccepted, casesAccepted,
    copiedEq.symm⟩

/-- Case binder freshness survives the match-hole dispatcher path as well as
the literal-head path. Special-form dispatch still copies the complete case
list before a hole head could be substituted. -/
theorem copyWithMacros_match_hole_case_tokens_fresh
    (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (matchHead : Atom)
    (scrutineeItems : List Tree) (firstCase secondCase : Tree) (tail : List Tree)
    (copied : Tree) (substitutedHead : Tree)
    (matchForm : matchHead.name = "match")
    (matchHole : lookup matchHead.name holes = some substitutedHead)
    (safe : MacroCounterSafeCases macros (firstCase :: secondCase :: tail))
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: tail)) =
        some (copied, final)) :
    ∃ copiedScrutinee afterScrutinee copiedCases,
      (operations macros fuel).copy origin holes renames fresh (.list scrutineeItems) =
        some (copiedScrutinee, afterScrutinee) ∧
      copyCasesWithMacros macros fuel origin holes renames afterScrutinee
        (firstCase :: secondCase :: tail) = some (copiedCases, final) ∧
      copied = .list (.atom matchHead :: copiedScrutinee :: copiedCases) ∧
      Unique (counterPreservingCaseTokens copiedCases) ∧
      (∀ sourceToken, sourceToken % 3 = 1 →
        sourceToken ∉ counterPreservingCaseTokens copiedCases) ∧
      (∀ token, token ∈ counterPreservingCaseTokens copiedCases →
        ∃ counter, afterScrutinee < counter ∧ counter ≤ final ∧ token = 3 * counter + 2) := by
  obtain ⟨copiedScrutinee, afterScrutinee, copiedCases, scrutineeCopy, casesCopy, shape⟩ :=
    copyWithMacros_match_hole_head_cases_parts macros fuel origin fresh final holes renames
      matchHead scrutineeItems firstCase secondCase tail copied substitutedHead matchForm matchHole
      accepted
  have casesCopy' : copyCasesWithMacros macros fuel origin holes renames afterScrutinee
      (firstCase :: secondCase :: tail) = some (copiedCases, final) := by
    simpa [copyCasesWithMacros] using casesCopy
  have preserving := macroCounterSafeCases_preserving macros
    (firstCase :: secondCase :: tail) safe
  refine ⟨copiedScrutinee, afterScrutinee, copiedCases, scrutineeCopy, casesCopy', shape, ?_, ?_, ?_⟩
  · exact copyCasesWithMacros_preserving_tokens_unique macros fuel origin holes renames
      afterScrutinee (firstCase :: secondCase :: tail) copiedCases final preserving casesCopy'
  · intro sourceToken sourceClass
    exact copyCasesWithMacros_preserving_tokens_avoid_source macros fuel origin holes renames
      afterScrutinee sourceToken (firstCase :: secondCase :: tail) copiedCases final preserving
      casesCopy' sourceClass
  · intro token member
    exact copyCasesWithMacros_preserving_tokens_within_interval macros fuel origin holes renames
      afterScrutinee (firstCase :: secondCase :: tail) copiedCases final preserving casesCopy' token member

/-- Once a copied special-form `match` with a hole-valued head is actually
matched by a macro rule, its two-argument redex is represented by the
same-arity substituted-head candidate at the source template. This connects
the dispatcher decomposition above to the edge used by the rank proof. -/
theorem match_hole_head_output_to_template_static_call
    (rules : List (Nat × Tree)) (templateHoles : List String) (copyHoles : Holes)
    (template : Tree) (matchHead : Atom) (sourceArguments copiedArguments : List Tree)
    (childOrigin : Nat) (childRule childTemplate output : Tree) (childHoles : Holes)
    (matchHole : lookup matchHead.name copyHoles = some (.atom matchHead))
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (templateEq : template = .list (.atom matchHead :: sourceArguments))
    (outputShape : output = .list (.atom matchHead :: copiedArguments))
    (sameArity : sourceArguments.length = copiedArguments.length)
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles template target := by
  obtain ⟨ruleName, arity, callHead, arguments, signatureMatch, inputShape,
    nameMatch, arityMatch⟩ := successful_match_has_signature childRule output childHoles
      childTemplate childMatched
  have outputItems : Tree.atom callHead :: arguments = Tree.atom matchHead :: copiedArguments := by
    apply Tree.list.inj
    calc
      Tree.list (Tree.atom callHead :: arguments) = output := inputShape.symm
      _ = Tree.list (Tree.atom matchHead :: copiedArguments) := outputShape
  have headEq : callHead = matchHead := Tree.atom.inj (List.cons.inj outputItems).1
  have argsEq : arguments = copiedArguments := (List.cons.inj outputItems).2
  have ruleNameEq : ruleName = matchHead.name := by
    calc
      ruleName = callHead.name := nameMatch.symm
      _ = matchHead.name := congrArg Atom.name headEq
  have arityEq : arity = sourceArguments.length := by
    calc
      arity = arguments.length := arityMatch
      _ = copiedArguments.length := congrArg List.length argsEq
      _ = sourceArguments.length := sameArity.symm
  have signatureMatch' : signature childRule = some (matchHead.name, sourceArguments.length) := by
    rw [signatureMatch, ruleNameEq, arityEq]
  obtain ⟨target, found⟩ := findRule_of_member_signature matchHead.name sourceArguments.length 0 rules
    childOrigin childRule childMember signatureMatch'
  have candidate := findRule_mem_targetsOfArity matchHead.name sourceArguments.length 0 rules target found
  have headIsHole : matchHead.name ∈ templateHoles := by
    rw [holesAgree]
    exact lookup_some_implies_mem_keys matchHead.name copyHoles (.atom matchHead) matchHole
  refine ⟨target, ?_⟩
  rw [templateEq]
  exact StaticCall.substitutedHead headIsHole candidate

inductive BindingRows : List Tree → Prop where
  | nil : BindingRows []
  | cons (name typ value : Tree) (tail : List Tree) :
      BindingRows tail → BindingRows (.list [.list [name, typ], value] :: tail)

/-- Find a successful initializer copy at any binding index. Prefix binders
and values may consume counter space; the returned state is the one actually
used when the selected initializer is copied. -/
theorem copyBindingsWithMacros_extract_initializer (macros : List String)
    (fuel origin fresh final : Nat) (holes : Holes) (outside names finalNames : Renames)
    (before : List Tree) (name typ value : Tree) (suffix copied : List Tree)
    (beforeValid : BindingRows before)
    (accepted : copyBindingsWithMacros macros (fuel + before.length + 1) origin holes outside
      names fresh (before ++ .list [.list [name, typ], value] :: suffix) =
        some (copied, finalNames, final)) :
    ∃ namesBefore freshBefore copiedName namesAfter next copiedValue afterValue,
      binder holes namesBefore freshBefore name = some (copiedName, namesAfter, next) ∧
        (operations macros fuel).copy origin holes outside next value =
          some (copiedValue, afterValue) := by
  induction beforeValid generalizing fuel fresh names copied finalNames final with
  | nil =>
      have accepted' : copyBindingsWithMacros macros (fuel + 1) origin holes outside names fresh
          (.list [.list [name, typ], value] :: suffix) = some (copied, finalNames, final) := by
        simpa using accepted
      obtain ⟨copiedName, namesAfter, next, copiedValue, afterValue, _copiedSuffix,
        _tailNames, binderAccepted, valueAccepted, _tailAccepted, _shape⟩ :=
        copyBindingsWithMacros_cons_parts macros fuel origin holes outside names finalNames fresh
          final name typ value suffix copied accepted'
      exact ⟨names, fresh, copiedName, namesAfter, next, copiedValue, afterValue,
        binderAccepted, valueAccepted⟩
  | @cons previousName previousType previousValue tail _tailValid ih =>
      have accepted' : copyBindingsWithMacros macros
          (fuel + tail.length + 1 + 1) origin holes outside names fresh
          (.list [.list [previousName, previousType], previousValue] ::
            (tail ++ .list [.list [name, typ], value] :: suffix)) =
            some (copied, finalNames, final) := by
        simpa [List.length, Nat.add_assoc] using accepted
      obtain ⟨_copiedPreviousName, namesAfterPrevious, _nextAfterPrevious,
        _copiedPreviousValue, afterPreviousValue, copiedRest, restNames,
        _previousBinder, _previousValue, restAccepted, _outerShape⟩ :=
        copyBindingsWithMacros_cons_parts macros (fuel + tail.length + 1) origin holes outside
          names finalNames fresh final previousName previousType previousValue
          (tail ++ .list [.list [name, typ], value] :: suffix) copied accepted'
      have tailAccepted : copyBindingsWithMacros macros (fuel + tail.length + 1) origin holes
          outside namesAfterPrevious afterPreviousValue
          (tail ++ .list [.list [name, typ], value] :: suffix) =
            some (copiedRest, restNames, final) := by
        simpa [copyBindingsWithMacros] using restAccepted
      exact ih (fuel := fuel) (fresh := afterPreviousValue)
        (names := namesAfterPrevious) (copied := copiedRest) (finalNames := restNames)
        (final := final) tailAccepted

/-- For a literal zero-argument macro call at the root of a template, copying
preserves its static target candidate whenever the head is not substituted.
This composes call-site extraction with the corresponding local copy fact. -/
theorem copied_zero_arg_template_call_preserves_static_candidate
    (rules : List (Nat × Tree)) (macros : List String) (holes : List String)
    (copyHoles : Holes)
    (origin fresh final target : Nat) (head : Atom)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ holes)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (output : Tree)
    (copied : copyWithMacros macros 2 origin copyHoles [] fresh (.list [.atom head]) =
      some (output, final))
    (call : StaticCall rules holes (.list [.atom head]) target) :
    StaticCall rules holes output target := by
  have copySpec := copyWithMacros_preserves_zero_arg_macro_call macros origin fresh
    copyHoles head known lookupNone
  have pairEq := Option.some.inj (copied.symm.trans copySpec)
  have outputEq := congrArg Prod.fst pairEq
  have outputEq' : output = .list [.atom {head with origin := some origin}] := by
    simpa using outputEq
  rw [outputEq']
  cases call with
  | direct headNotHole candidate =>
      apply StaticCall.direct
      · simpa using notHole
      · simpa using candidate
  | substitutedHead headIsHole _ =>
      exact False.elim (notHole headIsHole)
  | nested childMember nestedCall =>
      simp at childMember
      subst_vars
      cases nestedCall

/-- If a macro step immediately follows copying a literal zero-argument call,
the step's candidate is also a static candidate at the original template site.
This remains local to a root call whose head is not substituted. -/
theorem zero_arg_template_call_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (origin childOrigin fresh final : Nat) (head : Atom)
    (childRule childTemplate output : Tree) (childHoles : Holes)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (copySucceeded : copyWithMacros macros 2 origin copyHoles [] fresh (.list [.atom head]) =
      some (output, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles (.list [.atom head]) target := by
  have copySpec := copyWithMacros_preserves_zero_arg_macro_call macros origin fresh
    copyHoles head known lookupNone
  have pairEq := Option.some.inj (copySucceeded.symm.trans copySpec)
  have outputEq : output = .list [.atom {head with origin := some origin}] := by
    simpa using congrArg Prod.fst pairEq
  rw [outputEq] at childMatched
  obtain ⟨target, nextCall⟩ := macro_step_input_is_static_candidate rules childOrigin
    childRule (.list [.atom {head with origin := some origin}]) childTemplate childHoles
    childMember childMatched
  refine ⟨target, ?_⟩
  cases nextCall with
  | direct _ candidate =>
      apply StaticCall.direct
      · exact notHole
      · simpa using candidate
  | substitutedHead impossible _ =>
      simp at impossible
  | nested member nestedCall =>
      simp at member
      subst_vars
      cases nestedCall

/-- General root-call correspondence through copying: when a literal macro
head is not a hole, copying preserves its name and the argument count, so a
successful next rule match supplies a candidate already present at the source
template call site. -/
theorem root_template_call_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames)
    (origin childOrigin fuel fresh final : Nat) (head : Atom)
    (arguments copiedArguments : List Tree) (childRule childTemplate output : Tree)
    (childHoles : Holes)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (argumentsCopied : copyManyWithMacros macros fuel origin copyHoles renames fresh arguments =
      some (copiedArguments, final))
    (copySucceeded : copyWithMacros macros (fuel + 1) origin copyHoles renames fresh
      (.list (.atom head :: arguments)) = some (output, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles (.list (.atom head :: arguments)) target := by
  have copySpec := copyWithMacros_preserves_root_macro_call macros fuel origin copyHoles renames
    fresh final head arguments copiedArguments known lookupNone argumentsCopied
  have pairEq := Option.some.inj (copySucceeded.symm.trans copySpec)
  have outputShape : output = .list
      (.atom {head with origin := some origin} :: copiedArguments) := by
    simpa using congrArg Prod.fst pairEq
  have childMatchedCopied : matchRule childRule
      (.list (.atom {head with origin := some origin} :: copiedArguments)) =
        some (childHoles, childTemplate) := by simpa [outputShape] using childMatched
  obtain ⟨ruleName, arity, callHead, callArguments, signatureMatch, inputShape,
    nameMatch, arityMatch⟩ := successful_match_has_signature childRule
      (.list (.atom {head with origin := some origin} :: copiedArguments)) childHoles
      childTemplate childMatchedCopied
  have shapeEq : Tree.list (Tree.atom callHead :: callArguments) =
      Tree.list (Tree.atom {head with origin := some origin} :: copiedArguments) :=
    inputShape.symm
  have itemsEq : Tree.atom callHead :: callArguments =
      Tree.atom {head with origin := some origin} :: copiedArguments := Tree.list.inj shapeEq
  injection itemsEq with atomEq argumentsEq
  have callHeadEq : callHead = {head with origin := some origin} := Tree.atom.inj atomEq
  have callNameEq : callHead.name = head.name := by simpa using congrArg Atom.name callHeadEq
  have ruleNameEq : ruleName = head.name := nameMatch.symm.trans callNameEq
  have callArityEq : arity = arguments.length := by
    calc
      arity = callArguments.length := arityMatch
      _ = copiedArguments.length := by rw [argumentsEq]
      _ = arguments.length := copyManyWithMacros_preserves_length macros fuel origin
        copyHoles renames fresh arguments copiedArguments final argumentsCopied
  rw [ruleNameEq, callArityEq] at signatureMatch
  obtain ⟨target, found⟩ := findRule_of_member_signature head.name arguments.length 0 rules
    childOrigin childRule childMember signatureMatch
  have candidate := findRule_mem_targetsOfSignature head.name arguments.length 0 rules target found
  exact ⟨target, StaticCall.direct notHole candidate⟩

/-- A literal call used as the body of a lambda remains associated with its
template callsite after parameter freshening. `bodyCopied` is the body-copy
operation performed by the lambda dispatcher, under its returned rename map. -/
theorem copyWithMacros_let_parts (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (letHead : Atom) (bindings : List Tree)
    (body copied : Tree) (originalNames : List String)
    (letForm : letHead.name = "let")
    (letNotMacro : macros.contains letHead.name = false)
    (letNotHole : (lookup letHead.name holes).isNone = true)
    (bindingNamesMatch : bindingNames bindings = some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom letHead, .list bindings, body]) = some (copied, final)) :
    ∃ copiedBindings names next copiedBody,
      (operations macros fuel).copyBindings origin holes renames renames fresh bindings =
          some (copiedBindings, names, next) ∧
        (operations macros fuel).copy origin holes names next body = some (copiedBody, final) ∧
        copied = .list [.atom letHead, .list copiedBindings, copiedBody] := by
  have letNotMacro' : macros.contains "let" = false := by
    simpa [letForm] using letNotMacro
  have letNotHole' : (lookup "let" holes).isNone = true := by
    simpa [letForm] using letNotHole
  simp [copyWithMacros, operations, letForm, named, letNotMacro', letNotHole',
    bindingNamesMatch, bindingsDistinct] at accepted
  rcases accepted with ⟨⟨copiedBindings, names, next⟩, bindingsCopied,
    ⟨copiedBody, bodyFinal⟩, bodyCopied, copiedShape, finalEq⟩
  change bodyFinal = final at finalEq
  cases finalEq
  refine ⟨copiedBindings, names, next, copiedBody, bindingsCopied, ?_, ?_⟩
  · simpa using bodyCopied
  · simpa using copiedShape.symm

/-- A successful let copy exposes its dedicated binding phase, whose binder
tokens are fresh and bounded by the counter returned to the body phase. The
initializer counter-preservation condition is exactly the condition used by
the binding token sequence theorem. -/
theorem copyWithMacros_let_binding_tokens_fresh
    (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (letHead : Atom) (bindings : List Tree)
    (body copied : Tree) (originalNames : List String)
    (letForm : letHead.name = "let")
    (letNotMacro : macros.contains letHead.name = false)
    (letNotHole : (lookup letHead.name holes).isNone = true)
    (bindingNamesMatch : bindingNames bindings = some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (safe : MacroCounterSafeBindingInputs macros bindings)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom letHead, .list bindings, body]) = some (copied, final)) :
    ∃ copiedBindings names next copiedBody,
      copyBindingsWithMacros macros fuel origin holes renames renames fresh bindings =
          some (copiedBindings, names, next) ∧
        Unique (bindingTokens copiedBindings) ∧
        (∀ sourceToken, sourceToken % 3 = 1 →
          sourceToken ∉ bindingTokens copiedBindings) ∧
        (∀ token, token ∈ bindingTokens copiedBindings →
          ∃ counter, fresh < counter ∧ counter ≤ next ∧ token = 3 * counter + 2) ∧
        (operations macros fuel).copy origin holes names next body =
          some (copiedBody, final) := by
  obtain ⟨copiedBindings, names, next, copiedBody, bindingCopy, bodyCopy, _shape⟩ :=
    copyWithMacros_let_parts macros fuel origin fresh final holes renames letHead bindings
      body copied originalNames letForm letNotMacro letNotHole bindingNamesMatch
      bindingsDistinct accepted
  have bindingCopy' : copyBindingsWithMacros macros fuel origin holes renames renames fresh
      bindings = some (copiedBindings, names, next) := by
    simpa [copyBindingsWithMacros] using bindingCopy
  have preserving := macroCounterSafeBindingInputs_preserving macros bindings safe
  refine ⟨copiedBindings, names, next, copiedBody, bindingCopy', ?_, ?_, ?_, bodyCopy⟩
  · exact copyBindingsWithMacros_preserving_tokens_unique macros fuel origin holes renames renames
      fresh bindings copiedBindings names next preserving bindingCopy'
  · intro sourceToken sourceClass
    exact copyBindingsWithMacros_preserving_tokens_avoid_source macros fuel origin holes renames
      renames fresh bindings copiedBindings names next sourceToken preserving bindingCopy' sourceClass
  · intro token member
    exact copyBindingsWithMacros_preserving_tokens_within_interval macros fuel origin holes renames
      renames fresh bindings copiedBindings names next preserving bindingCopy' token member

/-- A hole named `let` is dispatched as a special form before ordinary
head substitution, so a successful copy keeps the literal `let` head and
processes bindings and body through their dedicated operations. -/
theorem copyWithMacros_let_hole_head_parts (macros : List String)
    (fuel origin fresh final : Nat) (holes : Holes) (renames : Renames)
    (letHead : Atom) (bindings : List Tree) (body copied : Tree)
    (originalNames : List String) (substitutedHead : Tree)
    (letForm : letHead.name = "let")
    (letHole : lookup letHead.name holes = some substitutedHead)
    (bindingNamesMatch : bindingNames bindings = some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom letHead, .list bindings, body]) = some (copied, final)) :
    ∃ copiedBindings names next copiedBody,
      (operations macros fuel).copyBindings origin holes renames renames fresh bindings =
          some (copiedBindings, names, next) ∧
        (operations macros fuel).copy origin holes names next body =
          some (copiedBody, final) ∧
        copied = .list [.atom letHead, .list copiedBindings, copiedBody] := by
  have letHole' : lookup "let" holes = some substitutedHead := by
    simpa [letForm] using letHole
  have letNotHole : (lookup "let" holes).isNone = false := by simp [letHole']
  simp [copyWithMacros, operations, letForm, named, letNotHole,
    bindingNamesMatch, bindingsDistinct] at accepted
  rcases accepted with ⟨⟨copiedBindings, names, next⟩, bindingsCopied,
    ⟨copiedBody, bodyFinal⟩, bodyCopied, copiedShape, finalEq⟩
  change bodyFinal = final at finalEq
  cases finalEq
  refine ⟨copiedBindings, names, next, copiedBody, bindingsCopied, ?_, ?_⟩
  · simpa using bodyCopied
  · simpa using copiedShape.symm

/-- Let binding freshness is independent of whether the literal `let` head is
also present in the hole environment: the special-form dispatcher still
selects the binding-copy phase before considering ordinary head substitution. -/
theorem copyWithMacros_let_hole_binding_tokens_fresh
    (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (letHead : Atom) (bindings : List Tree)
    (body copied : Tree) (originalNames : List String) (substitutedHead : Tree)
    (letForm : letHead.name = "let")
    (letHole : lookup letHead.name holes = some substitutedHead)
    (bindingNamesMatch : bindingNames bindings = some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (safe : MacroCounterSafeBindingInputs macros bindings)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom letHead, .list bindings, body]) = some (copied, final)) :
    ∃ copiedBindings names next copiedBody,
      copyBindingsWithMacros macros fuel origin holes renames renames fresh bindings =
          some (copiedBindings, names, next) ∧
        Unique (bindingTokens copiedBindings) ∧
        (∀ sourceToken, sourceToken % 3 = 1 →
          sourceToken ∉ bindingTokens copiedBindings) ∧
        (∀ token, token ∈ bindingTokens copiedBindings →
          ∃ counter, fresh < counter ∧ counter ≤ next ∧ token = 3 * counter + 2) ∧
        (operations macros fuel).copy origin holes names next body =
          some (copiedBody, final) := by
  obtain ⟨copiedBindings, names, next, copiedBody, bindingCopy, bodyCopy, _shape⟩ :=
    copyWithMacros_let_hole_head_parts macros fuel origin fresh final holes renames letHead
      bindings body copied originalNames substitutedHead letForm letHole bindingNamesMatch
      bindingsDistinct accepted
  have bindingCopy' : copyBindingsWithMacros macros fuel origin holes renames renames fresh
      bindings = some (copiedBindings, names, next) := by
    simpa [copyBindingsWithMacros] using bindingCopy
  have preserving := macroCounterSafeBindingInputs_preserving macros bindings safe
  refine ⟨copiedBindings, names, next, copiedBody, bindingCopy', ?_, ?_, ?_, bodyCopy⟩
  · exact copyBindingsWithMacros_preserving_tokens_unique macros fuel origin holes renames renames
      fresh bindings copiedBindings names next preserving bindingCopy'
  · intro sourceToken sourceClass
    exact copyBindingsWithMacros_preserving_tokens_avoid_source macros fuel origin holes renames
      renames fresh bindings copiedBindings names next sourceToken preserving bindingCopy' sourceClass
  · intro token member
    exact copyBindingsWithMacros_preserving_tokens_within_interval macros fuel origin holes renames
      renames fresh bindings copiedBindings names next preserving bindingCopy' token member

/-- A subsequent rule matching a copied `let` special form with a hole head
is represented by the substituted-head edge from its source template. -/
theorem let_hole_head_call_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (fuel origin childOrigin fresh final : Nat) (letHead : Atom)
    (bindings : List Tree) (body output childRule childTemplate : Tree)
    (originalNames : List String) (substitutedHead : Tree) (childHoles : Holes)
    (letForm : letHead.name = "let")
    (letHole : lookup letHead.name copyHoles = some substitutedHead)
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (bindingNamesMatch : bindingNames bindings = some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (copySucceeded : copyWithMacros macros (fuel + 1) origin copyHoles [] fresh
      (.list [.atom letHead, .list bindings, body]) = some (output, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom letHead, .list bindings, body]) target := by
  obtain ⟨copiedBindings, names, next, copiedBody, _bindingsCopied, _bodyCopied,
    outputShape⟩ := copyWithMacros_let_hole_head_parts macros fuel origin fresh final
      copyHoles [] letHead bindings body output originalNames substitutedHead
      letForm letHole bindingNamesMatch bindingsDistinct copySucceeded
  have headIsHole : letHead.name ∈ templateHoles := by
    rw [holesAgree]
    exact lookup_some_implies_mem_keys letHead.name copyHoles substitutedHead letHole
  obtain ⟨ruleName, arity, callHead, callArguments, signatureMatch, inputShape,
    nameMatch, arityMatch⟩ := successful_match_has_signature childRule output childHoles
      childTemplate childMatched
  have sourceShape : output = Tree.list
      (Tree.atom letHead :: Tree.list copiedBindings :: copiedBody :: []) := outputShape
  have listEq : Tree.atom letHead :: Tree.list copiedBindings :: copiedBody :: [] =
      Tree.atom callHead :: callArguments := by
    have listTreesEq : Tree.list
        (Tree.atom letHead :: Tree.list copiedBindings :: copiedBody :: []) =
          Tree.list (Tree.atom callHead :: callArguments) := sourceShape.symm.trans inputShape
    exact Tree.list.inj listTreesEq
  have headEq : letHead = callHead := by
    exact Tree.atom.inj (List.cons.inj listEq).1
  have argsEq : [Tree.list copiedBindings, copiedBody] = callArguments :=
    (List.cons.inj listEq).2
  have nameEq : ruleName = letHead.name := by
    calc
      ruleName = callHead.name := nameMatch.symm
      _ = letHead.name := by rw [← headEq]
  have arityEq : arity = 2 := by
    rw [arityMatch, ← argsEq]
    rfl
  rw [nameEq, arityEq] at signatureMatch
  obtain ⟨target, found⟩ := findRule_of_member_signature letHead.name 2 0 rules
    childOrigin childRule childMember signatureMatch
  have candidate := findRule_mem_targetsOfArity letHead.name 2 0 rules target found
  exact ⟨target, StaticCall.substitutedHead headIsHole candidate⟩

/-- A literal call used as the body of a lambda remains associated with its
template callsite after parameter freshening. `bodyCopied` is the body-copy
operation performed by the lambda dispatcher, under its returned rename map. -/
theorem copyWithMacros_lambda_parts (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (lambdaHead : Atom)
    (parameters : List Tree) (result body copied : Tree) (originalNames : List String)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaNotMacro : macros.contains lambdaHead.name = false)
    (lambdaNotHole : (lookup lambdaHead.name holes).isNone = true)
    (parameterNamesMatch : parameterNames parameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom lambdaHead, .list parameters, result, body]) = some (copied, final)) :
    ∃ copiedParameters names next copiedBody,
      (operations macros fuel).copyParameters holes renames fresh parameters =
          some (copiedParameters, names, next) ∧
        (operations macros fuel).copy origin holes names next body = some (copiedBody, final) ∧
        copied = .list [.atom lambdaHead, .list copiedParameters, result, copiedBody] := by
  have lambdaNotMacro' : macros.contains "lambda" = false := by
    simpa [lambdaForm] using lambdaNotMacro
  have lambdaNotHole' : (lookup "lambda" holes).isNone = true := by
    simpa [lambdaForm] using lambdaNotHole
  simp [copyWithMacros, operations, lambdaForm, named, lambdaNotMacro', lambdaNotHole',
    parameterNamesMatch, parametersDistinct] at accepted
  rcases accepted with ⟨⟨copiedParameters, names, next⟩, parametersCopied,
    ⟨copiedBody, bodyFinal⟩, bodyCopied, copiedShape, finalEq⟩
  change bodyFinal = final at finalEq
  cases finalEq
  refine ⟨copiedParameters, names, next, copiedBody, parametersCopied, ?_, ?_⟩
  · simpa using bodyCopied
  · simpa using copiedShape.symm

/-- A successful full lambda copy with an atomic body ends at the counter
returned by parameter freshening. This exposes the exact dispatcher-to-phase
counter relation for a real `copyWithMacros` call. -/
theorem copyWithMacros_lambda_atomic_body_final_counter
    (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (lambdaHead : Atom)
    (parameters : List Tree) (result : Tree) (bodyAtom : Atom) (copied : Tree)
    (originalNames : List String)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaNotMacro : macros.contains lambdaHead.name = false)
    (lambdaNotHole : (lookup lambdaHead.name holes).isNone = true)
    (parameterNamesMatch : parameterNames parameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom lambdaHead, .list parameters, result, .atom bodyAtom]) =
        some (copied, final)) :
    final = fresh + parameters.length := by
  obtain ⟨copiedParameters, names, next, copiedBody, parameterCopy, bodyCopy, _shape⟩ :=
    copyWithMacros_lambda_parts macros fuel origin fresh final holes renames lambdaHead
      parameters result (.atom bodyAtom) copied originalNames lambdaForm lambdaNotMacro
      lambdaNotHole parameterNamesMatch parametersDistinct accepted
  have parameterCounter := copyParameters_counter_with_macros macros fuel holes renames fresh
    parameters copiedParameters names next parameterCopy
  have bodyCounter := copyWithMacros_atom_keeps_counter macros fuel origin holes names next
    bodyAtom copiedBody final bodyCopy
  omega

/-- A successful full let copy with counter-preserving initializers and body
advances the counter by exactly the number of binding names. -/
theorem copyWithMacros_let_counter_preserving_body_final_counter
    (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (letHead : Atom)
    (bindings : List Tree) (body copied : Tree)
    (originalNames : List String)
    (letForm : letHead.name = "let")
    (letNotMacro : macros.contains letHead.name = false)
    (letNotHole : (lookup letHead.name holes).isNone = true)
    (bindingNamesMatch : bindingNames bindings = some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (safe : MacroCounterSafeBindingInputs macros bindings)
    (bodyPreserving : CounterPreservingInitializer macros body)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom letHead, .list bindings, body]) =
        some (copied, final)) :
    final = fresh + bindings.length := by
  obtain ⟨copiedBindings, names, next, copiedBody, bindingCopy, bodyCopy, _shape⟩ :=
    copyWithMacros_let_parts macros fuel origin fresh final holes renames letHead
      bindings body copied originalNames letForm letNotMacro letNotHole
      bindingNamesMatch bindingsDistinct accepted
  have bindingCounter := copyBindingsWithMacros_preserving_counter macros fuel origin
    holes renames renames fresh bindings copiedBindings names next
    (macroCounterSafeBindingInputs_preserving macros bindings safe) bindingCopy
  have bodyCounter := bodyPreserving fuel origin holes names next copiedBody final bodyCopy
  omega

/-- Freshness of lambda parameters follows from an accepted full lambda copy,
not merely from an isolated call to `copyParameters`. The dispatcher
decomposition exposes the exact parameter-copy result consumed by the
phase-level token sequence theorem. -/
private theorem operations_copyParameters_macro_independent (macros : List String)
    (fuel : Nat) :
    (operations macros fuel).copyParameters = (operations [] fuel).copyParameters := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      funext holes renames fresh trees
      simp [operations, ih]

theorem copyWithMacros_lambda_parameter_tokens_fresh
    (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (lambdaHead : Atom)
    (parameters : List Tree) (result body copied : Tree) (originalNames : List String)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaNotMacro : macros.contains lambdaHead.name = false)
    (lambdaNotHole : (lookup lambdaHead.name holes).isNone = true)
    (parameterNamesMatch : parameterNames parameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom lambdaHead, .list parameters, result, body]) = some (copied, final)) :
    ∃ copiedParameters names next copiedBody,
      copyParameters fuel holes renames fresh parameters =
          some (copiedParameters, names, next) ∧
        Unique (parameterTokens copiedParameters) ∧
        (∀ sourceToken, sourceToken % 3 = 1 →
          sourceToken ∉ parameterTokens copiedParameters) ∧
        (∀ token, token ∈ parameterTokens copiedParameters →
          ∃ counter, fresh < counter ∧ counter ≤ next ∧ token = 3 * counter + 2) ∧
        (operations macros fuel).copy origin holes names next body =
          some (copiedBody, final) := by
  obtain ⟨copiedParameters, names, next, copiedBody, parameterCopy, bodyCopy, _shape⟩ :=
    copyWithMacros_lambda_parts macros fuel origin fresh final holes renames lambdaHead
      parameters result body copied originalNames lambdaForm lambdaNotMacro lambdaNotHole
      parameterNamesMatch parametersDistinct accepted
  have parameterCopyDefault : copyParameters fuel holes renames fresh parameters =
      some (copiedParameters, names, next) := by
    change (operations [] fuel).copyParameters holes renames fresh parameters = _
    rw [← operations_copyParameters_macro_independent macros fuel]
    exact parameterCopy
  refine ⟨copiedParameters, names, next, copiedBody, parameterCopyDefault, ?_, ?_, ?_, bodyCopy⟩
  · exact copyParameters_tokens_unique fuel holes renames fresh parameters copiedParameters
      names next parameterCopyDefault
  · intro sourceToken sourceClass
    exact copyParameters_tokens_avoid_source fuel holes renames fresh parameters copiedParameters
      names next sourceToken parameterCopyDefault sourceClass
  · intro token member
    exact copyParameters_tokens_within_interval fuel holes renames fresh parameters copiedParameters
      names next parameterCopyDefault token member

/-- A hole whose spelling is `lambda` is still interpreted by the special-form
dispatcher before ordinary head substitution. The successful copy therefore
retains the literal lambda head and copies its body under the freshened
parameter environment; it cannot produce a macro call by substituting that
head hole. -/
theorem copyWithMacros_lambda_hole_head_parts (macros : List String)
    (fuel origin fresh final : Nat) (holes : Holes) (renames : Renames)
    (lambdaHead : Atom) (parameters : List Tree) (result body copied : Tree)
    (originalNames : List String) (substitutedHead : Tree)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaHole : lookup lambdaHead.name holes = some substitutedHead)
    (parameterNamesMatch : parameterNames parameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom lambdaHead, .list parameters, result, body]) = some (copied, final)) :
    ∃ copiedParameters names next copiedBody,
      (operations macros fuel).copyParameters holes renames fresh parameters =
          some (copiedParameters, names, next) ∧
        (operations macros fuel).copy origin holes names next body =
          some (copiedBody, final) ∧
        copied = .list [.atom lambdaHead, .list copiedParameters, result, copiedBody] := by
  have lambdaHole' : lookup "lambda" holes = some substitutedHead := by
    simpa [lambdaForm] using lambdaHole
  have lambdaNotHole : (lookup "lambda" holes).isNone = false := by
    simp [lambdaHole']
  simp [copyWithMacros, operations, lambdaForm, named, lambdaNotHole,
    parameterNamesMatch, parametersDistinct] at accepted
  rcases accepted with ⟨⟨copiedParameters, names, next⟩, parametersCopied,
    ⟨copiedBody, bodyFinal⟩, bodyCopied, copiedShape, finalEq⟩
  change bodyFinal = final at finalEq
  cases finalEq
  refine ⟨copiedParameters, names, next, copiedBody, parametersCopied, ?_, ?_⟩
  · simpa using bodyCopied
  · simpa using copiedShape.symm

/-- Parameter binder freshness also holds when the literal `lambda` head is
in the hole environment. Special-form dispatch keeps the head and runs the
same binder phase, so the full accepted copy still yields the counter proof. -/
theorem copyWithMacros_lambda_hole_parameter_tokens_fresh
    (macros : List String) (fuel origin fresh final : Nat)
    (holes : Holes) (renames : Renames) (lambdaHead : Atom)
    (parameters : List Tree) (result body copied : Tree) (originalNames : List String)
    (substitutedHead : Tree) (lambdaForm : lambdaHead.name = "lambda")
    (lambdaHole : lookup lambdaHead.name holes = some substitutedHead)
    (parameterNamesMatch : parameterNames parameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom lambdaHead, .list parameters, result, body]) = some (copied, final)) :
    ∃ copiedParameters names next copiedBody,
      copyParameters fuel holes renames fresh parameters =
          some (copiedParameters, names, next) ∧
        Unique (parameterTokens copiedParameters) ∧
        (∀ sourceToken, sourceToken % 3 = 1 →
          sourceToken ∉ parameterTokens copiedParameters) ∧
        (∀ token, token ∈ parameterTokens copiedParameters →
          ∃ counter, fresh < counter ∧ counter ≤ next ∧ token = 3 * counter + 2) ∧
        (operations macros fuel).copy origin holes names next body =
          some (copiedBody, final) := by
  obtain ⟨copiedParameters, names, next, copiedBody, parameterCopy, bodyCopy, _shape⟩ :=
    copyWithMacros_lambda_hole_head_parts macros fuel origin fresh final holes renames lambdaHead
      parameters result body copied originalNames substitutedHead lambdaForm lambdaHole
      parameterNamesMatch parametersDistinct accepted
  have parameterCopyDefault : copyParameters fuel holes renames fresh parameters =
      some (copiedParameters, names, next) := by
    change (operations [] fuel).copyParameters holes renames fresh parameters = _
    rw [← operations_copyParameters_macro_independent macros fuel]
    exact parameterCopy
  refine ⟨copiedParameters, names, next, copiedBody, parameterCopyDefault, ?_, ?_, ?_, bodyCopy⟩
  · exact copyParameters_tokens_unique fuel holes renames fresh parameters copiedParameters
      names next parameterCopyDefault
  · intro sourceToken sourceClass
    exact copyParameters_tokens_avoid_source fuel holes renames fresh parameters copiedParameters
      names next sourceToken parameterCopyDefault sourceClass
  · intro token member
    exact copyParameters_tokens_within_interval fuel holes renames fresh parameters copiedParameters
      names next parameterCopyDefault token member

/-- If a subsequent expansion step matches a copied lambda-shaped special
form whose literal head is also a template hole, that step is represented by
the conservative substituted-head edge from the original template node. -/
theorem lambda_hole_head_call_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (fuel origin childOrigin fresh final : Nat) (lambdaHead : Atom)
    (parameters : List Tree) (result body output childRule childTemplate : Tree)
    (originalNames : List String) (substitutedHead : Tree) (childHoles : Holes)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaHole : lookup lambdaHead.name copyHoles = some substitutedHead)
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (parameterNamesMatch : parameterNames parameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (copySucceeded : copyWithMacros macros (fuel + 1) origin copyHoles [] fresh
      (.list [.atom lambdaHead, .list parameters, result, body]) = some (output, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom lambdaHead, .list parameters, result, body]) target := by
  obtain ⟨copiedParameters, names, next, copiedBody, _parametersCopied, _bodyCopied,
    outputShape⟩ := copyWithMacros_lambda_hole_head_parts macros fuel origin fresh final
      copyHoles [] lambdaHead parameters result body output originalNames substitutedHead
      lambdaForm lambdaHole parameterNamesMatch parametersDistinct copySucceeded
  have headIsHole : lambdaHead.name ∈ templateHoles := by
    rw [holesAgree]
    exact lookup_some_implies_mem_keys lambdaHead.name copyHoles substitutedHead lambdaHole
  obtain ⟨ruleName, arity, callHead, callArguments, signatureMatch, inputShape,
    nameMatch, arityMatch⟩ := successful_match_has_signature childRule output childHoles
      childTemplate childMatched
  have sourceShape : output = .list
      (.atom lambdaHead :: .list copiedParameters :: result :: copiedBody :: []) := outputShape
  have listEq : .atom lambdaHead :: .list copiedParameters :: result :: copiedBody :: [] =
      .atom callHead :: callArguments := by
    have listTreesEq : Tree.list (.atom lambdaHead :: Tree.list copiedParameters :: result ::
        copiedBody :: []) = Tree.list (.atom callHead :: callArguments) :=
      sourceShape.symm.trans inputShape
    exact Tree.list.inj listTreesEq
  have headEq : lambdaHead = callHead := by
    have parts := List.cons.inj listEq
    exact Tree.atom.inj parts.1
  have argsEq : [.list copiedParameters, result, copiedBody] = callArguments := by
    exact (List.cons.inj listEq).2
  have nameEq : ruleName = lambdaHead.name := by
    calc
      ruleName = callHead.name := nameMatch.symm
      _ = lambdaHead.name := by rw [← headEq]
  have arityEq : arity = 3 := by
    rw [arityMatch, ← argsEq]
    rfl
  rw [nameEq, arityEq] at signatureMatch
  obtain ⟨target, found⟩ := findRule_of_member_signature lambdaHead.name 3 0 rules
    childOrigin childRule childMember signatureMatch
  have candidate := findRule_mem_targetsOfArity lambdaHead.name 3 0 rules target found
  exact ⟨target, StaticCall.substitutedHead headIsHole candidate⟩

/-- If lambda parameters are well-shaped and the copied body preserves its
counter, the successful lambda copy consumes exactly its parameter binder
count. -/
theorem copyWithMacros_lambda_counter_preserving_body (macros : List String)
    (fuel origin fresh final : Nat) (holes : Holes) (renames : Renames)
    (lambdaHead : Atom) (parameters : List Tree) (result body copied : Tree)
    (originalNames : List String)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaNotMacro : macros.contains lambdaHead.name = false)
    (lambdaNotHole : (lookup lambdaHead.name holes).isNone = true)
    (parameterNamesMatch : parameterNames parameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (bodyPreserving : CMacroCopy.CounterPreservingInitializer macros body)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom lambdaHead, .list parameters, result, body]) = some (copied, final)) :
    final = fresh + parameters.length := by
  obtain ⟨copiedParameters, names, next, copiedBody, parametersCopied, bodyCopied, _shape⟩ :=
    copyWithMacros_lambda_parts macros fuel origin fresh final holes renames lambdaHead
      parameters result body copied originalNames lambdaForm lambdaNotMacro lambdaNotHole
      parameterNamesMatch parametersDistinct accepted
  have parameterCounter : next = fresh + parameters.length := by
    exact CMacroCopy.copyParameters_counter_with_macros macros fuel holes renames fresh
      parameters copiedParameters names next parametersCopied
  have bodyCounter : final = next :=
    bodyPreserving fuel origin holes names next copiedBody final bodyCopied
  omega

/-- A lambda with an atom body consumes exactly one fresh counter for each
parameter. This is a first binder-bearing initializer case for composing copy
freshness; it does not cover nested or effectful bodies. -/
theorem copyWithMacros_lambda_atom_body_counter (macros : List String)
    (fuel origin fresh final : Nat) (holes : Holes) (renames : Renames)
    (lambdaHead bodyAtom : Atom) (parameters : List Tree) (result copied : Tree)
    (originalNames : List String)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaNotMacro : macros.contains lambdaHead.name = false)
    (lambdaNotHole : (lookup lambdaHead.name holes).isNone = true)
    (parameterNamesMatch : parameterNames parameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list [.atom lambdaHead, .list parameters, result, .atom bodyAtom]) =
        some (copied, final)) :
    final = fresh + parameters.length := by
  obtain ⟨copiedParameters, names, next, copiedBody, parametersCopied, bodyCopied, _shape⟩ :=
    copyWithMacros_lambda_parts macros fuel origin fresh final holes renames lambdaHead
      parameters result (.atom bodyAtom) copied originalNames lambdaForm lambdaNotMacro
      lambdaNotHole parameterNamesMatch parametersDistinct accepted
  have parameterCounter : next = fresh + parameters.length := by
    exact CMacroCopy.copyParameters_counter_with_macros macros fuel holes renames fresh
      parameters copiedParameters names next parametersCopied
  have bodyCounter : final = next := by
    cases fuel with
    | zero => simp [CMacroCopy.operations] at bodyCopied
    | succ fuel =>
        cases renamed : lookup bodyAtom.name names with
        | some renamed =>
            simp [CMacroCopy.operations, renamed] at bodyCopied
            exact bodyCopied.2.symm
        | none =>
            cases argument : lookup bodyAtom.name holes with
            | some argument =>
                simp [CMacroCopy.operations, renamed, argument] at bodyCopied
                exact bodyCopied.2.symm
            | none =>
                simp [CMacroCopy.operations, renamed, argument] at bodyCopied
                exact bodyCopied.2.symm
  omega

theorem lambda_body_literal_call_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin fuel fresh final : Nat)
    (lambdaHead head : Atom) (lambdaParameters : List Tree) (result : Tree)
    (arguments : List Tree) (output childRule childTemplate : Tree)
    (childHoles : Holes)
    (lambdaForm : lambdaHead.name = "lambda")
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (bodyCopied : copyWithMacros macros (fuel + 1) origin copyHoles renames fresh
      (.list (.atom head :: arguments)) = some (output, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom lambdaHead, .list lambdaParameters, result,
        .list (.atom head :: arguments)]) target := by
  obtain ⟨copiedArguments, argumentsCopied, _callShape⟩ :=
    copyWithMacros_root_macro_call_parts macros fuel origin copyHoles renames fresh final
      head arguments output known lookupNone bodyCopied
  obtain ⟨target, callSite⟩ := root_template_call_to_next_macro_step rules macros templateHoles
    copyHoles renames origin childOrigin fuel fresh final head arguments copiedArguments childRule
    childTemplate output childHoles known notHole lookupNone argumentsCopied bodyCopied
    childMember childMatched
  refine ⟨target, StaticCall.nested ?_ callSite⟩
  simp [lambdaForm]

/-- A literal macro call in the first element of an ordinary copied list is a
one-level context case of the root correspondence. -/
theorem nested_literal_call_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (origin childOrigin fuel fresh final : Nat) (head : Atom)
    (arguments copiedArguments tail copied : List Tree) (middle : Nat)
    (childRule childTemplate : Tree) (childHoles : Holes)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (argumentsCopied : copyManyWithMacros macros fuel origin copyHoles [] fresh arguments =
      some (copiedArguments, middle))
    (outerCopied : copyManyWithMacros macros (fuel + 2) origin copyHoles [] fresh
      (.list (.atom head :: arguments) :: tail) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule
      (.list (.atom {head with origin := some origin} :: copiedArguments)) =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list (.list (.atom head :: arguments) :: tail)) target := by
  obtain ⟨copiedCall, _copiedTail, outerMiddle, callCopy, _tailCopy, _outerShape⟩ :=
    copyManyWithMacros_cons_parts macros (fuel + 2) origin copyHoles [] fresh
      (.list (.atom head :: arguments)) tail copied final outerCopied
  have callCopy' : copyWithMacros macros (fuel + 1) origin copyHoles [] fresh
      (.list (.atom head :: arguments)) = some (copiedCall, outerMiddle) := by
    change (operations macros (fuel + 1)).copy origin copyHoles [] fresh
      (.list (.atom head :: arguments)) = some (copiedCall, outerMiddle)
    exact callCopy
  have rootCopy := copyWithMacros_preserves_root_macro_call macros fuel origin copyHoles []
    fresh middle head arguments copiedArguments known lookupNone argumentsCopied
  have pairEq := Option.some.inj (callCopy'.symm.trans rootCopy)
  have callEq : copiedCall = .list
      (.atom {head with origin := some origin} :: copiedArguments) := by
    simpa using congrArg Prod.fst pairEq
  have middleAgrees : outerMiddle = middle := by
    exact congrArg Prod.snd pairEq
  have callCopyForRoot : copyWithMacros macros (fuel + 1) origin copyHoles [] fresh
      (.list (.atom head :: arguments)) = some (copiedCall, middle) := by
    simpa [middleAgrees] using callCopy'
  have childMatchedActual : matchRule childRule copiedCall =
      some (childHoles, childTemplate) := by rw [callEq]; exact childMatched
  obtain ⟨target, sourceCall⟩ := root_template_call_to_next_macro_step rules macros
    templateHoles copyHoles [] origin childOrigin fuel fresh middle head arguments copiedArguments
    childRule childTemplate copiedCall childHoles known notHole lookupNone argumentsCopied
    callCopyForRoot childMember childMatchedActual
  refine ⟨target, StaticCall.nested ?_ sourceCall⟩
  simp

/-- A literal call at any sibling position in an ordinary copied list remains
linked to the next macro step. Earlier siblings consume copy fuel, but the
selected child's remaining fuel is kept explicit in the premise. -/
theorem literal_call_at_list_index_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin fuel fresh final : Nat) (head : Atom)
    (arguments beforeItems afterItems copied : List Tree)
    (childFuel : Nat) (childRule : Tree)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (fuelMatches : childFuel = fuel + 1)
    (outerCopied : copyManyWithMacros macros (childFuel + beforeItems.length + 1)
      origin copyHoles renames fresh
      (beforeItems ++ .list (.atom head :: arguments) :: afterItems) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedBefore copiedCall copiedAfter,
      copied = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)) target := by
  obtain ⟨copiedBefore, copiedCall, copiedAfter, callStart, callFinal, callCopy,
    _afterCopy, outputShape⟩ :=
    copyManyWithMacros_extract_element macros childFuel origin fresh copyHoles renames
      beforeItems (.list (.atom head :: arguments)) afterItems copied final outerCopied
  obtain ⟨childHoles, childTemplate, childMatched⟩ :=
    copiedChildMatches copiedBefore copiedCall copiedAfter outputShape
  have callCopy' : copyWithMacros macros (fuel + 1) origin copyHoles renames callStart
      (.list (.atom head :: arguments)) = some (copiedCall, callFinal) := by
    simpa [fuelMatches] using callCopy
  obtain ⟨copiedArguments, argumentsCopied, _callShape⟩ :=
    copyWithMacros_root_macro_call_parts macros fuel origin copyHoles renames callStart callFinal
      head arguments copiedCall known lookupNone callCopy'
  obtain ⟨target, sourceCall⟩ := root_template_call_to_next_macro_step rules macros
    templateHoles copyHoles renames origin childOrigin fuel callStart callFinal head arguments copiedArguments
    childRule childTemplate copiedCall childHoles known notHole lookupNone argumentsCopied
    callCopy' childMember childMatched
  refine ⟨target, StaticCall.nested ?_ sourceCall⟩
  apply mem_append_right
  simp

/-- Certified local-copy variant for one sibling callsite. A successful copy
of that source call plus an accepted child `checkStep` is enough to identify
the source template's static edge; unrelated sibling match premises are not
needed. This does not claim that the local counter came from a full parent
copy traversal. -/
theorem literal_call_at_list_index_to_certified_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin fuel callStart callFinal childFuel childFresh childFinal : Nat)
    (head : Atom) (arguments beforeItems afterItems : List Tree) (copiedCall : Tree)
    (childRule childOutput : Tree)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (fuelMatches : childFuel = fuel + 1)
    (callCopy : copyWithMacros macros childFuel origin copyHoles renames callStart
      (.list (.atom head :: arguments)) = some (copiedCall, callFinal))
    (childStepAccepted : NLisp.ExpansionCertificate.checkStep rules childOrigin childFuel
      childFresh childFinal childRule copiedCall childOutput = true) :
    ∃ target, StaticCall rules templateHoles
      (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)) target := by
  obtain ⟨childHoles, childTemplate, _member, childMatched, _copied⟩ :=
    NLisp.ExpansionCertificate.checkStep_sound childStepAccepted
  have callCopy' : copyWithMacros macros (fuel + 1) origin copyHoles renames callStart
      (.list (.atom head :: arguments)) = some (copiedCall, callFinal) := by
    simpa [fuelMatches] using callCopy
  obtain ⟨copiedArguments, argumentsCopied, _callShape⟩ :=
    copyWithMacros_root_macro_call_parts macros fuel origin copyHoles renames callStart callFinal
      head arguments copiedCall known lookupNone callCopy'
  obtain ⟨target, sourceCall⟩ := root_template_call_to_next_macro_step rules macros
    templateHoles copyHoles renames origin childOrigin fuel callStart callFinal head arguments
    copiedArguments childRule childTemplate copiedCall childHoles known notHole lookupNone
    argumentsCopied callCopy' _member childMatched
  refine ⟨target, StaticCall.nested ?_ sourceCall⟩
  apply mem_append_right
  simp

/- A recursive description of literal macro calls beneath ordinary copied
lists. The cost records the copy fuel needed for every sibling scan and list
wrapper along the selected path. -/
inductive LiteralCallSite (macros : List String) (head : Atom)
    (arguments : List Tree) : List Tree → Nat → Prop where
  | direct (before after : List Tree) :
      LiteralCallSite macros head arguments
        (before ++ .list (.atom head :: arguments) :: after) (before.length + 2)
  | nested (before after innerItems : List Tree) (innerCost : Nat)
      (headSafe : counterNeutralListHead macros innerItems = true)
      (inner : LiteralCallSite macros head arguments innerItems innerCost) :
      LiteralCallSite macros head arguments
        (before ++ .list innerItems :: after) (innerCost + before.length + 2)

/-- Arbitrary-depth copy-to-callsite correspondence for a literal macro head.
Each nested list on the path follows the ordinary copyMany branch; the premise
that the selected copied call matches a child rule is kept explicit. -/
theorem literal_call_site_to_next_macro_step
    (rules : List (Nat × Tree)) (macros : List String)
    (templateHoles : List String) (copyHoles : Holes) (renames : Renames)
    (origin childOrigin copyFuel fresh final : Nat) (head : Atom)
    (arguments copied : List Tree) (childRule : Tree)
    (site : LiteralCallSite macros head arguments items cost)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (outerCopied : copyManyWithMacros macros (copyFuel + cost) origin copyHoles renames fresh
      items = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles (.list items) target := by
  induction site generalizing fresh copied final with
  | direct before after =>
      exact literal_call_at_list_index_to_next_macro_step rules macros templateHoles copyHoles
        renames origin childOrigin copyFuel fresh final head arguments before after copied
        (copyFuel + 1) childRule known notHole lookupNone rfl
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using outerCopied) childMember
        (fun copiedBefore copiedCall copiedAfter shape =>
          copiedChildMatches copied copiedBefore copiedCall copiedAfter shape)
  | @nested before after innerItems innerCost headSafe _innerSite ih =>
      let innerFuel := copyFuel + innerCost
      have outerCopiedAtChild : copyManyWithMacros macros
          ((innerFuel + 1) + before.length + 1) origin copyHoles renames fresh
          (before ++ .list innerItems :: after) = some (copied, final) := by
        simpa [innerFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using outerCopied
      obtain ⟨copiedPrefix, copiedNested, copiedSuffix, beforeCounter, outerMiddle,
        nestedCopy, _suffixCopy, outputShape⟩ :=
        copyManyWithMacros_extract_element macros (innerFuel + 1) origin fresh copyHoles renames
          before (.list innerItems) after copied final outerCopiedAtChild
      have nestedCopy' : (operations macros (innerFuel + 1)).copy origin copyHoles renames beforeCounter
          (.list innerItems) = some (copiedNested, outerMiddle) := by
        simpa [innerFuel, Nat.add_assoc] using nestedCopy
      rw [copyNeutralList_uses_copyMany macros innerFuel origin copyHoles renames
        beforeCounter innerItems headSafe] at nestedCopy'
      have innerResult : ∃ copiedInner middle,
          copyManyWithMacros macros innerFuel origin copyHoles renames beforeCounter innerItems =
            some (copiedInner, middle) ∧ copiedNested = .list copiedInner ∧ middle = outerMiddle := by
        obtain ⟨innerPair, innerRun, outputRun⟩ := option_bind_some nestedCopy'
        rcases innerPair with ⟨copiedInner, middle⟩
        have outputEq := Option.some.inj outputRun
        have copiedEq := congrArg Prod.fst outputEq
        have counterEq := congrArg Prod.snd outputEq
        have innerAccepted : copyManyWithMacros macros innerFuel origin copyHoles renames
            beforeCounter innerItems = some (copiedInner, middle) := by
          simpa [copyManyWithMacros] using innerRun
        exact ⟨copiedInner, middle, innerAccepted, by simpa using copiedEq.symm,
          by simpa using counterEq⟩
      obtain ⟨copiedInner, middle, innerCopy, copiedNestedEq, middleEq⟩ := innerResult
      subst copiedNested
      subst outerMiddle
      obtain ⟨target, innerCall⟩ := ih (fresh := beforeCounter) (copied := copiedInner)
        (final := middle) innerCopy
      refine ⟨target, StaticCall.nested ?_ innerCall⟩
      apply mem_append_right
      exact List.mem_cons_self (.list innerItems) after

/-- A call at any ordinary-list path in a lambda body can be lifted through
the lambda's special copy branch after parameter freshening. -/
theorem lambda_body_call_site_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin bodyFuel fresh final : Nat)
    (lambdaHead : Atom) (lambdaParameters : List Tree) (result : Tree)
    (head : Atom) (arguments bodyItems copiedBodyItems : List Tree) (cost : Nat)
    (childRule : Tree) (site : LiteralCallSite macros head arguments bodyItems cost)
    (lambdaForm : lambdaHead.name = "lambda")
    (bodyHeadSafe : counterNeutralListHead macros bodyItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (bodyCopied : copyWithMacros macros (bodyFuel + cost + 1) origin copyHoles renames fresh
      (.list bodyItems) = some (.list copiedBodyItems, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom lambdaHead, .list lambdaParameters, result, .list bodyItems]) target := by
  have bodyCopyOperation :
      (operations macros (bodyFuel + cost + 1)).copy origin copyHoles renames fresh (.list bodyItems) =
        some (.list copiedBodyItems, final) := by
    change (operations macros (bodyFuel + cost + 1)).copy origin copyHoles renames fresh
      (.list bodyItems) = _ at bodyCopied
    exact bodyCopied
  rw [copyNeutralList_uses_copyMany macros (bodyFuel + cost) origin copyHoles renames fresh bodyItems
    bodyHeadSafe] at bodyCopyOperation
  obtain ⟨pair, bodyMany, outputRun⟩ := option_bind_some bodyCopyOperation
  rcases pair with ⟨copiedItems, afterBody⟩
  have outputEq : (Tree.list copiedItems, afterBody) = (Tree.list copiedBodyItems, final) := by
    simpa using Option.some.inj outputRun
  have bodyItemsCopied : copyManyWithMacros macros (bodyFuel + cost) origin copyHoles renames fresh bodyItems =
      some (copiedBodyItems, final) := by
    rcases Prod.mk.inj outputEq with ⟨itemsEq, finalEq⟩
    cases Tree.list.inj itemsEq
    cases finalEq
    simpa [copyManyWithMacros] using bodyMany
  obtain ⟨target, bodyCall⟩ := literal_call_site_to_next_macro_step rules macros templateHoles
    copyHoles renames origin childOrigin bodyFuel fresh final head arguments copiedBodyItems childRule
    site known notHole lookupNone bodyItemsCopied childMember copiedChildMatches
  refine ⟨target, StaticCall.nested ?_ bodyCall⟩
  simp [lambdaForm]

/-- Extract the parameter and body copies from the successful whole-lambda
copy, then connect a body callsite to the corresponding template edge. -/
theorem lambda_copy_body_call_site_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin bodyFuel fresh final : Nat)
    (lambdaHead : Atom) (lambdaParameters : List Tree) (result : Tree)
    (bodyItems copiedBodyItems : List Tree) (cost : Nat)
    (copied : Tree) (head : Atom) (arguments : List Tree)
    (childRule : Tree) (site : LiteralCallSite macros head arguments bodyItems cost)
    (originalNames : List String)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaNotMacro : macros.contains lambdaHead.name = false)
    (lambdaNotHole : (lookup lambdaHead.name copyHoles).isNone = true)
    (parameterNamesMatch : parameterNames lambdaParameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (bodyHeadSafe : counterNeutralListHead macros bodyItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (wholeCopied : copyWithMacros macros (bodyFuel + cost + 2) origin copyHoles renames fresh
      (.list [.atom lambdaHead, .list lambdaParameters, result, .list bodyItems]) =
        some (copied, final))
    (outputShape : ∃ copiedParameters,
      copied = .list [.atom lambdaHead, .list copiedParameters, result, .list copiedBodyItems])
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom lambdaHead, .list lambdaParameters, result, .list bodyItems]) target := by
  obtain ⟨copiedParameters, outputShape⟩ := outputShape
  obtain ⟨copiedParameters', names, next, copiedBody, _parametersCopied, bodyCopied,
    copiedShape⟩ := copyWithMacros_lambda_parts macros (bodyFuel + cost + 1) origin fresh final
      copyHoles renames lambdaHead lambdaParameters result (.list bodyItems) copied
      originalNames lambdaForm lambdaNotMacro lambdaNotHole parameterNamesMatch
      parametersDistinct wholeCopied
  have formEq :
      Tree.list [.atom lambdaHead, .list copiedParameters', result, copiedBody] =
        Tree.list [.atom lambdaHead, .list copiedParameters, result, Tree.list copiedBodyItems] := by
    calc
      Tree.list [.atom lambdaHead, .list copiedParameters', result, copiedBody] = copied :=
        copiedShape.symm
      _ = Tree.list [.atom lambdaHead, .list copiedParameters, result,
        Tree.list copiedBodyItems] :=
        outputShape
  have bodyListEq :
      [.atom lambdaHead, .list copiedParameters', result, copiedBody] =
        [.atom lambdaHead, .list copiedParameters, result, .list copiedBodyItems] :=
    Tree.list.inj formEq
  have bodyShape : copiedBody = .list copiedBodyItems := by
    injection bodyListEq with _ tailEq
    injection tailEq with _ tailEq
    injection tailEq with _ singletonEq
    injection singletonEq with bodyShape
  have bodyCopied' : copyWithMacros macros (bodyFuel + cost + 1) origin copyHoles names next
      (.list bodyItems) = some (.list copiedBodyItems, final) := by
    change (operations macros (bodyFuel + cost + 1)).copy origin copyHoles names next
      (.list bodyItems) = some (.list copiedBodyItems, final)
    rw [bodyShape] at bodyCopied
    exact bodyCopied
  exact lambda_body_call_site_to_next_macro_step rules macros templateHoles copyHoles names
    origin childOrigin bodyFuel next final lambdaHead lambdaParameters result head arguments
    bodyItems copiedBodyItems cost childRule site lambdaForm bodyHeadSafe known notHole lookupNone
    bodyCopied' childMember copiedChildMatches

/-- Calls in a let body retain their template callsite after the binding
copy has established the local rename environment. -/
theorem let_body_call_site_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin bodyFuel fresh final : Nat)
    (letHead : Atom) (bindings : List Tree) (bodyItems copiedBodyItems : List Tree)
    (cost : Nat) (head : Atom) (arguments : List Tree) (childRule : Tree)
    (site : LiteralCallSite macros head arguments bodyItems cost)
    (letForm : letHead.name = "let")
    (bodyHeadSafe : counterNeutralListHead macros bodyItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (bodyCopied : copyWithMacros macros (bodyFuel + cost + 1) origin copyHoles renames fresh
      (.list bodyItems) = some (.list copiedBodyItems, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom letHead, .list bindings, .list bodyItems]) target := by
  have bodyCopyOperation :
      (operations macros (bodyFuel + cost + 1)).copy origin copyHoles renames fresh
        (.list bodyItems) = some (.list copiedBodyItems, final) := by
    change (operations macros (bodyFuel + cost + 1)).copy origin copyHoles renames fresh
      (.list bodyItems) = _ at bodyCopied
    exact bodyCopied
  rw [copyNeutralList_uses_copyMany macros (bodyFuel + cost) origin copyHoles renames fresh
    bodyItems bodyHeadSafe] at bodyCopyOperation
  obtain ⟨pair, bodyMany, outputRun⟩ := option_bind_some bodyCopyOperation
  rcases pair with ⟨copiedItems, afterBody⟩
  have outputEq : (Tree.list copiedItems, afterBody) = (Tree.list copiedBodyItems, final) := by
    simpa using Option.some.inj outputRun
  have bodyItemsCopied : copyManyWithMacros macros (bodyFuel + cost) origin copyHoles renames
      fresh bodyItems = some (copiedBodyItems, final) := by
    rcases Prod.mk.inj outputEq with ⟨itemsEq, finalEq⟩
    cases Tree.list.inj itemsEq
    cases finalEq
    simpa [copyManyWithMacros] using bodyMany
  obtain ⟨target, bodyCall⟩ := literal_call_site_to_next_macro_step rules macros templateHoles
    copyHoles renames origin childOrigin bodyFuel fresh final head arguments copiedBodyItems childRule
    site known notHole lookupNone bodyItemsCopied childMember copiedChildMatches
  refine ⟨target, StaticCall.nested ?_ bodyCall⟩
  simp [letForm]

/-- Extract the binding and body operations from a successful whole-let copy
before connecting a call in its body to the template. -/
theorem let_copy_body_call_site_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin bodyFuel fresh final : Nat)
    (letHead : Atom) (bindings : List Tree) (bodyItems copiedBodyItems : List Tree)
    (cost : Nat) (copied : Tree) (head : Atom) (arguments : List Tree)
    (childRule : Tree) (site : LiteralCallSite macros head arguments bodyItems cost)
    (originalNames : List String)
    (letForm : letHead.name = "let")
    (letNotMacro : macros.contains letHead.name = false)
    (letNotHole : (lookup letHead.name copyHoles).isNone = true)
    (bindingNamesMatch : bindingNames bindings = some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (bodyHeadSafe : counterNeutralListHead macros bodyItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (wholeCopied : copyWithMacros macros (bodyFuel + cost + 2) origin copyHoles renames fresh
      (.list [.atom letHead, .list bindings, .list bodyItems]) = some (copied, final))
    (outputShape : ∃ copiedBindings,
      copied = .list [.atom letHead, .list copiedBindings, .list copiedBodyItems])
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom letHead, .list bindings, .list bodyItems]) target := by
  obtain ⟨copiedBindings, outputShape⟩ := outputShape
  obtain ⟨copiedBindings', names, next, copiedBody, _bindingsCopied, bodyCopied,
    copiedShape⟩ := copyWithMacros_let_parts macros (bodyFuel + cost + 1) origin fresh final
      copyHoles renames letHead bindings (.list bodyItems) copied originalNames letForm
      letNotMacro letNotHole bindingNamesMatch bindingsDistinct wholeCopied
  have formEq :
      Tree.list [.atom letHead, .list copiedBindings', copiedBody] =
        Tree.list [.atom letHead, .list copiedBindings, Tree.list copiedBodyItems] := by
    calc
      Tree.list [.atom letHead, .list copiedBindings', copiedBody] = copied := copiedShape.symm
      _ = Tree.list [.atom letHead, .list copiedBindings, Tree.list copiedBodyItems] := outputShape
  have bodyListEq : [.atom letHead, .list copiedBindings', copiedBody] =
      [.atom letHead, .list copiedBindings, Tree.list copiedBodyItems] := Tree.list.inj formEq
  have bodyShape : copiedBody = Tree.list copiedBodyItems := by
    injection bodyListEq with _ tailEq
    injection tailEq with _ singletonEq
    injection singletonEq with bodyShape
  have bodyCopied' : copyWithMacros macros (bodyFuel + cost + 1) origin copyHoles names next
      (.list bodyItems) = some (.list copiedBodyItems, final) := by
    change (operations macros (bodyFuel + cost + 1)).copy origin copyHoles names next
      (.list bodyItems) = some (.list copiedBodyItems, final)
    rw [bodyShape] at bodyCopied
    exact bodyCopied
  exact let_body_call_site_to_next_macro_step rules macros templateHoles copyHoles names origin
    childOrigin bodyFuel next final letHead bindings bodyItems copiedBodyItems cost head arguments
    childRule site letForm bodyHeadSafe known notHole lookupNone bodyCopied' childMember
    copiedChildMatches

/-- Connect a call in the first let initializer to its source template site.
The initializer is copied outside the newly introduced let bindings. -/
theorem let_first_initializer_call_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin bodyFuel fresh final : Nat)
    (letHead bindingName : Atom) (bindingType : Tree) (body : Tree)
    (initializerItems : List Tree) (cost : Nat)
    (copied : Tree) (head : Atom) (arguments : List Tree) (childRule : Tree)
    (site : LiteralCallSite macros head arguments initializerItems cost)
    (originalNames : List String)
    (letForm : letHead.name = "let")
    (letNotMacro : macros.contains letHead.name = false)
    (letNotHole : (lookup letHead.name copyHoles).isNone = true)
    (bindingNamesMatch : bindingNames
      [.list [.list [.atom bindingName, bindingType], .list initializerItems]] =
        some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (initializerHeadSafe : counterNeutralListHead macros initializerItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (wholeCopied : copyWithMacros macros (bodyFuel + cost + 3) origin copyHoles renames fresh
      (.list [.atom letHead,
        .list [.list [.list [.atom bindingName, bindingType], .list initializerItems]], body]) =
          some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom letHead,
        .list [.list [.list [.atom bindingName, bindingType], .list initializerItems]], body])
      target := by
  obtain ⟨copiedBindings', namesAfterBindings, afterBindings, _copiedBody', bindingsCopied,
    _bodyCopied, _copiedShape⟩ := copyWithMacros_let_parts macros (bodyFuel + cost + 2)
      origin fresh final copyHoles renames letHead
      [.list [.list [.atom bindingName, bindingType], .list initializerItems]] body copied
      originalNames letForm letNotMacro letNotHole bindingNamesMatch bindingsDistinct wholeCopied
  have bindingsCopied' : copyBindingsWithMacros macros (bodyFuel + cost + 2) origin copyHoles
      renames renames fresh
      [.list [.list [.atom bindingName, bindingType], .list initializerItems]] =
        some (copiedBindings', namesAfterBindings, afterBindings) := by
    simpa [copyBindingsWithMacros] using bindingsCopied
  obtain ⟨_copiedName, _namesAfterBinder, next, copiedInitializer, afterInitializer,
    _tail, _finalNames, _binderCopied, initializerCopied, _tailCopied, _shape⟩ :=
    copyBindingsWithMacros_cons_parts macros (bodyFuel + cost + 1) origin copyHoles renames
      renames namesAfterBindings fresh afterBindings (.atom bindingName) bindingType
      (.list initializerItems) [] copiedBindings'
      bindingsCopied'
  change (operations macros (bodyFuel + cost + 1)).copy origin copyHoles renames next
    (.list initializerItems) = some (copiedInitializer, afterInitializer) at initializerCopied
  rw [copyNeutralList_uses_copyMany macros (bodyFuel + cost) origin copyHoles renames next
    initializerItems initializerHeadSafe] at initializerCopied
  obtain ⟨pair, copiedRun, outputRun⟩ := option_bind_some initializerCopied
  rcases pair with ⟨copiedItems', afterCopy⟩
  have outputEq : (Tree.list copiedItems', afterCopy) =
      (copiedInitializer, afterInitializer) := by
    simpa using Option.some.inj outputRun
  have listEq : Tree.list copiedItems' = copiedInitializer := congrArg Prod.fst outputEq
  have finalEq : afterCopy = afterInitializer := congrArg Prod.snd outputEq
  cases copiedInitializer with
  | atom _ => simp at listEq
  | list copiedItems'' =>
      have itemsEq : copiedItems' = copiedItems'' := Tree.list.inj listEq
      subst copiedItems''
      subst afterCopy
      have initializerCopy : copyManyWithMacros macros (bodyFuel + cost) origin copyHoles
          renames next initializerItems = some (copiedItems', afterInitializer) := by
        simpa [copyManyWithMacros] using copiedRun
      obtain ⟨target, initializerCall⟩ := literal_call_site_to_next_macro_step rules macros
        templateHoles copyHoles renames origin childOrigin bodyFuel next afterInitializer head
        arguments copiedItems' childRule site known notHole lookupNone initializerCopy childMember
        copiedChildMatches
      have rowCall : StaticCall rules templateHoles
          (.list [.list [.atom bindingName, bindingType], .list initializerItems]) target :=
        StaticCall.nested (by simp) initializerCall
      have bindingsCall : StaticCall rules templateHoles
          (.list [.list [.list [.atom bindingName, bindingType], .list initializerItems]]) target :=
        StaticCall.nested (by simp) rowCall
      exact ⟨target, StaticCall.nested (by simp) bindingsCall⟩

/-- Connect a call in an arbitrary let initializer to its source template
site. Successful copies of earlier bindings determine the actual rename and
counter state used for the selected initializer. -/
theorem let_initializer_call_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin bodyFuel fresh final : Nat)
    (letHead bindingName : Atom) (bindingType body : Tree)
    (before : List Tree) (initializerItems suffix : List Tree) (cost : Nat)
    (copied : Tree) (head : Atom) (arguments : List Tree) (childRule : Tree)
    (site : LiteralCallSite macros head arguments initializerItems cost)
    (originalNames : List String) (beforeValid : BindingRows before)
    (letForm : letHead.name = "let")
    (letNotMacro : macros.contains letHead.name = false)
    (letNotHole : (lookup letHead.name copyHoles).isNone = true)
    (bindingNamesMatch : bindingNames
      (before ++ .list [.list [.atom bindingName, bindingType], .list initializerItems] :: suffix) =
        some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (initializerHeadSafe : counterNeutralListHead macros initializerItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (wholeCopied : copyWithMacros macros (bodyFuel + cost + before.length + 3) origin copyHoles
      renames fresh (.list [.atom letHead,
        .list (before ++ .list [.list [.atom bindingName, bindingType], .list initializerItems]
          :: suffix), body]) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom letHead,
        .list (before ++ .list [.list [.atom bindingName, bindingType], .list initializerItems]
          :: suffix), body]) target := by
  obtain ⟨copiedBindings, namesAfterBindings, afterBindings, _copiedBody,
    bindingCopy, _bodyCopy, _copiedShape⟩ := copyWithMacros_let_parts macros
      (bodyFuel + cost + before.length + 2) origin fresh final copyHoles renames letHead
      (before ++ .list [.list [.atom bindingName, bindingType], .list initializerItems] :: suffix)
      body copied originalNames letForm letNotMacro letNotHole bindingNamesMatch bindingsDistinct
      wholeCopied
  have bindingsAccepted : copyBindingsWithMacros macros
      (bodyFuel + cost + before.length + 2) origin copyHoles renames renames fresh
      (before ++ .list [.list [.atom bindingName, bindingType], .list initializerItems] :: suffix) =
        some (copiedBindings, namesAfterBindings, afterBindings) := by
    simpa [copyBindingsWithMacros] using bindingCopy
  have selectedInitializer := copyBindingsWithMacros_extract_initializer macros
    (bodyFuel + cost + 1) origin fresh afterBindings copyHoles renames renames namesAfterBindings
    before (.atom bindingName) bindingType (.list initializerItems) suffix copiedBindings beforeValid
    (by
      have fuelEq : (bodyFuel + cost + 1) + before.length + 1 =
          bodyFuel + cost + before.length + 2 := by omega
      rw [fuelEq]
      exact bindingsAccepted)
  obtain ⟨_namesBefore, _freshBefore, _copiedName, _namesAfter, next, copiedInitializer,
    afterInitializer, _binderAccepted, initializerAccepted⟩ := selectedInitializer
  change (operations macros (bodyFuel + cost + 1)).copy origin copyHoles renames next
    (.list initializerItems) = some (copiedInitializer, afterInitializer) at initializerAccepted
  rw [copyNeutralList_uses_copyMany macros (bodyFuel + cost) origin copyHoles renames next
    initializerItems initializerHeadSafe] at initializerAccepted
  obtain ⟨pair, copiedRun, outputRun⟩ := option_bind_some initializerAccepted
  rcases pair with ⟨copiedItems, afterCopy⟩
  have outputEq : (Tree.list copiedItems, afterCopy) =
      (copiedInitializer, afterInitializer) := by
    simpa using Option.some.inj outputRun
  have listEq : Tree.list copiedItems = copiedInitializer := congrArg Prod.fst outputEq
  have finalEq : afterCopy = afterInitializer := congrArg Prod.snd outputEq
  cases copiedInitializer with
  | atom _ => simp at listEq
  | list copiedInitializerItems =>
      have itemsEq : copiedItems = copiedInitializerItems := Tree.list.inj listEq
      subst copiedInitializerItems
      subst afterCopy
      have initializerCopy : copyManyWithMacros macros (bodyFuel + cost) origin copyHoles renames
          next initializerItems = some (copiedItems, afterInitializer) := by
        simpa [copyManyWithMacros] using copiedRun
      obtain ⟨target, initializerCall⟩ := literal_call_site_to_next_macro_step rules macros
        templateHoles copyHoles renames origin childOrigin bodyFuel next afterInitializer head
        arguments copiedItems childRule site known notHole lookupNone initializerCopy childMember
        copiedChildMatches
      have rowCall : StaticCall rules templateHoles
          (.list [.list [.atom bindingName, bindingType], .list initializerItems]) target :=
        StaticCall.nested (by simp) initializerCall
      have bindingsCall : StaticCall rules templateHoles
          (.list (before ++ .list [.list [.atom bindingName, bindingType],
            .list initializerItems] :: suffix)) target :=
        StaticCall.nested (by
          apply mem_append_right
          simp) rowCall
      exact ⟨target, StaticCall.nested (by simp) bindingsCall⟩

/-- Lift a call in a single empty-pattern match case from the successful
whole-match copy to the original match template. -/
theorem match_default_body_call_site_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin bodyFuel fresh final : Nat)
    (matchHead : Atom) (scrutineeItems bodyItems : List Tree)
    (cost : Nat) (copied : Tree) (head : Atom) (arguments : List Tree)
    (childRule : Tree) (site : LiteralCallSite macros head arguments bodyItems cost)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : macros.contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (bodyHeadSafe : counterNeutralListHead macros bodyItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (wholeCopied : copyWithMacros macros (bodyFuel + cost + 3) origin copyHoles renames fresh
      (.list [.atom matchHead, .list scrutineeItems,
        .list [.list [], .list bodyItems]]) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom matchHead, .list scrutineeItems, .list [.list [], .list bodyItems]]) target := by
  obtain ⟨_copiedScrutinee, afterScrutinee, copiedCases, _scrutineeCopied, casesCopied,
    _wholeShape⟩ := copyWithMacros_match_default_parts macros (bodyFuel + cost + 2) origin fresh
      final copyHoles renames matchHead scrutineeItems (.list [.list [], .list bodyItems]) copied
      matchForm matchNotMacro matchNotHole wholeCopied
  have casesCopied' : copyCasesWithMacros macros (bodyFuel + cost + 2) origin copyHoles renames
      afterScrutinee [.list [.list [], .list bodyItems]] = some (copiedCases, final) := by
    simpa [copyCasesWithMacros] using casesCopied
  obtain ⟨copiedBody, afterBody, copiedTail, bodyCopied, tailCopied, _caseShape⟩ :=
    copyCasesWithMacros_default_parts macros (bodyFuel + cost + 1) origin afterScrutinee final
      copyHoles renames (.list bodyItems) [] copiedCases casesCopied'
  have tailParts : [] = copiedTail ∧ afterBody = final := by
    simpa [operations] using tailCopied
  rw [tailParts.2] at bodyCopied
  have tailEmpty : copiedTail = [] := tailParts.1.symm
  subst copiedTail
  have bodyCopyOperation :
      (operations macros (bodyFuel + cost + 1)).copy origin copyHoles renames afterScrutinee
        (.list bodyItems) = some (copiedBody, final) := bodyCopied
  rw [copyNeutralList_uses_copyMany macros (bodyFuel + cost) origin copyHoles renames
    afterScrutinee bodyItems bodyHeadSafe] at bodyCopyOperation
  obtain ⟨pair, bodyMany, outputRun⟩ := option_bind_some bodyCopyOperation
  rcases pair with ⟨copiedItems, afterCopy⟩
  have outputEq : (Tree.list copiedItems, afterCopy) = (copiedBody, final) := by
    simpa using Option.some.inj outputRun
  have bodyListEq : Tree.list copiedItems = copiedBody := congrArg Prod.fst outputEq
  have finalEq : afterCopy = final := congrArg Prod.snd outputEq
  cases copiedBody with
  | atom _ => simp at bodyListEq
  | list copiedItems' =>
      have itemsEq : copiedItems = copiedItems' := Tree.list.inj bodyListEq
      subst copiedItems'
      subst afterCopy
      have bodyItemsCopied : copyManyWithMacros macros (bodyFuel + cost) origin copyHoles
          renames afterScrutinee bodyItems = some (copiedItems, final) := by
        simpa [copyManyWithMacros] using bodyMany
      obtain ⟨target, bodyCall⟩ := literal_call_site_to_next_macro_step rules macros
        templateHoles copyHoles renames origin childOrigin bodyFuel afterScrutinee final head
        arguments copiedItems childRule site known notHole lookupNone bodyItemsCopied childMember
        copiedChildMatches
      have caseCall : StaticCall rules templateHoles
          (.list [.list [], .list bodyItems]) target := StaticCall.nested (by simp) bodyCall
      exact ⟨target, StaticCall.nested (by simp) caseCall⟩

/-- Lift a call from an empty-pattern case at an arbitrary index in a
multi-case match. The witness states that the match contains at least two
cases, so the multi-row dispatcher is the one used by the copy. -/
theorem match_default_body_call_site_at_index_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin bodyFuel fresh final : Nat)
    (matchHead : Atom) (scrutineeItems bodyItems : List Tree)
    (before suffix : List Tree) (beforeValid : CaseRows before)
    (twoCases : ∃ firstCase secondCase tail,
      before ++ .list [.list [], .list bodyItems] :: suffix = firstCase :: secondCase :: tail)
    (cost : Nat) (copied : Tree) (head : Atom) (arguments : List Tree)
    (childRule : Tree) (site : LiteralCallSite macros head arguments bodyItems cost)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : macros.contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (bodyHeadSafe : counterNeutralListHead macros bodyItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (wholeCopied : copyWithMacros macros (bodyFuel + cost + before.length + 3) origin
      copyHoles renames fresh
      (.list (.atom matchHead :: .list scrutineeItems ::
        (before ++ .list [.list [], .list bodyItems] :: suffix))) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list (.atom matchHead :: .list scrutineeItems ::
        (before ++ .list [.list [], .list bodyItems] :: suffix))) target := by
  obtain ⟨firstCase, secondCase, tail, casesEq⟩ := twoCases
  have wholeCopied' : copyWithMacros macros (bodyFuel + cost + before.length + 3) origin
      copyHoles renames fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: tail)) =
        some (copied, final) := by
    simpa only [casesEq] using wholeCopied
  obtain ⟨copiedScrutinee, afterScrutinee, copiedCases, _scrutineeCopied, casesCopied,
    _wholeShape⟩ := copyWithMacros_match_cases_parts macros
      (bodyFuel + cost + before.length + 2) origin fresh final copyHoles renames matchHead
      scrutineeItems firstCase secondCase tail copied matchForm matchNotMacro matchNotHole
      wholeCopied'
  have casesCopied' : copyCasesWithMacros macros (bodyFuel + cost + before.length + 2) origin
      copyHoles renames afterScrutinee
      (before ++ .list [.list [], .list bodyItems] :: suffix) = some (copiedCases, final) := by
    rw [casesEq]
    simpa [copyCasesWithMacros] using casesCopied
  have extracted := copyCasesWithMacros_extract_default macros (bodyFuel + cost + 1) origin
    afterScrutinee final copyHoles renames before (.list bodyItems) suffix copiedCases beforeValid
    (by
      have fuelEq : (bodyFuel + cost + 1) + before.length + 1 =
          bodyFuel + cost + before.length + 2 := by omega
      rw [fuelEq]
      exact casesCopied')
  obtain ⟨bodyFresh, copiedBody, afterBody, bodyCopied⟩ := extracted
  have bodyCopyOperation :
      (operations macros (bodyFuel + cost + 1)).copy origin copyHoles renames bodyFresh
        (.list bodyItems) = some (copiedBody, afterBody) := bodyCopied
  rw [copyNeutralList_uses_copyMany macros (bodyFuel + cost) origin copyHoles renames
    bodyFresh bodyItems bodyHeadSafe] at bodyCopyOperation
  obtain ⟨pair, bodyMany, outputRun⟩ := option_bind_some bodyCopyOperation
  rcases pair with ⟨copiedItems, afterCopy⟩
  have outputEq : (Tree.list copiedItems, afterCopy) = (copiedBody, afterBody) := by
    simpa using Option.some.inj outputRun
  have bodyListEq : Tree.list copiedItems = copiedBody := congrArg Prod.fst outputEq
  cases copiedBody with
  | atom _ => simp at bodyListEq
  | list copiedItems' =>
      have itemsEq : copiedItems = copiedItems' := Tree.list.inj bodyListEq
      subst copiedItems'
      have bodyItemsCopied : copyManyWithMacros macros (bodyFuel + cost) origin copyHoles
          renames bodyFresh bodyItems = some (copiedItems, afterBody) := by
        have afterEq : afterCopy = afterBody := congrArg Prod.snd outputEq
        rw [afterEq] at bodyMany
        simpa [copyManyWithMacros] using bodyMany
      obtain ⟨target, bodyCall⟩ := literal_call_site_to_next_macro_step rules macros
        templateHoles copyHoles renames origin childOrigin bodyFuel bodyFresh afterBody head
        arguments copiedItems childRule site known notHole lookupNone bodyItemsCopied childMember
        copiedChildMatches
      have caseCall : StaticCall rules templateHoles
          (.list [.list [], .list bodyItems]) target := StaticCall.nested (by simp) bodyCall
      have selectedMember : .list [.list [], .list bodyItems] ∈
          before ++ .list [.list [], .list bodyItems] :: suffix := by
        apply mem_append_right
        simp
      have rootMember : .list [.list [], .list bodyItems] ∈
          .atom matchHead :: .list scrutineeItems ::
            (before ++ .list [.list [], .list bodyItems] :: suffix) :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ selectedMember)
      exact ⟨target, StaticCall.nested rootMember caseCall⟩

/-- Lift a call from a nonempty-pattern case at an arbitrary index in a
multi-case match, preserving the freshened rename environment and counter. -/
theorem match_pattern_body_call_site_at_index_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin bodyFuel fresh final : Nat)
    (matchHead : Atom) (scrutineeItems : List Tree) (constructor : Tree)
    (patternParameters bodyItems before suffix : List Tree) (beforeValid : CaseRows before)
    (twoCases : ∃ firstCase secondCase tail,
      before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix =
        firstCase :: secondCase :: tail)
    (cost : Nat) (copied : Tree) (head : Atom) (arguments : List Tree)
    (childRule : Tree) (site : LiteralCallSite macros head arguments bodyItems cost)
    (originalNames : List String)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : macros.contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (patternNamesMatch : patternNames patternParameters = some originalNames)
    (patternNamesDistinct : Lexical.distinctNames originalNames = true)
    (bodyHeadSafe : counterNeutralListHead macros bodyItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (wholeCopied : copyWithMacros macros (bodyFuel + cost + before.length + 3) origin
      copyHoles renames fresh
      (.list (.atom matchHead :: .list scrutineeItems ::
        (before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix))) =
          some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list (.atom matchHead :: .list scrutineeItems ::
        (before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix)))
        target := by
  obtain ⟨firstCase, secondCase, tail, casesEq⟩ := twoCases
  have wholeCopied' : copyWithMacros macros (bodyFuel + cost + before.length + 3) origin
      copyHoles renames fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: tail)) =
        some (copied, final) := by
    simpa only [casesEq] using wholeCopied
  obtain ⟨copiedScrutinee, afterScrutinee, copiedCases, _scrutineeCopied, casesCopied,
    _wholeShape⟩ := copyWithMacros_match_cases_parts macros
      (bodyFuel + cost + before.length + 2) origin fresh final copyHoles renames matchHead
      scrutineeItems firstCase secondCase tail copied matchForm matchNotMacro matchNotHole
      wholeCopied'
  have casesCopied' : copyCasesWithMacros macros (bodyFuel + cost + before.length + 2) origin
      copyHoles renames afterScrutinee
      (before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix) =
        some (copiedCases, final) := by
    rw [casesEq]
    simpa [copyCasesWithMacros] using casesCopied
  have extracted := copyCasesWithMacros_extract_pattern macros (bodyFuel + cost + 1) origin
    afterScrutinee final copyHoles renames before constructor patternParameters (.list bodyItems)
    suffix copiedCases beforeValid originalNames patternNamesMatch patternNamesDistinct
    (by
      have fuelEq : (bodyFuel + cost + 1) + before.length + 1 =
          bodyFuel + cost + before.length + 2 := by omega
      rw [fuelEq]
      exact casesCopied')
  obtain ⟨_patternFresh, _copiedParameters, localNames, afterPattern, copiedBody, afterBody,
    _patternCopied, bodyCopied⟩ := extracted
  have bodyCopyOperation :
      (operations macros (bodyFuel + cost + 1)).copy origin copyHoles localNames afterPattern
        (.list bodyItems) = some (copiedBody, afterBody) := bodyCopied
  rw [copyNeutralList_uses_copyMany macros (bodyFuel + cost) origin copyHoles localNames
    afterPattern bodyItems bodyHeadSafe] at bodyCopyOperation
  obtain ⟨pair, bodyMany, outputRun⟩ := option_bind_some bodyCopyOperation
  rcases pair with ⟨copiedItems, afterCopy⟩
  have outputEq : (Tree.list copiedItems, afterCopy) = (copiedBody, afterBody) := by
    simpa using Option.some.inj outputRun
  have bodyListEq : Tree.list copiedItems = copiedBody := congrArg Prod.fst outputEq
  cases copiedBody with
  | atom _ => simp at bodyListEq
  | list copiedItems' =>
      have itemsEq : copiedItems = copiedItems' := Tree.list.inj bodyListEq
      subst copiedItems'
      have bodyItemsCopied : copyManyWithMacros macros (bodyFuel + cost) origin copyHoles
          localNames afterPattern bodyItems = some (copiedItems, afterBody) := by
        have afterEq : afterCopy = afterBody := congrArg Prod.snd outputEq
        rw [afterEq] at bodyMany
        simpa [copyManyWithMacros] using bodyMany
      obtain ⟨target, bodyCall⟩ := literal_call_site_to_next_macro_step rules macros
        templateHoles copyHoles localNames origin childOrigin bodyFuel afterPattern afterBody head
        arguments copiedItems childRule site known notHole lookupNone bodyItemsCopied childMember
        copiedChildMatches
      have patternCaseCall : StaticCall rules templateHoles
          (.list [.list (constructor :: patternParameters), .list bodyItems]) target :=
        StaticCall.nested (List.mem_cons_of_mem _ (List.mem_cons_self _ _)) bodyCall
      have selectedMember : .list [.list (constructor :: patternParameters), .list bodyItems] ∈
          before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix := by
        exact mem_append_right before
          (.list [.list (constructor :: patternParameters), .list bodyItems] :: suffix)
          (List.mem_cons_self _ _)
      have rootMember : .list [.list (constructor :: patternParameters), .list bodyItems] ∈
          .atom matchHead :: .list scrutineeItems ::
            (before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix) :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ selectedMember)
      exact ⟨target, StaticCall.nested rootMember patternCaseCall⟩

/-- Lift a call from the scrutinee of a successful multi-case match copy to
the same callsite in the source template. -/
theorem match_scrutinee_call_site_at_index_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin scrutineeFuel fresh final : Nat)
    (matchHead : Atom) (scrutineeItems : List Tree) (firstCase secondCase : Tree)
    (tail : List Tree) (cost : Nat) (copied : Tree) (head : Atom)
    (arguments : List Tree) (childRule : Tree)
    (site : LiteralCallSite macros head arguments scrutineeItems cost)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : macros.contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (scrutineeHeadSafe : counterNeutralListHead macros scrutineeItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (wholeCopied : copyWithMacros macros (scrutineeFuel + cost + 2) origin copyHoles renames
      fresh (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: tail)) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: tail)) target := by
  obtain ⟨copiedScrutinee, afterScrutinee, _copiedCases, scrutineeCopied, _casesCopied,
    _wholeShape⟩ := copyWithMacros_match_cases_parts macros (scrutineeFuel + cost + 1) origin
      fresh final copyHoles renames matchHead scrutineeItems firstCase secondCase tail copied
      matchForm matchNotMacro matchNotHole wholeCopied
  have scrutineeCopyOperation :
      (operations macros (scrutineeFuel + cost + 1)).copy origin copyHoles renames fresh
        (.list scrutineeItems) = some (copiedScrutinee, afterScrutinee) := scrutineeCopied
  rw [copyNeutralList_uses_copyMany macros (scrutineeFuel + cost) origin copyHoles renames
    fresh scrutineeItems scrutineeHeadSafe] at scrutineeCopyOperation
  obtain ⟨pair, copiedMany, outputRun⟩ := option_bind_some scrutineeCopyOperation
  rcases pair with ⟨copiedItems, afterCopy⟩
  have outputEq : (Tree.list copiedItems, afterCopy) = (copiedScrutinee, afterScrutinee) := by
    simpa using Option.some.inj outputRun
  have listEq : Tree.list copiedItems = copiedScrutinee := congrArg Prod.fst outputEq
  cases copiedScrutinee with
  | atom _ => simp at listEq
  | list copiedScrutineeItems =>
      have itemsEq : copiedItems = copiedScrutineeItems := Tree.list.inj listEq
      subst copiedScrutineeItems
      have copiedArguments : copyManyWithMacros macros (scrutineeFuel + cost) origin copyHoles
          renames fresh scrutineeItems = some (copiedItems, afterScrutinee) := by
        have afterEq : afterCopy = afterScrutinee := congrArg Prod.snd outputEq
        rw [afterEq] at copiedMany
        simpa [copyManyWithMacros] using copiedMany
      obtain ⟨target, sourceCall⟩ := literal_call_site_to_next_macro_step rules macros
        templateHoles copyHoles renames origin childOrigin scrutineeFuel fresh afterScrutinee head
        arguments copiedItems childRule site known notHole lookupNone copiedArguments childMember
        copiedChildMatches
      have scrutineeMember : .list scrutineeItems ∈
          .atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: tail :=
        List.mem_cons_of_mem _ (List.mem_cons_self _ _)
      exact ⟨target, StaticCall.nested scrutineeMember sourceCall⟩

/-- Lift a call from the scrutinee of a single-case match through the
successful whole-match copy. -/
theorem match_scrutinee_call_site_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin scrutineeFuel fresh final : Nat)
    (matchHead : Atom) (scrutineeItems : List Tree) (caseBody : Tree)
    (cost : Nat) (copied : Tree) (head : Atom) (arguments : List Tree)
    (childRule : Tree) (site : LiteralCallSite macros head arguments scrutineeItems cost)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : macros.contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (scrutineeHeadSafe : counterNeutralListHead macros scrutineeItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (wholeCopied : copyWithMacros macros (scrutineeFuel + cost + 2) origin copyHoles renames
      fresh (.list [.atom matchHead, .list scrutineeItems, caseBody]) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom matchHead, .list scrutineeItems, caseBody]) target := by
  obtain ⟨copiedScrutinee, afterScrutinee, _copiedCases, scrutineeCopied, _casesCopied,
    _wholeShape⟩ := copyWithMacros_match_default_parts macros (scrutineeFuel + cost + 1) origin
      fresh final copyHoles renames matchHead scrutineeItems caseBody copied matchForm
      matchNotMacro matchNotHole wholeCopied
  have scrutineeCopyOperation :
      (operations macros (scrutineeFuel + cost + 1)).copy origin copyHoles renames fresh
        (.list scrutineeItems) = some (copiedScrutinee, afterScrutinee) := scrutineeCopied
  rw [copyNeutralList_uses_copyMany macros (scrutineeFuel + cost) origin copyHoles renames
    fresh scrutineeItems scrutineeHeadSafe] at scrutineeCopyOperation
  obtain ⟨pair, copiedMany, outputRun⟩ := option_bind_some scrutineeCopyOperation
  rcases pair with ⟨copiedItems, afterCopy⟩
  have outputEq : (Tree.list copiedItems, afterCopy) = (copiedScrutinee, afterScrutinee) := by
    simpa using Option.some.inj outputRun
  have listEq : Tree.list copiedItems = copiedScrutinee := congrArg Prod.fst outputEq
  cases copiedScrutinee with
  | atom _ => simp at listEq
  | list copiedScrutineeItems =>
      have itemsEq : copiedItems = copiedScrutineeItems := Tree.list.inj listEq
      subst copiedScrutineeItems
      have copiedArguments : copyManyWithMacros macros (scrutineeFuel + cost) origin copyHoles
          renames fresh scrutineeItems = some (copiedItems, afterScrutinee) := by
        have afterEq : afterCopy = afterScrutinee := congrArg Prod.snd outputEq
        rw [afterEq] at copiedMany
        simpa [copyManyWithMacros] using copiedMany
      obtain ⟨target, sourceCall⟩ := literal_call_site_to_next_macro_step rules macros
        templateHoles copyHoles renames origin childOrigin scrutineeFuel fresh afterScrutinee head
        arguments copiedItems childRule site known notHole lookupNone copiedArguments childMember
        copiedChildMatches
      have scrutineeMember : .list scrutineeItems ∈
          [.atom matchHead, .list scrutineeItems, caseBody] :=
        List.mem_cons_of_mem _ (List.mem_cons_self _ _)
      exact ⟨target, StaticCall.nested scrutineeMember sourceCall⟩

/-- Lift a call in a single nonempty-pattern match case through the actual
pattern freshening and case-body copy operations. -/
theorem match_pattern_body_call_site_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (renames : Renames) (origin childOrigin bodyFuel fresh final : Nat)
    (matchHead : Atom) (scrutineeItems : List Tree) (constructor : Tree)
    (patternParameters bodyItems : List Tree) (cost : Nat) (copied : Tree)
    (head : Atom) (arguments : List Tree) (childRule : Tree)
    (site : LiteralCallSite macros head arguments bodyItems cost)
    (originalNames : List String)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : macros.contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (patternNamesMatch : patternNames patternParameters = some originalNames)
    (patternNamesDistinct : Lexical.distinctNames originalNames = true)
    (bodyHeadSafe : counterNeutralListHead macros bodyItems = true)
    (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (wholeCopied : copyWithMacros macros (bodyFuel + cost + 3) origin copyHoles renames fresh
      (.list [.atom matchHead, .list scrutineeItems,
        .list [.list (constructor :: patternParameters), .list bodyItems]]) =
          some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom matchHead, .list scrutineeItems,
        .list [.list (constructor :: patternParameters), .list bodyItems]]) target := by
  obtain ⟨_copiedScrutinee, afterScrutinee, copiedCases, _scrutineeCopied, casesCopied,
    _wholeShape⟩ := copyWithMacros_match_default_parts macros (bodyFuel + cost + 2) origin fresh
      final copyHoles renames matchHead scrutineeItems
      (.list [.list (constructor :: patternParameters), .list bodyItems]) copied
      matchForm matchNotMacro matchNotHole wholeCopied
  have casesCopied' : copyCasesWithMacros macros (bodyFuel + cost + 2) origin copyHoles renames
      afterScrutinee [.list [.list (constructor :: patternParameters), .list bodyItems]] =
        some (copiedCases, final) := by
    simpa [copyCasesWithMacros] using casesCopied
  obtain ⟨_copiedParameters, localNames, afterPattern, copiedBody, afterBody, copiedTail,
    _patternCopied, bodyCopied, tailCopied, _caseShape⟩ :=
    copyCasesWithMacros_pattern_parts macros (bodyFuel + cost + 1) origin afterScrutinee final
      copyHoles renames constructor patternParameters (.list bodyItems) [] copiedCases
      originalNames patternNamesMatch patternNamesDistinct casesCopied'
  have tailParts : [] = copiedTail ∧ afterBody = final := by
    simpa [operations] using tailCopied
  rw [tailParts.2] at bodyCopied
  have tailEmpty : copiedTail = [] := tailParts.1.symm
  subst copiedTail
  have bodyCopyOperation :
      (operations macros (bodyFuel + cost + 1)).copy origin copyHoles localNames afterPattern
        (.list bodyItems) = some (copiedBody, final) := bodyCopied
  rw [copyNeutralList_uses_copyMany macros (bodyFuel + cost) origin copyHoles localNames
    afterPattern bodyItems bodyHeadSafe] at bodyCopyOperation
  obtain ⟨pair, bodyMany, outputRun⟩ := option_bind_some bodyCopyOperation
  rcases pair with ⟨copiedItems, afterCopy⟩
  have outputEq : (Tree.list copiedItems, afterCopy) = (copiedBody, final) := by
    simpa using Option.some.inj outputRun
  have bodyListEq : Tree.list copiedItems = copiedBody := congrArg Prod.fst outputEq
  have finalEq : afterCopy = final := congrArg Prod.snd outputEq
  cases copiedBody with
  | atom _ => simp at bodyListEq
  | list copiedItems' =>
      have itemsEq : copiedItems = copiedItems' := Tree.list.inj bodyListEq
      subst copiedItems'
      subst afterCopy
      have bodyItemsCopied : copyManyWithMacros macros (bodyFuel + cost) origin copyHoles
          localNames afterPattern bodyItems = some (copiedItems, final) := by
        simpa [copyManyWithMacros] using bodyMany
      obtain ⟨target, bodyCall⟩ := literal_call_site_to_next_macro_step rules macros
        templateHoles copyHoles localNames origin childOrigin bodyFuel afterPattern final head
        arguments copiedItems childRule site known notHole lookupNone bodyItemsCopied childMember
        copiedChildMatches
      have caseCall : StaticCall rules templateHoles
          (.list [.list (constructor :: patternParameters), .list bodyItems]) target :=
        StaticCall.nested (by simp) bodyCall
      exact ⟨target, StaticCall.nested (by simp) caseCall⟩

inductive SubstitutedHeadCallSite (macros : List String) (head : Atom)
    (arguments : List Tree) : List Tree → Nat → Prop where
  | direct (before after : List Tree) :
      SubstitutedHeadCallSite macros head arguments
        (before ++ .list (.atom head :: arguments) :: after) (before.length + 2)
  | nested (before after innerItems : List Tree) (innerCost : Nat)
      (headSafe : counterNeutralListHead macros innerItems = true)
      (inner : SubstitutedHeadCallSite macros head arguments innerItems innerCost) :
      SubstitutedHeadCallSite macros head arguments
        (before ++ .list innerItems :: after) (innerCost + before.length + 2)

/-- Arbitrary-depth callsite tracking for a substituted template head. The
parameter-to-hole correspondence and ordinary head dispatch are explicit. -/
theorem substituted_head_call_site_to_next_macro_step
    (rules : List (Nat × Tree)) (macros : List String)
    (templateHoles : List String) (copyHoles : Holes)
    (origin childOrigin copyFuel fresh final : Nat) (head : Atom)
    (arguments copied : List Tree) (childRule : Tree)
    (site : SubstitutedHeadCallSite macros head arguments items cost)
    (headIsHole : head.name ∈ templateHoles)
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (ordinaryHead : head.name ≠ "lambda" ∧ head.name ≠ "let" ∧ head.name ≠ "match")
    (outerCopied : copyManyWithMacros macros (copyFuel + cost) origin copyHoles [] fresh
      items = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles (.list items) target := by
  induction site generalizing fresh copied final with
  | direct before after =>
      obtain ⟨copiedPrefix, copiedCall, copiedSuffix, callStart, callFinal,
        callCopy, _suffixCopy, outputShape⟩ :=
        copyManyWithMacros_extract_element macros (copyFuel + 1) origin fresh copyHoles []
          before (.list (.atom head :: arguments)) after copied final
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using outerCopied)
      obtain ⟨childHoles, childTemplate, childMatched⟩ :=
        copiedChildMatches copied copiedPrefix copiedCall copiedSuffix outputShape
      obtain ⟨ruleHead, arity, callHead, callArguments, signatureMatch, inputShape,
        nameMatch, arityMatch⟩ := successful_match_has_signature childRule copiedCall
          childHoles childTemplate childMatched
      have callCopy' : copyWithMacros macros (copyFuel + 1) origin copyHoles [] callStart
          (.list (.atom head :: arguments)) =
          some (.list (.atom callHead :: callArguments), callFinal) := by
        change (operations macros (copyFuel + 1)).copy origin copyHoles [] callStart
          (.list (.atom head :: arguments)) = _
        rw [callCopy, inputShape]
      have headSubstituted : (lookup head.name copyHoles).isSome = true := by
        rw [holesAgree] at headIsHole
        exact lookup_isSome_of_mem_keys head.name copyHoles headIsHole
      have itemsCopiedOperation := copyWithMacros_substituted_head_uses_copyMany macros copyFuel
        origin copyHoles [] callStart head arguments (.atom callHead :: callArguments) callFinal
        headSubstituted ordinaryHead callCopy'
      have itemsCopied : copyManyWithMacros macros copyFuel origin copyHoles [] callStart
          (.atom head :: arguments) = some (.atom callHead :: callArguments, callFinal) := by
        change (operations macros copyFuel).copyMany origin copyHoles [] callStart
          (.atom head :: arguments) = _
        exact itemsCopiedOperation
      have arityEq : arity = arguments.length := by
        calc
          arity = callArguments.length := arityMatch
          _ = arguments.length := by
            have lengths := copyManyWithMacros_preserves_length macros copyFuel origin copyHoles []
              callStart (.atom head :: arguments) (.atom callHead :: callArguments) callFinal
              itemsCopied
            simp only [List.length_cons] at lengths
            omega
      have ruleNameEq : ruleHead = callHead.name := nameMatch.symm
      rw [ruleNameEq, arityEq] at signatureMatch
      obtain ⟨target, found⟩ := findRule_of_member_signature callHead.name arguments.length 0
        rules childOrigin childRule childMember signatureMatch
      have candidate := findRule_mem_targetsOfArity callHead.name arguments.length 0
        rules target found
      have callStatic : StaticCall rules templateHoles
          (.list (.atom head :: arguments)) target :=
        StaticCall.substitutedHead headIsHole candidate
      refine ⟨target, StaticCall.nested ?_ callStatic⟩
      apply mem_append_right
      exact List.mem_cons_self (.list (.atom head :: arguments)) after
  | @nested before after innerItems innerCost headSafe _innerSite ih =>
      let innerFuel := copyFuel + innerCost
      have outerCopiedAtChild : copyManyWithMacros macros
          ((innerFuel + 1) + before.length + 1) origin copyHoles [] fresh
          (before ++ .list innerItems :: after) = some (copied, final) := by
        simpa [innerFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using outerCopied
      obtain ⟨copiedPrefix, copiedNested, copiedSuffix, beforeCounter, outerMiddle,
        nestedCopy, _suffixCopy, _outputShape⟩ :=
        copyManyWithMacros_extract_element macros (innerFuel + 1) origin fresh copyHoles []
          before (.list innerItems) after copied final outerCopiedAtChild
      have nestedCopy' : (operations macros (innerFuel + 1)).copy origin copyHoles [] beforeCounter
          (.list innerItems) = some (copiedNested, outerMiddle) := by
        simpa [innerFuel, Nat.add_assoc] using nestedCopy
      rw [copyNeutralList_uses_copyMany macros innerFuel origin copyHoles []
        beforeCounter innerItems headSafe] at nestedCopy'
      have innerResult : ∃ copiedInner middle,
          copyManyWithMacros macros innerFuel origin copyHoles [] beforeCounter innerItems =
            some (copiedInner, middle) ∧ copiedNested = .list copiedInner ∧ middle = outerMiddle := by
        obtain ⟨innerPair, innerRun, outputRun⟩ := option_bind_some nestedCopy'
        rcases innerPair with ⟨copiedInner, middle⟩
        have outputEq := Option.some.inj outputRun
        have copiedEq := congrArg Prod.fst outputEq
        have counterEq := congrArg Prod.snd outputEq
        have innerAccepted : copyManyWithMacros macros innerFuel origin copyHoles [] beforeCounter
            innerItems = some (copiedInner, middle) := by
          simpa [copyManyWithMacros] using innerRun
        exact ⟨copiedInner, middle, innerAccepted, by simpa using copiedEq.symm,
          by simpa using counterEq⟩
      obtain ⟨copiedInner, middle, innerCopy, copiedNestedEq, middleEq⟩ := innerResult
      subst copiedNested
      subst outerMiddle
      obtain ⟨target, innerCall⟩ := ih (fresh := beforeCounter) (copied := copiedInner)
        (final := middle) innerCopy
      refine ⟨target, StaticCall.nested ?_ innerCall⟩
      apply mem_append_right
      exact List.mem_cons_self (.list innerItems) after

/-- Compose two list-context extractions. This covers a literal call at any
sibling position inside a nested ordinary list, where that list itself occurs
at any sibling position in the outer template. -/
theorem nested_literal_call_at_two_list_indices_to_next_macro_step
    (rules : List (Nat × Tree)) (macros : List String)
    (templateHoles : List String) (copyHoles : Holes)
    (origin childOrigin innerFuel fresh final : Nat) (head : Atom)
    (arguments innerBefore innerAfter innerItems : List Tree)
    (outerBefore outerAfter copied : List Tree)
    (childRule : Tree) (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (ordinaryInnerHead : counterNeutralListHead macros innerItems = true)
    (innerShape : innerItems = innerBefore ++ .list (.atom head :: arguments) :: innerAfter)
    (outerCopied : copyManyWithMacros macros
      (innerFuel + innerBefore.length + outerBefore.length + 4)
      origin copyHoles [] fresh
      (outerBefore ++ .list innerItems :: outerAfter) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedInner copiedBefore copiedCall copiedAfter,
      copiedInner = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list (outerBefore ++
        .list (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: outerAfter))
      target := by
  let nestedTree : Tree := .list innerItems
  let innerCopyFuel := innerFuel + innerBefore.length + 2
  let nestedFuel := innerCopyFuel + 1
  have outerCopiedAtChild : copyManyWithMacros macros
      (nestedFuel + outerBefore.length + 1) origin copyHoles [] fresh
      (outerBefore ++ nestedTree :: outerAfter) = some (copied, final) := by
    simpa [nestedFuel, innerCopyFuel, nestedTree, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using outerCopied
  obtain ⟨copiedPrefix, copiedNested, copiedSuffix, before, outerMiddle,
    nestedCopy, _outerSuffixCopy, outerShape⟩ :=
    copyManyWithMacros_extract_element macros nestedFuel origin fresh copyHoles []
      outerBefore nestedTree outerAfter copied final outerCopiedAtChild
  have ordinaryCopy := copyNeutralList_uses_copyMany macros innerCopyFuel origin copyHoles []
    before innerItems ordinaryInnerHead
  rw [innerShape] at ordinaryCopy
  have nestedCopy' : (operations macros (innerCopyFuel + 1)).copy origin copyHoles [] before
      (.list (innerBefore ++ .list (.atom head :: arguments) :: innerAfter)) =
        some (copiedNested, outerMiddle) := by
    simpa [nestedFuel, nestedTree, innerShape] using nestedCopy
  rw [ordinaryCopy] at nestedCopy'
  have innerResult : ∃ copiedInnerItems innerFinal,
      copyManyWithMacros macros innerCopyFuel origin copyHoles [] before
        (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) =
          some (copiedInnerItems, innerFinal) ∧
      copiedNested = .list copiedInnerItems ∧ innerFinal = outerMiddle := by
    have nestedCopy'' := nestedCopy'
    obtain ⟨innerPair, innerRun, outputRun⟩ := option_bind_some nestedCopy''
    rcases innerPair with ⟨copiedInnerItems, innerFinal⟩
    have outputEq := Option.some.inj outputRun
    have copiedEq := congrArg Prod.fst outputEq
    have finalEq := congrArg Prod.snd outputEq
    have innerAccepted : copyManyWithMacros macros innerCopyFuel origin copyHoles [] before
        (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) =
          some (copiedInnerItems, innerFinal) := by
      simpa [innerCopyFuel] using innerRun
    exact ⟨copiedInnerItems, innerFinal, innerAccepted, by simpa using copiedEq.symm,
      by simpa using finalEq⟩
  obtain ⟨copiedInnerItems, innerFinal, innerCopy, copiedNestedEq, finalEq⟩ := innerResult
  subst copiedNested
  subst outerMiddle
  obtain ⟨target, innerStatic⟩ := literal_call_at_list_index_to_next_macro_step
    rules macros templateHoles copyHoles [] origin childOrigin innerFuel before innerFinal
    head arguments innerBefore innerAfter copiedInnerItems
    (innerFuel + 1) childRule
    known notHole lookupNone rfl
    (by simpa [innerCopyFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using innerCopy)
    childMember
    (fun copiedBefore copiedCall copiedAfter shape =>
      copiedChildMatches copiedInnerItems copiedBefore copiedCall copiedAfter shape)
  refine ⟨target, StaticCall.nested ?_ innerStatic⟩
  apply mem_append_right
  simp [innerShape]

/-- Compose a third ordinary list context around the two-index result. Both
intermediate list heads must be neutral so their copy dispatch is the ordinary
list traversal. -/
theorem nested_literal_call_at_three_list_indices_to_next_macro_step
    (rules : List (Nat × Tree)) (macros : List String)
    (templateHoles : List String) (copyHoles : Holes)
    (origin childOrigin innerFuel fresh final : Nat) (head : Atom)
    (arguments innerBefore innerAfter innerItems : List Tree)
    (middleBefore middleAfter middleItems : List Tree)
    (outerBefore outerAfter copied : List Tree)
    (childRule : Tree) (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (ordinaryInnerHead : counterNeutralListHead macros innerItems = true)
    (ordinaryMiddleHead : counterNeutralListHead macros middleItems = true)
    (innerShape : innerItems = innerBefore ++ .list (.atom head :: arguments) :: innerAfter)
    (middleShape : middleItems = middleBefore ++ .list innerItems :: middleAfter)
    (outerCopied : copyManyWithMacros macros
      (innerFuel + innerBefore.length + middleBefore.length + outerBefore.length + 6)
      origin copyHoles [] fresh
      (outerBefore ++ .list middleItems :: outerAfter) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedInner copiedBefore copiedCall copiedAfter,
      copiedInner = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate, matchRule childRule copiedCall =
        some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list (outerBefore ++ .list
        (middleBefore ++ .list
          (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: middleAfter) :: outerAfter))
      target := by
  let innerTwoFuel := innerFuel + innerBefore.length + middleBefore.length + 4
  let selectedFuel := innerTwoFuel + 1
  have outerCopiedAtChild : copyManyWithMacros macros
      (selectedFuel + outerBefore.length + 1) origin copyHoles [] fresh
      (outerBefore ++ .list middleItems :: outerAfter) = some (copied, final) := by
    simpa [selectedFuel, innerTwoFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      outerCopied
  obtain ⟨copiedPrefix, copiedMiddle, copiedSuffix, before, outerMiddle,
    middleCopy, _outerSuffixCopy, outerShape⟩ :=
    copyManyWithMacros_extract_element macros selectedFuel origin fresh copyHoles []
      outerBefore (.list middleItems) outerAfter copied final outerCopiedAtChild
  have ordinaryCopy := copyNeutralList_uses_copyMany macros innerTwoFuel origin copyHoles []
    before middleItems ordinaryMiddleHead
  rw [middleShape] at ordinaryCopy
  have middleCopy' : (operations macros (innerTwoFuel + 1)).copy origin copyHoles [] before
      (.list (middleBefore ++ .list innerItems :: middleAfter)) =
        some (copiedMiddle, outerMiddle) := by
    simpa [selectedFuel, innerTwoFuel, middleShape] using middleCopy
  rw [ordinaryCopy] at middleCopy'
  have innerTwoResult : ∃ copiedMiddleItems middleFinal,
      copyManyWithMacros macros innerTwoFuel origin copyHoles [] before
        (middleBefore ++ .list innerItems :: middleAfter) =
          some (copiedMiddleItems, middleFinal) ∧
      copiedMiddle = .list copiedMiddleItems ∧ middleFinal = outerMiddle := by
    have middleCopy'' := middleCopy'
    obtain ⟨middlePair, middleRun, outputRun⟩ := option_bind_some middleCopy''
    rcases middlePair with ⟨copiedMiddleItems, middleFinal⟩
    have outputEq := Option.some.inj outputRun
    have copiedEq := congrArg Prod.fst outputEq
    have finalEq := congrArg Prod.snd outputEq
    have middleAccepted : copyManyWithMacros macros innerTwoFuel origin copyHoles [] before
        (middleBefore ++ .list innerItems :: middleAfter) = some (copiedMiddleItems, middleFinal) := by
      simpa [innerTwoFuel] using middleRun
    exact ⟨copiedMiddleItems, middleFinal, middleAccepted,
      by simpa using copiedEq.symm, by simpa using finalEq⟩
  obtain ⟨copiedMiddleItems, middleFinal, middleRun, copiedMiddleEq, finalEq⟩ := innerTwoResult
  subst copiedMiddle
  subst outerMiddle
  obtain ⟨target, innerStatic⟩ :=
    nested_literal_call_at_two_list_indices_to_next_macro_step rules macros templateHoles
      copyHoles origin childOrigin innerFuel before middleFinal head arguments innerBefore
      innerAfter innerItems middleBefore middleAfter copiedMiddleItems childRule known notHole
      lookupNone ordinaryInnerHead innerShape
      (by simpa [innerTwoFuel] using middleRun) childMember
      (fun copiedInner copiedBefore copiedCall copiedAfter shape =>
        copiedChildMatches copiedInner copiedBefore copiedCall copiedAfter shape)
  refine ⟨target, StaticCall.nested ?_ innerStatic⟩
  apply mem_append_right
  simp [middleShape, innerShape]

/-- Add an outer ordinary-list layer to the three-index correspondence. -/
theorem nested_literal_call_at_four_list_indices_to_next_macro_step
    (rules : List (Nat × Tree)) (macros : List String)
    (templateHoles : List String) (copyHoles : Holes)
    (origin childOrigin innerFuel fresh final : Nat) (head : Atom)
    (arguments innerBefore innerAfter innerItems : List Tree)
    (middleBefore middleAfter middleItems : List Tree)
    (outerBefore outerAfter outerItems : List Tree)
    (rootBefore rootAfter copied : List Tree)
    (childRule : Tree) (known : macros.contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (ordinaryInnerHead : counterNeutralListHead macros innerItems = true)
    (ordinaryMiddleHead : counterNeutralListHead macros middleItems = true)
    (ordinaryOuterHead : counterNeutralListHead macros outerItems = true)
    (innerShape : innerItems = innerBefore ++ .list (.atom head :: arguments) :: innerAfter)
    (middleShape : middleItems = middleBefore ++ .list innerItems :: middleAfter)
    (outerShape : outerItems = outerBefore ++ .list middleItems :: outerAfter)
    (rootCopied : copyManyWithMacros macros
      (innerFuel + innerBefore.length + middleBefore.length + outerBefore.length +
        rootBefore.length + 8)
      origin copyHoles [] fresh (rootBefore ++ .list outerItems :: rootAfter) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedInner copiedBefore copiedCall copiedAfter,
      copiedInner = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list (rootBefore ++ .list
        (outerBefore ++ .list
          (middleBefore ++ .list
            (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: middleAfter) :: outerAfter) :: rootAfter))
      target := by
  let threeFuel := innerFuel + innerBefore.length + middleBefore.length + outerBefore.length + 6
  let selectedFuel := threeFuel + 1
  have rootCopiedAtChild : copyManyWithMacros macros
      (selectedFuel + rootBefore.length + 1) origin copyHoles [] fresh
      (rootBefore ++ .list outerItems :: rootAfter) = some (copied, final) := by
    simpa [selectedFuel, threeFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rootCopied
  obtain ⟨copiedPrefix, copiedOuter, copiedSuffix, before, rootMiddle,
    outerCopy, _rootSuffixCopy, rootOutputShape⟩ :=
    copyManyWithMacros_extract_element macros selectedFuel origin fresh copyHoles []
      rootBefore (.list outerItems) rootAfter copied final rootCopiedAtChild
  have ordinaryCopy := copyNeutralList_uses_copyMany macros threeFuel origin copyHoles []
    before outerItems ordinaryOuterHead
  rw [outerShape] at ordinaryCopy
  have outerCopy' : (operations macros (threeFuel + 1)).copy origin copyHoles [] before
      (.list (outerBefore ++ .list middleItems :: outerAfter)) =
        some (copiedOuter, rootMiddle) := by
    simpa [selectedFuel, threeFuel, outerShape] using outerCopy
  rw [ordinaryCopy] at outerCopy'
  have threeResult : ∃ copiedOuterItems threeFinal,
      copyManyWithMacros macros threeFuel origin copyHoles [] before
        (outerBefore ++ .list middleItems :: outerAfter) =
          some (copiedOuterItems, threeFinal) ∧
      copiedOuter = .list copiedOuterItems ∧ threeFinal = rootMiddle := by
    have outerCopy'' := outerCopy'
    obtain ⟨outerPair, outerRun, outputRun⟩ := option_bind_some outerCopy''
    rcases outerPair with ⟨copiedOuterItems, threeFinal⟩
    have outputEq := Option.some.inj outputRun
    have copiedEq := congrArg Prod.fst outputEq
    have finalEq := congrArg Prod.snd outputEq
    have threeAccepted : copyManyWithMacros macros threeFuel origin copyHoles [] before
        (outerBefore ++ .list middleItems :: outerAfter) =
          some (copiedOuterItems, threeFinal) := by
      simpa [threeFuel] using outerRun
    exact ⟨copiedOuterItems, threeFinal, threeAccepted,
      by simpa using copiedEq.symm, by simpa using finalEq⟩
  obtain ⟨copiedOuterItems, threeFinal, threeRun, copiedOuterEq, finalEq⟩ := threeResult
  subst copiedOuter
  subst rootMiddle
  obtain ⟨target, innerStatic⟩ :=
    nested_literal_call_at_three_list_indices_to_next_macro_step rules macros templateHoles
      copyHoles origin childOrigin innerFuel before threeFinal head arguments innerBefore
      innerAfter innerItems middleBefore middleAfter middleItems outerBefore outerAfter
      copiedOuterItems childRule known notHole lookupNone ordinaryInnerHead ordinaryMiddleHead
      innerShape middleShape (by simpa [threeFuel] using threeRun) childMember
      copiedChildMatches
  refine ⟨target, StaticCall.nested ?_ innerStatic⟩
  apply mem_append_right
  simp [outerShape, middleShape, innerShape]

/-- A substituted call head is conservatively represented by every rule of its
arity. If the copied argument-list traversal succeeds and preserves list
length, an actual matching next step is therefore covered by the template's
substituted-head candidate. -/
theorem substituted_head_template_call_to_next_macro_step (rules : List (Nat × Tree))
    (macros : List String) (templateHoles : List String) (copyHoles : Holes)
    (origin childOrigin fuel fresh final : Nat) (head copiedHead : Atom)
    (arguments copiedArguments : List Tree) (childRule childTemplate : Tree)
    (childHoles : Holes)
    (headIsHole : head.name ∈ templateHoles)
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (ordinaryHead : head.name ≠ "lambda" ∧ head.name ≠ "let" ∧ head.name ≠ "match")
    (copySucceeded : copyWithMacros macros (fuel + 1) origin copyHoles [] fresh
      (.list (.atom head :: arguments)) =
        some (.list (.atom copiedHead :: copiedArguments), final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule (.list (.atom copiedHead :: copiedArguments)) =
      some (childHoles, childTemplate)) :
    ∃ target, StaticCall rules templateHoles
      (.list (.atom head :: arguments)) target := by
  have headSubstituted : (lookup head.name copyHoles).isSome = true := by
    rw [holesAgree] at headIsHole
    exact lookup_isSome_of_mem_keys head.name copyHoles headIsHole
  have itemsCopiedOperation := copyWithMacros_substituted_head_uses_copyMany macros fuel
    origin copyHoles [] fresh head arguments (.atom copiedHead :: copiedArguments) final
    headSubstituted ordinaryHead copySucceeded
  have itemsCopied : copyManyWithMacros macros fuel origin copyHoles [] fresh
      (.atom head :: arguments) = some (.atom copiedHead :: copiedArguments, final) := by
    change (operations macros fuel).copyMany origin copyHoles [] fresh
      (.atom head :: arguments) = some (.atom copiedHead :: copiedArguments, final)
    exact itemsCopiedOperation
  obtain ⟨ruleName, arity, callHead, callArguments, signatureMatch, inputShape,
    nameMatch, arityMatch⟩ := successful_match_has_signature childRule
      (.list (.atom copiedHead :: copiedArguments)) childHoles childTemplate childMatched
  have shapeEq : Tree.list (Tree.atom callHead :: callArguments) =
      Tree.list (Tree.atom copiedHead :: copiedArguments) := inputShape.symm
  have itemsEq : Tree.atom callHead :: callArguments =
      Tree.atom copiedHead :: copiedArguments := Tree.list.inj shapeEq
  injection itemsEq with atomEq argumentsEq
  have callHeadEq : callHead = copiedHead := Tree.atom.inj atomEq
  have ruleNameEq : ruleName = copiedHead.name := nameMatch.symm.trans
    (congrArg Atom.name callHeadEq)
  have arityEq : arity = arguments.length := by
    calc
      arity = callArguments.length := arityMatch
      _ = copiedArguments.length := by rw [argumentsEq]
      _ = arguments.length := by
        have lengths := copyManyWithMacros_preserves_length macros fuel origin copyHoles []
          fresh (.atom head :: arguments) (.atom copiedHead :: copiedArguments) final itemsCopied
        simp only [List.length_cons] at lengths
        omega
  rw [ruleNameEq, arityEq] at signatureMatch
  obtain ⟨target, found⟩ := findRule_of_member_signature copiedHead.name arguments.length 0
    rules childOrigin childRule childMember signatureMatch
  have candidate := findRule_mem_targetsOfArity copiedHead.name arguments.length 0
    rules target found
  exact ⟨target, StaticCall.substitutedHead headIsHole candidate⟩

def HasStaticCall (rules : List (Nat × Tree)) (holes : List String)
    (trees : List Tree) (target : Nat) : Prop :=
  ∃ tree, tree ∈ trees ∧ StaticCall rules holes tree target

theorem call_extraction_complete (fuel : Nat) :
    (∀ rules holes tree targets, calls fuel rules holes tree = some targets →
      ∀ target, StaticCall rules holes tree target → target ∈ targets) ∧
    (∀ rules holes trees targets, callsMany fuel rules holes trees = some targets →
      ∀ target, HasStaticCall rules holes trees target → target ∈ targets) := by
  induction fuel with
  | zero =>
      constructor
      · intro rules holes tree targets checked target _call
        simp [calls, callOperations] at checked
      · intro rules holes trees targets checked target _call
        simp [callsMany, callOperations] at checked
  | succ fuel ih =>
      constructor
      · intro rules holes tree targets checked target call
        cases tree with
        | atom atom => cases call
        | list items =>
            simp only [calls, callOperations] at checked
            generalize nestedResult : (callOperations fuel).callsMany rules holes items = nestedOption at checked
            cases nestedOption with
            | none => simp [nestedResult] at checked
            | some nested =>
                cases call with
                | direct notHole found =>
                    simp [nestedResult, notHole] at checked
                    subst targets
                    exact mem_append_left _ _ found
                | substitutedHead isHole member =>
                    simp [nestedResult, isHole] at checked
                    subst targets
                    exact mem_append_left _ _ member
                | nested member inside =>
                    have nestedMember := ih.2 rules holes items nested nestedResult target
                      ⟨_, member, inside⟩
                    cases items with
                    | nil => simp at member
                    | cons first rest =>
                        cases first with
                        | atom head =>
                            by_cases isHole : head.name ∈ holes
                            · simp [nestedResult, isHole] at checked
                              subst targets
                              exact mem_append_right _ _ nestedMember
                            · simp [nestedResult, isHole] at checked
                              subst targets
                              exact mem_append_right _ _ nestedMember
                        | list nestedHead =>
                            simp [nestedResult] at checked
                            subst targets
                            exact nestedMember
      · intro rules holes trees targets checked target call
        cases trees with
        | nil => rcases call with ⟨tree, member, _⟩; simp at member
        | cons head tail =>
            simp only [callsMany, callOperations] at checked
            generalize headResult : (callOperations fuel).calls rules holes head = headOption at checked
            cases headOption with
            | none => simp [headResult] at checked
            | some headCalls =>
                generalize tailResult : (callOperations fuel).callsMany rules holes tail = tailOption at checked
                cases tailOption with
                | none => simp [headResult, tailResult] at checked
                | some tailCalls =>
                    simp [headResult, tailResult] at checked
                    have resultEq : headCalls ++ tailCalls = targets := checked
                    subst targets
                    rcases call with ⟨tree, member, inside⟩
                    rcases List.mem_cons.mp member with same | inTail
                    · subst tree
                      exact mem_append_left _ _
                        (ih.1 rules holes head headCalls headResult target inside)
                    · exact mem_append_right _ _
                        (ih.2 rules holes tail tailCalls tailResult target ⟨tree, inTail, inside⟩)

def graphRows (fuel : Nat) (rules : List (Nat × Tree)) : Nat → List (Nat × Tree) → Option (List Edge)
  | _, [] => some []
  | index, (_, rule) :: tail => do
      let (holes, template) ← parameters rule
      let dependencies ← calls fuel rules holes template
      let remaining ← graphRows fuel rules (index + 1) tail
      pure (dependencies.map (fun child => (child, index)) ++ remaining)

theorem graphRows_dependency_edge (fuel : Nat) (rules : List (Nat × Tree))
    (index owner : Nat) (rule : Tree) (tail : List (Nat × Tree))
    (holes : List String) (template : Tree) (dependency : Nat) (edges : List Edge)
    (parsed : parameters rule = some (holes, template))
    (dependencyCheck : calls fuel rules holes template = some dependencies)
    (member : dependency ∈ dependencies)
    (checked : graphRows fuel rules index ((owner, rule) :: tail) = some edges) :
    (dependency, index) ∈ edges := by
  simp only [graphRows, parsed, bind, Option.bind] at checked
  obtain ⟨actualDependencies, actualCheck, restCheck⟩ := option_bind_some checked
  obtain ⟨remaining, _remainingCheck, resultEq⟩ := option_bind_some restCheck
  have sameDependencies : actualDependencies = dependencies :=
    Option.some.inj (actualCheck.symm.trans dependencyCheck)
  subst actualDependencies
  have edgesEq : dependencies.map (fun child => (child, index)) ++ remaining = edges := by
    simpa using resultEq
  rw [← edgesEq]
  exact mem_append_left _ _ (mem_map_counter dependencies dependency index member)

theorem graphRows_root_call_edge (fuel : Nat) (rules : List (Nat × Tree))
    (index owner : Nat) (rule : Tree) (tail : List (Nat × Tree))
    (holes : List String) (template : Tree) (head : Atom) (arguments : List Tree)
    (target : Nat) (edges : List Edge)
    (parsed : parameters rule = some (holes, template))
    (templateShape : template = .list (.atom head :: arguments))
    (notHole : head.name ∉ holes)
    (found : findRule head.name arguments.length 0 rules = some target)
    (checked : graphRows (fuel + 1) rules index ((owner, rule) :: tail) = some edges) :
    (target, index) ∈ edges := by
  have checkedCopy := checked
  simp only [graphRows, parsed, bind, Option.bind] at checkedCopy
  obtain ⟨dependencies, dependencyCheck, _restCheck⟩ := option_bind_some checkedCopy
  have included := calls_direct_macro_complete fuel rules holes head arguments target
    dependencies notHole found (by simpa [templateShape] using dependencyCheck)
  exact graphRows_dependency_edge (fuel + 1) rules index owner rule tail holes template
    target edges parsed dependencyCheck included checked

theorem graphRows_static_call_edge (fuel : Nat) (rules : List (Nat × Tree))
    (index owner : Nat) (rule : Tree) (tail : List (Nat × Tree))
    (holes : List String) (template : Tree) (target : Nat) (edges : List Edge)
    (parsed : parameters rule = some (holes, template))
    (dependencyCheck : calls fuel rules holes template = some dependencies)
    (staticCall : StaticCall rules holes template target)
    (checked : graphRows fuel rules index ((owner, rule) :: tail) = some edges) :
    (target, index) ∈ edges := by
  have included := (call_extraction_complete fuel).1 rules holes template dependencies
    dependencyCheck target staticCall
  exact graphRows_dependency_edge fuel rules index owner rule tail holes template target
    edges parsed dependencyCheck included checked

private theorem graphRows_cons_parts (fuel : Nat) (rules : List (Nat × Tree))
    (index owner : Nat) (rule : Tree) (tail : List (Nat × Tree)) (edges : List Edge)
    (accepted : graphRows fuel rules index ((owner, rule) :: tail) = some edges) :
    ∃ holes template dependencies remaining,
      parameters rule = some (holes, template) ∧
      calls fuel rules holes template = some dependencies ∧
      graphRows fuel rules (index + 1) tail = some remaining ∧
      dependencies.map (fun child => (child, index)) ++ remaining = edges := by
  simp only [graphRows, bind, Option.bind] at accepted
  obtain ⟨parsed, parsedResult, restCheck⟩ := option_bind_some accepted
  rcases parsed with ⟨holes, template⟩
  have parsedRule : parameters rule = some (holes, template) := parsedResult
  obtain ⟨dependencies, dependencyCheck, restCheck⟩ := option_bind_some restCheck
  obtain ⟨remaining, remainingCheck, resultEq⟩ := option_bind_some restCheck
  have edgesEq : dependencies.map (fun child => (child, index)) ++ remaining = edges := by
    simpa using resultEq
  exact ⟨holes, template, dependencies, remaining, parsedRule, dependencyCheck,
    remainingCheck, edgesEq⟩

inductive GraphCall (rules : List (Nat × Tree)) : Nat → List (Nat × Tree) → Edge → Prop where
  | here {index owner : Nat} {rule : Tree} {tail : List (Nat × Tree)}
      {holes : List String} {template : Tree} {child : Nat} :
      parameters rule = some (holes, template) → StaticCall rules holes template child →
      GraphCall rules index ((owner, rule) :: tail) (child, index)
  | later {index owner : Nat} {head : Tree} {tail : List (Nat × Tree)} {edge : Edge} :
      GraphCall rules (index + 1) tail edge →
      GraphCall rules index ((owner, head) :: tail) edge

theorem graphRows_contains_static_calls (fuel : Nat) (rules : List (Nat × Tree))
    (index : Nat) (rows : List (Nat × Tree)) (edges : List Edge)
    (checked : graphRows fuel rules index rows = some edges)
    (call : GraphCall rules index rows edge) : edge ∈ edges := by
  induction call generalizing edges with
  | @here index owner rule tail holes template child parsed staticCall =>
      simp only [graphRows, parsed, bind, Option.bind] at checked
      obtain ⟨dependencies, dependencyCheck, restCheck⟩ := option_bind_some checked
      obtain ⟨remaining, _remainingCheck, resultEq⟩ := option_bind_some restCheck
      have included := (call_extraction_complete fuel).1 rules holes template dependencies
        dependencyCheck child staticCall
      have mapped := mem_append_left (dependencies.map (fun target => (target, index)))
        remaining (mem_map_counter dependencies child index included)
      have edgesEq : dependencies.map (fun target => (target, index)) ++ remaining = edges := by
        simpa using resultEq
      rw [← edgesEq]
      exact mapped
  | @later index owner head tail edge _inner ih =>
      obtain ⟨_holes, _template, _dependencies, remaining, _parsed, _dependencyCheck,
        remainingCheck, edgesEq⟩ := graphRows_cons_parts fuel rules index owner head tail edges checked
      have edgeInTail := ih remaining remainingCheck
      rw [← edgesEq]
      exact mem_append_right _ _ edgeInTail

def graph (fuel : Nat) (rules : List (Nat × Tree)) : Option (List Edge) := graphRows fuel rules 0 rules

def rank (ranks : List Nat) (node : Nat) : Nat := (ranks[node]?).getD 0

def checkRanks (edges : List Edge) (ranks : List Nat) : Bool :=
  edges.all (fun edge => decide (rank ranks edge.1 < rank ranks edge.2))

def Calls (edges : List Edge) (child parent : Nat) : Prop := (child, parent) ∈ edges

theorem checkRanks_decreases (accepted : checkRanks edges ranks = true)
    (edge : Calls edges child parent) : rank ranks child < rank ranks parent := by
  have all := List.all_eq_true.mp accepted
  exact of_decide_eq_true (all (child, parent) edge)

theorem template_static_call_rank_decreases (fuel : Nat) (rules : List (Nat × Tree))
    (index owner : Nat) (rule : Tree) (tail : List (Nat × Tree))
    (holes : List String) (template : Tree) (target : Nat) (edges : List Edge)
    (ranks : List Nat)
    (parsed : parameters rule = some (holes, template))
    (dependencyCheck : calls fuel rules holes template = some dependencies)
    (staticCall : StaticCall rules holes template target)
    (graphAccepted : graphRows fuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    rank ranks target < rank ranks index :=
  checkRanks_decreases ranksAccepted
    (graphRows_static_call_edge fuel rules index owner rule tail holes template target edges
      parsed dependencyCheck staticCall graphAccepted)

/-- Add the accepted template graph rank to the certified local-copy result.
The child certificate therefore determines a decreasing graph edge for this
literal sibling callsite. -/
theorem literal_call_at_list_index_certified_rank_decreases
    (graphFuel : Nat) (rules : List (Nat × Tree)) (index owner childOrigin : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (arguments beforeItems afterItems : List Tree)
    (childRule copiedCall childOutput : Tree) (copyHoles : Holes) (renames : Renames)
    (origin fuel callStart callFinal childFuel childFresh childFinal : Nat)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (fuelMatches : childFuel = fuel + 1)
    (callCopy : copyWithMacros (macroNames rules) childFuel origin copyHoles renames callStart
      (.list (.atom head :: arguments)) = some (copiedCall, callFinal))
    (childStepAccepted : NLisp.ExpansionCertificate.checkStep rules childOrigin childFuel
      childFresh childFinal childRule copiedCall childOutput = true)
    (parsed : parameters rule = some (templateHoles,
      .list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)) =
        some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, StaticCall rules templateHoles
      (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)) target ∧
      rank ranks target < rank ranks index := by
  obtain ⟨target, staticCall⟩ := literal_call_at_list_index_to_certified_macro_step
    rules (macroNames rules) templateHoles copyHoles renames origin childOrigin fuel callStart
    callFinal childFuel childFresh childFinal head arguments beforeItems afterItems copiedCall
    childRule childOutput known notHole lookupNone fuelMatches callCopy childStepAccepted
  exact ⟨target, staticCall,
    template_static_call_rank_decreases graphFuel rules index owner rule tail templateHoles
      (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)) target edges ranks
      parsed dependencyCheck staticCall graphAccepted ranksAccepted⟩

/-- Compose full parent-list copying with a child expansion certificate at a
selected sibling position. The certificate is required for the exact element
and counter interval extracted from the successful parent copy; no independent
match premise for an unrelated copy result is needed. -/
theorem literal_call_at_list_index_full_copy_certified_rank_decreases
    (graphFuel rootFuel childFuel : Nat) (rules : List (Nat × Tree))
    (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (arguments beforeItems afterItems copied : List Tree)
    (childRule childOutput : Tree) (copyHoles : Holes)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (childFuelMatches : childFuel = rootFuel + 1)
    (parentCopy : copyManyWithMacros (macroNames rules)
      (childFuel + beforeItems.length + 1) origin copyHoles [] fresh
      (beforeItems ++ .list (.atom head :: arguments) :: afterItems) = some (copied, final))
    (selectedChildAccepted : ∀ copiedPrefix copiedCall copiedSuffix callStart callFinal,
      copyWithMacros (macroNames rules) childFuel origin copyHoles [] callStart
        (.list (.atom head :: arguments)) = some (copiedCall, callFinal) →
      copyManyWithMacros (macroNames rules) childFuel origin copyHoles [] callFinal
        afterItems = some (copiedSuffix, final) →
      copied = copiedPrefix ++ copiedCall :: copiedSuffix →
      ExpansionCertificate.checkStep rules childOrigin childFuel callStart callFinal
        childRule copiedCall childOutput = true)
    (parsed : parameters rule = some (templateHoles,
      .list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)) =
        some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget,
      StaticCall rules templateHoles
        (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)) childTarget ∧
      rank ranks childTarget < rank ranks index := by
  obtain ⟨copiedPrefix, copiedCall, copiedSuffix, callStart, callFinal,
      callCopy, suffixCopy, copiedEq⟩ :=
    copyManyWithMacros_extract_element (macroNames rules) childFuel origin fresh copyHoles []
      beforeItems (.list (.atom head :: arguments)) afterItems copied final parentCopy
  have childAccepted := selectedChildAccepted copiedPrefix copiedCall copiedSuffix
    callStart callFinal callCopy suffixCopy copiedEq
  obtain ⟨childHoles, childTemplate, childMember, childMatched, _childCopy⟩ :=
    ExpansionCertificate.checkStep_sound childAccepted
  have callCopy' : copyWithMacros (macroNames rules) (rootFuel + 1) origin copyHoles []
      callStart (.list (.atom head :: arguments)) = some (copiedCall, callFinal) := by
    simpa [childFuelMatches] using callCopy
  obtain ⟨copiedArguments, argumentsCopied, _callShape⟩ :=
    copyWithMacros_root_macro_call_parts (macroNames rules) rootFuel origin copyHoles []
      callStart callFinal head arguments copiedCall known lookupNone callCopy'
  obtain ⟨childTarget, templateCall⟩ := root_template_call_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles [] origin childOrigin rootFuel callStart callFinal
    head arguments copiedArguments childRule childTemplate copiedCall childHoles known notHole
    lookupNone argumentsCopied callCopy' childMember childMatched
  have staticCall : StaticCall rules templateHoles
      (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)) childTarget := by
    refine StaticCall.nested ?_ templateCall
    apply mem_append_right
    simp
  exact ⟨childTarget, staticCall,
    template_static_call_rank_decreases graphFuel rules index owner rule tail
      templateHoles (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems))
      childTarget edges ranks parsed dependencyCheck staticCall graphAccepted ranksAccepted⟩

/- Special-form dispatch gives lambda and let hole heads their own copy
branches. These two lemmas combine those branches with the already checked
template graph row, so a real subsequent match has an explicit decreasing
rank edge even though the dispatcher kept the special head literal. -/
theorem let_hole_head_copy_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule template childRule childTemplate output : Tree) (tail : List (Nat × Tree))
    (templateHoles : List String) (copyHoles : Holes) (letHead : Atom)
    (bindings : List Tree) (body : Tree) (originalNames : List String)
    (substitutedHead : Tree) (childHoles : Holes) (dependencies : List Nat)
    (edges : List Edge) (ranks : List Nat)
    (letForm : letHead.name = "let")
    (letHole : lookup letHead.name copyHoles = some substitutedHead)
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (bindingNamesMatch : bindingNames bindings = some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (copySucceeded : copyWithMacros (macroNames rules) (copyFuel + 1) origin copyHoles []
      fresh (.list [.atom letHead, .list bindings, body]) = some (output, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate))
    (parsed : MacroTermination.parameters rule = some
      (templateHoles, .list [.atom letHead, .list bindings, body]))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom letHead, .list bindings, body]) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom letHead, .list bindings, body]) target ∧
      rank ranks target < rank ranks index := by
  obtain ⟨target, staticCall⟩ := let_hole_head_call_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles copyFuel origin childOrigin fresh final letHead
    bindings body output childRule childTemplate originalNames substitutedHead childHoles
    letForm letHole holesAgree bindingNamesMatch bindingsDistinct copySucceeded childMember childMatched
  exact ⟨target, staticCall, template_static_call_rank_decreases graphFuel rules index owner
    rule tail templateHoles (.list [.atom letHead, .list bindings, body]) target edges ranks
    parsed dependencyCheck staticCall graphAccepted ranksAccepted⟩

theorem lambda_hole_head_copy_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule template childRule childTemplate output : Tree) (tail : List (Nat × Tree))
    (templateHoles : List String) (copyHoles : Holes) (lambdaHead : Atom)
    (parameters : List Tree) (result body : Tree) (originalNames : List String)
    (substitutedHead : Tree) (childHoles : Holes) (dependencies : List Nat)
    (edges : List Edge) (ranks : List Nat)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaHole : lookup lambdaHead.name copyHoles = some substitutedHead)
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (parameterNamesMatch : parameterNames parameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (copySucceeded : copyWithMacros (macroNames rules) (copyFuel + 1) origin copyHoles []
      fresh (.list [.atom lambdaHead, .list parameters, result, body]) = some (output, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate))
    (parsed : MacroTermination.parameters rule = some
      (templateHoles, .list [.atom lambdaHead, .list parameters, result, body]))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom lambdaHead, .list parameters, result, body]) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom lambdaHead, .list parameters, result, body]) target ∧
      rank ranks target < rank ranks index := by
  obtain ⟨target, staticCall⟩ := lambda_hole_head_call_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles copyFuel origin childOrigin fresh final lambdaHead
    parameters result body output childRule childTemplate originalNames substitutedHead childHoles
    lambdaForm lambdaHole holesAgree parameterNamesMatch parametersDistinct copySucceeded
    childMember childMatched
  exact ⟨target, staticCall, template_static_call_rank_decreases graphFuel rules index owner
    rule tail templateHoles (.list [.atom lambdaHead, .list parameters, result, body]) target
    edges ranks parsed dependencyCheck staticCall graphAccepted ranksAccepted⟩

/-- The let-special-form hole-head path also accepts the real child-step
certificate: its checker proof supplies the child rule match used by the
template edge and strict rank decrease. -/
theorem let_hole_head_certified_rank_decreases (graphFuel copyFuel childFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final childFresh childFinal : Nat)
    (rule template childRule output childOutput : Tree) (tail : List (Nat × Tree))
    (templateHoles : List String) (copyHoles : Holes) (letHead : Atom)
    (bindings : List Tree) (body : Tree) (originalNames : List String)
    (substitutedHead : Tree) (dependencies : List Nat) (edges : List Edge)
    (ranks : List Nat)
    (letForm : letHead.name = "let")
    (letHole : lookup letHead.name copyHoles = some substitutedHead)
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (bindingNamesMatch : bindingNames bindings = some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (copySucceeded : copyWithMacros (macroNames rules) (copyFuel + 1) origin copyHoles []
      fresh (.list [.atom letHead, .list bindings, body]) = some (output, final))
    (childStepAccepted : NLisp.ExpansionCertificate.checkStep rules childOrigin childFuel
      childFresh childFinal childRule output childOutput = true)
    (parsed : MacroTermination.parameters rule = some
      (templateHoles, .list [.atom letHead, .list bindings, body]))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom letHead, .list bindings, body]) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom letHead, .list bindings, body]) target ∧
      rank ranks target < rank ranks index := by
  obtain ⟨childHoles, childTemplate, childMember, childMatched, _childCopied⟩ :=
    NLisp.ExpansionCertificate.checkStep_sound childStepAccepted
  exact let_hole_head_copy_rank_decreases graphFuel copyFuel rules index owner childOrigin origin
    fresh final rule template childRule childTemplate output tail templateHoles copyHoles letHead
    bindings body originalNames substitutedHead childHoles dependencies edges ranks letForm letHole
    holesAgree bindingNamesMatch bindingsDistinct copySucceeded childMember childMatched parsed
    dependencyCheck graphAccepted ranksAccepted

/-- The lambda-special-form hole-head path exposes the same certified child
step connection as let, including its template edge and rank decrease. -/
theorem lambda_hole_head_certified_rank_decreases (graphFuel copyFuel childFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final childFresh childFinal : Nat)
    (rule template childRule output childOutput : Tree) (tail : List (Nat × Tree))
    (templateHoles : List String) (copyHoles : Holes) (lambdaHead : Atom)
    (parameters : List Tree) (result body : Tree) (originalNames : List String)
    (substitutedHead : Tree) (dependencies : List Nat) (edges : List Edge)
    (ranks : List Nat)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaHole : lookup lambdaHead.name copyHoles = some substitutedHead)
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (parameterNamesMatch : parameterNames parameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (copySucceeded : copyWithMacros (macroNames rules) (copyFuel + 1) origin copyHoles []
      fresh (.list [.atom lambdaHead, .list parameters, result, body]) = some (output, final))
    (childStepAccepted : NLisp.ExpansionCertificate.checkStep rules childOrigin childFuel
      childFresh childFinal childRule output childOutput = true)
    (parsed : MacroTermination.parameters rule = some
      (templateHoles, .list [.atom lambdaHead, .list parameters, result, body]))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom lambdaHead, .list parameters, result, body]) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, StaticCall rules templateHoles
      (.list [.atom lambdaHead, .list parameters, result, body]) target ∧
      rank ranks target < rank ranks index := by
  obtain ⟨childHoles, childTemplate, childMember, childMatched, _childCopied⟩ :=
    NLisp.ExpansionCertificate.checkStep_sound childStepAccepted
  exact lambda_hole_head_copy_rank_decreases graphFuel copyFuel rules index owner childOrigin
    origin fresh final rule template childRule childTemplate output tail templateHoles copyHoles
    lambdaHead parameters result body originalNames substitutedHead childHoles dependencies edges
    ranks lambdaForm lambdaHole holesAgree parameterNamesMatch parametersDistinct copySucceeded
    childMember childMatched parsed dependencyCheck graphAccepted ranksAccepted

/-- The actual successful child-rule match on a copied special-form `match`
whose literal head is also a template hole yields a strict decrease in the
accepted conservative graph rank. The copy-to-output shape and arity remain
explicit, so this theorem does not claim that arbitrary match-case copying
preserves case count. -/
theorem match_hole_head_output_rank_decreases (fuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (template : Tree) (copyHoles : Holes) (matchHead : Atom)
    (sourceArguments copiedArguments : List Tree)
    (childRule childTemplate output : Tree) (childHoles : Holes)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchHole : lookup matchHead.name copyHoles = some (.atom matchHead))
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (templateEq : template = .list (.atom matchHead :: sourceArguments))
    (outputShape : output = .list (.atom matchHead :: copiedArguments))
    (sameArity : sourceArguments.length = copiedArguments.length)
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate))
    (parsed : parameters rule = some (templateHoles, template))
    (dependencyCheck : calls fuel rules templateHoles template = some dependencies)
    (graphAccepted : graphRows fuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, StaticCall rules templateHoles template target ∧
      rank ranks target < rank ranks index := by
  obtain ⟨target, staticCall⟩ := match_hole_head_output_to_template_static_call
    rules templateHoles copyHoles template matchHead sourceArguments copiedArguments childOrigin
    childRule childTemplate output childHoles matchHole holesAgree templateEq outputShape sameArity
    childMember childMatched
  exact ⟨target, staticCall, template_static_call_rank_decreases fuel rules index owner rule
    tail templateHoles template target edges ranks parsed dependencyCheck staticCall
    graphAccepted ranksAccepted⟩

/-- In the one-case special-form encoding, the copy decomposition and the
structural length theorem for `copyCases` discharge the output arity premise
needed above. Thus an actual successful child match on this copied `match`
has a decreasing rank edge from the root source template. -/
theorem match_hole_head_default_copy_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule template childRule childTemplate copied : Tree)
    (tail : List (Nat × Tree)) (templateHoles : List String) (copyHoles : Holes)
    (matchHead : Atom) (scrutineeItems : List Tree) (caseBody : Tree)
    (childHoles : Holes) (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchHole : lookup matchHead.name copyHoles = some (.atom matchHead))
    (matchForm : matchHead.name = "match")
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (templateEq : template = .list [.atom matchHead, .list scrutineeItems, caseBody])
    (copiedSuccessfully : copyWithMacros (macroNames rules) (copyFuel + 1) origin
      copyHoles [] fresh (.list [.atom matchHead, .list scrutineeItems, caseBody]) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule copied = some (childHoles, childTemplate))
    (parsed : parameters rule = some (templateHoles, template))
    (dependencyCheck : calls graphFuel rules templateHoles template = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, StaticCall rules templateHoles template target ∧
      rank ranks target < rank ranks index := by
  let sourceArguments : List Tree := [.list scrutineeItems, caseBody]
  obtain ⟨copiedScrutinee, afterScrutinee, copiedCases, _scrutineeCopy, casesCopy,
    copiedShape⟩ := copyWithMacros_match_hole_head_default_parts (macroNames rules)
      copyFuel origin fresh final copyHoles [] matchHead scrutineeItems caseBody copied
      (.atom matchHead) matchForm matchHole copiedSuccessfully
  have copiedCasesLength := copyCasesWithMacros_preserves_length (macroNames rules)
    copyFuel origin copyHoles [] afterScrutinee [caseBody] copiedCases final casesCopy
  have casesLength : copiedCases.length = 1 := by simpa using copiedCasesLength
  have copiedArgumentsLength : (copiedScrutinee :: copiedCases).length = sourceArguments.length := by
    simp [casesLength, sourceArguments]
  have sourceArgumentsLength : sourceArguments.length = (copiedScrutinee :: copiedCases).length :=
    copiedArgumentsLength.symm
  have sourceTemplateShape : template = .list (.atom matchHead :: sourceArguments) := by
    simpa [sourceArguments] using templateEq
  have outputShape : copied = .list
      (.atom matchHead :: (copiedScrutinee :: copiedCases)) := copiedShape
  exact match_hole_head_output_rank_decreases graphFuel rules index owner childOrigin
    rule tail templateHoles template copyHoles matchHead sourceArguments
    (copiedScrutinee :: copiedCases) childRule childTemplate copied childHoles dependencies
    edges ranks matchHole holesAgree sourceTemplateShape outputShape sourceArgumentsLength
    childMember (by simpa using childMatched) parsed dependencyCheck
    graphAccepted ranksAccepted

/-- A successful expansion-certificate child step on the copied one-case
`match` is enough to obtain the child rule match needed by the rank argument.
This connects the special-form copy path to an actual accepted macro step. -/
theorem match_hole_head_default_certified_rank_decreases
    (graphFuel copyFuel childFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final childFresh childFinal : Nat)
    (rule template childRule copied childOutput : Tree) (tail : List (Nat × Tree))
    (templateHoles : List String) (copyHoles : Holes) (matchHead : Atom)
    (scrutineeItems : List Tree) (caseBody : Tree) (dependencies : List Nat)
    (edges : List Edge) (ranks : List Nat)
    (matchHole : lookup matchHead.name copyHoles = some (.atom matchHead))
    (matchForm : matchHead.name = "match")
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (templateEq : template = .list [.atom matchHead, .list scrutineeItems, caseBody])
    (copiedSuccessfully : copyWithMacros (macroNames rules) (copyFuel + 1) origin
      copyHoles [] fresh (.list [.atom matchHead, .list scrutineeItems, caseBody]) =
        some (copied, final))
    (childStepAccepted : NLisp.ExpansionCertificate.checkStep rules childOrigin childFuel
      childFresh childFinal childRule copied childOutput = true)
    (parsed : parameters rule = some (templateHoles, template))
    (dependencyCheck : calls graphFuel rules templateHoles template = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, StaticCall rules templateHoles template target ∧
      rank ranks target < rank ranks index := by
  obtain ⟨childHoles, childTemplate, childMember, childMatched, _childCopied⟩ :=
    NLisp.ExpansionCertificate.checkStep_sound childStepAccepted
  exact match_hole_head_default_copy_rank_decreases graphFuel copyFuel rules index owner
    childOrigin origin fresh final rule template childRule childTemplate copied tail
    templateHoles copyHoles matchHead scrutineeItems caseBody childHoles dependencies edges ranks
    matchHole matchForm holesAgree templateEq copiedSuccessfully childMember childMatched
    parsed dependencyCheck graphAccepted ranksAccepted

/-- The same copy-to-rank argument covers the multi-case dispatcher path.
The source call and copied call may have any arity; `copyCases` length
preservation establishes that the child rule sees the same number of
arguments after copying. -/
theorem match_hole_head_cases_copy_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule template childRule childTemplate copied : Tree)
    (tailRules : List (Nat × Tree)) (templateHoles : List String) (copyHoles : Holes)
    (matchHead : Atom) (scrutineeItems : List Tree) (firstCase secondCase : Tree)
    (caseTail : List Tree) (childHoles : Holes)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchHole : lookup matchHead.name copyHoles = some (.atom matchHead))
    (matchForm : matchHead.name = "match")
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (templateEq : template = .list
      (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail))
    (copiedSuccessfully : copyWithMacros (macroNames rules) (copyFuel + 1) origin
      copyHoles [] fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule copied = some (childHoles, childTemplate))
    (parsed : parameters rule = some (templateHoles, template))
    (dependencyCheck : calls graphFuel rules templateHoles template = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tailRules) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, StaticCall rules templateHoles template target ∧
      rank ranks target < rank ranks index := by
  let sourceArguments : List Tree :=
    .list scrutineeItems :: firstCase :: secondCase :: caseTail
  obtain ⟨copiedScrutinee, afterScrutinee, copiedCases, _scrutineeCopy, casesCopy,
    copiedShape⟩ := copyWithMacros_match_hole_head_cases_parts (macroNames rules)
      copyFuel origin fresh final copyHoles [] matchHead scrutineeItems firstCase secondCase
      caseTail copied (.atom matchHead) matchForm matchHole copiedSuccessfully
  have copiedCasesLength := copyCasesWithMacros_preserves_length (macroNames rules)
    copyFuel origin copyHoles [] afterScrutinee
    (firstCase :: secondCase :: caseTail) copiedCases final casesCopy
  have sameArity : (copiedScrutinee :: copiedCases).length = sourceArguments.length := by
    simp [sourceArguments, copiedCasesLength]
  have sourceTemplateShape : template = .list (.atom matchHead :: sourceArguments) := by
    simpa [sourceArguments] using templateEq
  have outputShape : copied = .list
      (.atom matchHead :: (copiedScrutinee :: copiedCases)) := copiedShape
  exact match_hole_head_output_rank_decreases graphFuel rules index owner childOrigin
    rule tailRules templateHoles template copyHoles matchHead sourceArguments
    (copiedScrutinee :: copiedCases) childRule childTemplate copied childHoles dependencies
    edges ranks matchHole holesAgree sourceTemplateShape outputShape sameArity.symm childMember
    (by simpa using childMatched) parsed dependencyCheck graphAccepted ranksAccepted

/-- Multi-case hole-head `match` rank decrease from an actually accepted
child expansion step. The certificate checker supplies the rule membership
and successful child match consumed by the copy-to-rank proof. -/
theorem match_hole_head_cases_certified_rank_decreases
    (graphFuel copyFuel childFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final childFresh childFinal : Nat)
    (rule template childRule copied childOutput : Tree) (tailRules : List (Nat × Tree))
    (templateHoles : List String) (copyHoles : Holes) (matchHead : Atom)
    (scrutineeItems : List Tree) (firstCase secondCase : Tree) (caseTail : List Tree)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchHole : lookup matchHead.name copyHoles = some (.atom matchHead))
    (matchForm : matchHead.name = "match")
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (templateEq : template = .list
      (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail))
    (copiedSuccessfully : copyWithMacros (macroNames rules) (copyFuel + 1) origin
      copyHoles [] fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)) =
        some (copied, final))
    (childStepAccepted : NLisp.ExpansionCertificate.checkStep rules childOrigin childFuel
      childFresh childFinal childRule copied childOutput = true)
    (parsed : parameters rule = some (templateHoles, template))
    (dependencyCheck : calls graphFuel rules templateHoles template = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tailRules) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, StaticCall rules templateHoles template target ∧
      rank ranks target < rank ranks index := by
  obtain ⟨childHoles, childTemplate, childMember, childMatched, _childCopied⟩ :=
    NLisp.ExpansionCertificate.checkStep_sound childStepAccepted
  exact match_hole_head_cases_copy_rank_decreases graphFuel copyFuel rules index owner
    childOrigin origin fresh final rule template childRule childTemplate copied tailRules
    templateHoles copyHoles matchHead scrutineeItems firstCase secondCase caseTail childHoles
    dependencies edges ranks matchHole matchForm holesAgree templateEq copiedSuccessfully
    childMember childMatched parsed dependencyCheck graphAccepted ranksAccepted

/-- Compose the operational next-step rank decrease with case-binder
freshness for the same accepted hole-head match copy. -/
theorem match_hole_head_cases_copy_rank_and_freshness
    (graphFuel copyFuel : Nat) (rules : List (Nat × Tree))
    (index owner childOrigin origin fresh final : Nat)
    (rule template childRule childTemplate copied : Tree)
    (tailRules : List (Nat × Tree)) (templateHoles : List String) (copyHoles : Holes)
    (matchHead : Atom) (scrutineeItems : List Tree)
    (firstCase secondCase : Tree) (caseTail : List Tree) (childHoles : Holes)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchHole : lookup matchHead.name copyHoles = some (.atom matchHead))
    (matchForm : matchHead.name = "match")
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (templateEq : template = .list
      (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail))
    (copiedSuccessfully : copyWithMacros (macroNames rules) (copyFuel + 1) origin
      copyHoles [] fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule copied = some (childHoles, childTemplate))
    (parsed : parameters rule = some (templateHoles, template))
    (dependencyCheck : calls graphFuel rules templateHoles template = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tailRules) = some edges)
    (ranksAccepted : checkRanks edges ranks = true)
    (safe : MacroCounterSafeCases (macroNames rules) (firstCase :: secondCase :: caseTail)) :
    ∃ target copiedScrutinee afterScrutinee copiedCases,
      StaticCall rules templateHoles template target ∧
      rank ranks target < rank ranks index ∧
      (operations (macroNames rules) copyFuel).copy origin copyHoles [] fresh
        (.list scrutineeItems) = some (copiedScrutinee, afterScrutinee) ∧
      copyCasesWithMacros (macroNames rules) copyFuel origin copyHoles [] afterScrutinee
        (firstCase :: secondCase :: caseTail) = some (copiedCases, final) ∧
      copied = .list (.atom matchHead :: copiedScrutinee :: copiedCases) ∧
      Unique (counterPreservingCaseTokens copiedCases) ∧
      (∀ sourceToken, sourceToken % 3 = 1 →
        sourceToken ∉ counterPreservingCaseTokens copiedCases) ∧
      (∀ token, token ∈ counterPreservingCaseTokens copiedCases →
        ∃ counter, afterScrutinee < counter ∧ counter ≤ final ∧ token = 3 * counter + 2) := by
  obtain ⟨target, staticCall, rankDecrease⟩ := match_hole_head_cases_copy_rank_decreases
    graphFuel copyFuel rules index owner childOrigin origin fresh final rule template childRule
    childTemplate copied tailRules templateHoles copyHoles matchHead scrutineeItems firstCase
    secondCase caseTail childHoles dependencies edges ranks matchHole matchForm holesAgree
    templateEq copiedSuccessfully childMember childMatched parsed dependencyCheck graphAccepted
    ranksAccepted
  obtain ⟨copiedScrutinee, afterScrutinee, copiedCases, scrutineeCopy, casesCopy, shape,
      unique, sourceAvoid, interval⟩ := copyWithMacros_match_hole_case_tokens_fresh
    (macroNames rules) copyFuel origin fresh final copyHoles [] matchHead scrutineeItems firstCase
    secondCase caseTail copied (.atom matchHead) matchForm matchHole safe copiedSuccessfully
  exact ⟨target, copiedScrutinee, afterScrutinee, copiedCases, staticCall, rankDecrease,
    scrutineeCopy, casesCopy, shape, unique, sourceAvoid, interval⟩

/-- The accepted graph rank decreases for the next macro step in a default
match case, starting from a successful copy of the complete match form. -/
theorem match_default_body_call_site_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (matchHead : Atom) (scrutineeItems bodyItems : List Tree)
    (cost : Nat) (copied : Tree) (head : Atom) (arguments : List Tree)
    (site : LiteralCallSite (macroNames rules) head arguments bodyItems cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : (macroNames rules).contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (bodyHeadSafe : counterNeutralListHead (macroNames rules) bodyItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list [.atom matchHead, .list scrutineeItems, .list [.list [], .list bodyItems]]))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + 3) origin copyHoles
      renames fresh (.list [.atom matchHead, .list scrutineeItems,
        .list [.list [], .list bodyItems]]) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom matchHead, .list scrutineeItems, .list [.list [], .list bodyItems]]) =
        some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := match_default_body_call_site_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles renames origin childOrigin copyFuel fresh final
    matchHead scrutineeItems bodyItems cost copied head arguments childRule site matchForm
    matchNotMacro matchNotHole bodyHeadSafe known notHole lookupNone wholeCopied childMember
    copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list [.atom matchHead, .list scrutineeItems,
      .list [.list [], .list bodyItems]]) childTarget edges ranks parsed dependencyCheck templateCall
    graphAccepted ranksAccepted⟩

/-- Accepted graph ranks decrease for a body call in any empty-pattern case
of a successful multi-case match copy. -/
theorem match_default_body_call_site_at_index_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (matchHead : Atom) (scrutineeItems bodyItems before suffix : List Tree)
    (beforeValid : CaseRows before)
    (twoCases : ∃ firstCase secondCase rest,
      before ++ .list [.list [], .list bodyItems] :: suffix = firstCase :: secondCase :: rest)
    (cost : Nat) (copied : Tree) (head : Atom) (arguments : List Tree)
    (site : LiteralCallSite (macroNames rules) head arguments bodyItems cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : (macroNames rules).contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (bodyHeadSafe : counterNeutralListHead (macroNames rules) bodyItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list (.atom matchHead :: .list scrutineeItems ::
        (before ++ .list [.list [], .list bodyItems] :: suffix))))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + before.length + 3)
      origin copyHoles renames fresh
      (.list (.atom matchHead :: .list scrutineeItems ::
        (before ++ .list [.list [], .list bodyItems] :: suffix))) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (.atom matchHead :: .list scrutineeItems ::
        (before ++ .list [.list [], .list bodyItems] :: suffix))) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ :=
    match_default_body_call_site_at_index_to_next_macro_step rules (macroNames rules)
      templateHoles copyHoles renames origin childOrigin copyFuel fresh final matchHead
      scrutineeItems bodyItems before suffix beforeValid twoCases cost copied head arguments
      childRule site matchForm matchNotMacro matchNotHole bodyHeadSafe known notHole lookupNone
      wholeCopied childMember copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list (.atom matchHead :: .list scrutineeItems ::
      (before ++ .list [.list [], .list bodyItems] :: suffix))) childTarget edges ranks parsed
    dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Rank decrease for a call in a nonempty-pattern match case, including the
pattern's freshened names and the successful whole-match copy. -/
theorem match_pattern_body_call_site_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (matchHead : Atom) (scrutineeItems : List Tree) (constructor : Tree)
    (patternParameters bodyItems : List Tree) (head : Atom) (arguments : List Tree)
    (cost : Nat) (site : LiteralCallSite (macroNames rules) head arguments bodyItems cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames) (copied : Tree)
    (originalNames : List String) (dependencies : List Nat) (edges : List Edge)
    (ranks : List Nat)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : (macroNames rules).contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (patternNamesMatch : patternNames patternParameters = some originalNames)
    (patternNamesDistinct : Lexical.distinctNames originalNames = true)
    (bodyHeadSafe : counterNeutralListHead (macroNames rules) bodyItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list [.atom matchHead, .list scrutineeItems,
        .list [.list (constructor :: patternParameters), .list bodyItems]]))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + 3) origin copyHoles
      renames fresh (.list [.atom matchHead, .list scrutineeItems,
        .list [.list (constructor :: patternParameters), .list bodyItems]]) =
          some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom matchHead, .list scrutineeItems,
        .list [.list (constructor :: patternParameters), .list bodyItems]]) =
          some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := match_pattern_body_call_site_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles renames origin childOrigin copyFuel fresh final
    matchHead scrutineeItems constructor patternParameters bodyItems cost copied head arguments
    childRule site originalNames matchForm matchNotMacro matchNotHole patternNamesMatch
    patternNamesDistinct bodyHeadSafe known notHole lookupNone wholeCopied childMember
    copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list [.atom matchHead, .list scrutineeItems,
      .list [.list (constructor :: patternParameters), .list bodyItems]]) childTarget edges ranks
    parsed dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Accepted graph ranks decrease for a body call in any nonempty-pattern case
of a successful multi-case match copy. -/
theorem match_pattern_body_call_site_at_index_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (matchHead : Atom) (scrutineeItems : List Tree) (constructor : Tree)
    (patternParameters bodyItems before suffix : List Tree) (beforeValid : CaseRows before)
    (twoCases : ∃ firstCase secondCase rest,
      before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix =
        firstCase :: secondCase :: rest)
    (originalNames : List String) (cost : Nat) (copied : Tree) (head : Atom)
    (arguments : List Tree)
    (site : LiteralCallSite (macroNames rules) head arguments bodyItems cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : (macroNames rules).contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (patternNamesMatch : patternNames patternParameters = some originalNames)
    (patternNamesDistinct : Lexical.distinctNames originalNames = true)
    (bodyHeadSafe : counterNeutralListHead (macroNames rules) bodyItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list (.atom matchHead :: .list scrutineeItems ::
        (before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix))))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + before.length + 3)
      origin copyHoles renames fresh
      (.list (.atom matchHead :: .list scrutineeItems ::
        (before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix))) =
          some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (.atom matchHead :: .list scrutineeItems ::
        (before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix))) =
          some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ :=
    match_pattern_body_call_site_at_index_to_next_macro_step rules (macroNames rules)
      templateHoles copyHoles renames origin childOrigin copyFuel fresh final matchHead
      scrutineeItems constructor patternParameters bodyItems before suffix beforeValid twoCases
      cost copied head arguments childRule site originalNames matchForm matchNotMacro matchNotHole
      patternNamesMatch patternNamesDistinct bodyHeadSafe known notHole lookupNone wholeCopied
      childMember copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list (.atom matchHead :: .list scrutineeItems ::
      (before ++ .list [.list (constructor :: patternParameters), .list bodyItems] :: suffix)))
    childTarget edges ranks parsed dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Accepted graph ranks decrease for a call in the scrutinee of a copied
multi-case match. -/
theorem match_scrutinee_call_site_at_index_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (matchHead : Atom) (scrutineeItems : List Tree) (firstCase secondCase : Tree)
    (caseTail : List Tree) (cost : Nat) (copied : Tree) (head : Atom)
    (arguments : List Tree) (site : LiteralCallSite (macroNames rules) head arguments
      scrutineeItems cost) (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : (macroNames rules).contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (scrutineeHeadSafe : counterNeutralListHead (macroNames rules) scrutineeItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + 2) origin copyHoles
      renames fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)) =
        some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ :=
    match_scrutinee_call_site_at_index_to_next_macro_step rules (macroNames rules)
      templateHoles copyHoles renames origin childOrigin copyFuel fresh final matchHead
      scrutineeItems firstCase secondCase caseTail cost copied head arguments childRule site
      matchForm matchNotMacro matchNotHole scrutineeHeadSafe known notHole lookupNone wholeCopied
      childMember copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail))
    childTarget edges ranks parsed dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Accepted graph ranks decrease for a call in the scrutinee of a
single-case match. -/
theorem match_scrutinee_call_site_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (matchHead : Atom) (scrutineeItems : List Tree) (caseBody : Tree)
    (cost : Nat) (copied : Tree) (head : Atom) (arguments : List Tree)
    (site : LiteralCallSite (macroNames rules) head arguments scrutineeItems cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchForm : matchHead.name = "match")
    (matchNotMacro : (macroNames rules).contains matchHead.name = false)
    (matchNotHole : (lookup matchHead.name copyHoles).isNone = true)
    (scrutineeHeadSafe : counterNeutralListHead (macroNames rules) scrutineeItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list [.atom matchHead, .list scrutineeItems, caseBody]))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + 2) origin copyHoles
      renames fresh (.list [.atom matchHead, .list scrutineeItems, caseBody]) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom matchHead, .list scrutineeItems, caseBody]) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ :=
    match_scrutinee_call_site_to_next_macro_step rules (macroNames rules) templateHoles
      copyHoles renames origin childOrigin copyFuel fresh final matchHead scrutineeItems caseBody
      cost copied head arguments childRule site matchForm matchNotMacro matchNotHole
      scrutineeHeadSafe known notHole lookupNone wholeCopied childMember copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list [.atom matchHead, .list scrutineeItems, caseBody]) childTarget edges
    ranks parsed dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- A successful next step in a lambda body inherits the accepted parent
template's rank decrease, including the source call path through the lambda. -/
theorem lambda_body_next_macro_step_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (lambdaHead head : Atom) (lambdaParameters : List Tree) (result : Tree)
    (arguments : List Tree) (output childRule childTemplate : Tree)
    (copyHoles : Holes) (renames : Renames) (childHoles : Holes) (dependencies : List Nat)
    (edges : List Edge) (ranks : List Nat)
    (lambdaForm : lambdaHead.name = "lambda")
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list [.atom lambdaHead, .list lambdaParameters, result,
        .list (.atom head :: arguments)]))
    (bodyCopied : copyWithMacros (macroNames rules) (copyFuel + 1) origin copyHoles
      renames fresh (.list (.atom head :: arguments)) = some (output, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom lambdaHead, .list lambdaParameters, result,
        .list (.atom head :: arguments)]) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, callSite⟩ := lambda_body_literal_call_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles renames origin childOrigin copyFuel fresh final
    lambdaHead head lambdaParameters result arguments output childRule childTemplate childHoles
    lambdaForm known notHole lookupNone bodyCopied childMember childMatched
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list [.atom lambdaHead, .list lambdaParameters, result,
      .list (.atom head :: arguments)]) childTarget edges ranks parsed dependencyCheck callSite
    graphAccepted ranksAccepted⟩

/-- An arbitrary-depth ordinary-list callsite inherits the rank decrease from
the accepted graph row once its copied redex matches a child rule. -/
theorem literal_call_site_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (arguments items copied : List Tree) (cost : Nat)
    (site : LiteralCallSite (macroNames rules) head arguments items cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames) (dependencies : List Nat)
    (edges : List Edge) (ranks : List Nat)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles, .list items))
    (outerCopied : copyManyWithMacros (macroNames rules) (copyFuel + cost)
      origin copyHoles renames fresh items = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles (.list items) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := literal_call_site_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles renames origin childOrigin copyFuel fresh final head
    arguments copied childRule site known notHole lookupNone outerCopied childMember copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list items) childTarget edges ranks parsed dependencyCheck templateCall
    graphAccepted ranksAccepted⟩

/-- A call anywhere in an ordinary-list lambda body inherits the accepted
lambda-template row's rank decrease after its parameter rename environment. -/
theorem lambda_body_call_site_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (lambdaHead : Atom) (lambdaParameters : List Tree) (result : Tree)
    (head : Atom) (arguments bodyItems copiedBodyItems : List Tree) (cost : Nat)
    (site : LiteralCallSite (macroNames rules) head arguments bodyItems cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (lambdaForm : lambdaHead.name = "lambda")
    (bodyHeadSafe : counterNeutralListHead (macroNames rules) bodyItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list [.atom lambdaHead, .list lambdaParameters, result, .list bodyItems]))
    (bodyCopied : copyWithMacros (macroNames rules) (copyFuel + cost + 1) origin
      copyHoles renames fresh (.list bodyItems) = some (.list copiedBodyItems, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom lambdaHead, .list lambdaParameters, result, .list bodyItems]) =
        some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := lambda_body_call_site_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles renames origin childOrigin copyFuel fresh final
    lambdaHead lambdaParameters result head arguments bodyItems copiedBodyItems cost childRule site
    lambdaForm bodyHeadSafe known notHole lookupNone bodyCopied childMember copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list [.atom lambdaHead, .list lambdaParameters, result, .list bodyItems])
    childTarget edges ranks parsed dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Rank decrease for a call in a lambda body, starting from the successful
copy of the complete lambda form. -/
theorem lambda_copy_body_call_site_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (lambdaHead : Atom) (lambdaParameters : List Tree) (result : Tree)
    (head : Atom) (arguments bodyItems copiedBodyItems : List Tree) (cost : Nat)
    (site : LiteralCallSite (macroNames rules) head arguments bodyItems cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (copied : Tree) (originalNames : List String)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (lambdaForm : lambdaHead.name = "lambda")
    (lambdaNotMacro : (macroNames rules).contains lambdaHead.name = false)
    (lambdaNotHole : (lookup lambdaHead.name copyHoles).isNone = true)
    (parameterNamesMatch : parameterNames lambdaParameters = some originalNames)
    (parametersDistinct : Lexical.distinctNames originalNames = true)
    (bodyHeadSafe : counterNeutralListHead (macroNames rules) bodyItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list [.atom lambdaHead, .list lambdaParameters, result, .list bodyItems]))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + 2) origin copyHoles
      renames fresh (.list [.atom lambdaHead, .list lambdaParameters, result, .list bodyItems]) =
        some (copied, final))
    (outputShape : ∃ copiedParameters,
      copied = .list [.atom lambdaHead, .list copiedParameters, result, .list copiedBodyItems])
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom lambdaHead, .list lambdaParameters, result, .list bodyItems]) =
        some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := lambda_copy_body_call_site_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles renames origin childOrigin copyFuel fresh final
    lambdaHead lambdaParameters result bodyItems copiedBodyItems cost copied head arguments childRule
    site originalNames lambdaForm lambdaNotMacro lambdaNotHole parameterNamesMatch
    parametersDistinct bodyHeadSafe known notHole lookupNone wholeCopied outputShape childMember
    copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list [.atom lambdaHead, .list lambdaParameters, result, .list bodyItems])
    childTarget edges ranks parsed dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Rank decrease for a call in a let body, starting from the successful copy
of the complete let form. -/
theorem let_copy_body_call_site_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (letHead : Atom) (bindings : List Tree) (bodyItems copiedBodyItems : List Tree)
    (head : Atom) (arguments : List Tree) (cost : Nat)
    (site : LiteralCallSite (macroNames rules) head arguments bodyItems cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (copied : Tree) (originalNames : List String)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (letForm : letHead.name = "let")
    (letNotMacro : (macroNames rules).contains letHead.name = false)
    (letNotHole : (lookup letHead.name copyHoles).isNone = true)
    (bindingNamesMatch : bindingNames bindings = some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (bodyHeadSafe : counterNeutralListHead (macroNames rules) bodyItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list [.atom letHead, .list bindings, .list bodyItems]))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + 2) origin copyHoles
      renames fresh (.list [.atom letHead, .list bindings, .list bodyItems]) =
        some (copied, final))
    (outputShape : ∃ copiedBindings,
      copied = .list [.atom letHead, .list copiedBindings, .list copiedBodyItems])
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom letHead, .list bindings, .list bodyItems]) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := let_copy_body_call_site_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles renames origin childOrigin copyFuel fresh final
    letHead bindings bodyItems copiedBodyItems cost copied head arguments childRule site originalNames
    letForm letNotMacro letNotHole bindingNamesMatch bindingsDistinct bodyHeadSafe known notHole
    lookupNone wholeCopied outputShape childMember copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list [.atom letHead, .list bindings, .list bodyItems]) childTarget edges ranks
    parsed dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Rank decrease for a call in the first let initializer, starting from the
successful whole-let copy and the accepted static call graph. -/
theorem let_first_initializer_call_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (letHead bindingName : Atom) (bindingType body : Tree) (initializerItems : List Tree)
    (head : Atom) (arguments : List Tree) (cost : Nat)
    (site : LiteralCallSite (macroNames rules) head arguments initializerItems cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (copied : Tree) (originalNames : List String)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (letForm : letHead.name = "let")
    (letNotMacro : (macroNames rules).contains letHead.name = false)
    (letNotHole : (lookup letHead.name copyHoles).isNone = true)
    (bindingNamesMatch : bindingNames
      [.list [.list [.atom bindingName, bindingType], .list initializerItems]] =
        some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (initializerHeadSafe : counterNeutralListHead (macroNames rules) initializerItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list [.atom letHead,
        .list [.list [.list [.atom bindingName, bindingType], .list initializerItems]], body]))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + 3) origin copyHoles
      renames fresh (.list [.atom letHead,
        .list [.list [.list [.atom bindingName, bindingType], .list initializerItems]], body]) =
          some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list [.atom letHead,
        .list [.list [.list [.atom bindingName, bindingType], .list initializerItems]], body]) =
          some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ :=
    let_first_initializer_call_to_next_macro_step rules (macroNames rules) templateHoles copyHoles
      renames origin childOrigin copyFuel fresh final letHead bindingName bindingType body
      initializerItems cost copied head arguments childRule site originalNames letForm letNotMacro
      letNotHole bindingNamesMatch bindingsDistinct initializerHeadSafe known notHole lookupNone
      wholeCopied childMember copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list [.atom letHead,
      .list [.list [.list [.atom bindingName, bindingType], .list initializerItems]], body])
    childTarget edges ranks parsed dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Rank decrease for a call in an arbitrary let initializer, derived from
the successful complete let copy and the accepted call-graph certificate. -/
theorem let_initializer_call_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tailRules : List (Nat × Tree)) (templateHoles : List String)
    (letHead bindingName : Atom) (bindingType body : Tree) (before : List Tree)
    (initializerItems suffix : List Tree) (head : Atom) (arguments : List Tree) (cost : Nat)
    (site : LiteralCallSite (macroNames rules) head arguments initializerItems cost)
    (childRule : Tree) (copyHoles : Holes) (renames : Renames) (copied : Tree)
    (originalNames : List String) (beforeValid : BindingRows before)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (letForm : letHead.name = "let")
    (letNotMacro : (macroNames rules).contains letHead.name = false)
    (letNotHole : (lookup letHead.name copyHoles).isNone = true)
    (bindingNamesMatch : bindingNames
      (before ++ .list [.list [.atom bindingName, bindingType], .list initializerItems] :: suffix) =
        some originalNames)
    (bindingsDistinct : Lexical.distinctNames originalNames = true)
    (initializerHeadSafe : counterNeutralListHead (macroNames rules) initializerItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles, .list [.atom letHead,
      .list (before ++ .list [.list [.atom bindingName, bindingType], .list initializerItems]
        :: suffix), body]))
    (wholeCopied : copyWithMacros (macroNames rules)
      (copyFuel + cost + before.length + 3) origin copyHoles renames fresh
      (.list [.atom letHead,
        .list (before ++ .list [.list [.atom bindingName, bindingType], .list initializerItems]
          :: suffix), body]) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles (.list [.atom letHead,
      .list (before ++ .list [.list [.atom bindingName, bindingType], .list initializerItems]
        :: suffix), body]) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tailRules) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := let_initializer_call_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles renames origin childOrigin copyFuel fresh final
    letHead bindingName bindingType body before initializerItems suffix cost copied head arguments
    childRule site originalNames beforeValid letForm letNotMacro letNotHole bindingNamesMatch
    bindingsDistinct initializerHeadSafe known notHole lookupNone wholeCopied childMember
    copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tailRules
    templateHoles (.list [.atom letHead,
      .list (before ++ .list [.list [.atom bindingName, bindingType], .list initializerItems]
        :: suffix), body]) childTarget edges ranks parsed dependencyCheck templateCall graphAccepted
    ranksAccepted⟩

/-- Rank decrease for an arbitrary-depth ordinary-list path whose call head is
substituted from a template parameter. -/
theorem substituted_head_call_site_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (arguments items copied : List Tree) (cost : Nat)
    (site : SubstitutedHeadCallSite (macroNames rules) head arguments items cost)
    (childRule : Tree) (copyHoles : Holes) (dependencies : List Nat)
    (edges : List Edge) (ranks : List Nat)
    (headIsHole : head.name ∈ templateHoles)
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (ordinaryHead : head.name ≠ "lambda" ∧ head.name ≠ "let" ∧ head.name ≠ "match")
    (parsed : parameters rule = some (templateHoles, .list items))
    (outerCopied : copyManyWithMacros (macroNames rules) (copyFuel + cost)
      origin copyHoles [] fresh items = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles (.list items) = some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := substituted_head_call_site_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles origin childOrigin copyFuel fresh final head
    arguments copied childRule site headIsHole holesAgree ordinaryHead outerCopied childMember
    copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list items) childTarget edges ranks parsed dependencyCheck templateCall
    graphAccepted ranksAccepted⟩

/-- In the same root, literal zero-argument case, the next successful macro
step inherits the accepted call-graph rank decrease from its parent template
row. -/
theorem zero_arg_next_macro_step_rank_decreases (fuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (childRule childTemplate output : Tree)
    (copyHoles childHoles : Holes) (dependencies : List Nat) (edges : List Edge)
    (ranks : List Nat)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles, .list [.atom head]))
    (copySucceeded : copyWithMacros (macroNames rules) 2 origin copyHoles [] fresh
      (.list [.atom head]) = some (output, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate))
    (dependencyCheck : calls fuel rules templateHoles (.list [.atom head]) =
      some dependencies)
    (graphAccepted : graphRows fuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := zero_arg_template_call_to_next_macro_step
    rules (macroNames rules) templateHoles copyHoles origin childOrigin fresh final head
    childRule childTemplate output childHoles known notHole lookupNone copySucceeded
    childMember childMatched
  exact ⟨childTarget, template_static_call_rank_decreases fuel rules index owner rule tail
    templateHoles (.list [.atom head]) childTarget edges ranks parsed dependencyCheck
    templateCall graphAccepted ranksAccepted⟩

/-- General-arity version of the local next-step rank argument for a literal
root call. The argument-copy success and copy fuel are explicit, and the
candidate graph row is checked against the original argument count. -/
theorem root_next_macro_step_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (arguments copiedArguments : List Tree)
    (childRule childTemplate output : Tree) (copyHoles childHoles : Holes)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles, .list (.atom head :: arguments)))
    (argumentsCopied : copyManyWithMacros (macroNames rules) copyFuel origin copyHoles []
      fresh arguments = some (copiedArguments, final))
    (copySucceeded : copyWithMacros (macroNames rules) (copyFuel + 1) origin copyHoles []
      fresh (.list (.atom head :: arguments)) = some (output, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule output = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles (.list (.atom head :: arguments)) =
      some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := root_template_call_to_next_macro_step rules
    (macroNames rules) templateHoles copyHoles [] origin childOrigin copyFuel fresh final head
    arguments copiedArguments childRule childTemplate output childHoles known notHole
    lookupNone argumentsCopied copySucceeded childMember childMatched
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list (.atom head :: arguments)) childTarget edges ranks parsed
    dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Root-template rank decrease with the child call supplied as an accepted
expansion-certificate macro step. `checkStep_sound` recovers its exact rule
membership, match, and bounded-copy derivation before applying the static
parent-template edge theorem. -/
theorem root_certified_macroStep_rank_decreases (graphFuel copyFuel childFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final childFresh childFinal : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (arguments copiedArguments : List Tree)
    (childRule output childOutput : Tree) (copyHoles : Holes)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles, .list (.atom head :: arguments)))
    (argumentsCopied : copyManyWithMacros (macroNames rules) copyFuel origin copyHoles []
      fresh arguments = some (copiedArguments, final))
    (copySucceeded : copyWithMacros (macroNames rules) (copyFuel + 1) origin copyHoles []
      fresh (.list (.atom head :: arguments)) = some (output, final))
    (childStepAccepted : NLisp.ExpansionCertificate.checkStep rules childOrigin childFuel
      childFresh childFinal childRule output childOutput = true)
    (dependencyCheck : calls graphFuel rules templateHoles (.list (.atom head :: arguments)) =
      some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childHoles, childTemplate, childMember, childMatched, _childCopied⟩ :=
    NLisp.ExpansionCertificate.checkStep_sound childStepAccepted
  exact root_next_macro_step_rank_decreases graphFuel copyFuel rules index owner childOrigin
    origin fresh final rule tail templateHoles head arguments copiedArguments childRule
    childTemplate output copyHoles childHoles dependencies edges ranks known notHole lookupNone
    parsed argumentsCopied copySucceeded childMember childMatched dependencyCheck graphAccepted
    ranksAccepted

/-- Rank decrease for a literal-head child at any sibling position of the
parent template's ordinary list. The accepted graph row is for the complete
parent template, so the nested StaticCall inherits its checked edge. -/
theorem list_index_next_macro_step_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (arguments beforeItems afterItems copied : List Tree)
    (childRule : Tree) (copyHoles : Holes) (dependencies : List Nat)
    (edges : List Edge) (ranks : List Nat)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)))
    (outerCopied : copyManyWithMacros (macroNames rules) (copyFuel + beforeItems.length + 2)
      origin copyHoles [] fresh
      (beforeItems ++ .list (.atom head :: arguments) :: afterItems) = some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedBefore copiedCall copiedAfter,
      copied = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems)) =
        some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  have outerCopied' : copyManyWithMacros (macroNames rules)
      ((copyFuel + 1) + beforeItems.length + 1) origin copyHoles [] fresh
      (beforeItems ++ .list (.atom head :: arguments) :: afterItems) = some (copied, final) := by
    have fuelEq : copyFuel + beforeItems.length + 2 =
        copyFuel + (1 + (beforeItems.length + 1)) := by omega
    simpa only [Nat.add_assoc, fuelEq] using outerCopied
  obtain ⟨childTarget, templateCall⟩ := literal_call_at_list_index_to_next_macro_step
    rules (macroNames rules) templateHoles copyHoles [] origin childOrigin copyFuel fresh final
    head arguments beforeItems afterItems copied (copyFuel + 1) childRule known notHole
    lookupNone rfl outerCopied' childMember copiedChildMatches
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list (beforeItems ++ .list (.atom head :: arguments) :: afterItems))
    childTarget edges ranks parsed dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Rank decrease for a literal macro call selected through two nested
ordinary list contexts. Both selected list positions may have arbitrary
siblings before and after them. -/
theorem nested_two_indices_next_macro_step_rank_decreases (graphFuel innerFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (arguments innerBefore innerAfter innerItems : List Tree)
    (outerBefore outerAfter copied : List Tree)
    (childRule : Tree) (copyHoles : Holes) (dependencies : List Nat)
    (edges : List Edge) (ranks : List Nat)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (ordinaryInnerHead : counterNeutralListHead (macroNames rules) innerItems = true)
    (innerShape : innerItems = innerBefore ++ .list (.atom head :: arguments) :: innerAfter)
    (parsed : parameters rule = some (templateHoles,
      .list (outerBefore ++ .list innerItems :: outerAfter)))
    (outerCopied : copyManyWithMacros (macroNames rules)
      (innerFuel + innerBefore.length + outerBefore.length + 4)
      origin copyHoles [] fresh (outerBefore ++ .list innerItems :: outerAfter) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedInner' copiedBefore copiedCall copiedAfter,
      copiedInner' = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (outerBefore ++
        .list (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: outerAfter)) =
          some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := nested_literal_call_at_two_list_indices_to_next_macro_step
    rules (macroNames rules) templateHoles copyHoles origin childOrigin innerFuel fresh final
    head arguments innerBefore innerAfter innerItems outerBefore outerAfter copied
    childRule known notHole lookupNone ordinaryInnerHead innerShape outerCopied childMember
    copiedChildMatches
  have parsedExpanded : parameters rule = some (templateHoles,
      .list (outerBefore ++
        .list (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: outerAfter)) := by
    simpa [innerShape] using parsed
  exact ⟨childTarget,
    template_static_call_rank_decreases graphFuel rules index owner rule tail templateHoles
      (.list (outerBefore ++
        .list (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: outerAfter))
      childTarget edges ranks parsedExpanded dependencyCheck templateCall
      graphAccepted ranksAccepted⟩

/-- Rank decrease for a literal macro call selected through three nested
ordinary list contexts. -/
theorem nested_three_indices_next_macro_step_rank_decreases (graphFuel innerFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (arguments innerBefore innerAfter innerItems : List Tree)
    (middleBefore middleAfter middleItems : List Tree)
    (outerBefore outerAfter copied : List Tree)
    (childRule : Tree) (copyHoles : Holes) (dependencies : List Nat)
    (edges : List Edge) (ranks : List Nat)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (ordinaryInnerHead : counterNeutralListHead (macroNames rules) innerItems = true)
    (ordinaryMiddleHead : counterNeutralListHead (macroNames rules) middleItems = true)
    (innerShape : innerItems = innerBefore ++ .list (.atom head :: arguments) :: innerAfter)
    (middleShape : middleItems = middleBefore ++ .list innerItems :: middleAfter)
    (parsed : parameters rule = some (templateHoles,
      .list (outerBefore ++ .list middleItems :: outerAfter)))
    (outerCopied : copyManyWithMacros (macroNames rules)
      (innerFuel + innerBefore.length + middleBefore.length + outerBefore.length + 6)
      origin copyHoles [] fresh (outerBefore ++ .list middleItems :: outerAfter) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedInner copiedBefore copiedCall copiedAfter,
      copiedInner = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (outerBefore ++ .list
        (middleBefore ++ .list
          (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: middleAfter) :: outerAfter)) =
          some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ :=
    nested_literal_call_at_three_list_indices_to_next_macro_step rules (macroNames rules)
      templateHoles copyHoles origin childOrigin innerFuel fresh final head arguments
      innerBefore innerAfter innerItems middleBefore middleAfter middleItems outerBefore
      outerAfter copied childRule known notHole lookupNone ordinaryInnerHead ordinaryMiddleHead
      innerShape middleShape outerCopied childMember copiedChildMatches
  have parsedExpanded : parameters rule = some (templateHoles,
      .list (outerBefore ++ .list
        (middleBefore ++ .list
          (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: middleAfter) :: outerAfter)) := by
    simpa [middleShape, innerShape] using parsed
  exact ⟨childTarget,
    template_static_call_rank_decreases graphFuel rules index owner rule tail templateHoles
      (.list (outerBefore ++ .list
        (middleBefore ++ .list
          (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: middleAfter) :: outerAfter))
      childTarget edges ranks parsedExpanded dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- Rank decrease for a literal macro call selected through four nested
ordinary list contexts. -/
theorem nested_four_indices_next_macro_step_rank_decreases (graphFuel innerFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head : Atom) (arguments innerBefore innerAfter innerItems : List Tree)
    (middleBefore middleAfter middleItems : List Tree)
    (outerBefore outerAfter outerItems : List Tree)
    (rootBefore rootAfter copied : List Tree)
    (childRule : Tree) (copyHoles : Holes) (dependencies : List Nat)
    (edges : List Edge) (ranks : List Nat)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (ordinaryInnerHead : counterNeutralListHead (macroNames rules) innerItems = true)
    (ordinaryMiddleHead : counterNeutralListHead (macroNames rules) middleItems = true)
    (ordinaryOuterHead : counterNeutralListHead (macroNames rules) outerItems = true)
    (innerShape : innerItems = innerBefore ++ .list (.atom head :: arguments) :: innerAfter)
    (middleShape : middleItems = middleBefore ++ .list innerItems :: middleAfter)
    (outerShape : outerItems = outerBefore ++ .list middleItems :: outerAfter)
    (parsed : parameters rule = some (templateHoles,
      .list (rootBefore ++ .list outerItems :: rootAfter)))
    (rootCopied : copyManyWithMacros (macroNames rules)
      (innerFuel + innerBefore.length + middleBefore.length + outerBefore.length +
        rootBefore.length + 8)
      origin copyHoles [] fresh (rootBefore ++ .list outerItems :: rootAfter) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedInner copiedBefore copiedCall copiedAfter,
      copiedInner = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (rootBefore ++ .list
        (outerBefore ++ .list
          (middleBefore ++ .list
            (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: middleAfter) :: outerAfter) :: rootAfter)) =
          some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ :=
    nested_literal_call_at_four_list_indices_to_next_macro_step rules (macroNames rules)
      templateHoles copyHoles origin childOrigin innerFuel fresh final head arguments
      innerBefore innerAfter innerItems middleBefore middleAfter middleItems outerBefore
      outerAfter outerItems rootBefore rootAfter copied childRule known notHole lookupNone
      ordinaryInnerHead ordinaryMiddleHead ordinaryOuterHead innerShape middleShape outerShape
      rootCopied childMember copiedChildMatches
  have parsedExpanded : parameters rule = some (templateHoles,
      .list (rootBefore ++ .list
        (outerBefore ++ .list
          (middleBefore ++ .list
            (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: middleAfter) :: outerAfter) :: rootAfter)) := by
    simpa [outerShape, middleShape, innerShape] using parsed
  exact ⟨childTarget,
    template_static_call_rank_decreases graphFuel rules index owner rule tail templateHoles
      (.list (rootBefore ++ .list
        (outerBefore ++ .list
          (middleBefore ++ .list
            (innerBefore ++ .list (.atom head :: arguments) :: innerAfter) :: middleAfter) :: outerAfter) :: rootAfter))
      childTarget edges ranks parsedExpanded dependencyCheck templateCall graphAccepted ranksAccepted⟩

/- For a head-position hole, the accepted whole-list copy and the corresponding
copyMany result expose the substituted atom head and preserve argument count.
The static analysis already includes every rule with that arity. -/
theorem substituted_head_next_macro_step_rank_decreases (graphFuel copyFuel : Nat)
    (rules : List (Nat × Tree)) (index owner childOrigin origin fresh final : Nat)
    (rule : Tree) (tail : List (Nat × Tree)) (templateHoles : List String)
    (head copiedHead : Atom) (arguments copiedArguments : List Tree)
    (childRule childTemplate : Tree) (copyHoles childHoles : Holes)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (parsed : parameters rule = some (templateHoles, .list (.atom head :: arguments)))
    (headIsHole : head.name ∈ templateHoles)
    (holesAgree : templateHoles = copyHoles.map Prod.fst)
    (ordinaryHead : head.name ≠ "lambda" ∧ head.name ≠ "let" ∧ head.name ≠ "match")
    (copySucceeded : copyWithMacros (macroNames rules) (copyFuel + 1) origin copyHoles [] fresh
      (.list (.atom head :: arguments)) =
        some (.list (.atom copiedHead :: copiedArguments), final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (childMatched : matchRule childRule
      (.list (.atom copiedHead :: copiedArguments)) = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles (.list (.atom head :: arguments)) =
      some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tail) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ childTarget, rank ranks childTarget < rank ranks index := by
  obtain ⟨childTarget, templateCall⟩ := substituted_head_template_call_to_next_macro_step
    rules (macroNames rules) templateHoles copyHoles origin childOrigin copyFuel fresh final
    head copiedHead arguments copiedArguments childRule childTemplate childHoles headIsHole
    holesAgree ordinaryHead copySucceeded childMember childMatched
  exact ⟨childTarget, template_static_call_rank_decreases graphFuel rules index owner rule tail
    templateHoles (.list (.atom head :: arguments)) childTarget edges ranks parsed
    dependencyCheck templateCall graphAccepted ranksAccepted⟩

/-- The abstract expansion machine has two kinds of work remaining: the
certified macro rank and the finite syntax traversal below the current call.
Macro expansion may increase syntax size, so its progress is measured in the
first component; ordinary syntax traversal keeps that component fixed and
decreases the second. -/
abbrev ExpansionProgress := Prod.Lex Nat.lt Nat.lt

theorem macroExpansionProgress_decreases {parentRank childRank parentNodes childNodes : Nat}
    (rankDecreases : childRank < parentRank) :
    ExpansionProgress (childRank, childNodes) (parentRank, parentNodes) := by
  exact Prod.Lex.left childNodes parentNodes rankDecreases

theorem syntaxTraversalProgress_decreases {rank parentNodes childNodes : Nat}
    (nodesDecrease : childNodes < parentNodes) :
    ExpansionProgress (rank, childNodes) (rank, parentNodes) := by
  exact Prod.Lex.right rank nodesDecrease

theorem treeChild_expansionProgress_decreases {rank : Nat} {child parent : Tree}
    (edge : TreeChild child parent) :
    ExpansionProgress (rank, treeNodeCount child) (rank, treeNodeCount parent) :=
  syntaxTraversalProgress_decreases (treeChild_nodeCount_decreases edge)

theorem treeList_tail_expansionProgress_decreases {rank : Nat} (head : Tree)
    (tail : List Tree) :
    ExpansionProgress (rank, treeListNodeCount tail)
      (rank, treeListNodeCount (head :: tail)) :=
  syntaxTraversalProgress_decreases (treeListNodeCount_cons_tail_decreases head tail)

/-- Any process whose steps are either certified macro-rank decreases or
strict syntax-traversal decreases is well-founded, even when macro expansion
increases the size of the generated syntax. -/
theorem expansionProgress_wellFounded : WellFounded ExpansionProgress := by
  simpa [ExpansionProgress, Prod.lex, Nat.lt_wfRel] using
    (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/- This is Lean's ordinary well-founded recursion mechanism, with the
certificate's rule rank as termination_by measure. It constructs accessibility
for every node rather than merely testing a recursion-depth threshold. -/
def accessible (edges : List Edge) (ranks : List Nat)
    (accepted : checkRanks edges ranks = true) (node : Nat) : Acc (Calls edges) node :=
  Acc.intro node (fun child _edge => accessible edges ranks accepted child)
termination_by rank ranks node
decreasing_by exact checkRanks_decreases accepted _edge

theorem ranked_graph_wellFounded (accepted : checkRanks edges ranks = true) :
    WellFounded (Calls edges) := ⟨accessible edges ranks accepted⟩

/-- A user-supplied well-founded measure for a call relation.  The measure
domain and decrease relation are independent of the finite `Nat` ranking
checker, so structural orders and lexicographic measures can be used when the
conservative static graph is too imprecise for a numeric rank vector. -/
structure WellFoundedDecreaseCertificate (edges : List Edge) where
  Carrier : Type
  measure : Nat → Carrier
  decrease : Carrier → Carrier → Prop
  wellFounded : WellFounded decrease
  calls_decrease : ∀ {child parent}, Calls edges child parent →
    decrease (measure child) (measure parent)

/-- Any certified well-founded measure on call edges induces a well-founded
call graph.  This theorem is a reusable sufficient condition; it does not
claim that a particular macro expansion step has been extracted as an edge. -/
theorem wellFoundedDecreaseCertificate_calls_wellFounded
    (certificate : WellFoundedDecreaseCertificate edges) :
    WellFounded (Calls edges) := by
  let motive : certificate.Carrier → Sort := fun measureValue =>
    ∀ node, certificate.measure node = measureValue → Acc (Calls edges) node
  have accessibleMeasure : ∀ measureValue, Acc certificate.decrease measureValue →
      motive measureValue := by
    intro measureValue accessible
    induction accessible with
    | intro measureValue smaller ih =>
        intro node measureEq
        apply Acc.intro
        intro child edge
        have childDecrease : certificate.decrease (certificate.measure child)
            measureValue := by
          rw [← measureEq]
          exact certificate.calls_decrease edge
        exact ih (certificate.measure child) childDecrease child rfl
  exact ⟨fun node => accessibleMeasure (certificate.measure node)
    (certificate.wellFounded.apply (certificate.measure node)) node rfl⟩

/- A path is a finite prefix of nested recursive invocations. -/
inductive Path (edges : List Edge) : Nat → Nat → Nat → Prop where
  | zero (node : Nat) : Path edges node node 0
  | step : Calls edges next first → Path edges next last count →
      Path edges first last (count + 1)

theorem path_length_bounded (accepted : checkRanks edges ranks = true)
    (path : Path edges first last count) : count + rank ranks last ≤ rank ranks first := by
  induction path with
  | zero _ => omega
  | step edge _ ih =>
      have decrease := checkRanks_decreases accepted edge
      omega

/-- Every finite prefix of a chain of certified child-to-parent calls consumes
at least one unit of the parent's rank per step. This is the sequence form of
the graph path bound and makes the no-infinite-call consequence explicit. -/
theorem call_chain_length_bounded (accepted : checkRanks edges ranks = true)
    (chain : Nat → Nat)
    (step : ∀ index, Calls edges (chain (index + 1)) (chain index)) :
    ∀ count, count + rank ranks (chain count) ≤ rank ranks (chain 0) := by
  intro count
  induction count with
  | zero => simp
  | succ count ih =>
      have decrease := checkRanks_decreases accepted (step count)
      omega

theorem no_infinite_call_chain (accepted : checkRanks edges ranks = true)
    (chain : Nat → Nat)
    (step : ∀ index, Calls edges (chain (index + 1)) (chain index)) : False := by
  have bounded := call_chain_length_bounded accepted chain step (rank ranks (chain 0) + 1)
  omega

/-- A call in a match scrutinee inherits the parent template's rank decrease
even when the special-form `match` head is supplied by a template hole. The
match-specific copy path keeps that head literal, so the scrutinee copy is
extracted separately before following the nested call site. -/
theorem match_hole_head_scrutinee_call_site_rank_decreases
    (graphFuel copyFuel : Nat) (rules : List (Nat × Tree))
    (index owner childOrigin origin fresh final : Nat) (rule : Tree)
    (tailRules : List (Nat × Tree)) (templateHoles : List String)
    (matchHead : Atom) (scrutineeItems : List Tree) (firstCase secondCase : Tree)
    (caseTail : List Tree) (cost : Nat) (copied : Tree) (head : Atom)
    (arguments : List Tree) (site : LiteralCallSite (macroNames rules) head arguments
      scrutineeItems cost) (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchForm : matchHead.name = "match")
    (matchIsHole : lookup matchHead.name copyHoles = some (.atom matchHead))
    (scrutineeHeadSafe : counterNeutralListHead (macroNames rules) scrutineeItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + 2) origin copyHoles
      renames fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate))
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)) =
        some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tailRules) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, rank ranks target < rank ranks index := by
  obtain ⟨copiedScrutinee, afterScrutinee, _copiedCases, scrutineeCopied, _casesCopied,
    _wholeShape⟩ := copyWithMacros_match_hole_head_cases_parts (macroNames rules)
      (copyFuel + cost + 1) origin fresh final copyHoles renames matchHead
      scrutineeItems firstCase secondCase caseTail copied (.atom matchHead) matchForm matchIsHole
      wholeCopied
  have scrutineeCopyOperation :
      (operations (macroNames rules) (copyFuel + cost + 1)).copy origin copyHoles renames fresh
        (.list scrutineeItems) = some (copiedScrutinee, afterScrutinee) := scrutineeCopied
  rw [copyNeutralList_uses_copyMany (macroNames rules) (copyFuel + cost) origin copyHoles
    renames fresh scrutineeItems scrutineeHeadSafe] at scrutineeCopyOperation
  obtain ⟨pair, copiedMany, outputRun⟩ := option_bind_some scrutineeCopyOperation
  rcases pair with ⟨copiedItems, afterCopy⟩
  have outputEq : (Tree.list copiedItems, afterCopy) = (copiedScrutinee, afterScrutinee) := by
    simpa using Option.some.inj outputRun
  have listEq : Tree.list copiedItems = copiedScrutinee := congrArg Prod.fst outputEq
  cases copiedScrutinee with
  | atom _ => simp at listEq
  | list copiedScrutineeItems =>
      have itemsEq : copiedItems = copiedScrutineeItems := Tree.list.inj listEq
      subst copiedScrutineeItems
      have copiedArguments : copyManyWithMacros (macroNames rules) (copyFuel + cost) origin
          copyHoles renames fresh scrutineeItems = some (copiedItems, afterScrutinee) := by
        have afterEq : afterCopy = afterScrutinee := congrArg Prod.snd outputEq
        rw [afterEq] at copiedMany
        simpa [copyManyWithMacros] using copiedMany
      obtain ⟨target, templateCall⟩ := literal_call_site_to_next_macro_step rules
        (macroNames rules) templateHoles copyHoles renames origin childOrigin copyFuel fresh
        afterScrutinee head arguments copiedItems childRule site known notHole lookupNone
        copiedArguments childMember copiedChildMatches
      have scrutineeMember : .list scrutineeItems ∈
          .atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail :=
        List.mem_cons_of_mem _ (List.mem_cons_self _ _)
      have staticCall := StaticCall.nested scrutineeMember templateCall
      exact ⟨target, template_static_call_rank_decreases graphFuel rules index owner rule tailRules
        templateHoles
        (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail))
        target edges ranks parsed dependencyCheck staticCall graphAccepted ranksAccepted⟩

/-- Certified version: for every copied redex selected by the scrutinee
`LiteralCallSite`, an accepted child `checkStep` supplies the successful rule
match consumed by the rank proof. Fresh counters and child outputs are allowed
to depend on the selected occurrence. -/
theorem match_hole_head_scrutinee_certified_rank_decreases
    (graphFuel copyFuel childFuel : Nat) (rules : List (Nat × Tree))
    (index owner childOrigin origin fresh final : Nat) (rule : Tree)
    (tailRules : List (Nat × Tree)) (templateHoles : List String)
    (matchHead : Atom) (scrutineeItems : List Tree) (firstCase secondCase : Tree)
    (caseTail : List Tree) (cost : Nat) (copied : Tree) (head : Atom)
    (arguments : List Tree) (site : LiteralCallSite (macroNames rules) head arguments
      scrutineeItems cost) (childRule : Tree) (copyHoles : Holes) (renames : Renames)
    (dependencies : List Nat) (edges : List Edge) (ranks : List Nat)
    (matchForm : matchHead.name = "match")
    (matchIsHole : lookup matchHead.name copyHoles = some (.atom matchHead))
    (scrutineeHeadSafe : counterNeutralListHead (macroNames rules) scrutineeItems = true)
    (known : (macroNames rules).contains head.name = true)
    (notHole : head.name ∉ templateHoles)
    (lookupNone : (lookup head.name copyHoles).isNone = true)
    (parsed : parameters rule = some (templateHoles,
      .list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)))
    (wholeCopied : copyWithMacros (macroNames rules) (copyFuel + cost + 2) origin copyHoles
      renames fresh
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)) =
        some (copied, final))
    (childMember : (childOrigin, childRule) ∈ rules)
    (copiedChildSteps : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childFresh childFinal childOutput,
        NLisp.ExpansionCertificate.checkStep rules childOrigin childFuel childFresh childFinal
          childRule copiedCall childOutput = true)
    (dependencyCheck : calls graphFuel rules templateHoles
      (.list (.atom matchHead :: .list scrutineeItems :: firstCase :: secondCase :: caseTail)) =
        some dependencies)
    (graphAccepted : graphRows graphFuel rules index ((owner, rule) :: tailRules) = some edges)
    (ranksAccepted : checkRanks edges ranks = true) :
    ∃ target, rank ranks target < rank ranks index := by
  have childMatches : ∀ copiedItems copiedBefore copiedCall copiedAfter,
      copiedItems = copiedBefore ++ copiedCall :: copiedAfter →
      ∃ childHoles childTemplate,
        matchRule childRule copiedCall = some (childHoles, childTemplate) := by
    intro copiedItems copiedBefore copiedCall copiedAfter split
    obtain ⟨childFresh, childFinal, childOutput, accepted⟩ :=
      copiedChildSteps copiedItems copiedBefore copiedCall copiedAfter split
    obtain ⟨childHoles, childTemplate, _member, matched, _copied⟩ :=
      NLisp.ExpansionCertificate.checkStep_sound accepted
    exact ⟨childHoles, childTemplate, matched⟩
  exact match_hole_head_scrutinee_call_site_rank_decreases graphFuel copyFuel rules
    index owner childOrigin origin fresh final rule tailRules templateHoles matchHead
    scrutineeItems firstCase secondCase caseTail cost copied head arguments site childRule
    copyHoles renames dependencies edges ranks matchForm matchIsHole scrutineeHeadSafe known
    notHole lookupNone parsed wholeCopied childMember childMatches dependencyCheck graphAccepted
    ranksAccepted

end NLisp.MacroTermination
