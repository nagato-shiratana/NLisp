# Macro reference model: implementation status

`NLisp.MacroReferenceModel` は、decode・型付け済みの `CMacroCopy.Tree` を入力として、
関数本体相当の構文木を左端・深さ優先で走査する小さな参照実行器である。

## 実装済み

- `tryRoot` / `stepAt` / `run`: ルール照合、hygienic copy、生成された呼び出しの反復展開。
- `RunResult.completed`: redexがなくなった結果。
- `RunResult.fuelExhausted`: redexが残ったまま展開fuelを使い切った結果。
- `RunResult.failed`: ルール照合後のcopyが失敗した結果。
- `normalize`: atomの`origin`と`token`を比較から除外する正規化。
- `compare`: C結果とLean結果の正規化済み構文を比較する型。
- `rankStatus`: `MacroTermination.checkRanks` が通った場合だけ `proven`、それ以外は `unproved`。
- `rankTraceStatus` / `GoodRankTrace`: C traceのrule index列について、静的辺と順位減少を
  各隣接stepで確認する。`rankTraceStatus_proven` はこの条件から `proven` を導く。
- `tools/macro_reference_bridge.py`: C `export-core` のJSON `macro_trace`を読み、Leanソースを
  自動生成して各traceの`input`を参照モデルへ入力し、Cの`result`と正規化キーを比較する。
  同時に既存のtermination planからedges/ranksを取得し、逆順C traceをLeanの
  `GoodRankTrace`として検査する。

この `proven` は、与えられた静的グラフと順位列が全辺で減少することだけを意味する。
任意の実展開列がそのグラフに対応することや、C実装全体の正しさは主張しない。

## 再現コマンド

```sh
PATH="$PWD/.tools/lean-4.8.0/bin:$PATH" .tools/lean-4.8.0/bin/lake build NLisp.MacroReferenceModel
PATH="$PWD/.tools/lean-4.8.0/bin:$PATH" .tools/lean-4.8.0/bin/lake env lean tests/MacroReferenceModel.lean
python3 tools/macro_reference_bridge.py ./build/nlisp examples/recursive_expansion.nlisp \
  --lake .tools/lean-4.8.0/bin/lake --fuel 64
```

専用テストは、整数式の穴1個をテンプレートで2回使い、lambda binderを1個freshenする固定ケースを含む。

## 残るGPT-6向け指示

1. C側の成功、資源上限による`Unknown`、型／形状失敗を、
   `RunResult`と同じ `completed`／`fuelExhausted`／`failed` の分類へ写像する。
   現在のbridgeはCLI失敗時の大分類まで実装済みであり、trace単位のC側成功結果との比較を行う。
   Cの`Unknown`を発散と表示してはならない。
2. Cの`Unknown`とLean fuel切れを同じ入力・同じ資源設定で比較するテスト、意図的な
   構文不一致を検出するテスト、rank未証明を表示するテストを追加する。
