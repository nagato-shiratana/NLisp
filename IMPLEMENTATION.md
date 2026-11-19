# NLisp-Core C参照処理系

このディレクトリには、`SPECIFICATION.md` の組み込み関数と型付き関数・マクロを実行するC17処理系を置く。Leanコアの保証範囲は `LEAN_FORMAL_SPECIFICATION.md` を参照する。

## 対応機能

### 2026-11-19 追補: 構文照合と束縛ID意味論

`ExpansionLowering.lean` は、CBindingWalkが検査した同じ注釈付き構文と、提案されたSurfaceの各ノードを独立に照合する。シグネチャ、型注釈、束縛IDから局所添字への対応、引数順、並列let、match節、組み込み関数の固定表現を検査する。省略した型引数を持つ呼び出しは、全型変数が仮引数型に現れる場合に限る。型整合性は別途SurfaceCheckerが検査する。mainの宣言名・シグネチャと整数エントリーポイントも照合する。

`NamedSemantics.lean` は、局所変数を束縛IDで参照し、環境をIDと値の対応列として扱う独立した有限評価意味論である。`NamedDecoder.lean` は元の注釈付き構文からこの操作的構文を読み取る。型注釈・型適用は操作的構文では実行しないが、元構文と型付きIRの注釈対応を上記の照合器で検査する。

`NameLowering.evaluation_preserved` は任意の有限のNamed評価を、位置添字を使う実行用IRの評価へ移す一般定理である。クロージャ、共有された再帰関数表、並列let、List/Option照合を含む。poly証書は元構文の読み取り、生成IRとの型消去後の一致、`source_evaluation_preserved` を入力ごとにカーネル検査する。単に型が合う別の出力を提示しても受理されない。

この定理は有限評価の前向き保存であり、逆向きの評価反映、Named意味論とC実行器の対応、新多相モデルの型安全性、検査器全体の多項式時間を追加で保証するものではない。保証範囲の `formal_semantic_preservation` は処理系全体の保証ではないためfalseを維持し、polyのkernel_checksに上記の部分保証を列挙する。

名前変換は数値IDを含むsizeOfによる再帰から、構文の入れ子帰納原理へ変更した。Lean 4.8のネイティブコード生成がこの帰納原理に未対応のため、この証明用変換はnoncomputable指定だがカーネル内では簡約できる。Cの実行器と既存の実行可能な型消去関数は維持する。これは検査器全体の計算量上界の証明ではない。

`TypeArguments.lean` は一方向の型引数収集アルゴリズムと証明付き結果を追加する。戻り値の期待型を入力にせず、呼び出し側の型変数を固定した構文として扱い、未決定変数や競合する制約を拒否する。成功値は型引数個数、呼び出し側での整形式性、仮引数型の具体化と実引数型の一致、一意性を保持する。`inferred_arguments_unique` は、全量化変数が仮引数型に現れるという判定の受理から、任意の二つの整合する型引数列が等しいことを証明する。一般的な完全性、Cの推論器との一般的な対応、新多相モデルの型安全性は別課題である。

### 2026-11-19 追補: 多相評価器の型安全性

`PolymorphicSafety.lean` は、型変数の解釈、型付きの実行時値・環境、共有された全関数本体の型付け条件を定義する。`evaluator_type_safe` はfuelに関する帰納法で、式・引数列・begin列の評価が、型に合う値またはoutOfFuelに限られることを同時に証明する。`evaluation_preserves_type` は成功結果の型保存、`evaluation_no_type_error` はunbound/wrongArity/wrongShapeが起きないことの系である。汎用本体を一つだけ保持し、多相再帰で変わる型引数は証明中の解釈だけで扱う。

`elaborateProgram_programTyped` はSurfaceCheckerの成功から全ソース本体の型付け条件を導く。証明付き項を生成した事実だけでなく、その項のexpressionが元の入力本体と同じであることも証明する。poly証書に `program_typed` と `entry_has_no_type_error` を追加し、型検査済みの実際のエントリーポイントへ接続した。`tests/PolymorphicSafety.lean` は汎用identityと型が成長する多相再帰を扱い、依存公理は標準3公理のみ。

対象は新SurfaceモデルのBoolean/Integer/Unit/関数/List/Optionである。これは有限予算の評価器に関する意味的な型安全性であり、別途定義した小ステップ関係に対する構文的Progress定理やC実行器全体の正しさと同一視しない。初期実装記録にある新多相モデルの「型安全性未証明」は、この評価器と対象型の範囲について更新された。

### 2026-11-19 追補: 大域値を捕捉するCクロージャ

C実行器で、大域値の初期化前に生成したクロージャが、後から初期化された同じ束縛を参照できない例を修正した。全大域値に未初期化の共有セルを先に確保し、ソース順に各初期化式を実行してセルを一度だけ埋める。関数・ラムダは同じセルを参照する。未初期化セルを実際に読むと、内部のunboundではなく「before its initialization」の初期化エラーを返す。局所束縛やマクロ定義位置のスコープは維持する。

`tests/global_initialization.py` は、後から初期化されるセルを参照する脱出クロージャ、局所シャドーイング、初期化中の読み出し、未選択分岐、未使用でも実行する初期化式、マクロの定義位置を確認する。Cの修正と規範仕様の明確化であり、polyモードへのdefineの変換と初期化・捕捉の意味保存証明はまだ実装していない。

`GlobalIR.lean` はこの変換を接続するための実行可能な基礎モデルである。大域値は未初期化/初期化済みのストアに保持し、内部の0引数getterが呼び出し時のストアを読む。クロージャの局所環境へ古い大域値を固定せず、初期化式をソース順に実行してからエントリーポイントを実行する。`initialization_length`、`initialized_prefix_unchanged`、`initialized_cells_present` により、成功した初期化はセル数を変えず、先行セルを上書きせず、処理した範囲を初期化済みにすることを証明した。`tests/GlobalIR.lean` はCと同じ脱出クロージャの例を実行する。このモデルの入力はIRであり、元ソースのdefineからの変換・型安全性・C実行器との対応を証明したとは扱わない。

### 2026-11-19 追補: 整数の大きさと証明検査コスト

`PolyIR.erase` の終了性の尺度を、既定のsizeOfから `sourceNodes` / `sourceListNodes` に変更した。既定の尺度には整数・添字の数値の大きさが入る一方、新尺度は再帰する構文ノードだけを数える。これは同じ型消去関数の終了性を別の尺度で証明する変更であり、消去結果は変えない。尺度の計算は証明にのみ現れ、型消去関数のネイティブ実行は維持する。

`tests/ErasureMagnitude.lean` で100桁超の整数の型消去をカーネル簡約とネイティブ実行の両方で確認する。`examples/large_integer.nlisp` は同じ問題の証書検査例である。数値の大きさに依存した余分な終了性証明の計算を避ける修正であって、独立検査器全体のビット計算量が多項式であることを証明したものではない。

### 2026-11-18 追補: 表層意味論・多相IR・型消去

`EvaluatorCorrectness.lean` と `EvaluatorCompleteness.lean` は、実行用評価器の成功と有限の大ステップ導出の同値、および十分なfuel以後の結果の安定性を証明する。表層の注釈付き評価器についても `SurfaceEvaluatorCorrectness.lean` と `SurfaceEvaluatorCompleteness.lean` で同じ健全性・完全性を証明した。双方の評価関係の決定性も検査済み。

`Erasure.lean` の `evaluation_preserved` は表層の有限評価導出から型消去先の有限評価導出を構成する。`ErasureExecution.lean` の `execution_commutes` は同じfuelでの実行結果が値・エラーの両方について一致すること、`finite_evaluation_iff` は終了の保存と反映、`execution_error_iff` はエラーの対応を示す。`fuel_divergence_iff` は「すべての有限fuelでoutOfFuel」の同値であり、1回の予算切れを非停止と判定するものではない。公理監査はLean標準3公理のみで、独自公理・sorryAxはない。

新しいLeanモデルとして `NLisp/Surface.lean`、`NLisp/SurfaceSemantics.lean`、`NLisp/PolyIR.lean` を追加した。旧単相コアとは別の意味論であり、C/JSONからの変換はpolyモードで構成する。旧経路との一般的な対応定理はまだない。

- Surface: 型変数付き単相型、rank-1関数シグネチャ、明示的グローバル型適用、複数引数・0引数lambda/app、並列let、非空begin、List/Option照合、外在的型付け判断。
- SurfaceSemantics: 型注釈と型引数を保持したクロージャによる、独立した有限の大ステップ評価関係。共有されたグローバル関数表で自己再帰と相互再帰を表す。
- PolyIR: 型導出を保持するCheckedExprとDefinition、全本体の型導出を要求するProgram。実行用Termへの全域的な型消去、タグ付きValue、予算付き評価器。

関数本体は型引数ごとに複製しない。型抽象はDefinitionのtypeArityに対応するシグネチャ束縛、型適用はglobalの明示的な型引数列として保持する。実行用表現だけからこれらを除く。新モデルは既存TypedExpansion.Tyとは別の型であり、両者の一般的な対応は未接続。

`SurfaceChecker.lean` は全Surface構文の実行可能な型検査と証明付きIR構築を行う。`elaborateProgram` は共有された全シグネチャの下で各汎用本体を一度検査し、再帰・相互再帰・多相再帰を具体化なしに受理する。成功値自体に `HasType` の証明を保持する。明示的型引数を持つ展開後構文が入力であり、Cの一方向型引数推論の正しさはまだ接続していない。checkerの深さ予算超過と型不適合はともにnoneとなるため、noneは不適合の証明として使わない。一般的な完全性・型保存・Progressは未証明。

局所環境は先頭パラメーターが添字0。並列letの全右辺は元の環境で評価し、結果列を同時に追加する。グローバル本体の局所環境は引数だけ。`verify_lean.py --mode poly` はC展開結果から明示的型引数を持つSurfaceへ変換し、全汎用本体・mainの型検査と検査済みProgramの型消去対応をLeanで照合する。旧経路と異なり再帰本体のインライン化・型ごとの具体化は行わない。Python変換とC構文の一般的な対応定理、トップレベル初期化・捕捉の明示化、C型表現との対応は未接続。トップレベルdefineはpolyモードで明示的に拒否する。fuelは導出深さを制限し、総実行ステップ数や多項式時間保証ではない。新SurfaceモデルはBoolean/Integer/Unit/関数/List/Optionの範囲で、Float/String/Characterと残りの組み込み関数は旧TypedExpansionモデル・C実装の範囲に残る。

Lean 4.8.0で全モジュールとSurfaceIR/Erasure/EvaluatorCorrectness/ErasureExecution/SurfaceCheckerの検査を実施する。auto/core/typesには移行前の具体化経路を残し、polyを明示指定して新経路を利用する。以下の対応機能一覧はC処理系の範囲を表す。

- S式と行コメント
- `Boolean`、任意精度`Integer`、binary64 `Float`、UTF-8 `String`、Unicode scalar `Character`、`Unit`
- 関数、クロージャ、一般再帰、相互再帰
- `if`、`let`、`begin`、`lambda`
- `List`、`Option`、網羅的`match`
- 仕様8.2節の全26組み込み関数（整数・浮動小数点演算、比較、真偽値、文字列、文字、数値変換）
- 静的型検査
- 左から右のcall-by-value評価
- `check`、`run`、`expand`、`export-core`コマンド
- 単相の型契約を持つ、予算付きの再帰的な型付き衛生テンプレートマクロ

## 現在の意図的な制限

- `Integer`にはGMPを使用する。ビルドにGMPのヘッダーとライブラリが必要。
- `Float`の四則演算はホストCのbinary64演算を使用する。C APIの処理中は呼び出し元の浮動小数点環境を保存し、例外トラップを保留した上でroundTiesToEvenを選び、終了時に環境を復元する。小数リテラルの変換は四則演算経路と分け、10進仮数・指数をGMPの整数比にしてからbinary64ビット列へroundTiesToEvenで一度だけ丸める。`strtod` と数値ロケールに依存しない。CMakeでは浮動小数点環境を尊重するコンパイラ設定（GCC/Clangの`-frounding-math`、MSVCの`/fp:strict`）を使う。Lean上の浮動小数点評価意味論とC実装全体の正しさは未証明である。
- rank-1多相関数、明示的型適用、実引数型からの一方向型引数決定に対応。
- マクロの各規則は固定引数・単相契約。同一マクロに異なる引数個数の規則を複数定義できる。同じ引数個数の重複規則は拒否する。
- マクロの後方参照と直接・間接の再帰に対応する。定義は参照先の型契約を用いて検査し、実際に使用した場合だけ本体を予算付きで展開する。循環だけでは拒否しない。
- `defrec` は単相・多相の関数群に対応し、スコープ索引を割り当てる前に個別の関数宣言へ正規化する。従来の `defun` 間の相互参照も利用できる。
- メモリは処理終了時に一括解放するarena方式。
- ソースファイルは1個、エントリーポイントは`main : () -> Integer`。

未実装構文は受理せず、診断を返す。

文字列はバイト長を保持するため、`\\u{0}` を含む値も比較・連結できる。入力のUTF-8、文字とエスケープのUnicode scalar範囲を検査する。`quotient` と `remainder` は0除算で `None`、それ以外では0方向へ丸めた商・余りを `Some` で返す。`float-truncate` は有限値を任意精度整数へ変換し、NaN・無限大では `None`。小数リテラルと `to-float` は、捨てる余りを整数で比較して最近接・偶数丸めを行う。Float四則演算の形式的評価意味論とC演算器全体の正しさは未証明である。

## 多相関数と型引数

```lisp
(defun identity
  (forall (T) ((value T)) T)
  value)

(identity 42)
((type-app identity Integer) 42)
```

呼び出しごとに新しい型代入を作り、実引数の型と仮引数の型を構造的に照合する。同じ型変数から得られた制約は完全一致を要求する。戻り値の期待型は使用しない。型変数が未決定なら`type-app`を要求する。

```lisp
(defun empty (forall (T) () (List T)) (Nil T))
((type-app empty Integer))
```

型変数は関数ごとに異なる識別を持ち、本体の宣言型、ラムダ、コンストラクタ型引数でも有効である。List、Option、関数型の内部を再帰的に照合する。多相関数を高階関数へ渡す場合は`type-app`で単相化する。暗黙の一般化、高階ランク多相、期待戻り値型からの型引数決定は行わない。

型適用は実行時に消去する。ラムダの仮引数情報は静的検査時に保持し、実行時に型変数を再解釈しない。

使用例は`examples/polymorphism.nlisp`。Lean連携テストで具体化後のコア式を型検査する。多相型検査アルゴリズム全体の健全性・完全性を証明したものではない。

## 型付き衛生マクロ

```lisp
(define-macro when
  (syntax-rules/typed
    ((when condition body)
     ((condition (Syntax Boolean)) (body (Syntax Unit)))
     (Syntax Unit)
     (if condition body unit))))
```

定義時には入力を宣言型の不透明な式としてテンプレートを検査する。呼び出し時には実引数の型を検査してからテンプレートを生成し、出力型を検査する。全展開の後、プログラム全体の型検査を再実行する。

テンプレートが導入するlambda仮引数、let束縛、matchパターン変数には新しい内部名を与える。挿入する引数構文は呼び出し位置の束縛を維持し、テンプレートの自由変数はマクロ定義位置の値環境を参照する。内部名の接頭辞`#%nlisp`はソースで使用できない。

パターン変数は式の穴だけを表す。束縛名の穴、型の穴、反復パターン、手続き的マクロ、意図的捕捉は対応しない。マクロの依存先は宣言順に制限されず、循環も許可する。各規則の入力・出力契約は定義時と利用時に検査する。自由変数の参照先は各規則の定義位置で決まり、後方参照先マクロの自由変数を呼び出し位置の同名変数へ結び直さない。後方参照を通じて未初期化のトップレベル値を読む利用は静的エラーとする。有限の入力でもテンプレートの複製により展開サイズは増大し得る。

```text
build/Release/nlisp run examples/macros.nlisp
build/Release/nlisp expand examples/macros.nlisp
```

使用例の結果は44。定義位置のoffsetと加算、呼び出し位置のtemp、入れ子のtwiceを組み合わせる。expandは内部束縛名を含む診断表示であり、自由変数の定義位置情報を直列化しないため再実行用ソースや証明書としては使用できない。

Lean側では `TypedMacro` と型付き置換による抽象コアテンプレート展開を追加し、出力型の保存と束縛子下での穴のシフトを検査する。`export-core` は診断表示と異なり、各アトムに `origin` を保持するJSONを出力する。`tools/verify_lean.py` は定義位置と呼び出し位置を区別して型付きコア式と非stuck性の証明を生成し、Leanで検査する。JSONと橋渡しツールは信頼する証明基盤に含めず、生成した項をLeanが再検査する。ただし、生成項が入力ソースと同じ意味であることは別の証明義務であり、C展開実装全体の正しさはまだ証明していない。

`--mode types` は `NLisp.TypedExpansion` に対する証明書を生成し、Float・String・Characterを含む全実行時型と26組み込み関数の型を検査する。浮動小数点リテラルはbinary64のビット列、文字列・文字はUnicode scalar列として保持する。`Expr.hasType` は型添字を消した項に外在的な型付け導出を与える。このモードは型付けの保証に限り、非stuck性やIEEE 754演算の正しさを主張しない。既定の `auto` はコア対象外の式にこの証明書を使い、結果表示で区別する。

## ビルド手順

```text
cmake -S . -B build
cmake --build build --config Debug
ctest --test-dir build -C Debug --output-on-failure
```

## 実行

```text
build/Debug/nlisp check examples/factorial.nlisp
build/Debug/nlisp run examples/factorial.nlisp
```


## 展開予算と Unknown

`NLISP_UNKNOWN`（終了コード7）は処理予算内で確認できなかったことを表す。型・構文エラーとは異なり、非停止の証明ではない。すべてのコマンドで同じ上限を使い、Unknownではstdoutに成功結果・展開テキスト・JSONを出力しない。`run` は実行を開始しない。実行時プログラムの再帰計算には、このコンパイル時予算を適用しない。

| CLIオプション | 既定値 | 計数対象 |
|---|---:|---|
| `--max-expansions` | 10000 | 実際に処理するマクロ呼び出し数（定義の記号的検査は除く） |
| `--max-generated-nodes` | 100000 | 定義検査を含むテンプレート複製ノード数、および共有を展開した最終プログラムのノード数。それぞれが上限以下である必要がある |
| `--max-expansion-depth` | 128 | ソース構文、テンプレート複製、展開後の検査・出力木の深さ。ネイティブスタック保護のため設定値の最大は512 |
| `--max-check-steps` | 1000000 | マクロ定義・利用・展開後の再検査を含む式型検査の訪問回数 |

各カウンターは1コマンド全体で共有し、展開後の再検査でリセットしない。0は無制限ではなく予算ゼロを表す。上限値以下の処理を許し、さらに処理が必要になった時点でUnknownを返す。共有された構文を繰り返し印字して出力サイズが爆発することを避けるため、最終木の論理サイズと深さもメモ化して検査する。

既存のC APIは既定値を使う。設定する場合は `nlisp_default_limits` と `nlisp_process_file` に `NLispLimits` を渡す。CLIの上限オプションはファイル名の前後どちらでも指定できる。

Lean連携ツールにも同じ4つのオプションを指定できる。C処理系のUnknownと、具体化・変換の深さ制限超過は終了コード7で伝え、新しい証明書を書き出さずLean検査を開始しない。以前の実行で作ったファイルは書き換えないため、終了コードと記録された入力ハッシュで成功結果を識別する必要がある。

連携ツールにはさらに `--max-certificate-bytes`（既定4194304バイト）と `--max-conversion-steps`（既定100000）を設ける。具体化・描画中の中間項と最終証明書のサイズ、式変換と項組み立ての作業回数を検査する。停止性モードと通常モードで付随する候補解析では、規則・構文の走査、候補辺の生成、順位グラフ構築にも同じ上限値を別工程として適用する。予算不足によるUnknownには、停止性モードの候補解析が試行した作業量と上限値を含める。これは全工程を合算した厳密な実行時間上限ではない。具体化の依存深さ100の上限とPythonの再帰制限もUnknownに分類する。`auto` の各変換方式はそれぞれの予算で試し、予算を使い切った場合は別方式を試して成功扱いにしない。

証明書は一時ファイルでLean検査し、成功した場合だけ出力先へ置き換える。Leanが再帰深さ・heartbeats・メモリ・スタックの資源上限を報告した場合もUnknownとし、一時ファイルを削除して以前の証明書を保持する。通常のLean型検査エラーでも不完全な新しい証明書を出力先へ公開しない。これらの実装上の予算管理の一般的な正しさはまだ形式証明していない。


## 過程の記録と証明書形式

`export-core` は `nlisp-scoped-expansion-v2` を出力する。従来の `declarations` に加え、`source_text`、`source_ast`、`normalized_ast`、`limits`、`macro_trace`、`name_resolution` を含む。展開履歴は成功して完了した呼び出しの順に並べ、呼び出しID、マクロ名、規則の引数個数、定義位置、呼び出し位置、規則、未展開の入力、衛生的置換直後の構文、完全展開後の結果を記録する。参照共有で履歴出力が膨大になる場合も、履歴の論理ノード数と深さを検査してUnknownを返す。予算超過時に不完全な履歴をstdoutへ出力しない。

単一ファイルの `nlisp-process-certificate-v1` は元ソースをBase64で保持し、展開文書、式ごとの変換文脈・出力項・型、閉じたプログラムの構築記録、Lean本文ハッシュ、Leanモデルとツールチェーン指定ファイルのハッシュ、保証範囲をJSONに格納する。JSON全体をさらにBase64化し、ハッシュとともにLeanコメントに埋め込む。Lean本文は同じファイルの末尾に置く。ファイル全体に `--max-certificate-bytes` の上限を適用する。変換記録を含む中間データもサイズ上限を検査する。

`--verify-certificate` は埋め込まれた元ソースを一時ディレクトリに復元して `export-core` を再実行し、全過程を照合する。記録した方式の変換も再実行し、変換記録とLean本文を照合してからLean検査する。検証前にファイルサイズ・宣言された予算を検証者の上限と比較する。予算の引き上げを証明書の自己申告だけで許可しない。本文は再生成結果と一致した場合だけLeanへ渡す。再検証は元ファイルを変更しない。

`--verify-certificate ... --independent` はC処理系を起動しない。元ソースと展開導出の証拠、変換記録から本文を再構成し、読み取り・正規化・局所展開・束縛対応をLeanカーネルで検査する。存在しない `--nlisp` を指定して数学マクロの実証書を検査する統合確認に成功した。通常の再実行方式も残す。

JSON内の重複キー、不正なBase64、ダイジェスト不一致、別のLean環境、再現できない入力・規則適用・変換・本文はエラーとする。暗号署名はなく、保証範囲のフィールドにもその旨を明記する。検査器全体の正しさと多項式時間上界の一般証明は残る。証書のassurance内のprocess欄は生成時の記録方式であり、再検査にCを起動したかは選択した検査モードによる。

元ソース・証明書の読み込みとC過程出力の取り込みにも証明書のバイト上限を適用し、上限を超えた出力をメモリへ無制限に取り込まない。上限超過時は自分が起動したC子プロセスを終了して回収し、Unknownを返す。証明書自体の改行はLFに固定し、同梱する元ソースの改行・UTF-8バイト列はそのまま保持する。


## 束縛環境の形式モデル

`NLisp/ScopedSyntax.lean` は全実行時型の型付けモデルに、束縛IDを持つ環境、所属環境付き構文、定義位置・呼び出し位置からの別々の埋め込みを追加する。埋め込みには型保存だけでなく束縛ID保存の証明を要求する。重複IDの環境は許可しない。テンプレートの穴と捕捉変数を別の代入領域として定義し、導入した束縛子の下では既存参照を持ち上げる。

C処理系は一意化した内部名、定義位置の環境スナップショット、Macro.originに加え、アトムのトークンID・実際に選んだ束縛ID・型タグ・名前解決に使用した環境を記録する。通常の証明書は、有限の展開に関する衛生的置換と束縛IDをLeanで照合する。証明書は使用した各Leanモデルのハッシュも記録し、異なるモデルに対する過程記録を黙って受理しない。C全体の機械意味論と形式モデルの一般的な対応証明は含まない。


## 2026-11-18追加: C展開とスコープの証明書検査

識別子IDは組み込みが `3*(index+1)`、元の字句が `3*(tokenIndex+1)+1`、生成した束縛名が `3*freshCounter+2` である。名前の文字列比較による実際の探索境界で、要求名・選択した束縛・環境・定義位置を観測する。型タグはCの型オブジェクトの識別用であり、型意味論の証明済み符号化とは扱わない。

`CNameResolution.findName_sound` は環境の先頭側にある同名束縛を選ぶ関係との対応を示す。観測値は同じ環境ごとにまとめて閉じた計算で検査し、`observations_correspond` により型付きの `ScopedSyntax.Var` と同じ束縛IDを持つことへ接続する。

`CMacroCopy.copy` は予算付き衛生的置換の独立した関数仕様である。穴の引数をそのまま挿入し、自由識別子には定義位置を付け、束縛子とその参照だけを同じ生成名へ変える。lambdaのパラメーター、並列letの右辺と本体、matchの各節の局所環境を区別する。元の字句のID領域と内部名予約を検査し、各展開が新しく使ったカウンター区間の重複を拒否する。

`CExpansion.Expands` は、元の規則に属すること、呼び出し名と引数個数が一致すること、衛生的置換の計算結果が一致することを前提とする展開ステップと、その文脈閉包・推移閉包である。`ExpansionCertificate.Certificate` は `refl`、リスト内の単一子変更 `congList`、マクロ `step`、連続性を検査する `trans` からなる局所データである。汎用Boolean関数 `check` が規則所属・パターン照合・衛生的コピーを再計算し、`check_sound` が受理から `CExpansion.Expands` を導く。生成器はCの展開履歴をこのデータへ変換して同じ `check` へ渡す。

`CBindingWalk` はCの観測環境を受け取らず、最終構文から環境を導出する。関数の前方参照、順番に初期化されるトップレベル値、lambda、並列let、List/Optionのmatch、型適用を扱う。各参照について、実効環境での名前解決とCの束縛IDの一致、両環境のIDの重複がないこと、選んだ束縛が呼び出し時点の環境にも存在することを検査する。結果は任意の型解釈に対する型付き変数への対応として示す。これにより同じ型でも別の束縛へ移すことや、定義位置にある未初期化値を呼び出し側から読むことを拒否する。

検査用の構文の消去結果と `program_expands` の出力が一致することも証明書に含める。局所証書の各 `check` を小さい補題で合成し、カーネル内で証明項全体を単一の大きな再帰計算へ展開しない。Leanが強制終了された場合もUnknownにし、新しいファイルを公開せず以前の証明書を保持する。

`SourceReader.readWithFuel` による独立した読み取り、`SourceReader.normalize` による正規化、文字列のUTF-8バイト列の一致もLeanで検査する。`ProcessCertificate.CheckedExpansion` は同じデータに対する各証明を一つにまとめる。コメント内の過程記録とLean本文が対応することは専用検証器の再生成照合で確認する。コアへの変換の一般的な意味保存や、C型タグの意味論との同値は未証明である。保証範囲フィールドの `formal_semantic_preservation` は引き続き `false` とする。

## マクロ規則の静的な終了性検査

`export-syntax` は `nlisp-syntax-v1` として、元の文字列、元の構文、正規化済み構文、使用予算を出力する。マクロを展開せず、式の型検査もしない。従って循環規則の静的解析にも利用できる。

`--mode termination` は規則を名前と引数個数で区別して呼び出し関係を作る。名前付き呼び出しでは同じ名前・arityの全規則を候補にし、構文穴が呼び出し先になる位置では、そのarityに合う全マクロ規則を候補辺へ加える。後者は動的な候補を取りこぼさないための過近似であり、実際には発生しない辺を含んで証明できなくなる場合がある。型注釈も保守的に走査する。順位候補は基底規則から逆向きに作り、Leanが辺の抽出と各辺の厳密減少を独立に検査する。

`targetsOfSignature` は名前付き呼び出しに一致する全規則を候補にし、`targetsOfArity` は穴頭位置に対して同arityの全規則を候補に加える。`findRule_mem_targetsOfSignature` と `findRule_mem_targetsOfArity` は既存の名前検索先がそれぞれの候補集合に含まれることを示す。`MacroTermination.accessible` は `termination_by rank ranks node` によりアクセシビリティを構成する。`ranked_graph_wellFounded` が候補辺を含む関係の整礎性、`path_length_bounded` が呼び出し鎖の長さに関する上限を示す。偽の順位や辺の省略はLeanが拒否する。

静的に証明できない場合はUnknownであり、非停止の証明ではない。このモードは新しい証明書を発行しない。通常の有限展開モードでは、静的解析がUnknownでも実際の展開が完了していれば、その有限導出を証明できる。両者を過程記録のモードと保証範囲で区別する。

候補呼び出し関係の整礎性からC展開器全体の終了性を導く一般的なシミュレーション定理、穴の実引数に基づくより精密な動的呼び出し解析、構造的減少の自動証明、利用者が指定する任意の整礎関係の入力構文は未実装である。実行時のNLisp関数の停止性も今回の証明対象には含めない。通常の展開予算は証明の有無にかかわらず適用する。


## ソースとモデルの照合

`SourceReader` はCとは別に空白・コメント・S式・リテラルを読み取り、括弧も含むトークン位置からIDを付ける。CRLF、Unicodeの識別子とコメント、エスケープ、区切り文字の文字リテラルも扱う。文字列のUTF-8エンコード結果を元のバイト値と照合し、解析結果と正規化結果をCの構文木に照合する。予算は証明書内の自然数として明示する。有限の予算で全ソース・トークンを読み終えた結果に一致することが成功条件であり、部分読み取りを成功扱いにしない。

`ProcessCertificate.CheckedSource` はバイト列・文字列・読み取り・正規化を結び付ける。`CheckedExpansion` はさらに衛生的展開と全参照のスコープ検査を、`CheckedStaticTermination` は保守的な呼び出し候補関係の整礎性を同じソースへ結び付ける。本文の別々の箇所に互いに無関係な検査結果を置くだけでは、これらの構造体を構成できない。

生成時と再検証時には `lake build` を実行し、古いoleanを使って新しいソースハッシュだけを記録することを避ける。実際のLeanの版も検査する。全Leanモジュール、ルートモジュール、`lean-toolchain`、Lake設定、依存指定のハッシュを記録し、ビルドや本文検査の途中にファイルが変わった場合は拒否する。


## 名前空間と字句規則の補正

予約語、型名、コンストラクタ名、リテラルを束縛名として受理しないよう、関数・値・パラメーター・型変数・マクロ・パターン・テンプレートの束縛位置を検査する。テンプレートでは一意化する前の名前の重複を拒否し、別の内側スコープによる遮蔽は維持する。

空白はUnicode 18.0のWhite_Space属性の25コードポイントを用い、CとLeanの両方で同じ境界を認識する。NEL、LINE SEPARATOR、PARAGRAPH SEPARATORもコメントの行末として扱う。U+180E、U+200B、U+FEFFは空白に加えない。属性値は[Unicode PropList](https://www.unicode.org/Public/18.0.0/ucd/PropList.txt)を基準にする。

値とマクロの名前空間も分離する。引数として値に解決済みの識別子を先頭位置へ挿入しても、その束縛を保持してマクロとして再解釈しない。テンプレートの静的なマクロ呼び出し先は、同名の値の束縛をα変換しても変更しない。定義検査用の穴には新しい不透明な値の識別子を与え、穴の名前が既存マクロと衝突してもその契約へ誤って解決しない。Leanのコピー仕様にもマクロ名前空間を渡し、`macro_head_retains_namespace` で値の一意化がマクロ名を変更しないことを示す。

生成した証明書の全定理についても、公開前に公理依存を検査する。Lean標準の `propext`、`Classical.choice`、`Quot.sound` 以外を許可せず、`sorryAx` や独自公理を含む証明書は拒否する。監査コマンドは検証用一時ファイルにだけ追加し、公開するファイルはハッシュを計算した元の内容に戻す。コードに埋め込む束縛ID・起源・生成カウンターは非負整数として検証する。


## 2026-11-18 作業報告と検証結果

今回の実装では、元のUTF-8ソースから読み取った構文、`defrec`正規化、元の規則を使った有限のマクロ展開、展開後の束縛IDまでを、同じデータを共有するLean証明書へまとめた。Cの展開結果を別の型の合う式へ置き換えるだけでは、ソースからの展開導出を構成できない。引数の呼び出し位置とテンプレートの定義位置を分け、同じ型の別の変数へのすり替え、初期化前の値への参照、起源や生成カウンターの改変も検査する。

停止性については、Leanの整礎再帰を利用する正の検査を追加した。規則を名前と引数個数で区別し、同じ名前・arityの全直接候補と穴頭位置の同arity候補をLeanで再計算して自然数の順位減少を確認する。証明できない場合はUnknownであり、非停止と断定しない。候補解析がUnknownでも、実際に完了した展開の有限導出を通常モードで証明できる。実際の展開、生成サイズ、深さ、型検査、証明書作業の上限は維持している。

検証中に見つかった、Unicode空白、予約語の束縛、一意化前の重複束縛、値とマクロの同名参照の問題も修正した。特に、呼び出し位置で値として検査した引数をマクロ名へ再解釈する問題と、値のα変換で静的なマクロ名まで変更する問題を分離して直した。`examples/macro_namespaces.nlisp` は3種類の衝突を含み、Cで42を返し、Leanで展開とスコープの対応を検査できる。

| 検証 | 結果 |
|---|---|
| Lean 4.8.0の全モデルのビルド | 成功 |
| 通常構成のCTest | 15/15成功 |
| ASan・LeakSanitizer・UBSan構成のCテスト | 11/11成功 |
| 同じサニタイザー構成のLean連携とビルドfixture | 4/4成功 |
| Pythonテスト | 組み込み5、構文19、Lean連携29、終了性7、読み取り7の計67メソッド |
| ライブラリ定理の公理監査 | 47件成功。追加の独自公理・sorryAxなし |
| 生成証明書の公理監査 | 公開前に全生成定理を検査。sorry・独自公理の混入を拒否 |
| 静的終了性証明書 | 展開予算0で生成し、同梱ソースからの再検証に成功 |
| 全26組み込み関数の証明書 | `build/BuiltinsCertificate.lean`をtypesモードで生成し、過程再実行・Lean検査・生成定理の公理監査に成功 |

通常構成の最終CTestは505.91秒だった。サニタイザー構成は、Cテスト11件と、残るLean関連4件に分けて実行し、それぞれ13.23秒、497.85秒で成功した。テストは元ソースを削除した後の単一ファイル再検証、ハッシュを付け直した改変、同型の誤束縛、無関係な型の合う出力、偽の終了順位、依存辺の省略、資源超過、Leanの強制終了時の旧ファイル保持を含む。

保証の限界も残る。展開構文から型付きコアへの変換について、相互再帰・単相化・カリー化等を含む一般的な意味保存は証明していない。C型タグは不透明な識別子として扱っており、その意味論とLeanの型の同値も未証明である。保守的な呼び出し候補関係からC展開器全体の終了性を導く一般的なシミュレーション、Float等の評価意味論、C実行器全体の正しさ、実行時関数の終了性も今回の完了範囲には含めない。暗号署名による発行者の認証も付けていない。

Gitの初期化・ステージ・コミット・pushなどのコマンドは実行していない。変更はローカルのソース、テスト、仕様・実装文書に残している。ビルド出力と証明書例は`.gitignore`の対象である。

## 2026-11-19 小数リテラルと浮動小数点環境

仕様の「10進有理数からbinary64へ一度だけroundTiesToEven」とC処理系の実装を合わせた。`float_atom` は `strtod` を呼ばず、仮数の数字列と10の指数からGMP整数の分子・分母を作る。二進指数に合わせて整数比をスケーリングし、商と余りを比較して最近接・偶数を決め、binary64の64ビット列を構成する。桁区切りはASCII数字で判定し、数値ロケールに依存しない。符号付きゼロ、サブノーマル、丸めによる最小正規数への繰り上がり、オーバーフローもこの経路で扱う。

`nlisp_process_file` はC API呼び出し元の浮動小数点環境を保存し、例外トラップを保留してから最近接・偶数モードで処理し、終了時に環境を復元する。コンパイラにも浮動小数点環境を尊重する設定を付けた。環境の保存または設定に失敗した場合は実行前にランタイムエラーを返す。

この作業ではCMakeビルドを確認した。CTestや追加テストは実行していない。LeanのFloat演算評価意味論、C浮動小数点命令とIEEE 754の一般的な対応定理、C実行器全体の正しさは依然として未証明である。

## 2026-11-19 局所展開証書と汎用検査器

`NLisp.ExpansionCertificate` に明示的な局所証書データ型とBoolean検査器を追加した。証書はソース・結果、マクロ規則の定義位置、コピーfuel、新規束縛カウンター範囲、リスト文脈、連続する中間結果を保持する。マクロの規則所属、穴の照合、衛生的コピー結果は元の規則集合と入力から検査する。`check_sound` は証書受理から有限の `CExpansion.Expands` 関係を導く。`checkFresh` はさらに全記録区間の非重複を要求し、`checkFresh_sound` と `checkFresh_intervals` が展開関係と区間条件をそれぞれ導く。`checkFresh_separates_interval_counters` は別々の区間内にあるカウンタ値が一致しないことを導く。`CMacroCopy.binder_success_counter` と `sequential_binders_have_distinct_tokens` は、成功した連続binder呼び出しがcounterを1ずつ進め異なるtoken identityを作ることを証明する。

`tools/verify_lean.py` はC展開履歴からこの証書データを構成し、生成証明書の `program_expands` はfreshness付き汎用 `checkFresh` の健全性定理から導く。証明項を全体に対して一度に `decide` するとLeanの再帰スタックに達したため、各局所検査と推移合成を個別補題で作る方式にした。`examples/macros.nlisp` の過程付き証明書がLean検査・公理監査に通った。

これでRESEARCH_FORMALIZATION.mdのPhase 1は完了した。連続binder呼び出しと異なる区間内カウンタ値の非衝突までは証明したが、copy群全体でこの性質を合成し、出力中の全生成識別子についてcounter区間所属を示す一般補題、入力識別子との非衝突、非捕捉・表層型保存を同時に導く主定理、型付き抽象展開との一般対応、局所変更時の増分検査とビットサイズ計算量は未完了である。CTestは実行していない。

2026-11-20追補: `CExpansion.disjoint_members_separated` は受理済み区間列の異なる要素が分離されることを一般化し、`disjoint_interval_counters_differ` と `disjoint_interval_generated_ids_differ` は各counterが対応区間内にある場合のcounter/token衝突を排除する。`ExpansionCertificate.checkFresh_generated_tokens_differ` はこの結論を証書検査へ接続する。また、`CMacroCopy.binder_success_counter` と `sequential_binders_have_distinct_tokens` は連続して成功する2つのbinder呼び出しが異なるtokenを作ることを証明する。`successful_binder_avoids_source_identity` は単一のbinder出力が予約済み剰余類にあるsource tokenと衝突しないことを示す。copy群全体で各binder生成値のcounter境界と逐次性を合成する証明は未完了である。Lean全体のビルドと `examples/macros.nlisp` の生成証明書・Lean検査は成功した。

`CMacroCopy.copyParameters_counter` は成功したパラメータコピーで、終了counterが開始counterとパラメータ数の和になることを証明する。counter増分の個数との一致は得られたが、生成token列をcounter順へ結び付ける性質や、残りのcopy関数への合成は未完了である。

`copyParameters_token_sequence` は、出力されたパラメータtokenが開始counterから順に生成される列と一致することを証明する。`copyParameters_tokens_unique` はその列の一意性を示し、`copyParameters_tokens_avoid_source` は剰余類1のsource tokenが出力列に含まれないことを導く。これは仮引数リスト操作に関する定理である。let bindingとmatch casesにも独立した条件付き合成定理を追加したが、全構文形状を含む`copy`全体の主定理は未完了。

同様に `copyPattern_token_sequence`、`copyPattern_tokens_unique`、`copyPattern_tokens_avoid_source` は、match patternでのbinder列のtoken順序、一意性、source-token剰余類との非衝突を証明する。さらに `copyCasesWithMacros_preserving_*` は、各case bodyがcounterを保持する条件の下で、case列全体のpattern binder token列を合成する。任意のbodyについてcounter保存を示すことと、結果を `copy` 全体へ接続することは未完了である。

`parameter_then_pattern_tokens_unique` は、パラメータコピーで進んだcounterからpatternコピーを続けた場合、両方のbinder tokenを合わせても重複しないことを証明する。共通counterを介した二つの局所copy操作の合成例である。case pattern列については、counter-preserving body条件下の合成定理を別途追加した。

`copy_atom_keeps_counter` は、成功したatomコピーがcounterを変更しないことを証明する。atom自体はbinderを導入しないための基本補題であり、リスト全体やbinderを含むcopyの単調性までは主張しない。

マクロ名集合を明示する `copyWithMacros_atom_keeps_counter` と `copyManyWithMacros_atomic_counter` も追加した。後者は任意のマクロ名集合でatomだけからなる子リストの走査がcounterを保持することを示す。`copyBindingsWithMacros` により、C展開経路が使うマクロ名集合付きのbindingコピーもモデル上で呼び出せる。既存の `copyBindings_atomic_counter` 自体は空のマクロ名集合に対する定理として維持し、任意マクロ集合のcounter-safe initializer族は別の定理群で扱う。C実装との対応は未証明である。

`copyBindingsWithMacros_atoms_counter` はマクロ名集合を任意にした場合にも、各initializerがatomであるbinding列のcounter消費量がbinding数と一致することを示す。`copyBindingsWithMacros_atoms_token_sequence` と `copyBindingsWithMacros_atoms_tokens_unique` は出力binder token列がcounterから順に生成され、一意であることを示す。`copyBindingsWithMacros_atoms_tokens_avoid_source` は予約済みsource-tokenクラスとの非衝突を、`copyBindingsWithMacros_atoms_tokens_within_interval` は出力tokenがfresh区間内counterから生成されることを示す。任意マクロ集合の形状限定initializerは `MacroCounterSafeInitializer` の節を参照。より深い構文木・束縛子を含むinitializerの個別証明は残る。

`checkFresh_separates_macro_aware_atom_binding_tokens` は、上のfresh区間所属を受理済み・非重複証書へ接続し、別々の区間からコピーしたatom-initializer binding列間のtoken非衝突を示す。この接続も一般のinitializerおよびC `copy_template`とのシミュレーションまでは含まない。

このatom制限を外へ一般化するため、`CounterPreservingInitializer` は特定のinitializerがマクロ集合付き `copy` でcounterを保持する性質を表し、`CounterPreservingBindings` はそれをbinding列へ持ち上げる。`copyBindingsWithMacros_preserving_counter` と `copyBindingsWithMacros_preserving_token_sequence` はこの前提からcounter増分とtoken列を導き、派生補題がtoken一意性・source-token分離・区間所属を示す。`checkFresh_separates_counter_preserving_binding_tokens` は別証書区間間の非衝突まで接続する。これはinitializerのcounter保存そのものやC関数との対応を証明する仕組みではなく、initializer別の証明が必要である。

`atom_initializer_counter_preserving` と `atom_binding_inputs_counter_preserving` により、atom initializerの既存ケースをこの一般インターフェースへ埋め込める。

マクロ名集合が任意でも、`copyWithMacros_single_atom_list_keeps_counter` と `copyWithMacros_two_atom_list_keeps_counter` はそれぞれatom一個・二個のlist initializerでcounterが保持されることを示し、`singleton_atom_list_counter_preserving` と `pair_atom_list_counter_preserving` がこれらを一般インターフェースへ接続する。

同様に `counterSafeInitializer_preserving` と `atomic_binding_inputs_counter_preserving` は、空のマクロ集合で既に証明したatom・短いatom-list initializerを一般インターフェースへ接続する。この接続で既存の `copyBindings_atomic_*` 定理の主張範囲が自動的に広がるわけではないが、counter-preserving性を入力仮定とする一般定理を直接適用できる。

`CounterPreservingTrees` と `copyManyWithMacros_preserving_counter` は、各子要素のcounter不変性から任意の子リスト走査のcounter不変性を合成する。走査部分はリスト長や木形状に依存せず再利用できるが、各子要素が前提を満たす証明は別途必要である。

任意のマクロ集合に対する `MacroCounterSafeInitializer` / `MacroCounterSafeBindingInputs` は、atom、atom一個・二個listに加えて、先頭が`match`でない任意長のatom-only listを表す。`atomList` constructorのcounter保存は `copyWithMacros_atomTrees_keeps_counter` で示す。短い各形状と任意長のatom-only形状のcounter保存証明を `CounterPreservingBindings` に変換でき、一般定理からbinder token列の一意性、source-token分離、fresh区間所属を導く。`checkFresh_separates_macro_counter_safe_binding_tokens` はその出力を別証書区間間の非衝突へ接続する。ネストした式、binderを含むinitializer、および先頭が`match`である長いatom-only listはこの構成的条件に含まない。

`CounterPreservingCases` は、match case列の各bodyがcounterを保持する前提を表す。`copyCasesWithMacros_preserving_counter` はpattern中のbinder数だけcounterが進み、それ以外のbody/tail走査はその前提の下でcounterを追加消費しないことを証明する。`copyCasesWithMacros_preserving_token_sequence` は各出力pattern binder tokenを連続counter列に同定し、派生補題が一意性・source-token分離・区間所属を導く。`checkFresh_separates_case_copy_tokens` は別々の証書区間間の非衝突を示す。これらはcase bodyのcounter保存を前提とし、C実装との対応は未証明。

`MacroCounterSafeCases` は各case bodyに `MacroCounterSafeInitializer` 条件を与える構成的な入力型であり、atom、短いlist形状、または先頭が`match`でない任意長atom-only listを扱う。`macroCounterSafeCases_preserving` により抽象case条件へ変換でき、`checkFresh_separates_macro_counter_safe_case_tokens` はこの条件付き入力に対する区間間非衝突を直接導く。

`counterTokens_within_interval` は生成token列の各要素から対応counterを復元し、開始値より大きく、開始値と操作内binder数の和以下であることを示す。これを `copyParameters_tokens_within_interval` と `copyPattern_tokens_within_interval` へ接続し、出力tokenをfresh区間内のcounterへ対応付けた。証書に記録された任意の `copy` 区間との対応には、構造全体のcounter合成がなお必要である。

`ExpansionCertificate.checkFresh_separates_parameter_copy_tokens` と `checkFresh_separates_pattern_copy_tokens` に加え、`checkFresh_separates_case_copy_tokens` と制限付き `checkFresh_separates_macro_counter_safe_case_tokens` は、局所copy出力の区間所属を証書全体の受理済みfresh区間へ接続する。記録区間が異なる場合、対象操作の出力tokenが一致しないことを導く。任意のC展開証書の全生成tokenを列挙し、すべてのcopy分岐を含める完全なfreshness定理は未完了である。

`CounterSafeInitializer` は空マクロ集合の下でatom、atom一個・二個のlist、または先頭atomが`match`でないatom三個・四個のlistを表し、`AtomicBindingInputs` はこの条件を満たすlet binding listを表す。この条件の下で `copyBindings_atomic_counter` は最終counterがbinding数だけ進むことを示し、`copyBindings_atomic_token_sequence`、`copyBindings_atomic_tokens_unique`、`copyBindings_atomic_tokens_avoid_source`、`copyBindings_atomic_tokens_within_interval` がbinder token列の順序、一意性、source-token非衝突、区間所属を導く。`checkFresh_separates_atomic_binding_tokens` は区間非重複へ接続する。initializerがさらに深い式や束縛子を含む一般のletについては、initializerコピーが消費するcounterとの合成が残る。

`AtomicTrees` と `copyMany_atomic_counter` は空マクロ集合で、atomだけからなる子リストを順にコピーしてもcounterが変わらないことを証明する。`copy_single_atom_list_keeps_counter`、`copy_two_atom_list_keeps_counter`、`copy_three_atom_list_keeps_counter`、`copy_four_atom_list_keeps_counter` は、記載した制約内の短いlist構文全体でもcounter保存を示す。任意長リストのマクロ集合付き結果は `MacroCounterSafeInitializer` の節を参照。

`call_extraction_complete` は、有限fuelの`calls`/`callsMany`が成功すれば、構文木中の任意の深さにある直接呼び出しと穴頭位置の候補呼び出しが抽出結果に含まれることを帰納法で示す。`graphRows_static_call_edge` はその抽出結果が行の辺として保存されることを導き、`GraphCall` と `graphRows_contains_static_calls` は全規則行を走査したグラフにも各行の辺が残ることを示す。`ProcessCertificate.source_static_calls_decrease` はこの結果を一般の受理済み停止性証書から取り出す定理であり、生成証明書の `every_static_rule_call_decreases` も同じ接続を確認する。root呼び出し補題`calls_direct_macro_complete`と行保存補題`graphRows_dependency_edge`は構成要素である。テンプレート構文の呼び出し候補抽出と辺生成は網羅するが、実際の置換・引数複製・各macroStepがこの関係上の辺に対応することや、C展開器全体の停止性は未証明である。

この追加後に `examples/math_macros.nlisp` の `--mode termination` 証明書を生成し、Lean検査した。これは既存のグラフ再計算・順位検査の確認であり、新しい局所補題を使った実展開シミュレーションではない。

2026-11-20追補: `MacroCounterSafeInitializer.atomList` と `copyWithMacros_atomTrees_keeps_counter` により、任意長で先頭atomが`match`でないatom-only list initializerのcounter保存を任意マクロ集合で証明し、binding列・case bodyのfreshness合成へ接続した。Lean 4.8.0の `lake build` 成功後、`examples/macros.nlisp` のcore証明書と `examples/dynamic_macro_head.nlisp` の停止性証明書を現行ソースから生成し、どちらも独立再検証に成功した。候補解析の作業予算診断に試行量・上限値を加え、小さな直接呼び出しで上限12の13操作目がUnknownになることを確認した。実CLIの上限0では34ノードの入力が証明書なしのUnknownになることも確認した。CMakeの `nlisp_core` と `nlisp` もビルド成功。対象外はネストしたinitializer、binderを含むinitializer、先頭`match`の任意長list、およびC `copy_template`との一般シミュレーションである。CTestはこの追補では実行していない。
