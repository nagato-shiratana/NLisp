# nagato-Lisp Lean 形式仕様書

**文書番号:** NLISP-LEAN-SPEC-0.2  
**対応仕様:** NLISP-SPEC-0.2  
**検証器:** Lean 4.8.0  
**検証状態:** 型安全性、型付きテンプレート、スコープモデル、および入力ごとの読み取り・正規化・有限展開・束縛IDをカーネル検査
**規範ソース:** 第2節に示す `NLisp/*.lean` の各定義

---

## 1. 文書の目的

本書は `SPECIFICATION.md` に定める NLisp 0.2 のうち、実行時コア言語を Lean で定義し、その型安全性を機械検証した形式仕様である。

自然言語仕様と Lean 定義が矛盾する場合、ここで「検証済みコア」と明示した範囲については `NLisp/Core.lean` の型および定理を形式上の基準とする。ただし、ソース表記、字句解析、診断文など Lean モデル外の事項には `SPECIFICATION.md` を適用する。

本書における「証明済み」は、Lean の `axiom`、`sorry`、`admit` を使用せず、指定ツールチェーンのカーネルが生成された証明項を受理したことを意味する。

## 2. 検証単位

検証プロジェクトは次のファイルから成る。

| ファイル | 役割 |
|---|---|
| `lean-toolchain` | Lean 4.8.0 の固定 |
| `lakefile.toml` | Lake ビルド定義 |
| `NLisp.lean` | ライブラリの入口 |
| `NLisp/Lexical.lean` | Unicode空白、リテラル、予約語、束縛名の分類 |
| `NLisp/Core.lean` | 型、項、置換、型付きマクロ展開、値、遷移、定理 |
| `NLisp/TypedExpansion.lean` | 全実行時型、全26プリミティブ、外在的型付け導出 |
| `NLisp/ScopedSyntax.lean` | 束縛ID付き環境、所属スコープ、起源を保つ埋め込みと展開 |
| `NLisp/CNameResolution.lean` | 観測環境の先頭優先探索と型付き変数への対応 |
| `NLisp/CMacroCopy.lean` | 起源・穴・生成束縛を含む衛生的置換の関数仕様 |
| `NLisp/CExpansion.lean` | 元の規則による有限展開導出と生成IDの分離 |
| `NLisp/CBindingWalk.lean` | 構文からの環境導出と実効位置・呼び出し位置での束縛ID検査 |
| `NLisp/SourceReader.lean` | ソース文字列の独立した字句解析・S式読み取り・defrec正規化 |
| `NLisp/MacroTermination.lean` | 静的呼び出し関係と順位に基づく整礎性 |
| `NLisp/ProcessCertificate.lean` | ソースから有限展開・スコープまでを結ぶ検査済み証明書データ |

検証コマンドは次である。

```text
lake build
```

成功条件は終了コード `0` であり、上記のモジュールと `NLisp` がビルドされることである。

## 3. 検証済み範囲

### 3.1 型

Lean の `Ty` は次の NLisp 型を表す。

```text
Boolean
Integer
Unit
(Function (A) B)
(List A)
(Option A)
```

本形式化では、関数型は単一引数である。自然言語仕様の複数引数関数は、右結合する単一引数関数または入れ子のラムダ式へ脱糖する。

### 3.2 項

`Expr Γ T` は、型環境 `Γ` の下で型 `T` を持つ式だけを表す。次を構成できる。

- 変数
- Boolean、Integer、Unit リテラル
- ラムダ式と関数適用
- `if`
- Integer 加算・減算・乗算・等値比較と `<=`
- `Nil`、`Cons`
- `List` の網羅的照合
- `None`、`Some`
- `Option` の網羅的照合
- 一般再帰を表す `fix`

型が式の添字に含まれるため、次のような式は Lean 上で構成できない。

- Integer を条件にした `if`
- Integer と Boolean の加算
- 引数型が一致しない関数適用
- 異なる型を返す分岐
- 要素型が一致しない `Cons`
- 結果型が一致しないパターン照合節

### 3.3 変数とスコープ

変数は文字列ではなく、型付き de Bruijn index `Var Γ T` で表す。

- `zero` は環境先頭の変数を参照する。
- `succ` は一つ外側の変数を参照する。
- 変数の型は環境の対応位置の型と必ず一致する。

この表現では未束縛変数を構成できず、α 同値な式は同じ内部表現になる。したがって、実行時コアでは名前捕捉が発生しない。

### 3.4 名前変更と置換

次を全型に対して定義する。

```text
Ren Γ Δ = Γ の型付き変数を Δ の同型変数へ写す関数
Sub Γ Δ = Γ の型付き変数を Δ の同型式へ写す関数
```

`Expr.rename` は束縛子を越える場合に `liftRen` を使用する。`Expr.subst` は `liftSub` を使用する。

関数の β 簡約、`Option` の `Some` 節、再帰展開には単一置換 `instantiate` を用いる。`List` の `Cons` 節には head と tail を同時に型付き置換する `instantiateCons` を用いる。

置換結果の型は Lean の関数シグネチャによって保存される。誤った型の式を代入する定義はカーネルに拒否される。

### 3.5 型付きテンプレートマクロ展開

コア形式化は `TypedMacro holes output` で入力穴の型列、出力型、テンプレート式を表す。各穴は型付き de Bruijn 変数であり、呼び出し側は型を一致させた `Sub holes Γ` を渡す。`TypedMacro.expand` は `Expr.subst` により式を代入し、束縛子の下では `liftSub` が置換を持ち上げる。

`TypedMacro.expand_preserves_type` は、展開後も出力型が維持されることを示す。誤った型の穴や引数は `Sub` の型からLean上で構成できない。これは intrinsically typed なコア表現上の保証であり、表層 `syntax-rules/typed` のパーサーや C 実装との対応を証明するものではない。`twiceTemplate` の例では、展開結果が同じ引数を二度加える式になることを `expandTwice_eq` で確認する。

捕獲回避は文字列名の freshening ではなく、de Bruijn index と `liftSub` による置換で扱う。`lambdaHoleTemplate` はラムダが導入する束縛変数と、外側のマクロ穴を同時に参照し、`expandLambdaHole_closed` は穴に `41` を渡した展開がラムダ引数を捕まえず、`.lam (.add (.int 41) (.var .zero))` となることを確認する。これはコア表現内の捕獲回避の例であり、C処理系の字句スコープ・ソース位置を含む衛生性の証明ではない。

`liftSub_keeps_bound` は導入した束縛変数を維持し、`liftSub_shifts_hole` は任意の外側変数に挿入する式を一段シフトする。`subst_under_lambda` はこれらをラムダ本体の置換に使うことを示す。`expandLambdaHole_hygienic` は任意の呼び出し側の式について展開がシフトを含むことを示し、`expandLambdaHole_open` は呼び出し側の変数が展開先のラムダ引数とは別の index に残る具体例である。

これらの定理を含む `NLisp.Core` と `NLisp` は Lean 4.8.0 の `lake build` でカーネル検査する。型保存の存在定理は型添字に組み込んだ保証を公開するものであり、未型付けの表層入力を検査するアルゴリズムの正しさを述べるものではない。

2026-11-17の検証では `lake build` が成功し、`TypedMacro.expand_preserves_type`、`liftSub_keeps_bound`、`liftSub_shifts_hole`、`subst_under_lambda`、`expandLambdaHole_hygienic`、`expandLambdaHole_open`、`expandTwice_eq` に対する `#print axioms` はすべて追加公理への依存なしと報告した。再確認する場合は `import NLisp` と各定理の `#print axioms` を含むLeanファイルを `lake env lean <file.lean>` で検査する。

再現可能な公理監査は `tests/LeanAudit.lean` と `tests/lean_bridge.py` に含める。`progress` と `notStuck` は Lean標準公理 `propext`、`Classical.choice`、`Quot.sound` に依存する。従来の型付きテンプレート展開・捕獲回避の監査対象定理は公理依存なしである。追加した対応検査・終了性の定理には標準公理を使うものもある。テストは標準公理以外の依存と `sorryAx` を許可しない。

### 3.6 全実行時型の型付け証明書

`NLisp.TypedExpansion` は実行意味論を持つ `NLisp.Core` と別の名前空間で、全実行時型と26組み込み関数の型を定義する。`Expr Γ T` は型付き項、`Term` は型添字を持たない項、`HasType Γ term T` は外在的な型付け関係である。`Expr.erase` は型添字を消し、変数index・リテラル値・プリミティブ識別子・式構造を保持する。`Expr.hasType` は任意の型付き項の消去結果に型付け導出が存在することを構造帰納法で示す。この定理も公理依存なしで検査する。

Floatはbinary64の64bitパターン、StringとCharacterはLeanのUnicode文字を用いて表す。全プリミティブについて引数型・結果型を定義するが、Float・String・Characterの演算の評価規則は与えない。この証明書は展開後の型付けを保証し、これらの演算の非stuck性・値の正しさ・IEEE 754への適合性は主張しない。

### 3.7 定義位置と呼び出し位置を区別するスコープ付き構文

`NLisp.ScopedSyntax` は3.6節の全実行時型の型付けモデルに対する形式化である。`TypedExpansion.Expr.rename` と `TypedExpansion.Expr.subst` を全構成子について定義し、Floatのビット列・文字列・文字・プリミティブも保持する。`Binding` は印字名ではなく `identity : Nat` と `type : Ty` を持つ。`Scope` はその列、`Valid` は束縛IDが重複しないことを検査する有限のBoolean判定に基づく述語である。`Syntax Γ T` は所属スコープの妥当性と `Expr (types Γ) T` を持つ。

`Embedding Γ Ω` は型付き変数の写像と、写像前後で束縛IDが等しいという証明を持つ。型だけを保存する任意の `Ren` と異なり、同じ型の別の束縛へ写すことは許さない。`distinct_origins_remain_distinct` は、定義位置と呼び出し位置でIDの異なる変数が、共通の展開先で同じ変数へ合流しないことを示す。

`Macro Γd H R` のテンプレートは `Expr (H ++ types Γd) R`、`Arguments Γc H` は呼び出し位置の式による穴の代入である。`Macro.expand` は別々の埋め込み `Embedding Γd Ω` と `Embedding Γc Ω` を受け取り、引数を呼び出し位置から移し、捕捉した自由変数を定義位置から移して `Syntax Ω R` を返す。`appendSub_hole` / `appendSub_definition` が代入の二つの領域を分離し、`expand_hole` / `expand_capture` がそれぞれ正しい埋め込みを使うことを示す。型保存はこの関数の型添字で保証する。

`Embedding.weaken` は新しい束縛を加えた環境がValidであるという証明を要求し、既存の変数を一段持ち上げる。具体例では同じInteger型のID 10と20を区別し、ラムダを導入した場合もどちらも捕捉しないことと、新しいID 30の環境を追加しても両方の参照を保持することを検査する。重複IDの環境はValidにならず、型だけ合う誤った埋め込みを作るLeanコードは拒否する。

このモデルに追加した監査対象14定理は公理依存なしである。変数の起源のほか、String・Floatビット列・プリミティブが環境移送で保持されることも確認する。Cの文字列名・Macro.originによる有限の実際の展開は、第3.8節の独立検査によって束縛IDモデルへ接続する。Cプログラム全体の機械意味論との一般的なシミュレーションや、コア変換の意味保存とは区別する。このスコープ付きモデルは型付けの形式化であり、Float等の評価意味論やC実行器の正しさを追加で証明するものではない。

### 3.8 ソース・展開・名前解決の入力ごとの対応検査

`SourceReader.readWithFuel` はUnicode White_Spaceの空白・コメント、Unicodeの識別子、文字列と文字リテラルを読み取り、トークン位置から元の束縛IDを構成する。`SourceReader.normalize` はトップレベルの `defrec` を `defun` 列へ変換する。単一証明書のLean本文は、元のUTF-8バイト列に一致する文字列、読み取り結果、正規化結果を定数として持ち、それぞれの計算結果がCの出力と一致することを閉じた計算で検査する。字句・読み取り・正規化のC実装の一般定理ではなく、当該入力の独立した結果照合である。

`CNameResolution.findName_sound` は先頭優先の名前解決を関係 `Resolves` に接続し、`checked_lookup_corresponds` と `observations_correspond` が観測した選択を型付き変数と同じ束縛IDへ接続する。型タグはCの型オブジェクトの識別値であり、型意味論の証明済み符号化ではない。対応はタグの任意の `Ty` 解釈について成り立つ。

`CMacroCopy.copy` はCの衛生的置換に対する関数仕様である。引数の構文・起源はそのまま挿入し、テンプレートの自由識別子には定義位置を付け、束縛子とその参照には同じ新しいIDを使う。lambda、並列let、matchをそれぞれのスコープ規則で扱う。証明書は各置換の入力・出力・生成カウンターを照合し、新規カウンター区間の重複も拒否する。

`CExpansion.Expands` は、元の規則に属すること、呼び出し名・引数個数の一致、衛生的置換の一致を前提とする展開ステップと、その反射・文脈・推移閉包である。`program_expands` は正規化済み宣言から今回の最終宣言までの有限導出を示す。変換器が無関係な型の合う式を出力した場合は、この導出を作れない。

`CBindingWalk` は最終構文から関数・トップレベル値・局所束縛の環境を導出する。各変数について、実効位置で選んだ束縛IDとCの参照IDの一致、両環境のIDの妥当性、選んだ束縛が呼び出し時点の環境にも存在することを確認する。同名の局所変数による遮蔽があっても、定義位置の参照は同じIDを保つ。検査用構文の消去結果と展開導出の出力の一致もLeanで検査する。

`ProcessCertificate.CheckedExpansion` はUTF-8バイト列の一致、読み取り、正規化、有限展開、スコープの各証明を、同じ構文データを共有する一つの構造体にまとめる。生成する `VerifiedNLispSource.source_expands_with_scopes` はこれらを一つの命題として示す。ただし、相互再帰・多相化・カリー化などを含むコア変換の意味保存や、C型表現と `Ty` の意味的同値までは含まない。

### 3.9 静的なマクロ呼び出し関係の整礎性

`--mode termination` は展開を行わず、名前と引数個数で区別した規則間の静的な辺をLeanで再計算する。Pythonが合成した自然数の順位について、各辺で厳密に減少することを検査する。`MacroTermination.accessible` は `termination_by rank ranks node` によりアクセシビリティを構成し、`ranked_graph_wellFounded` が整礎性を、`path_length_bounded` が呼び出し鎖の長さの上限を示す。

同じマクロ名でも、例えば `answer/1 → answer/0` のような規則は証明できる。循環が残る場合、または構文の穴が呼び出し先となる場合はUnknownとする。これは非停止の証明ではない。通常のモードでは、静的解析がUnknownでも実際の有限展開が完成すれば、その入力の有限導出を証明できる。

`ProcessCertificate.CheckedStaticTermination` はソースの読み取り・正規化と、抽出した関係の整礎性を同じデータへ結び付ける。このモードには式の型付けや実行の証明を含めない。また、抽出した関係が整礎であることから、C展開器の全処理が終了することを導く一般的なシミュレーション定理は未証明である。動的な呼び出し先、一般の構造的減少、利用者が指定する任意の整礎関係の自動検査も今後の対象とする。実行時関数の停止性とは区別し、証明の有無にかかわらず処理予算を維持する。

## 4. 値

`Value e` は閉じた式 `e : Expr [] T` が値であることを表す。

値は次に限る。

- Boolean、Integer、Unit リテラル
- ラムダ式
- `Nil`
- head と tail がともに値である `Cons`
- `None`
- 内容が値である `Some`

`fix` は値ではなく、必ず展開可能である。

## 5. 小ステップ評価

`Step e e'` は閉じた式の 1 ステップ評価を表す。関係の始点と終点は同じ型添字を持つ。

### 5.1 評価順序

評価順序は call-by-value、左から右である。

- 関数適用では関数位置、引数の順に評価する。
- 加算と比較では左辺、右辺の順に評価する。
- `Cons` では head、tail の順に評価する。
- `if` では条件だけを先に評価し、選ばれた分岐だけを残す。
- `match` では被検査式だけを先に評価し、対応する節だけを残す。
- `Some` の内容は値になるまで評価する。

### 5.2 β 簡約

```text
v が値
──────────────────────────────
((lambda body) v) → body[v/0]
```

### 5.3 条件分岐

```text
(if true  yes no) → yes
(if false yes no) → no
```

### 5.4 Integer 演算

```text
(+ n m)  → Int(n + m)
(- n m)  → Int(n - m)
(* n m)  → Int(n * m)
(integer= n m) → Bool(decide(n = m))
(<= n m) → Bool(decide(n ≤ m))
```

Lean の `Int` を用いるため、本モデルの Integer は数学的な任意精度符号付き整数である。

### 5.4.1 C展開結果との橋渡し

`export-core` は `nlisp-scoped-expansion-v2` 形式で、マクロを展開したS式とアトムの定義位置を出力する。`tools/verify_lean.py` はこの情報を使い、対応範囲について `expandedProgram : Expr [] Ty.integer` と `expandedProgram_notStuck` を生成する。生成項は `lake env lean <certificate.lean>` で型検査する。マクロ由来の自由識別子は呼び出し位置の局所束縛から切り離して解決し、定義位置以降の値を参照する入力を拒否する。

`--mode types` では3.6節の項と `expandedProgram_wellTyped : HasType [] expandedProgram.erase Ty.integer` を生成する。`--mode auto` はコア対象式には非stuck性を含む証明書を使い、それ以外では全実行時型の型付け証明書へ切り替える。CLIは使用したモードを明示する。

CLIが保存する単一の証明書には、元ソース、読み取り・正規化・マクロ展開・変換の記録、使用予算、SHA-256、選択したモード、Lean本文を同梱する。展開の前後でソースが変化した場合は生成を拒否する。ハッシュは再現性と追跡のための情報であり、ソースと生成項の意味的同値の証明ではない。

`defrec` は宣言の索引付けより前に個別の `defun` へ正規化するため、展開JSONの宣言順とマクロ定義位置の索引は一致する。複数規則のマクロと再帰を含む後方参照も、規則ごとの定義位置を保持して同じ形式へ展開する。これらの成功例と多相 `defrec` を両証明書モードでテストする。正規化および予算付き展開アルゴリズム自体の一般証明は含まない。

対応範囲はREADMEに列挙する。未対応の演算や型はエラーにし、`begin` の途中の式と未使用のトップレベル初期化式を含めて省略しない。再帰は `fix`、複数引数はカリー化、0引数関数はUnitを取る関数、letとbeginは厳密な関数適用で表す。相互再帰は外側の再帰関数を参照する入れ子の `fix` で表し、rank-1多相関数は呼び出し位置で単相化する。無限に異なる単相インスタンスを必要とする入力は制限に達した時点で拒否する。これらの変換アルゴリズム自体の一般的な意味保存は証明していない。今回の証明書は生成項の型安全性を確認する。Cの型検査結果やJSONを正しいと仮定してLeanカーネルを通さず受理することはないが、C展開結果と生成項の意味保存の一般証明はまだない。

### 5.5 List 照合

```text
(match Nil nilCase consCase) → nilCase

(match (Cons head tail) nilCase consCase)
  → consCase[head/0, tail/1]
```

`Cons` の簡約は head と tail がともに値の場合にだけ行う。

### 5.6 Option 照合

```text
(match None noneCase someCase) → noneCase
(match (Some value) noneCase someCase) → someCase[value/0]
```

### 5.7 一般再帰

```text
(fix body) → body[(fix body)/0]
```

この規則により停止しない式を表現できる。型安全性は停止性を主張しない。

## 6. 機械検証された性質

### 6.1 Progress

Lean 定理 `progress` は次を証明する。

```text
任意の閉じた型付き式 e について、
e は値であるか、e → e' となる e' が存在する。
```

形式的には次である。

```lean
(term : Expr [] t) → Value term ∨ ∃ next, Step term next
```

これにより、閉じた型付き式は未束縛変数、非関数適用、非 Boolean 条件、非網羅照合等による stuck state にならない。

### 6.2 Preservation

`Step` の型は、始点と終点に同一の型添字 `t` を要求する。

```lean
Step : Expr [] t → Expr [] t → Prop
```

したがって、型を変える評価規則は定義時に Lean カーネルが拒否する。定理 `preservation` は、遷移先が同じ `Expr [] t` に属することを証明項として公開する。

本形式化では Preservation を後から補題として回復するのではなく、操作的意味論の型へ直接符号化している。この方式を「構成による型保存」と呼ぶ。

### 6.3 値は正規形である

Lean 定理 `valueCannotStep` は次を証明する。

```text
Value e ならば、e → e' となる e' は存在しない。
```

したがって `progress` の「値」と「遷移可能」の二つの場合は重ならない。

### 6.4 非 stuck 性

定理 `notStuck` は Progress を利用者向けの名前で再公開する。

```lean
Value term ∨ ∃ next : Expr [] t, Step term next
```

## 7. 証明の信頼境界

本検証が信頼するものは次である。

1. Lean 4.8.0 のパーサ、エラボレータ、カーネル
2. Lean 標準ライブラリの `Bool`、`Int`、`List`、命題論理
3. ホストOS、ファイルシステム、実行バイナリが改変されていないこと

本プロジェクト自身は外部 Lean パッケージや Mathlib に依存しない。

`unsafe` 定義、`partial` 定義、追加公理を意味論および定理に使用してはならない。CI は次の語を検査対象ソースで拒否すべきである。

```text
sorry
admit
axiom
unsafe
partial
```

コメント内の説明語を除外するため、実際のCIでは Lean 構文としての出現を検査する。

## 8. 自然言語仕様との対応

| NLisp 0.2 項目 | Lean 上の定義 | 状態 |
|---|---|---|
| Boolean | `Ty.boolean`, `Expr.bool` | 証明対象 |
| Integer | `Ty.integer`, `Expr.int` | 証明対象 |
| Unit | `Ty.unit`, `Expr.unit` | 証明対象 |
| 関数型 | `Ty.fn`, `Expr.lam`, `Expr.app` | 証明対象 |
| 条件分岐 | `Expr.ite`, `Step.if*` | 証明対象 |
| 左から右評価 | `Step` の合同規則 | 証明対象 |
| List | `Ty.list`, `nil`, `cons`, `matchList` | 証明対象 |
| Option | `Ty.option`, `none`, `some`, `matchOption` | 証明対象 |
| 一般再帰 | `Expr.fix`, `Step.unfoldFix` | 証明対象 |
| 字句スコープ | `Var` と de Bruijn index | 証明対象 |
| 型付き置換 | `rename`, `subst`, `instantiate` | 証明対象 |
| 型付きコアマクロ展開 | `TypedMacro.expand`, `TypedMacro.expand_preserves_type` | 証明済み |
| 束縛子下の穴の捕獲回避 | `liftSub_keeps_bound`, `liftSub_shifts_hole`, `subst_under_lambda`, `expandLambdaHole_hygienic` | 証明済み |
| 開いた式と閉じた式の展開例 | `expandLambdaHole_open`, `expandLambdaHole_closed`, `expandTwice_eq` | 証明済み |
| Progress | `progress` | 証明済み |
| Preservation | `Step` の型添字、`preservation` | 証明済み |
| 値の正規形性 | `valueCannotStep` | 証明済み |
| 非 stuck 性 | `notStuck` | 証明済み |

## 9. 現時点で証明範囲外の事項

次は NLisp 0.2 自然言語仕様に存在するが、まだ一般的な正しさや評価意味論を証明していない。3.6節の型付け証明書に含める部分についても、ここに列挙する広い意味での検証を完了したとは扱わない。

- UTF-8 字句解析とS式パーサについてのC実装の一般的な正しさ（個別入力の独立した読み取り照合は第3.8節）
- `Float`、`String`、`Character` の演算の評価意味論
- 複数引数関数の直接表現
- `let` と `begin` の直接表現
- C処理系全体の機械意味論とのシミュレーション、全入力に対する資源管理・展開戦略の正しさ（有限の衛生的展開導出と名前解決は第3.8節）
- predicative rank-1 多相
- 型適用と型引数の一方向決定アルゴリズム
- 組み込み関数表全体の評価意味論（型付けは3.6節で扱う）
- 表層の型付き衛生マクロと展開関係（上記コアテンプレートモデルを除く）
- マクロ環境全体における予算付き展開の結果分類、完了時の決定性、型保存、衛生性
- ソース位置と診断
- `main` およびコンパイル単位
- コンパイラ中間表現とコード生成の意味保存

これらについて「Leanで証明済み」と表記してはならない。

## 10. 次段階の証明義務

### Phase L2: 外在的型付け

型を添字に持たない `RawExpr` と判断 `HasType Γ e T` を定義し、次を証明する。

1. 型検査アルゴリズムの健全性
2. 型検査アルゴリズムの完全性
3. 型の一意性
4. `RawExpr` の Progress と Preservation

### Phase L3: 多相性

1. 型変数環境と monotype の整形式性
2. 明示的型適用
3. 一方向照合アルゴリズム
4. 照合の健全性、完全性、一意性、停止性
5. 戻り値期待型を使用しないことの形式化

### Phase L4: マクロ

1. スコープ集合付き構文オブジェクト
2. 型付きマクロ入力・出力契約
3. 展開関係
4. 予算付き展開処理の終了と結果分類、展開完了時の決定性
5. α 変換に対する展開の同変性
6. 展開の型保存
7. 展開後再型検査の健全性

### Phase L5: 実装対応

1. S 式パーサから `RawExpr` への変換
2. 型検査済み `RawExpr` から intrinsic `Expr` への elaboration
3. elaboration 前後の意味保存
4. インタプリタまたはコンパイラの意味保存

## 11. 適合性の表記

処理系または論文は、検証状態を次のいずれかで表示する。

- **NLisp-Core Lean-checked:** 本書3章のコア構文と6章の定理に適合する。
- **NLisp 0.2 implemented:** 自然言語仕様を実装するが、証明範囲外を含む。
- **NLisp 0.2 fully verified:** 9章の全項目を含む証明が完成するまで使用禁止。

現在のプロジェクトが名乗れるのは **NLisp-Core Lean-checked** である。

## 付録 A. 検証結果

初期のWindows検証環境で次の結果を得た。

```text
Lean (version 4.8.0, x86_64-w64-windows-gnu, Release)
Built NLisp.Core
Built NLisp
Build completed successfully.
```

この結果はソースの意味が正しいこと全般を保証するものではなく、記述された定義と定理が Lean の型理論上整合し、証明項がカーネルに受理されたことを保証する。

2026-11-17のLinux環境では、次を確認した。

- Lean 4.8.0で `NLisp.Core`、`NLisp.TypedExpansion`、`NLisp` のビルド成功。
- Release構成のCTest 11件成功。
- AddressSanitizer・LeakSanitizer・UndefinedBehaviorSanitizerを有効にした構成でもCTest 11件成功。
- 全26組み込み関数を含む `examples/builtins.nlisp` は `42` を返し、全型のLean証明書の検査に成功。
- 全10コード例について全型の証明書を検査し、コアに属する既存9例については非stuck性を含む証明書も検査。
- 全組み込み名と仕様書の照合、整数丸め・符号付き除算・Unicode境界・不正入力拒否を自動テスト。
- 公理監査12定理と、意図的に型を壊した証明書の拒否を自動テスト。

実行手順と証明の保証範囲はREADMEおよび本書3.5・3.6・5.4.1節に記載する。Cの実行結果の正しさをLeanで一般証明したとは扱わない。


## 予算付き展開の検証範囲

再帰マクロの展開完了は一般には仮定しない。処理予算超過はUnknownとして扱い、C処理系は展開結果を出力せず、連携ツールも新しい証明書を発行しない。展開が完了して型検査を通った項について、既存の型付け・非stuck性の証明を適用する。Unknownから不正や非停止を導く定理は提供しない。資源カウンターとUnknown分類のC実装そのものの正しさは、今後の形式化対象である。


## 過程付き単一証明書の信頼境界

`nlisp-process-certificate-v1` は過程記録をLeanコメント内のBase64 JSONとして保持する。Leanカーネルが直接検査するのはLean本文の定義と定理である。専用の `--verify-certificate` が同梱ソースからC処理系とPython変換器を再実行し、読み取り結果・正規化・展開履歴・変換記録・本文を照合する。元ソースの別ファイルは不要である。

同じ実装の再実行だけでは同じ誤りの再現を排除できないため、第3.8節の読み取り・正規化・名前解決・有限展開の独立したLean検査も本文に含める。コメント内の元ソース・過程記録とLean本文の定数が対応することは、専用検証器が本文を再生成して照合する。`lake env lean` だけではコメントを解釈しない。コア変換の一般的な意味保存はなお未証明であり、保証範囲にはその旨と暗号署名がないことを記録する。


値の束縛とマクロの名前空間は区別する。`CMacroCopy.copyWithMacros` は有効なマクロ名の集合を引数とし、静的なマクロ呼び出しの先頭を値のα変換から保護する。`macro_head_retains_namespace` は同名の値の置換があっても先頭のマクロ名を保つことを示す。C処理系では、型検査で値に解決した引数の名前空間を挿入後も保持し、定義検査用の穴は新しい不透明な値の名前へ写す。これらを組み合わせた実例の展開・スコープ検査を行う。


## 2026-11-18の追加検証

全モデルのビルド、ライブラリ定理47件の公理監査、通常CTest15件、ASan・LeakSanitizer・UBSan構成のCTest15件の対象に成功した。サニタイザー構成はC側11件とLean関連4件に分けて実行した。Pythonのテストは合計67メソッドである。入力ごとの読み取り・正規化・展開導出・スコープの拒否テスト、名前空間の同名衝突、Unicode空白、静的な整礎性証明、生成証明書への独自公理・sorryの混入拒否を含む。詳細と再現手順は `IMPLEMENTATION.md` を参照する。
