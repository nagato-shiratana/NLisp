# nagato-Lisp Lean 形式仕様書

**文書番号:** NLISP-LEAN-SPEC-0.2  
**対応仕様:** NLISP-SPEC-0.2  
**検証器:** Lean 4.8.0  
**検証状態:** NLisp-Core Phase 1 カーネル検査済み  
**規範ソース:** `NLisp/Core.lean`

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
| `NLisp/Core.lean` | 型、項、置換、値、遷移、定理 |

検証コマンドは次である。

```text
lake build
```

成功条件は終了コード `0` であり、`NLisp.Core` と `NLisp` の両ターゲットがビルドされることである。

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
- Integer 加算と `<=`
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
(<= n m) → Bool(decide(n ≤ m))
```

Lean の `Int` を用いるため、本モデルの Integer は数学的な任意精度符号付き整数である。

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
| Progress | `progress` | 証明済み |
| Preservation | `Step` の型添字、`preservation` | 証明済み |
| 値の正規形性 | `valueCannotStep` | 証明済み |
| 非 stuck 性 | `notStuck` | 証明済み |

## 9. 現時点で証明範囲外の事項

次は NLisp 0.2 自然言語仕様には存在するが、本版の Lean モデルにはまだ含めない。

- UTF-8 字句解析と S 式パーサの正しさ
- `Float`、`String`、`Character`
- 複数引数関数の直接表現
- `let` と `begin` の直接表現
- predicative rank-1 多相
- 型適用と型引数の一方向決定アルゴリズム
- 組み込み関数表全体
- 型付き衛生マクロと展開関係
- マクロ展開の停止性、決定性、型保存、衛生性
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
4. 展開の停止性と決定性
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

検証環境で次の結果を得た。

```text
Lean (version 4.8.0, x86_64-w64-windows-gnu, Release)
Built NLisp.Core
Built NLisp
Build completed successfully.
```

この結果はソースの意味が正しいこと全般を保証するものではなく、記述された定義と定理が Lean の型理論上整合し、証明項がカーネルに受理されたことを保証する。
