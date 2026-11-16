# NLisp-Core C参照処理系

このディレクトリには、`SPECIFICATION.md` と `NLisp/Core.lean` の共通部分を実行する最小のC17処理系を置く。

## 対応機能

- S式と行コメント
- `Boolean`、`Integer`、`Unit`
- 関数、クロージャ、一般再帰、相互再帰
- `if`、`let`、`begin`、`lambda`
- `List`、`Option`、網羅的`match`
- `+`、`-`、`*`、`<=`、`integer=`
- 静的型検査
- 左から右のcall-by-value評価
- `check`、`run`、`expand`コマンド
- 単相の型契約を持つ、非再帰的な型付き衛生テンプレートマクロ

## 現在の意図的な制限

- `Integer`は検査付き`int64_t`。オーバーフローは実行時エラーとなる。
- `Float`、`String`、`Character`は未実装。
- rank-1多相関数、明示的型適用、実引数型からの一方向型引数決定に対応。
- マクロは固定引数・1規則・単相契約に限定する。マクロ定義はソース順に可視となり、後方参照と再帰を許さない。
- `defrec`構文は未実装。トップレベル関数は相互参照可能であり、最小処理系ではこれにより相互再帰を表す。
- メモリは処理終了時に一括解放するarena方式。
- ソースファイルは1個、エントリーポイントは`main : () -> Integer`。

未実装構文は受理せず、診断を返す。

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

使用例は`examples/polymorphism.nlisp`。この追加分の自動テストとLean証明は未実施であり、既存コアの機械検証とは区別する。

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

パターン変数は式の穴だけを表す。束縛名の穴、型の穴、反復パターン、手続き的マクロ、意図的捕捉は対応しない。マクロ依存先は先に宣言されたマクロに限る。有限の入力でもテンプレートの複製により展開サイズは増大し得る。

```text
build/Release/nlisp run examples/macros.nlisp
build/Release/nlisp expand examples/macros.nlisp
```

使用例の結果は44。定義位置のoffsetと加算、呼び出し位置のtemp、入れ子のtwiceを組み合わせる。expandは内部束縛名を含む診断表示であり、自由変数の定義位置情報を直列化しないため再実行用ソースや証明書としては使用できない。

このC実装に対するLeanの型保存・衛生性証明、独立した展開証明書検証器は未実装。既存のLeanコア定理の保証範囲は拡張されていない。

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
