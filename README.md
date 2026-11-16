# nagato-Lisp

nagato-Lisp（NLisp）は、明示的な静的型付けと検証可能なLispを目標とする研究用言語である。

現在のリポジトリには次が含まれる。

- `SPECIFICATION.md`: NLisp 0.2規範仕様
- `LEAN_FORMAL_SPECIFICATION.md`: Lean形式仕様と検証範囲
- `NLisp/Core.lean`: Leanで検査済みのコア計算体系
- `src/nlisp.c`: C17製NLisp-Core参照処理系
- `examples/`: 適合プログラム例
- `tests/`: 拒否すべきプログラム例

## C参照処理系

```text
cmake -S . -B build -A x64
cmake --build build --config Release
ctest --test-dir build -C Release --output-on-failure
```

```text
build/Release/nlisp check examples/factorial.nlisp
build/Release/nlisp run examples/factorial.nlisp
```

詳細と現在の制限は`IMPLEMENTATION.md`を参照する。

rank-1多相関数、`type-app`、実引数型だけからの一方向型引数決定、および固定引数の型付き衛生テンプレートマクロを実装している。

```text
build/Release/nlisp run examples/polymorphism.nlisp
```

この例は`42`を返す。多相型の追加分はReleaseビルドと使用例の実行を確認済み。追加分の自動テストおよびLean証明は未実施。

```text
build/Release/nlisp run examples/macros.nlisp
build/Release/nlisp expand examples/macros.nlisp
```

マクロ使用例は`44`を返す。型契約は定義時・利用時・展開後に検査する。lambda、let、matchが導入する名前を一意化し、テンプレートの自由変数は定義位置で解決する。マクロのLean証明および証明書検証は未実装。

## 現在の検証状態

- MSVC C17、`/W4 /WX`でDebug／Releaseビルド成功
- 既存コアの統合テスト8件成功（多相型追加前の結果）
- Lean側はNLisp-CoreのProgress、型保存、非stuck性を検査済み

C実装とLean意味論の対応そのものは、今後証明または証明書検証の対象とする。
