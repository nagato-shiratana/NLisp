# nagato-Lisp

nagato-Lisp（NLisp）は、明示的な静的型付けと検証可能なLispを目標とする研究用言語である。

現在のリポジトリには次が含まれる。

- `SPECIFICATION.md`: NLisp 0.2規範仕様
- `LEAN_FORMAL_SPECIFICATION.md`: Lean形式仕様と検証範囲
- `NLisp/Core.lean`: Leanで検査済みのコア計算体系
- `NLisp/TypedExpansion.lean`: 全実行時型・組み込み関数の型付け証明書
- `NLisp/ScopedSyntax.lean`: 束縛IDと所属環境を明示した構文・マクロ展開モデル
- `NLisp/CNameResolution.lean`、`NLisp/CMacroCopy.lean`、`NLisp/CExpansion.lean`、`NLisp/CBindingWalk.lean`: 有限のC展開結果に対する名前解決・衛生的置換・展開導出・スコープの独立検査
- `NLisp/MacroTermination.lean`: 規則の順位による静的呼び出し関係の整礎性
- `NLisp/SourceReader.lean`、`NLisp/ProcessCertificate.lean`: 元のUTF-8ソース、読み取り、正規化、展開、スコープを結ぶ証明書
- `src/nlisp.c`: C17製NLisp-Core参照処理系
- `examples/`: 適合プログラム例
- `tests/`: 拒否すべきプログラム例と組み込み関数の実行テスト

## C参照処理系

ビルドにはC17コンパイラ、CMake、GMPの開発用ヘッダー・ライブラリが必要。仕様8.2節の全26組み込み関数を実装し、整数は任意精度、浮動小数点はbinary64、文字列・文字はUnicodeに対応する。

Floatリテラルは10進有理数からGMP整数演算でbinary64へ最近接・偶数丸めするため、数値ロケールに依存しない。Lean上のFloat評価意味論とC実装全体の正しさは未証明である。

Linuxでは次の手順でビルド・検証できる。

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build
ctest --test-dir build --output-on-failure
```

Windowsの構成例は次のとおり（GMPのパス設定が必要）。

```text
cmake -S . -B build -A x64
cmake --build build --config Release
ctest --test-dir build -C Release --output-on-failure
```

```text
build/Release/nlisp check examples/factorial.nlisp
build/Release/nlisp run examples/factorial.nlisp
```

フィボナッチ数列の例は`55`を返す。

```text
build/Release/nlisp run examples/fibonacci.nlisp
```

詳細と現在の制限は`IMPLEMENTATION.md`を参照する。

rank-1多相関数、`type-app`、実引数型だけからの一方向型引数決定、および固定引数の型付き衛生テンプレートマクロを実装している。

```text
build/Release/nlisp run examples/polymorphism.nlisp
```

この例は`42`を返す。Lean連携テストでも、型引数を具体化したコア式を生成して型検査する。多相型検査アルゴリズム自体の一般的な正しさの証明は今後の課題である。

```text
build/Release/nlisp run examples/macros.nlisp
build/Release/nlisp expand examples/macros.nlisp
```

マクロ使用例は`44`を返す。型契約は定義時・利用時・展開後に検査する。lambda、let、matchが導入する名前を一意化し、テンプレートの自由変数は定義位置で解決する。Leanでは型付きコアテンプレートの展開と型保存、束縛子下での捕獲回避を形式化している。対応範囲の展開結果をLeanで独立に型検査する連携を提供する。C実装全体との対応証明は今後の課題である。

`defrec` による単相・多相の相互再帰、引数個数の異なるマクロの複数規則、再帰を含むマクロの後方参照に対応する。これらを組み合わせた `examples/recursive_macros.nlisp` は `42` を返す。規則の引数個数の重複と未初期化値の参照は拒否する。マクロの循環だけでは拒否しない。展開結果は既存のLean連携でも検査できる。

## 現在の検証状態

- MSVC C17、`/W4 /WX`でDebug／Releaseビルド成功
- GCC C17のReleaseビルドで全組み込み関数とLean連携を含む統合テストを検証
- Lean側はNLisp-CoreのProgress、型保存、非stuck性を検査済み
- 型付きコアマクロの展開と捕獲回避の定理をLean 4.8.0で検査済み（`lake build`）

C実装とLean意味論の対応そのものは、今後証明または証明書検証の対象とする。

## 展開結果のLean検証

`export-core` は展開済みS式と各識別子のマクロ定義位置をJSONで出力する。Pythonの橋渡しツールはこれを型付きLeanコア式に変換し、Leanで独立に型検査する。

```sh
lake build
python3 tools/verify_lean.py examples/macros.nlisp \
  --nlisp build/nlisp --output build/MacroCertificate.lean
```

証明書は次の2種類を提供する。既定の `--mode auto` は対応するコア式では `core`、その他では `types` を使用し、検証後に選ばれた種類を表示する。明示的にモードを指定することもできる。

| モード | 対象 | Leanで確認する性質 |
|---|---|---|
| `core` | 整数・真偽値・Unit・関数・List・Option、整数の加減乗算・等値比較・`<=` | 展開後の型と非stuck性 |
| `types` | 全実行時型と全26組み込み関数 | 展開後の型と、型添字を消した項の型付け導出 |

両モードとも条件分岐、ラムダ、let、begin、単独再帰と相互再帰に対応する。rank-1多相関数は実引数型または `type-app` の型引数で具体化する。無限に異なる型の具体化が必要な再帰や、依存の展開深さが制限を超える入力は拒否する。未対応式を省略して成功扱いにはしない。全26関数を含む `examples/builtins.nlisp` はCで `42` を返し、`types` 証明書をLeanで検査できる。

`types` モードは浮動小数点のビット列、文字列、文字、組み込み関数の識別子を保持するが、それらの演算の評価意味論は形式化していない。両モードともCの展開アルゴリズム全体との意味保存や、実行結果・停止性は証明しない。


## 再帰マクロと処理予算

`examples/recursive_expansion.nlisp` は自分自身へ展開する規則を含み、有限回で展開して `42` を返す。マクロ定義は他の規則の型契約で検査するため、未使用の再帰マクロを停止性の理由で拒否しない。これは既存のテンプレート方式の再帰を許すもので、手続き的なコンパイル時計算や新しいパターン構文を追加するものではない。

```sh
build/nlisp check input.nlisp --max-expansions 1000 --max-generated-nodes 100000
```

展開が予算内に完了しない場合は `Unknown`（終了コード7）とし、実行や新しい証明書の発行を行わない。型違反などのエラーや、非停止が証明されたという結果とは区別する。深さと検査作業量にも上限がある。既定値・計数方式は `IMPLEMENTATION.md` を参照。

`tools/verify_lean.py` にも同じ上限オプションを渡せる。Unknownの場合は以前の証明書を更新しないため、成功表示だけでなく終了コードと入力ハッシュも確認する。

証明書変換には `--max-certificate-bytes` と `--max-conversion-steps` も指定できる。証明書はLean検査に成功してから公開する。Lean自身の既知の資源上限に達した場合もUnknownとなる。


## 単一ファイルの過程付き証明書

生成物は1つの `.lean` ファイルで扱う。元ソースのバイト列、読み取り後の構文木、`defrec` 正規化後の構文木、マクロの規則適用履歴、展開結果、変換時の文脈・型・生成項、使用予算、Lean定義とツールチェーン指定のハッシュ、Lean証明本文を同梱する。メタデータはBase64化したJSONをLeanコメントとして埋め込み、本文は通常のLeanコードとする。

```sh
python3 tools/verify_lean.py examples/recursive_expansion.nlisp \
  --nlisp build/nlisp --output build/ProgramCertificate.lean

# 元ソースや中間JSONを別に用意する必要はない。
python3 tools/verify_lean.py --verify-certificate build/ProgramCertificate.lean \
  --nlisp build/nlisp
```

全体の再検証は専用コマンドを使う。埋め込んだ元ソースから読み取り・正規化・マクロ展開を再実行し、履歴と結果を照合する。その後、記録したモードで変換を再実行して記録とLean本文を照合し、Lean検査を行う。証明書自身は書き換えない。`lake env lean ProgramCertificate.lean` だけを実行した場合は、コメント内の過程記録を検査せずLean本文のみを検査する。

この過程照合は現在のC処理系とPython変換器による再実行検査であり、ソースからコアまでの意味保存の一般的なLean証明ではない。また、秘密鍵による暗号署名は付けていないため、署名者の認証や改ざん者の特定は保証しない。ハッシュを付け替えた不整合な過程記録は再実行照合で拒否するが、別の整合したソースと証明書への丸ごとの差し替えを認証情報で防ぐものではない。

再検証には同じLean定義とツールチェーン指定が必要。証明書が検証者の許可する予算を超える場合はUnknownとし、上限を無断で引き上げない。旧形式のLean本文だけの証明書は、過程検証を行うには新版ツールで再生成する必要がある。


## スコープを含む型付け

表層の `(Syntax T)` は形式仕様では `Syntax[Γ, T]` とし、所属する束縛環境を保持する。マクロの定義位置 `Γd` と呼び出し位置 `Γc` は分け、展開先 `Ω` への写像は型と束縛IDを保存する。名前や型が同じという理由だけで別の束縛を同一視しない。

`NLisp/ScopedSyntax.lean` では全実行時型の型付けモデルに対してこのモデルを定義し、引数と捕捉変数の代入先、起源の分離、ラムダ導入時の捕獲回避を検査する。表層構文を変更するものではない。有限の実際の展開については、Cが記録した束縛IDと衛生的置換をLeanで独立に検査する。Cプログラム全体の機械意味論との一般的な対応や、ソースからコアへの変換の意味保存とは区別する。


## 展開過程と束縛IDの独立検査

通常の `core` / `types` 証明書には、生成項の型検査に加えて次のLean証明を含める。

- `CExpansionCorrespondence.program_expands`: 正規化済みの元の宣言から、実在するマクロ規則の衛生的置換を経て、今回の展開結果が得られる有限の導出。
- `CCopyCorrespondence.substitution…_sound`: 引数の構文と起源をそのまま保持し、テンプレートの自由識別子に定義位置を付け、lambda・let・matchの束縛子を一意化する処理の照合。新しく使用したカウンター区間の重複も拒否する。
- `CProgramScope.all_references_correspond`: 構文から局所環境・定義位置の環境をLeanで組み立て、各参照がCと同じ束縛IDに対応することを確認する。同じ型の別変数へのすり替え、重複ID、呼び出し時点で利用できない捕捉変数を拒否する。

スコープ検査用の構文と展開導出の結果が同じであることもLeanで検査する。Cの環境観測に含まれる型は不透明なタグとして扱い、名前解決から型付き変数への対応はタグの任意の解釈に対して示す。この事実だけで、Cの型表現とLeanの型意味論の同値を主張するものではない。

ソース文字列のUTF-8バイト列、独立したS式読み取り、`defrec`正規化もLeanで照合する。`VerifiedNLispSource.source_expands_with_scopes` は、同じデータを共有する一つの証明書構造で、元ソースから有限展開・スコープまでを結ぶ。コメント内の過程記録とLean本文の対応は専用の再検証コマンドで確認する。相互再帰や多相関数を含むコア変換そのものの一般的な意味保存、C実行器の正しさ、Float等の評価意味論は未証明である。

## Leanによる終了性の十分条件の検査

```sh
python3 tools/verify_lean.py examples/recursive_expansion.nlisp \
  --mode termination --max-expansions 0 --output build/MacroTermination.lean
python3 tools/verify_lean.py --verify-certificate build/MacroTermination.lean
```

このモードは展開を実行せず、`export-syntax` が出した構文から「マクロ名と引数個数」で規則を識別する。Pythonが順位を候補として作り、Leanがソースの規則から呼び出し辺を再計算し、すべての辺で順位が下がることを検査する。`termination_by` を使って各規則のアクセシビリティを構成し、呼び出し関係の整礎性と呼び出し鎖の長さの上限を証明する。たとえば `answer/1 → answer/0` は同じマクロ名でも証明できる。

循環が残る場合や、構文の穴が呼び出し先を動的に作る場合は `Unknown`（終了コード7）とし、このモードの証明書を発行しない。停止を証明できなかったことを非停止や言語としての不正とは扱わない。通常のモードでは未使用の循環規則があっても、今回の展開が完了すれば有限導出の証明書を発行できる。

ここで証明するのは、構文から抽出した静的なマクロ呼び出し関係の整礎性である。型検査、C展開器全体の終了性との対応、展開サイズ・実行時間の上限、NLisp関数本体の実行終了性は別の問題として残る。証明を得た場合も、通常の展開・検査・出力の資源上限は維持する。証明書は他のモードと同じく元ソース・構文・過程・Lean本文を一つのファイルにまとめる。

専用検証器はLeanモデルをビルドし、実際のLeanの版が `lean-toolchain` と一致することを確認してから本文を検査する。モデル、Lake設定、依存指定のハッシュを記録し、検査途中にそれらが変化した場合は公開しない。


`examples/macro_namespaces.nlisp` は、マクロと同名の値の引数、マクロと同名のテンプレート局所変数、マクロ名と同じパターン変数を組み合わせ、`42`を返す。値として解決した引数を再びマクロ名として解釈せず、値のα変換でマクロの名前空間を変えない。
