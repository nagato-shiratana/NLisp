# NLisp 残課題一覧

更新日: 2026-11-20

本書は、継続作業の対象である課題1〜7について、現在の到達点と未完了の作業をまとめる。既存の単相コア、新多相モデル、C処理系の保証範囲を区別する。すべての課題が完了した状態ではない。

## 現在の到達点

| 課題 | 検証・実装済み | 主な残り |
| --- | --- | --- |
| 1. 展開後構文からIRへの意味保存 | 元構文とIRの独立照合、束縛ID意味論からIRへの有限評価の前向き保存 | 逆向き評価反映、エラー・発散の対応 |
| 2. 新多相モデルの型安全性 | 評価結果の型保存、参照切れ・引数個数違い・形状違いの排除、型検査器の受理結果との接続 | 小ステップProgressを主張する場合の簡約関係と証明、拡張モデルへの適用 |
| 3. 一方向型引数決定 | Lean推論器の成功結果の健全性・一意性、Surface型検査器の十分なfuelでの完全性、型の一意性 | C推論器との一般的な対応、型引数収集アルゴリズムの完全性・明示的資源上界 |
| 4. トップレベル値・初期化 | Cの共有セルと脱出クロージャの修正、GlobalIR実行モデル、初期化セルの保存・充足の証明 | defineの証書経路への接続、変換の意味保存、GlobalIRの型安全性 |
| 5. 全型・組み込み関数 | C処理系と旧型付けモデルは全26組み込み関数に対応 | 新評価モデルへのFloat/String/Character・演算の追加と証明 |
| 6. マクロ展開全体の終了性 | 名前・arity一致の全直接候補と穴頭位置の同arity候補辺の整礎性・呼び出し鎖上界、成功する有限fuel走査の抽出網羅性、全規則行を含むgraphへの保存と証書順位の減少、候補生成作業の予算制限 | 実際のmacroStep列との対応、展開アルゴリズム全体へのシミュレーション・終了性の接続 |
| 7. 独立検査器の保証・計算量 | C展開器を起動しない検査、個別の構文・束縛・型付け・意味保存の検査、整数の数値に依存しない型消去尺度、局所展開証書の区間非重複検査、区間内counter/token非衝突、連続binder呼び出しのtoken一意性、単一binderとsource tokenの非衝突、`copyParameters`・`copyPattern`と空マクロ集合かつ`CounterSafeInitializer`条件下の`copyBindings`のtoken列一意性・source token非衝突・fresh区間内所属、別々の受理済み区間に属するこれらの出力間の非衝突、任意マクロ集合のatomおよび先頭`match`でない任意長atom-only listのcounter保存、`MacroCounterSafeBindingInputs`条件下のtoken列一意性・source-token分離・区間所属および受理済み証書区間間の非衝突、initializerのcounter保持条件からbinding列へfreshnessを合成する一般定理、要素別前提から任意の`copyMany`走査へcounter保持を合成する定理、counter-preserving case body条件下の`copyCases` pattern token列・一意性・source-token分離・区間所属・証書区間間非衝突、`MacroCounterSafeCases`条件下の区間分離 | ネストしたinitializer等についてcounter保持を証明して`CounterPreservingBindings`条件へ入力する作業、case bodyのcounter保存を導く構造的証明、全体`copy`の結果への合成、C `copy_template`とのシミュレーション、counter境界の全体統合、入力識別子との非衝突のcopy全体への合成、全検査過程の合成的健全性、証書のビットサイズに対する計算量上界 |

新しい意味保存・型安全性・型検査器の完全性の対象型は、Boolean、Integer、Unit、関数、List、Optionである。C実行器全体の正しさを証明したとは扱わない。

## 1. 展開後構文からIRへの意味保存

実装済み: `ExpansionLowering.lean`、`NamedSemantics.lean`、`NamedDecoder.lean`、`NameLowering.lean`。

- [ ] 型付きIRの終了する評価から、対応するNamedソースの評価を構成する逆向き定理を証明する。
- [ ] ソース側の実行時エラーを定義し、変換前後のエラー対応を証明する。
- [ ] 非停止の定義を明示し、その保存・反映を証明する。
- [ ] 元ソースの読み取り・有限展開・束縛対応と、上記の意味対応を一つの証書の主定理へまとめる。

完了条件: 展開後構文からIRまで、値・終了・対象とするエラー・非停止の対応を、保証範囲を限定した一般定理で説明できること。

## 2. 新多相モデルの型安全性

実装済み: `PolymorphicSafety.lean`。`evaluator_type_safe`、`evaluation_preserves_type`、`evaluation_no_type_error` を型検査器とpoly証書へ接続した。

- [x] 保証対象を、現行の予算付き大ステップ評価器に対する意味的型安全性と明示する。新多相モデルの小ステップProgressは現時点で主張しない。
- [ ] 将来、新多相モデルについて小ステップProgressを主張する場合は、別途簡約関係・実行状態・値を定義し、Progressと型保存を証明する。
- [ ] GlobalIRおよび課題5の拡張型・演算に対して型安全性を証明する。

完了条件: 採用する意味論に対する型安全性の主張と証明が一致すること。旧単相コアのProgressを新多相モデルの証明として流用しない。

## 3. 一方向型引数決定と型検査

実装済み: `TypeArguments.lean` の収集・検査アルゴリズムと成功結果の証明。`CheckerCompleteness.lean` の `inference_eventually` と `type_unique`。

- [ ] Cの型引数決定と、Leanの制約・代入・呼び出し側の型変数の扱いを一般的に対応付ける。
- [ ] 整合する型引数列が存在し、全量化変数が仮引数型に現れる場合、十分な資源で収集アルゴリズムがその列を返すことを証明する。
- [ ] 型検査に十分なfuelの明示的な上界を、式・型・シグネチャの構造から与える。
- [ ] 深さ予算超過と型不適合を診断で区別する。現在のOptionのnoneだけから不適合とは結論しない。

完了条件: 期待する戻り値型を使わないこと、呼び出し側の型変数を固定して扱うこと、未決定変数へ既定値を入れないことを維持し、成功・失敗・資源超過の保証を整理すること。

## 4. トップレベル値・初期化・捕捉

実装済み: C実行器の共有セル、初期化前読み出しの診断、`GlobalIR.lean` と初期化の不変条件。

- [ ] 注釈付きソースのdefineを読み取り、大域値の型・束縛ID・初期化順を保持する。
- [ ] 大域値への参照をGlobalIRのgetterへ変換し、局所変数・関数参照と区別する。
- [ ] poly証書生成経路へ接続する。現状のpolyモードはトップレベルdefineを拒否する。
- [ ] 初期化の成功・初期化前読み出し・非停止と、クロージャによる大域値参照を形式化する。
- [ ] ソースからGlobalIRへの意味保存と、初期化後の型安全性を証明する。
- [ ] Cの共有セル実装との対応を示す。

完了条件: 先に作ったクロージャが後から初期化された大域値を正しく参照し、実際の初期化前読み出しは初期化エラーとなること。未使用の初期化式も省略しないこと。

## 5. 全型・全組み込み関数

- [ ] 新Surface・IR・値・評価器・型付けへFloat、String、Characterを追加する。
- [ ] 全26組み込み関数について型と評価規則を対応付ける。
- [ ] binary64の丸め、NaN・無限大・符号付きゼロ・サブノーマルを仕様と整合させる。
- [ ] UTF-8、Unicode scalar、埋め込みNUL、文字列操作をモデルと対応付ける。
- [ ] 整数除算・余り・数値変換のOption結果を含め、型安全性・意味保存を拡張する。
- [ ] C演算とモデルの対応について、証明した部分と信頼する前提を明記する。

完了条件: 旧型付けモデルやC実装で対応している事実だけでなく、新しい評価モデルで全演算の意味と保証を説明できること。

## 6. マクロ展開処理全体の終了性

- [x] `calls_direct_macro_complete` と `graphRows_root_call_edge` で、root位置の呼び出しが成功した構文走査で抽出され、該当する呼び出しグラフ行の辺になることを証明する。
- [x] `graphRows_dependency_edge` で、成功した任意のグラフ行にある抽出済み依存先が辺として保持されることを証明する。
- [x] `call_extraction_complete` と `graphRows_static_call_edge` で、成功した構文走査が木中の任意の深さにあるStaticCallを抽出し、グラフ辺にすることを証明する。
- [x] `GraphCall` と `graphRows_contains_static_calls` で、全規則行のStaticCallを完成したグラフへ保存し、証明済み順位の減少へ接続する。
- [x] `ProcessCertificate.source_static_calls_decrease` で、一般の受理済み停止性証書から各全規則StaticCallの順位減少を再利用可能な定理として取り出す。
- [x] `targetsOfArity` で構文穴が呼び出し先になる位置に同じ引数個数の全規則を候補辺として加え、`findRule_mem_targetsOfArity` で実際の名前検索先の候補所属を証明し、Python順位候補生成とLeanグラフ再計算を一致させる。
- [x] `targetsOfSignature` で名前付き呼び出しも同名・同arityの全規則を候補辺とし、`findRule_mem_targetsOfSignature` で名前検索先が候補に含まれることを証明する。
- [ ] 実際に発生する各macroStepが、そのStaticCall関係の辺に対応することを証明する。
- [ ] テンプレートの置換、引数の複製、構文走査、名前生成を含む状態遷移を定義する。
- [ ] 順位の減少と構文処理の進行から、展開処理全体の終了を導く。
- [ ] Cの展開処理との対応を示す。
- [ ] より精密な動的呼び出し解析や、利用者指定の一般的な構造的減少を別の十分条件として設計する。構文穴の呼び出し先については、同じ引数個数を持つ全マクロ規則を候補辺へ加える保守的解析を実装済み。

完了条件: 呼び出しグラフの整礎性を、展開器全体の終了性と取り違えないこと。証明不能はUnknownとし、非停止や入力不正とは判定しないこと。展開サイズ・時間の上界は別に扱う。

## 7. 独立検査器の保証・計算量

- [x] 停止性候補グラフの構文走査・候補辺列挙・順位構築を `--max-conversion-steps` で逐次制限し、予算超過をUnknownにする。これは作業予算であり、ビットサイズに対する漸近上界の証明ではない。
- [x] 停止性解析が作業予算を使い切った場合、Unknown診断へ試行操作数と設定上限を含める。

- [x] 局所展開証書データ型と汎用Boolean検査器を実装し、Cの実例を同じ `check` 関数への入力として受理する。`check_sound` は受理から有限の `CExpansion.Expands` 導出を返す。
- [x] 証書に記録されたfresh counter区間を抽出し、`checkFresh` で区間非重複と `check` の両方を要求する。`checkFresh_sound` は有限展開を導き、区間条件も独立に取り出せる。
- [x] `disjoint_interval_counters_differ` と `checkFresh_separates_interval_counters` を証明し、別々の受理済み区間内のカウンタ値が一致しないことを導く。
- [x] カウンタから生成されるtoken identity `3*n+2` の区別を、上記区間条件から導く補題を追加する。
- [x] 連続して成功する `binder` 呼び出しがcounterを1ずつ進め、異なるtokenを生成することを証明する。
- [x] source tokenが予約済み剰余類に属する場合、単一の成功したbinderが同じsource token identityを生成しないことを証明する。
- [ ] 受理から得られる構文対応・freshness・非捕捉・型保存を、一つの合成的健全性定理へまとめる。
- [ ] `copy`、`copyMany`、`copyParameters`、`copyBindings`、`copyPattern`、`copyCases` の結果について、上記のbinder性質を構造的に合成し、全生成識別子がcounter境界内かつ相互に異なることを示す。入力識別子との非衝突と合わせて全体のFreshnessを導く。
- [x] `copyParameters_counter` で、成功時のcounter増分がパラメータ数に等しいことを証明する。
- [x] `copyParameters_token_sequence` と `copyParameters_tokens_unique` で、出力binder token列が連続counter列と一致し、重複しないことを証明する。
- [x] `copyParameters_tokens_avoid_source` で、予約済みsource-token剰余類の識別子が出力binder token列に現れないことを証明する。
- [x] `copyPattern_token_sequence`、`copyPattern_tokens_unique`、`copyPattern_tokens_avoid_source` で、match patternのbinder token列について同じ性質を証明する。
- [x] `parameter_then_pattern_tokens_unique` で、異なるcopy操作の連続実行時も共通counterを使えばbinder token集合が重複しないことを証明する。
- [x] `copyParameters_tokens_within_interval` と `copyPattern_tokens_within_interval` で、各出力tokenをその操作のfresh counter区間内の生成counterへ対応付ける。
- [x] `checkFresh_separates_parameter_copy_tokens` と `checkFresh_separates_pattern_copy_tokens` で、別々の証書区間に属する当該操作の出力token同士が異なることを示す。
- [x] `AtomicBindingInputs`と`CounterSafeInitializer`条件の下で`copyBindings_atomic_counter`と`copyBindings_atomic_token_sequence`を証明する。空マクロ集合で各let initializerはatom、atom一個・二個のlist、または先頭が`match`でないatom三個・四個のlistに限る。
- [x] `copyBindings_atomic_tokens_unique`、`copyBindings_atomic_tokens_avoid_source`、`copyBindings_atomic_tokens_within_interval`で、この制限付きcopyBindings結果のfreshness特性を導く。
- [x] `checkFresh_separates_atomic_binding_tokens`で、条件を満たすcopyBindings結果について別区間間のtoken非衝突を証明する。
- [x] 任意のマクロ名集合に対応する `copyWithMacros_atom_keeps_counter`、`copyManyWithMacros_atomic_counter`、`copyBindingsWithMacros_atoms_counter` を証明する。
- [x] atom initializer列に限ってマクロ名集合付き `copyBindings` のtoken列、一意性、source-token分離、区間所属を証明する。
- [x] `checkFresh_separates_macro_aware_atom_binding_tokens`で、そのtoken非衝突を受理済み証書区間へ接続する。
- [x] `CounterPreservingInitializer`条件をbinding列へ合成し、counter/token列、token一意性、source-token分離、区間所属とfresh証書区間間の非衝突を導く一般定理を追加する。
- [x] 空マクロ集合の`CounterSafeInitializer`族と、任意マクロ集合のatom initializerを`CounterPreservingInitializer`条件へ接続する。
- [x] 要素ごとのcounter-preserving性から、任意のマクロ集合での`copyMany`全体のcounter保持を証明する。
- [x] 任意マクロ集合でatom一個・二個のlist initializerがcounterを保持し、`CounterPreservingInitializer`条件へ接続することを証明する。
- [x] 任意マクロ集合で先頭が`match`でない任意長atom-only listのcounter保存を証明し、`MacroCounterSafeBindingInputs`と受理済みfresh区間へ接続する。
- [x] counter-preserving body仮定の下で、`copyCases`のcounter差分を全case pattern binder数へ合成する。
- [x] そのcase binder token列をcounter列へ同定し、token一意性・source-token分離・fresh区間とfresh証書区間間の非衝突を証明する。
- [x] `MacroCounterSafeCases`からcase bodyの抽象counter保存条件へ変換し、fresh区間非衝突を接続する。
- [x] `copyMany_atomic_counter`で、atomだけからなるリストの走査がfresh counterを消費しないことを証明する。
- [x] `copy_single_atom_list_keeps_counter`で、atom一個だけのlist構文のcopyもfresh counterを保持することを証明する。
- [x] `copy_two_atom_list_keeps_counter`で、atom二個だけのlist構文のcopyもfresh counterを保持することを証明する。
- [x] `copy_three_atom_list_keeps_counter`で、先頭atomが`match`でないatom三個のlist構文もfresh counterを保持することを証明する。
- [x] `copy_four_atom_list_keeps_counter`で、先頭atomが`match`でないatom四個のlist構文もfresh counterを保持することを証明する。
- [x] `copyWithMacros_atomTrees_keeps_counter`で、先頭が`match`でない任意長atom-only listのcounter保存を証明する。
- [ ] マクロ契約の型付けと、実際の置換・展開証書の型情報を同一モデルへ接続する。
- [ ] コメント内の過程記録、Lean本文、検査対象データの対応と信頼境界を整理する。
- [ ] 計算量の入力サイズNを、証書・型・識別子・数値の符号化を含むビットサイズで定義する。
- [ ] 検査手続きのコストモデルを定義し、構文走査・環境探索・型照合・局所証書検査の上界を証明する。
- [ ] 共有やキャッシュを使う場合は、DAG・依存関係・再検査の条件を定める。
- [ ] Leanの本文生成・精緻化・カーネル検査まで含む範囲と、専用検査アルゴリズムの範囲を区別する。
- [ ] 証明対象の範囲について多項式上界を示し、対象外の計算には保証を拡大しない。

完了条件: 「今回検査できた」「予算付きで動く」「構文ノードだけなら線形」を、検査器全体の多項式時間保証として扱わないこと。元ソースに対して証書が大きくなり得ることと、証書サイズに対する検査時間を区別すること。

## 追加の研究・仕上げ作業

- [ ] 証書なしの処理系、再実行方式、独立検査方式の比較実験を行う。
- [ ] 入力・展開結果・証書のサイズ、生成時間、検査時間、メモリを測定する。
- [ ] 型は合う別の束縛・演算へのすり替え、偽のfreshness、改変した入力・証書、資源超過を継続して検証する。
- [ ] 論文の主張を、カーネル検査済みの定理と実験で支持できる範囲へそろえる。

## 推奨する実装順

1. マクロcopyの状態遷移とC `copy_template`の対応を定義し、観測された一例の再検査から一般の一段シミュレーションへ進める。ここが停止性と全体freshnessの共通基盤になる。
2. `copy`系各操作のcounter/token境界を、let initializerとmatch bodyの条件付き補題から全構文へ合成する。得られたcopyシミュレーションと組み合わせ、入力識別子との非衝突を含むfreshness定理を作る。
3. その対応を使い、静的呼び出し候補の整礎性を実際の展開処理全体の終了性へ接続する。証明できない入力はUnknownのままにする。
4. Named意味論からIRへの逆向き評価対応を追加し、エラーと非停止の定義・対応を定める。
5. GlobalIR、Cの型推論、Float/String/Characterの意味論をそれぞれ接続し、証明の対象範囲を広げる。

この順序は依存関係に基づく提案であり、各段階でC実装との実際の対応を示せない場合は、保証範囲を局所モデルに限定する。

## 作業上の注意

- 予算切れは非停止の証明ではない。
- 型が合う出力を生成できることだけでは、元プログラムとの意味保存にならない。
- 証明済みという記載は、本体のLeanファイルと公理監査を確認して更新する。
- モデル更新後の証書は再生成する。古い環境ハッシュの証書を黙って受理しない。
- 今回の追加修正には未ステージのファイルがある。Gitのステージ・コミット・アップロードはユーザー側で行う。
