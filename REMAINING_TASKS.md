# NLisp 残課題一覧

更新日: 2026-11-22

本書は、継続作業の対象である課題1〜7について、現在の到達点と未完了の作業をまとめる。既存の単相コア、新多相モデル、C処理系の保証範囲を区別する。すべての課題が完了した状態ではない。

## 作業状況の要約

未完了項目は32件。課題1: 5件、課題2: 1件、課題3: 1件、課題4: 4件、課題5: 5件、課題6: 4件、課題7: 12件。詳細と現在の証明範囲は各節のチェックリストを正とする。

直近の利用者WSLログでは、`CMacroCopy`がリプレイ成功し、`CExpansion`のコスト証明も失敗対象から外れた。ビルド失敗は`ExpansionLowering.globalValueIndex_lookup_sound`のリストindex証明と、`ExpansionCertificate`のmembership・検査コスト・endpointサイズ上界の証明に残っている。ログ後にこれらの証明を修正したが、作業ツリー上の変更は未検証。unused-variable警告は`lake build`失敗の原因ではない。

Lean変更は機能単位の`CMacroCopy`、`MacroTermination`、`ExpansionCertificate`、`NameLowering`、`GlobalIR`などへ分けている。今回の大規模差分は未コミットで、`git status`にはC実装・Lean形式化・テスト・文書・benchmark用ファイルが混在している。現在は大半がステージ済みで、この文書には今回の追記を含む未ステージ差分もある。既存のステージ状態は維持し、コミット前にビルドとステージ内容を確認する。

## 次に進める実装順

1. **ビルドを安定させる**: WSL `lake build` の最新失敗（`ExpansionLowering`と`ExpansionCertificate`）に対する作業ツリー修正を検証し、新たな失敗を順に解消する。通過を確認するまでは、関連する残課題を完了扱いにしない。
2. **トップレベル値とGlobalIR**: decode結果からtyped runtime table/store条件を構成し、initializerの評価型を導出する。GlobalIR評価器の型保存とsource/Cとの意味対応を個別に進める。
3. **Named意味論の反映と総合定理**: decoderが保証するbinder/layout条件を使い、評価全体の逆向き反映を合成する。その後にエラー・発散の対応と有限展開証書を含む主定理を組み立てる。
4. **残る型保証**: C型引数推論とLean制約モデルを一般対応付けする。Float/String/Characterおよび全組み込み関数の仕様・評価・型安全性を拡張する。
5. **macro copyのC対応**: Leanのcopy状態遷移とC `copy_template`の一段シミュレーションを定義し、binder freshnessと非捕捉を全構文へ合成する。
6. **停止性・独立検査の統合**: template callsiteから次の実macroStepまでのシミュレーションを完成させて終了性を示す。freshness・型保存・構文対応の健全性定理を統合し、コストモデルを証書byte長へ接続する。

順序は、現時点の依存関係と直近のビルド阻害要因に基づく。各保証はLean証明・C対応・文書の証拠が揃った範囲だけ完了にする。

## 現在の到達点

| 課題 | 検証・実装済み | 主な残り |
| --- | --- | --- |
| 1. 展開後構文からIRへの意味保存 | 元構文とIRの独立照合、束縛ID意味論からIRへの有限評価の前向き保存 | well-scopedソース条件付きの逆向き評価反映、エラー・発散の対応 |
| 2. 新多相モデルの型安全性 | 評価結果の型保存、参照切れ・引数個数違い・形状違いの排除、型検査器の受理結果との接続 | 小ステップProgressを主張する場合の簡約関係と証明、拡張モデルへの適用 |
| 3. 一方向型引数決定 | Lean推論器の成功結果の健全性・一意性、Surface型検査器の十分fuel下の完全性と計算可能な構造上界、候補条件下の型引数決定完全性 | C推論器との一般的な対応、候補条件なしの型引数決定完全性 |
| 4. トップレベル値・初期化 | Cの共有セルと脱出クロージャの修正、注釈付きdefineのGlobalHeader読み取り、GlobalIR実行モデル、初期化セルの保存・充足の証明 | defineのpoly証書・GlobalIR経路への接続、変換の意味保存、GlobalIRの型安全性、C対応 |
| 5. 全型・組み込み関数 | C処理系と旧型付けモデルは全26組み込み関数に対応 | 新評価モデルへのFloat/String/Character・演算の追加と証明 |
| 6. マクロ展開全体の終了性 | 名前・arity一致の全直接候補と穴頭位置の同arity候補辺の整礎性・呼び出し鎖上界、成功する有限fuel走査の抽出網羅性、全規則行を含むgraphへの保存と証書順位の減少、候補生成作業の予算制限 | 実際のmacroStep列との対応、展開アルゴリズム全体へのシミュレーション・終了性の接続 |
| 7. 独立検査器の保証・計算量 | C展開器を起動しない検査、個別の構文・束縛・型付け・意味保存の検査、整数の数値に依存しない型消去尺度、局所展開証書の区間非重複検査、区間内counter/token非衝突、連続binder呼び出しのtoken一意性、単一binderとsource tokenの非衝突、`copyParameters`・`copyPattern`と空マクロ集合かつ`CounterSafeInitializer`条件下の`copyBindings`のtoken列一意性・source token非衝突・fresh区間内所属、別々の受理済み区間に属するこれらの出力間の非衝突、任意マクロ集合のatom・制限付きatom-only list・binder特殊headを含まない任意ネスト木のcounter保存、`MacroCounterSafeBindingInputs`条件下のtoken列一意性・source-token分離・区間所属および受理済み証書区間間の非衝突、initializerのcounter保持条件からbinding列へfreshnessを合成する一般定理、要素別前提から任意の`copyMany`走査へcounter保持を合成する定理、counter-preserving case body条件下の`copyCases` pattern token列・一意性・source-token分離・区間所属・証書区間間非衝突、`MacroCounterSafeCases`条件下の区間分離 | binderを含むinitializerを含む全構文への拡張、case bodyのcounter保存を導く構造的証明、全体`copy`の結果への合成、C `copy_template`とのシミュレーション、counter境界の全体統合、入力識別子との非衝突のcopy全体への合成、全検査過程の合成的健全性、証書のビットサイズに対する計算量上界 |

新しい意味保存・型安全性・型検査器の完全性の対象型は、Boolean、Integer、Unit、関数、List、Optionである。C実行器全体の正しさを証明したとは扱わない。

## 1. 展開後構文からIRへの意味保存

実装済み: `ExpansionLowering.lean`、`NamedSemantics.lean`、`NamedDecoder.lean`、`NameLowering.lean`。

- [ ] デコーダ／型検査が保証するwell-scopedソース条件（特にletManyのbinder数）と、プログラム・捕捉環境内closureの不変条件を明示した上で、型付きIRの終了評価からNamed評価を構成する一般逆向き定理を証明する。binder ID数が不一致の任意Exprにはこの主張は成立しない。
- [x] `lookup_lowered_reflects` で、位置添字IR環境のlookup成功から、同じlowered値を返すNamed環境lookupを構成する。`variable_evaluation_reflected` でIR評価関係の変数規則もNamed側へ反映する。これは変数ケースだけであり、評価全体の反映は未証明。
- [x] `definitions_lookup_reflects` と `global_evaluation_reflected` で、lowered定義表のglobal lookupと評価をNamed側へ反映する。IR評価全体の逆向き定理は未証明。
- [x] `boolean_evaluation_reflected`、`integer_evaluation_reflected`、`unit_evaluation_reflected`、`nil_evaluation_reflected`、`none_evaluation_reflected` で、IRの各リテラル評価をNamed側へ反映し、lowered値との一致を示した。
- [x] `lambda_evaluation_reflected` で、IRのクロージャ生成評価をNamedラムダ評価へ反映し、lowered closureの一致を示した。クロージャ適用を含む一般の評価反映は未証明。
- [x] `lowerEnv_bind_append`、`identities_bind_append`、`lower_call_body` で、引数bind後のNamed環境・binder ID列・クロージャ本体のIR lowerが一致することを証明した。これらを使うクロージャ適用の評価反映は未完了。
- [x] `add_evaluation_reflected` で、左右の部分式の反映証明を前提に、整数加算のIR評価をNamed評価へ合成した。これは個別の演算子ケースであり、全式の逆向き定理は未証明。
- [x] `sub_evaluation_reflected`、`mul_evaluation_reflected`、`le_evaluation_reflected`、`intEq_evaluation_reflected` で、左右の部分式から減算・乗算・大小比較・整数等値比較の評価反映を合成した。演算子ケースの補題であり、全式の逆向き定理は未証明。
- [x] `ite_evaluation_reflected` で、条件と選択された枝の反映から条件分岐評価をNamed側へ戻した。これは条件分岐ケースであり、全式の逆向き定理は未証明。
- [x] `some_evaluation_reflected` と `cons_evaluation_reflected` で、子式からOption/List構築式の評価反映を合成した。リスト・オプションcase分析やクロージャ適用を含む全式の証明は未完了。
- [x] `arguments_evaluation_reflected`、`sequence_evaluation_reflected`、`begin_evaluation_reflected` で、各要素の反映証明を入力として引数列・begin列の評価反映を合成した。任意要素の反映証明を前提とする補助定理であり、全式の逆向き定理は未証明。
- [x] `letMany_evaluation_reflected` で、初期値数とbinder数が一致する条件下、引数列と本体の反映証明からletMany評価をNamed側へ合成した。IRがbinder ID数を消去するためこの整形式条件を明示しており、これを含む一般の全式定理は未証明。
- [x] `matchList_evaluation_reflected` で、target/empty/cons本体の反映証明からlist match評価をNamed側へ合成した。cons本体ではパターン値とlowered環境の対応を前提にする。matchOptionと全式の逆向き定理は未証明。
- [x] `matchOption_evaluation_reflected` で、target/empty/some本体の反映証明からoption match評価をNamed側へ合成した。some本体ではpayloadとlowered環境の対応を前提にする。全式の逆向き定理は未証明。
- [x] `EvaluationReflection` を帰納仮定の形に定義し、`appClosure_evaluation_reflected` と `appGlobal_evaluation_reflected` で両application規則からNamed評価を組み立てた。これは相互帰納法のアプリケーション各ステップであり、`EvaluationReflection` 自体の証明は未完了。
- [x] `tests/NameLowering.lean` にletMany binder数不一致の反例を追加し、IR評価は成功する一方、対応するNamed評価は存在しないことをLeanで証明した。一般逆向き定理にはdecoderが保証する整形式条件が必要。
- [x] `NamedDecoder.letParts_lengths` と `decodeExprs_length` に加え、let分岐を `decodeLetMany` に集約し `decodeLetMany_lengths` を証明した。成功したlet decodeではbinder数とinitializer数が一致する。ネストしたdecode結果のwell-scoped性および逆向き評価定理との接続は未完了。
- [ ] `letLayoutsAligned` と `decodeExprChecked` を追加し、`decodeFunctions` が全ネストletのbinder/initializer件数を検査してから本体を返す経路へ変更した。`decodeExprChecked_spec`、`decodeExprChecked_letMany_lengths`、`decodeExprChecked_letMany_evaluation_reflected`、`decodeFunctions_letLayoutsAligned`、`decodeProgram_letLayoutsAligned`、`definitionsLetLayoutsAligned_mem`、`decodeProgram_member_letMany_lengths`、`decodeProgram_lookup_letMany_lengths` でdecodeProgramの保証を個別letの評価反映ケースと出力index lookupまでつないだ。Leanビルド確認と一般逆向き評価定理への組み込みは未完了。
- [ ] ソース側の実行時エラーを定義し、変換前後のエラー対応を証明する。
- [ ] 非停止の定義を明示し、その保存・反映を証明する。
- [ ] 元ソースの読み取り・有限展開・束縛対応と、上記の意味対応を一つの証書の主定理へまとめる。

完了条件: 展開後構文からIRまで、値・終了・対象とするエラー・非停止の対応を、保証範囲を限定した一般定理で説明できること。

## 2. 新多相モデルの型安全性

実装済み: `PolymorphicSafety.lean`。`evaluator_type_safe`、`evaluation_preserves_type`、`evaluation_no_type_error` を型検査器とpoly証書へ接続した。

- [x] 保証対象を、現行の予算付き大ステップ評価器に対する意味的型安全性と明示する。新多相モデルの小ステップProgressは現時点で主張しない。
- [x] 現行保証では新多相モデルの小ステップProgressを主張しないことを明記した。将来その主張を追加する場合の簡約関係・実行状態・値・Progress・型保存は、その追加時の別タスクとする。
- [x] `GlobalIR.StoreWellTyped` と `getter_call_preserves_type` で、型付きstoreからgetterが読み出す値の型保存を証明した。`StoreWellTyped.set` と `initializeValues_preserves_typed` は、各initializer評価が型付き値を返し、slot/type対応がある条件下で初期化後も不変条件が保たれることを証明する。評価器自体の型安全性、関数評価、拡張型への一般化は未完了。
- [ ] GlobalIRおよび課題5の拡張型・演算に対して型安全性を証明する。

完了条件: 採用する意味論に対する型安全性の主張と証明が一致すること。旧単相コアのProgressを新多相モデルの証明として流用しない。

## 3. 一方向型引数決定と型検査

実装済み: `TypeArguments.lean` の収集・検査アルゴリズムと成功結果の証明。`CheckerCompleteness.lean` の `inference_eventually` と `type_unique`。

`checkerTypeFuel` / `checkerTypesFuel` は型木および関数型引数リストから整形式性検査のfuelを計算し、`checkWF_sufficient` / `checkTypesWF_sufficient` が十分性を証明する。`checkerSignatureFuel` / `checkSignatureWF_sufficient` はその境界をシグネチャのparameter・result両方へ合成する。`checkerExprFuel` / `checkerExprsFuel` は式・式列・注釈・全global signatureから計算可能な境界を返し、各構文ケースで注釈・子式のfuelを親fuel内に収める。`inference_structural_fuel` はその式fuelから`infer`の成功を証明する。C推論器との一般的な対応と、候補条件に依存しない型引数決定の完全性は未完了。

- [ ] Cの型引数決定と、Leanの制約・代入・呼び出し側の型変数の扱いを一般的に対応付ける。
- [x] `collectArgument_first_variable_capture`、`collectArgument_repeated_variable_same`、`collectArgument_repeated_variable_conflict` で、C `match_type` と同じく最初の制約は実引数型をそのまま格納し、再出現は完全一致だけ受け入れることを証明した。これはcollector局所の規則一致で、Cのpointer identity・monotype検査・全呼び出しとの一般シミュレーションは未証明。
- [x] `AssignmentsAgree.set`、`collectArgument_*_agrees`、`collectArgument_variable_complete` で、候補型引数列と代入状態の整合性を保ちながら、型変数1個の制約収集が候補に対して完全であることを証明した。
- [x] `collectorTypeFuel` / `collectorTypesFuel` で型・引数列の走査fuelを計算可能な再帰関数として定義し、`collectArgument_complete` / `collectArguments_complete` でこの境界の下の成功・代入整合性・代入列長を証明した。
- [x] `collectArgument_preserves_assigned` と `collectArguments_preserves_assigned` で、成功する追加制約の走査が既に割り当て済みの型引数スロットを消去・変更しないことを証明した。
- [x] `inferTypeArguments_complete_from_candidate` で、整形式の候補型引数列が実引数型と整合し、全量化変数が仮引数型に現れ、collectorと型検査双方の構造fuelが足りるなら、一方向推論器がその候補を含む証明付きsolutionを返すことを証明した。`inferTypeArgumentsCandidateFuel` は二つの計算可能なfuel境界の最大値を返し、`inferTypeArguments_complete_at_candidate_fuel` がその十分性を示す。
- [x] `checkerExprFuel` / `checkerExprsFuel` と `inference_structural_fuel` で、式・式列・型注釈・参照されるシグネチャの構造から計算可能なfuel上界を与え、そのfuel以上で型検査器が成功することを証明した。`checkSignatureWF_sufficient` はシグネチャのparameter型列とresult型の境界を構成する。
- [x] C CLIでは深さ・作業予算超過を `Unknown`、型不適合を型エラーとして診断することを明記した。Lean `Option` checkerのnoneは予算超過と拒否を区別せず、不適合の証明には使わない。

完了条件: 期待する戻り値型を使わないこと、呼び出し側の型変数を固定して扱うこと、未決定変数へ既定値を入れないことを維持し、成功・失敗・資源超過の保証を整理すること。

## 4. トップレベル値・初期化・捕捉

実装済み: C実行器の共有セル、初期化前読み出しの診断、`GlobalIR.lean` と初期化の不変条件。

追加済みの補助定理: `evaluate_lambda_store_independent`、`getter_call_reads_current_store`、`getter_call_reports_early_read`、`initializeValues_stops_on_error`、`initializeValues_commits_head`。IR上でクロージャ作成がストアに依存せず、getter呼び出しは呼び出し時のストアを読むこと、未初期化セルのエラー、初期化式の失敗時に後続へ進まないこと、成功した値をセルへ確定してから次へ進むことを証明する。さらに`Diverges`を全ての正のfuelでfuel切れとなる性質として定義し、再帰呼び出しの例と、発散するinitializerが初期化列をfuel切れにすることを証明した。これらはソース変換、GlobalIRの型安全性、C実装とのシミュレーションを証明するものではない。

- [x] `ExpansionLowering.readGlobalHeader` / `readGlobalHeaders` で注釈付き`define`を読み取り、大域値の型・束縛ID・初期化式・宣言位置を保持する。`tests/ExpansionLowering.lean` で関数宣言が間にある場合も大域初期化順が保たれることを確認した。
- [x] `GlobalIR.lowerGlobalReads`でGlobalIR定義表上の大域値indexをgetter呼び出しへ変換する。局所変数は維持し、getter対応表にない大域関数の呼び出し先は直接参照のままにする。大域値を関数値として呼ぶ場合はgetterで取得してから適用する。`tests/GlobalIR.lean`の例をLeanで検査した。source binder IDからこの対応表を作る変換接続は意味保存項目に残す。
- [ ] poly証書生成経路へ接続する。現状のpolyモードはトップレベルdefineを拒否する。
- [x] GlobalIRモデル内で初期化の成功・初期化前読み出し・非停止と、クロージャによる大域値参照を形式化した。`Diverges`は正の全fuelに対するfuel切れであり、Cやソース意味論との対応は別項目に残す。
- [ ] `GlobalProgramTyped` でfunctionSourcesを明示し、combined runtime table indexとsource function definition indexを分けた上で、関数定義のarity/body型とgetter index・slot型・global signatureの対応を定義した。`function_layout_typed` / `getter_layout_typed` で両方のentryから元の型情報を取得できる。`typed_getter_call_preserves_type`、`typed_getter_call_reports_early_read` で型付きgetterの返値型と初期化前read errorをレイアウト条件へ接続した。`functionSourcesFor` / `mem_functionSourcesFor_iff` は関数prefixのindex対応を生成・特徴付ける。`functionEntries` はSurface関数本体をerase後にgetter参照へ書き換え、`assembleProgram` はその関数列とslot getter列を連結する。`assembleGlobals` は対応するsignature列を構成し、`assembled_function_source_layout` / `assembled_getter_layout` で型・runtime entryのindex対応を結ぶ。さらに `AssembledSourceTyped` の下で `assembleProgram_typed` が `GlobalProgramTyped` を構成する。`getterMappings` / `getterFor_getterMappings` と `lowerGlobalReads_global_value_getter` は関数prefix後のglobal value indexをgetter callへ接続し、`ExpansionLowering.globalValueIndex` / `globalValueReferenceIndex_sound` はGlobalHeaderのbinder IDをvalue slotからfunction-prefix込みglobal indexへ解決する。`InitializerTypesAgree.slot_type_at` はinitializer indexからslot型を取得し、`empty_store_well_typed` と `initializeValues_from_empty_preserves_typed` も実装済み。実ソースからruntime table・slot・initializer列をまとめて構成する変換、GlobalIRの一般fuel付き評価器の型保存、initializer評価の型付き前提の導出は未完了。Leanビルド確認待ち。
- [ ] `ExpansionLowering.readProgramHeaders` は混在したdefun/define列をそれぞれの順序を保って読み取る。`NamedDecoder.decodeTopLevelProgram` は関数headerの後にvalue headerを並べ、関数bodyとinitializerのglobal参照をcombined indexでdecodeする。`globalIndex_value_reference` はbinder IDから値globalの `functionCount + slot` への対応を証明し、`decodeGlobalInitializers_length` / `decodeProgramWithGlobals_layout` / `decodeTopLevelProgram_layout` はslot型と初期化式の件数一致を示す。`GlobalIR.assembleNamedProgram` / `programOfNamed` はdecoded functionとinitializerからgetter付き実行table・初期化列を構成する。`assembleNamedProgram_length` / `programOfNamed_definition_count` はruntime tableの関数prefix・slot getter suffixの全長を、`programOfNamed_getter_lookup` はslot番号からgetter entryの位置を示す。追加した`decodedProgram_layout`はdecode成功時にruntime table全長・initializer数・値slot getter位置をまとめて示す。decode結果からGlobalProgramTypedを導く型証明と、ソースからGlobalIRへの意味保存・初期化後の型安全性は未証明。
- [ ] Cでは`RBind.value == NULL` / `some Value`相当が未初期化/初期化済みセルであり、`value_slots[i]`が各`D_VAL`の共有binding nodeを指し、GlobalIRでは同じslotをstore indexとgetterで表すというデータ表現の対応を文書化した。`Program` indexからvalue slot ordinalへの写像、Cの文字列名検索とNamed binder IDの対応、C evaluator stepとGlobalIR evaluator stepのシミュレーションは未証明。

完了条件: 先に作ったクロージャが後から初期化された大域値を正しく参照し、実際の初期化前読み出しは初期化エラーとなること。未使用の初期化式も省略しないこと。

## 5. 全型・全組み込み関数

- [ ] 新Surface・IR・値・評価器・型付けへFloat、String、Characterを追加する。
- [ ] 全26組み込み関数について型と評価規則を対応付ける。
- [ ] binary64の丸め、NaN・無限大・符号付きゼロ・サブノーマルを仕様と整合させる。
- [ ] UTF-8、Unicode scalar、埋め込みNUL、文字列操作をモデルと対応付ける。
- [ ] 整数除算・余り・数値変換のOption結果を含め、型安全性・意味保存を拡張する。
- [x] C演算とモデルの対応について、Leanで形式化した範囲とCのIEEE 754・文字列実装等を信頼する前提を `IMPLEMENTATION.md` に明記する。

完了条件: 旧型付けモデルやC実装で対応している事実だけでなく、新しい評価モデルで全演算の意味と保証を説明できること。

## 6. マクロ展開処理全体の終了性

- [x] `calls_direct_macro_complete` と `graphRows_root_call_edge` で、root位置の呼び出しが成功した構文走査で抽出され、該当する呼び出しグラフ行の辺になることを証明する。
- [x] `graphRows_dependency_edge` で、成功した任意のグラフ行にある抽出済み依存先が辺として保持されることを証明する。
- [x] `call_extraction_complete` と `graphRows_static_call_edge` で、成功した構文走査が木中の任意の深さにあるStaticCallを抽出し、グラフ辺にすることを証明する。
- [x] `GraphCall` と `graphRows_contains_static_calls` で、全規則行のStaticCallを完成したグラフへ保存し、証明済み順位の減少へ接続する。
- [x] `template_static_call_rank_decreases` で、親規則templateにあるStaticCallがグラフ行へ保存されていれば、子候補rule indexの順位が親rule indexより小さいことを明示した。実際の次macroStepがそのtemplate call siteから来たことの証明は未完了。
- [x] `ProcessCertificate.source_static_calls_decrease` で、一般の受理済み停止性証書から各全規則StaticCallの順位減少を再利用可能な定理として取り出す。
- [x] `targetsOfArity` で構文穴が呼び出し先になる位置に同じ引数個数の全規則を候補辺として加え、`findRule_mem_targetsOfArity` で実際の名前検索先の候補所属を証明し、Python順位候補生成とLeanグラフ再計算を一致させる。
- [x] `targetsOfSignature` で名前付き呼び出しも同名・同arityの全規則を候補辺とし、`findRule_mem_targetsOfSignature` で名前検索先が候補に含まれることを証明する。
- [x] `copyWithMacros_match_cases_parts` で複数case形式matchのscrutinee/case走査を分解し、`match_default_body_call_site_at_index_to_next_macro_step` / `match_default_body_call_site_at_index_rank_decreases` で有効なcase prefixの後の任意位置にあるempty-pattern case body callを、multi-case構文の同じtemplate `StaticCall` と順位減少へ接続する。body headのcounter-neutral性、成功copy、copy後callのrule matchを前提とする。非空pattern caseの複数case位置は未対応。
- [x] match_pattern_body_call_site_at_index_to_next_macro_step / match_pattern_body_call_site_at_index_rank_decreases で、複数case形式matchの任意位置にある有効なpattern case body callを、pattern freshening後のrename環境・counterを保ちながらtemplate StaticCall と順位減少へ接続する。counter-neutralなbody head、成功copy、copy後callのrule matchを前提とする。
- [x] match_scrutinee_call_site_at_index_to_next_macro_step / match_scrutinee_call_site_at_index_rank_decreases で、複数case形式matchのscrutinee内にあるcounter-neutralなcallを、成功したmatch copyから抽出してtemplate StaticCall と順位減少へ接続する。copy後callのrule matchを前提とする。
- [x] match_scrutinee_call_site_to_next_macro_step / match_scrutinee_call_site_rank_decreases で、単一case形式matchのscrutinee内counter-neutral callを、成功したcopyからtemplate StaticCall と順位減少へ接続する。
- [ ] 展開された親規則のtemplateから次の実行macroStepへ、同じ `StaticCall` 辺を追跡し、各遷移の親・子rule indexで順位が減ることを証明する。リテラルheadでは `root_template_call_to_next_macro_step` / `root_next_macro_step_rank_decreases` が任意arityを扱う。`copyManyWithMacros_extract_element` は任意位置の要素copyと前後のcopy走査を分解し、`literal_call_at_list_index_to_next_macro_step` は通常のコピー対象リストの任意の兄弟位置にあるリテラルcallを、対象引数のcopy/match条件下で静的辺へ接続する。再帰的な `LiteralCallSite` と `SubstitutedHeadCallSite`、対応する `*_to_next_macro_step` / `*_rank_decreases` 定理は各中間list headの中立性を前提として、任意深さの通常リスト経路にあるリテラルheadと、parameter/hole名が一致する非特殊フォームの置換headを、実match条件下で同じtemplate `StaticCall` と順位減少へ接続する。`copyWithMacros_lambda_parts` / `lambda_body_call_site_to_next_macro_step` と `copyWithMacros_let_parts` / `let_copy_body_call_site_to_next_macro_step` は、それぞれ通常dispatcherで成功したlambda/let全体copyから専用binding処理とbody copy結果を抽出し、body内callをtemplate edgeへ接続する。さらに `BindingRows` / `copyBindingsWithMacros_extract_initializer` / `let_initializer_call_to_next_macro_step` / `let_initializer_call_rank_decreases` は、有効なbinding prefixの後にある任意initializer内の任意深さの通常リストcallを接続する。`CaseRows` / `copyCasesWithMacros_extract_default` / `copyCasesWithMacros_extract_pattern` は、case列の有効なprefixの後の任意位置からdefault/pattern case bodyのコピーを抽出し、pattern fresheningで更新された開始counterも返す。default caseについては `match_default_body_call_site_at_index_to_next_macro_step` / `match_default_body_call_site_at_index_rank_decreases` が複数case matchの任意位置をtemplate `StaticCall` と順位減少へ接続する。pattern caseについても `match_pattern_body_call_site_at_index_to_next_macro_step` / `match_pattern_body_call_site_at_index_rank_decreases` が、pattern freshening後のrename環境とcounterを保って任意位置のbody callをtemplate `StaticCall` と順位減少へ接続する。 `match_scrutinee_call_site_at_index_to_next_macro_step` / `match_scrutinee_call_site_at_index_rank_decreases` はcounter-neutral条件下で複数case形式matchのscrutinee callを同じtemplate callsiteへ接続する。 `match_scrutinee_call_site_to_next_macro_step` / `match_scrutinee_call_site_rank_decreases` は単一case形式matchについて同じ接続を与える。`copyCasesWithMacros_default_parts` / `copyWithMacros_match_default_parts` と `copyCasesWithMacros_pattern_parts` / `match_default_body_call_site_to_next_macro_step` / `match_default_body_call_site_rank_decreases` は単一caseのbody callをcounter-neutral条件下で接続する。特殊フォームとして解釈される穴head、実行macroStep列全体を覆う定理も未証明。
- [x] `nested_literal_call_at_two_list_indices_to_next_macro_step` と `nested_two_indices_next_macro_step_rank_decreases` で、通常リストが二段ネストした任意の兄弟位置のリテラルhead callを、子ruleの実matchを前提に同じtemplate `StaticCall` と順位減少へ接続した。内側list headの中立性が必要で、3段以上・特殊フォーム・展開列全体への一般化は未完了。
- [x] `nested_literal_call_at_three_list_indices_to_next_macro_step` と `nested_three_indices_next_macro_step_rank_decreases` で、通常リスト三段の任意の兄弟位置にあるリテラルhead callも、実matchを前提に同じtemplate `StaticCall` と受理済み順位減少へ接続した。中間list headの中立性が必要で、四段以上・特殊フォーム・展開列全体への一般化は未完了。
- [x] `nested_literal_call_at_four_list_indices_to_next_macro_step` と `nested_four_indices_next_macro_step_rank_decreases` で、通常リスト四段の任意の兄弟位置にあるリテラルhead callを、実matchを前提に同じtemplate `StaticCall` と受理済み順位減少へ接続した。各中間list headの中立性が必要で、五段以上・特殊フォーム・展開列全体への一般化は未完了。
- [x] `LiteralCallSite` で通常リスト中のリテラルcallの任意深さの兄弟位置を帰納的に記述し、path由来のcopy fuel costを定義した。`literal_call_site_to_next_macro_step` と `literal_call_site_rank_decreases` で、各中間list headがcounter-neutralで、コピー済みcallが子ruleにmatchする条件下、任意深さでtemplate `StaticCall` と受理済み順位減少へ接続した。穴head・特殊フォーム経路や展開列全体の停止性を証明するものではない。
- [x] `SubstitutedHeadCallSite` と `substituted_head_call_site_to_next_macro_step` / `substituted_head_call_site_rank_decreases` を追加し、parameter名とcopy hole名の一致、headが `lambda` / `let` / `match` でない条件、中間list headのcounter-neutral性の下で、置換head callも通常リスト中の任意深さから実matchと順位減少へ接続した。特殊フォームheadや展開列全体への一般化は未完了。
- [x] `literal_call_at_list_index_to_next_macro_step`、`LiteralCallSite`、`literal_call_site_to_next_macro_step` / `literal_call_site_rank_decreases` を任意の `Renames` 環境へ一般化した。`copyWithMacros_lambda_parts` / `copyWithMacros_let_parts` は有効なlambda parameter列またはlet binding列と通常dispatcher条件の下で、成功した全体copyを専用copy・rename・body copyへ分解する。`lambda_copy_body_call_site_to_next_macro_step` / `lambda_copy_body_call_site_rank_decreases` と `let_copy_body_call_site_to_next_macro_step` / `let_copy_body_call_site_rank_decreases` はcounter-neutralなbody listと実matchの下で、任意深さの本体callをtemplate edge・順位減少へ接続する。`BindingRows` / `copyBindingsWithMacros_extract_initializer` / `let_initializer_call_to_next_macro_step` / `let_initializer_call_rank_decreases` は、形状が有効なprefix binding列の後の任意initializerへ同じ接続を与える。`CaseRows` / `copyCasesWithMacros_extract_default` / `copyCasesWithMacros_extract_pattern` は、成功した複数case走査の任意位置からdefault/pattern case body copyと、その位置の開始counterを抽出する。これは複数caseの走査分解までであり、match構文内callsiteとtemplate edgeを結ぶ一般定理は未完了。`copyCasesWithMacros_default_parts` / `copyWithMacros_match_default_parts` / `match_default_body_call_site_to_next_macro_step` / `match_default_body_call_site_rank_decreases` と `copyCasesWithMacros_pattern_parts` / `match_pattern_body_call_site_to_next_macro_step` / `match_pattern_body_call_site_rank_decreases` は、単一の空patternまたは有効な非空patternのcase bodyを同じ条件下で接続する。特殊フォームhead、展開列全体の停止性も未完了。
- [x] テンプレート置換・引数挿入・構文木内の文脈・名前生成を含む局所遷移を `CExpansion.Expands.macroStep` と `CMacroCopy.operations` で定義した。C実装の実際のステップとの対応は別項目として残す。
- [ ] 順位の減少と構文処理の進行から、展開処理全体の終了を導く。
- [ ] Cの展開処理との対応を示す。
- [ ] より精密な動的呼び出し解析や、利用者指定の一般的な構造的減少を別の十分条件として設計する。構文穴の呼び出し先については、同じ引数個数を持つ全マクロ規則を候補辺へ加える保守的解析を実装済み。

完了条件: 呼び出しグラフの整礎性を、展開器全体の終了性と取り違えないこと。証明不能はUnknownとし、非停止や入力不正とは判定しないこと。展開サイズ・時間の上界は別に扱う。

追加済みの前提補題: `successful_match_has_signature` は成功した`matchRule`から規則signature・呼び出しhead名・引数数の一致を取り出す。`macro_step_input_is_static_candidate` はrule membershipも仮定して、その実呼び出しをsome targetへの`StaticCall`として導く。`tests/MacroTermination.lean`で具体例を検査する。親マクロのowner/node indexを含む呼び出し元行へ辺を張る合成は未証明のため、上の全macroStep項目は未完了。

## 7. 独立検査器の保証・計算量

- [x] 停止性候補グラフの構文走査・候補辺列挙・順位構築を `--max-conversion-steps` で逐次制限し、予算超過をUnknownにする。これは作業予算であり、ビットサイズに対する漸近上界の証明ではない。
- [x] 停止性解析が作業予算を使い切った場合、Unknown診断へ試行操作数と設定上限を含める。

- [x] 局所展開証書データ型と汎用Boolean検査器を実装し、Cの実例を同じ `check` 関数への入力として受理する。`check_sound` は受理から有限の `CExpansion.Expands` 導出を返す。
- [x] 証書に記録されたfresh counter区間を抽出し、`checkFresh` で区間非重複と `check` の両方を要求する。`checkFresh_sound` は有限展開を導き、区間条件も独立に取り出せる。
- [x] `disjoint_interval_counters_differ` と `checkFresh_separates_interval_counters` を証明し、別々の受理済み区間内のカウンタ値が一致しないことを導く。
- [x] カウンタから生成されるtoken identity `3*n+2` の区別を、上記区間条件から導く補題を追加する。
- [x] 連続して成功する `binder` 呼び出しがcounterを1ずつ進め、異なるtokenを生成することを証明する。
- [x] source tokenが予約済み剰余類に属する場合、単一の成功したbinderが同じsource token identityを生成しないことを証明する。
- [x] Cの生成counterを `3*n+2` が `size_t` に収まる範囲へ制限し、識別子IDの範囲超過を `Unknown` として扱う。
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
- [x] `MacroCounterSafeInitializer.singletonWrapped` と `copyWithMacros_singleton_child_preserves_counter` により、counter保存条件を満たす子を単一要素listで包んだinitializerも再帰的に扱えるようにした。任意の子木形状を許すものではない。
- [x] `MacroCounterSafeInitializer.pairChild` と `copyWithMacros_pair_child_preserves_counter` により、atom headの二要素listでcounter保存条件を満たす子を持てるようにした。通常の特殊フォームを追加で解釈する一般リスト証明ではない。
- [x] `MacroCounterSafeBindingInputs` の具体例で `pairChild` initializerをbinding列の `CounterPreservingBindings` 条件へ合成した。全構文のinitializerを受け入れる一般条件ではない。
- [x] `MacroCounterSafeInitializer.tripleChildren` と `copyWithMacros_triple_children_preserves_counter` で、先頭が `match` / `let` でなく第2要素がatomの場合、第3要素にcounter-preservingな子を持てるようにし、binding列への合成例もLeanで検査した。
- [x] `MacroCounterSafeInitializer.quadrupleChildren` と `copyWithMacros_quadruple_children_preserves_counter` で、先頭が `match` でない4要素listの第4要素にもcounter-preservingな子を持てるようにし、既存のbinding列合成定理からfreshness条件へ渡せることを示した。任意形状の全initializerへ一般化したものではない。
- [x] `CounterNeutralTree` と `counterNeutralTree_preserving` で、headがマクロ名や `match` / `let` / `lambda` でない任意のネスト木（およびatom木）のcopyがcounterを保持することを構造帰納法で示し、`MacroCounterSafeInitializer.neutralTree` から `MacroCounterSafeBindingInputs` のtoken freshness合成へ接続した。この条件はbinder特殊フォームやマクロ呼び出しを含む任意initializerには適用できない。
- [ ] マクロ契約の型付けと、実際の置換・展開証書の型情報を同一モデルへ接続する。
- [x] コメント内の過程記録、Lean本文、検査対象データの対応と信頼境界を整理する（`IMPLEMENTATION.md` の証明書形式・再検証・独立検査の節）。
- [x] 計算量の入力サイズNを、証明書全体の実バイト長からビットサイズ `N = 8B` として定義し、型・識別子・数値の符号化を含める。
- [ ] 検査手続きのコストモデルを定義し、構文走査・環境探索・型照合・局所証書検査の上界を証明する。
- [x] `CMacroCopy.lookupWithCost` と `binderWithLookupCost` に、リスト環境lookupの比較回数とbinderのlookup部分の長さ上界を追加した。`lookupWithCost_miss_scans_all` は失敗lookupの走査回数が環境長と等しいことを示す。Lean 4.8のWSLビルドで `NLisp.CMacroCopy` のコンパイル成功を確認した。構文・型照合・copy全体の費用は未計量。
- [x] `copyParametersWithLookupCost` でパラメータbinder列走査へbinderのhole-lookup回数を合成する。通常の`copyParameters`との結果一致と「パラメータ列長×(hole環境長+1)+1」の上界を追加し、WSL Lean 4.8のビルドで`NLisp.CMacroCopy`成功を確認した。型payload検査・他のcopy分岐は未計量。
- [x] `copyPatternWithLookupCost` で任意マクロ集合の`copyPatternWithMacros` binder列も結果一致させ、同じhole lookup費用上界を追加し、WSL Lean 4.8のビルドで確認した。pattern形状検査・body copy・他のcopy分岐は未計量。
- [x] `copyBindingsWithBinderLookupCost` で任意マクロ集合のlet binding列のbinder走査費を計量し、通常の`copyBindingsWithMacros`との結果一致と同じ列長上界を追加し、WSL Lean 4.8のビルドで確認した。initializer copy本体は実行するが費用を除外する部分モデル。
- [x] `CExpansion.holeEntriesWithCost` は、マクロ引数と仮引数の対ごとに1単位、終端または形状不一致に1単位を課し、通常の `holeEntries` と同じ結果および仮引数数+1の上界を与える。2026-11-21のWSL Lean 4.8 `lake build` で当該モジュールを含む他ターゲットの依存ビルド成功を確認。文字列比較・割当コストと `matchRule` / `copyWithMacros` 全体は未計量。
- [x] `matchRuleWithCost` は浅い規則・呼び出しheadの判定と `holeEntriesWithCost` を合成し、通常の `matchRule` との結果一致、および仮引数数+2の構造上界を与える。2026-11-21のWSL Lean 4.8 `lake build` で当該モジュールを含む他ターゲットの依存ビルド成功を確認。文字列長依存・リスト形状検査のbit/constructorコスト、copy全体は未計量。
- [ ] `ExpansionCertificate.membershipWithCost` は規則一覧の実探索比較回数を数え、長さ以下であることを示す。`checkStepWithMatchCost` は照合費と実際の規則所属探索を接続し、通常の `checkStep` との判定一致と「仮引数数 + 規則一覧長 + 2」の上界を与える。copy本体の実行費は除外し、Leanビルド確認待ち。
- [ ] `checkWithMatchTraversalCost` は局所stepの照合費と`trans` endpoint比較費を証書全体へ合成する。比較結果は通常の `check` と一致し、上界へ証書node走査・trans判定呼び出し・左endpointの構文node数を含める。copy本体とatom payload比較は未計量で、Leanビルド確認待ち。
- [ ] `CMacroCopy.treeNodeCount` / `treeEqWithWorstCaseCost` の保守的な比較費用を `certificateTransComparisonCost` として証書の各transへ合成した。累積費用境界と検査cost上界には全endpoint比較のnode数を明示する。証書byte長への上界接続、atom payload比較のbit costは未完了で、Leanビルド確認待ち。
- [ ] `separatedManyWithCost` / `disjointIntervalsWithCost` でfresh区間検査の実比較費を短絡評価に沿って計量し、`checkFreshWithMatchCost` で規則照合費と合成する。設計上の部分上界は `certificateMatchCostBound rules + n² + n`（nは証書ノード数）。copy本体、構文payload、Natのbit操作は含まず、Leanビルド確認待ち。
- [ ] `certificateMatchCostBound_eq_components` で累積局所費用境界を「証書node数 + macroStepの仮引数総数 + macroStep数×(規則一覧長+1) + trans数 + endpoint比較node総数」へ分解する。全体費用の合成と同じくLeanビルド確認待ち。
- [ ] `certificateMacroStepCount_le_nodes`、`certificateTransCount_le_nodes`、`certificateTransComparisonCost_le_count_mul_max` で、照合費を証書node数・規則一覧長・仮引数総数・最大endpoint構文node数の多項式へ抑える。freshness込みの `checkFreshWithMatchCost_le_endpoint_polynomial` も追加した。最大endpointサイズを証書byte長へ接続する証明、copy本体・atom payload bit costは未完了でLeanビルド確認待ち。
- [x] `ExpansionCertificate.checkWithTraversalCost` / `certificateNodeCount` で、証書コンストラクタのみを数える基礎モデルを定義し、検査結果の一致と費用が証書ノード数以下であることを証明した。endpoint等値判定やmacroStep内部のcopy・照合はこの基礎モデルに含めない。
- [ ] `ExpansionCertificate.checkWithMatchTraversalCost` / `certificateTransCount` / `certificateTransComparisonCost` で、証書走査、trans判定呼び出し、左endpoint構文node比較費を分けて数える。検査結果の一致と費用が `certificateMatchCostBound` 以下となるモデルの費用式を更新した。証書byte長への上界接続・copy本体・atom payload bit costは未完了で、Leanビルド確認待ち。
- [x] `freshIntervalCount_le_nodes` でfresh区間数を証書ノード数以下とし、`intervalPairComparisonCost_le_square` で区間重複検査のpair比較回数を区間数の二乗以下と証明した。Nat比較のビットコストと他の検査工程は未計量。
- [x] `checkFreshStructuralCost_polynomial` で、証書ノード走査とfresh区間pair比較を合わせた部分コストを `n + n²` 以下に合成した。macroStep内部、Natのビットコスト、環境探索、型照合、Lean検査は含まない。
- [x] 共有・キャッシュの扱いを定める。証書は木として直列化し、共有構文は出現ごとに検査し、結果キャッシュは使わない。
- [x] Leanの本文生成・精緻化・カーネル検査と、専用検査アルゴリズムの保証範囲を文書で区別する。
- [ ] 証明対象の範囲について多項式上界を示し、対象外の計算には保証を拡大しない。

補足: `certificateEndpointPayloadNodes` と `certificateMaxEndpointNodes_le_payload` を追加し、証書から再構成される全endpointの構文nodeを集計する尺度を導入した。`checkFreshWithMatchCost_le_payload_polynomial` はこの構造サイズを使う上界を与える設計である。Leanビルド確認待ちであり、シリアライズされた証書byte長への接続やpayload比較のbit費用、copy本体は未完了。

完了条件: 「今回検査できた」「予算付きで動く」「構文ノードだけなら線形」を、検査器全体の多項式時間保証として扱わないこと。元ソースに対して証書が大きくなり得ることと、証書サイズに対する検査時間を区別すること。

## 追加の研究・仕上げ作業

- [x] 証書なしの処理系、再実行方式、独立検査方式を `tools/benchmark_certificates.py` で比較した。現HEADより前の既存Cバイナリによる探索的測定であり、後続C修正を含む再計測値とは区別する。
- [x] 代表例の入力・展開結果・証書サイズ、生成時間、検査時間、サンプルRSSを測定し、`IMPLEMENTATION.md` に記録した。各条件1回の予備的観測。
- [x] 同型の誤束縛・演算すり替え、偽のfreshness、改変した入力・証書、資源超過に対する回帰ケースを追加・整理した。fresh区間の重複拒否テストをLean 4.8で実行確認した。
- [x] `RESEARCH_FORMALIZATION.md`で総合健全性式を未達の研究目標と明記し、確認済みの有限展開・区間分離・条件付きcopy freshness・静的候補グラフと、未証明の全体freshness/非捕捉/型保存/C対応を区別した。性能値は1回の予備測定で多項式計算量の根拠ではない旨も対応文書へ明記した。

## 作業上の注意

- 予算切れは非停止の証明ではない。
- 型が合う出力を生成できることだけでは、元プログラムとの意味保存にならない。
- 証明済みという記載は、本体のLeanファイルと公理監査を確認して更新する。
- モデル更新後の証書は再生成する。古い環境ハッシュの証書を黙って受理しない。
- 今回の追加修正には未ステージのファイルがある。Gitのステージ・コミット・アップロードはユーザー側で行う。
