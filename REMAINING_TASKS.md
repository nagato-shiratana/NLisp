## 作業状況の要約

未チェックの大項目は21件。課題1: 3件、課題2: 1件、課題3: 1件、課題4: 3件、課題5: 5件、課題6: 4件、課題7: 4件。完了済みのチェック項目は一覧から削除し、そこに併記されていた未完了範囲は各節の「既存証明の適用範囲として残る課題」へ移した。細目は重複・粒度が混在するため、大項目数には加算していない。

2026-11-25時点でLean 4.8の全体 `.tools/lean-4.8.0/bin/lake build NLisp` は全46ターゲットで成功した。`polymorphism.nlisp` のpoly証明生成・Lean検査ではraw source decode、関数列との一致、Named評価からPolyIR評価への有限保存定理を検査済み。top-level defineのpoly対応や一般的なソース意味保存など、下記の未完了チェック項目は残っている。詳細と現在の証明範囲は各節のチェックリストを正とする。

2026-11-24時点で `.tools/lean-4.8.0/bin/lake build` は全42ターゲットで成功。`GlobalIR`のlookup補題・initializer/store型不変条件を検証済み。`ExpansionCertificate`のmembership・検査コスト・endpointサイズ上界も全体ビルドで検証済み。`GlobalProgramEntry.lean`にソース順の関数・値宣言型を定義し、値識別子/型列の長さ一致、compiled layout/runtime definition列の長さ一致、重複識別子検査の健全性、値IDからgetter添字へのlayout対応を証明した。型検査済みinitializerを保持する表現と、限定initializer構文についての型付け・GlobalIR erase対応を追加した。`GlobalSourceLowering.lean`はbool/integer/Float/unit、if/begin、lambda/let、Nil/None/Some/Cons、List/Option match、整数演算、局所関数適用、可視なトップレベル関数の参照・呼び出し・明示的`type-app`、値getterを呼ぶ関数適用からなる限定initializer構文を処理し、値置換が宣言ID列・compiled layoutを保つことを単一置換から全値宣言列へ合成した。Float literalについてはdecodeから型付きrow・GlobalIR評価・初期化後のtyped storeへ接続した。証明traceを受け取る`lowerAndReplaceValuesCertified_preserves_runtimeProgramLayout`もlayoutとinitializer数の不変性を導く。lambda/let binderとmatch case binderの識別子をlocal positionへ解決し、Namedの`position`およびlocal lookupへ結んだ。対応する一般source-to-GlobalIR意味保存とpoly証書生成経路への接続は未完了。`NamedArithmeticReflection.arithmeticFragment_evaluation_reflected`でvar/global参照、lambda生成、基本値・List/Option構築・if・整数演算、binder依存枝を含むList/Option match fragmentおよびfragment要素の任意長列、begin・letMany外側コンビネータについてIRからNamedへの評価反映を追加した。poly証明生成器では`polymorphism.nlisp`についてraw source decode成功、decoded source function列との一致、lowered sourceとPolyIRの一致、およびNamedからPolyIRへの有限評価保存証明をLeanで確認した。GlobalIR型保存断片は整数演算、List/Option構築、if、List/Option matchに拡張した。unused-variable警告は残るが、ビルドを妨げない。

Lean変更は機能単位の`CMacroCopy`、`MacroTermination`、`ExpansionCertificate`、`NameLowering`、`GlobalIR`などへ分けている。作業ツリーには未コミットのLean・仕様書変更と未追跡Leanファイルがある。2026-11-24の最新作業ツリーで `.tools/lean-4.8.0/bin/lake build` が全42ターゲット成功した。追加で、`CBindingWalk.acceptsWithLookupCost` / `checkSitesWithLookupCost` / `checkWithLookupCost` が既存判定と一致し、実際のsite lookup比較費用を問い合わせ名・環境の符号長で抑えることを証明した。これはlookup費用部分モデルで、構文走査とscope検査費用を含むchecker全体の上界は未証明。Gitへのcommit/pushは行っていない。

2026-11-25追記: String/Characterの追加をNamed側へ広げ、AST・値・評価規則、de Bruijn lowering/値変換、layout整合走査、well-scoped評価不変条件を拡張した。全45ターゲットの `lake build NLisp` が成功。decoderリテラル読取、C readerのUTF-8/Unicode/NUL対応、文字列操作は未接続。
2026-11-25追記: 全44ターゲットの `lake build NLisp` が成功した。`CTypeArguments.lean` に `cPointerIndex_result_lt_length` と `decodeCType_variable_wellFormed` を追加し、C pointer identity検索の返却slotがLeanのscheme型変数scope内にあることを証明した。さらに `cPointerIndex_same_slot_identity`、`decodeCType_variable_injective`、`decodeCType_variable_slot_identity` を追加し、同じslotへdecodeされるidentityの一意性と、decodeされたslotに保存されるidentityの逆向きを示した。型木全体のdecode単射性・制約走査・呼び出し全体のC実装シミュレーションは未完了。
2026-11-25追記: `CTypeArguments.cMatchType_captures_rigid_caller_variable` を追加した。quantified variableとcaller variableのC pointer array lookupを、C `match_type`のslot更新とLean `collectArgument`のrigid `.var`保存へ同時に接続し、caller pointer列が重複なしならdecodeされた型変数のscope安全性も得る。`lake build NLisp.CTypeArguments` と全44ターゲットの `lake build NLisp` が成功。複合型の引数列全体を通したassignment状態シミュレーション、C実データ構造からpointer列条件を導く証明、C `check_call`全体のシミュレーションは未完了。
2026-11-25追記: `CTypeArguments.cMatchType_list_constraint_step` は、実引数がCのmonotype条件を満たすとき、C/LeanのList型制約収集がそれぞれ1 fuel減らして子型へ進む定義等式と、List型nodeのdecodeをまとめる。`lake build NLisp.CTypeArguments` および全44ターゲットの `lake build NLisp` が成功。これはList一段の構造対応であり、Option/Function型、引数列全体のassignment対応とC `check_call`の実メモリ状態simulationは残る。
2026-11-25追記: `CTypeArguments.cMatchType_function_constraint_step` は、Function型制約でC `cMatchTypes` とLean `collectArguments` がparameter列を走査してからresult制約へ進む分岐を明示し、arity成立時のdecode結果も同時に示す。`lake build NLisp.CTypeArguments` および全44ターゲットの `lake build NLisp` が成功。これはFunction節の一段の構造対応で、recursive assignment relationを最後まで合成する一般simulationとC `check_call`実装全体は未完了。
2026-11-25追記: `decodeCTypes_length` はCの型配列をLean型列へdecodeしたときの長さ保存を示す。`cMatchType_rejects_function_arity_mismatch` はC `match_type`のfunction parameter数guardとLean `collectArguments`の同期走査が同じ不一致を拒否し、成功decodeの下でresult型を含むconstructor対応も保つことを証明する。`lake build NLisp.CTypeArguments` と全44ターゲットの `lake build NLisp` 成功。型引数制約の再帰全体とC `check_call`のstate simulationは未完了。
2026-11-25追記: `cSubstituteVariable` はC `substitute_type`のquantified-pointer lookupをモデル化し、`cSubstituteVariable_matches_Lean_inferred_argument` は同じslotでCのsubstitution arrayとLean `Ty.instantiate`が同一のcaller typeを選ぶことを示す。`lake build NLisp.CTypeArguments` と全44ターゲットの `lake build NLisp` 成功。複合型全体の代入可換性および制約収集結果からこのassignment correspondenceを導く一般simulationは未完了。
2026-11-25追記: `cSubstituteVariable_preserves_rigid_caller_variable` はquantified schemeに属さないcaller pointerをC substitutionが保持し、Lean側ではquantified prefix分のde Bruijn offsetを除去して同一caller slotを得ることを示す。`lake build NLisp.CTypeArguments` と全44ターゲットの `lake build NLisp` 成功。これら単一variable補題を複合型のsubstitution関数と `check_call` の推論stateへ合成する一般定理は未完了。
2026-11-25追記: 再帰モデル`cSubstituteType` / `cSubstituteTypes`とassignment対応predicate`CSubstitutionRowsAgree`、定理`cSubstituteType_decodes_to_instantiate`を追加した。対応するassignment rowが各quantified slotで与えられれば、CのList/Option/Functionを含む型木置換結果がLean `Ty.instantiate`とdecode上で一致する。`lake build NLisp.CTypeArguments` と全44ターゲットの `lake build NLisp` 成功。制約収集結果から`CSubstitutionRowsAgree`を生成する一般simulationとC `check_call`全体は未接続。
2026-11-25追記: `CSubstitutionStateAgree` と `cSubstitutionStateAgree_first_capture` を追加し、未割当slotを含むC/Lean substitution配列のpointwise対応を定義した。空slotへの同時初回captureが配列長と全slotの対応を保つことを証明する。`lake build NLisp.CTypeArguments` と全44ターゲットの `lake build NLisp` 成功。既存slotの一致分岐を含む`cMatchType` / `collectArgument`の全遷移と複合型再帰への合成は未完了。
2026-11-25追記: `CTypeArguments.cMatchType_matches_Lean_rigid_variable_repeat` は、Cの2つのcaller型変数nodeが同一Lean `.var` slotへdecodeされることからC pointer identityの一致と構造比較の受理を導き、C/Lean両constraint collectorが既存代入を保持することを示す。`lake build NLisp.CTypeArguments` と全44ターゲットの `lake build NLisp` が成功。型木全体のdecode-comparison完全性と複合引数列のassignment状態simulationは未完了。
2026-11-25追記: `CTypeArguments.cMatchType_rejects_decoded_variable_conflict` は、Cの構造比較soundnessとprevious/actual両nodeの成功decodeから、Lean型が異なる場合のC比較拒否を導き、同じ繰り返し制約でLean collectorも拒否することを示す。`lake build NLisp.CTypeArguments` と全44ターゲットの `lake build NLisp` が成功。型木全体の比較完全性と複合argument列・C `check_call`状態の一体simulationは未完了。
2026-11-25追記: `CTypeArguments.cMatchType_option_constraint_step` を加え、Option型wrapperでもC/Leanの制約収集が子型へ一段fuelを減らして進み、decode結果が対応することを証明した。`lake build NLisp.CTypeArguments` と全44ターゲットの `lake build NLisp` が成功。List/Option/Functionそれぞれの局所構造caseはあるが、相互帰納による任意型木・引数列全体のassignment simulationとC `check_call`実装への接続は未完了。

2026-11-25追記: `GlobalIR.assembled_global_value_read_preserves_type` を追加した。slot型に合う初期化済みstore、`assembleProgram`のgetter layout、`lowerGlobalReads`によるglobal値参照から、実行結果の`ValueTyped`を結ぶ。`lake build NLisp.GlobalIR` 成功。これはGlobalIRのgetter経路の型保存補題であり、一般評価器・関数呼出し・課題5の拡張型を含む型安全性定理は未完了。

2026-11-25追記: `ContextualGlobalArithmeticTerm` と `evaluate_contextualGlobalArithmeticTerm_preserves_type` を追加した。既存のcontextual arithmetic/local-variable fragmentに、`GlobalProgramTyped` layoutから得るglobal function referenceを加え、同じ型保存定理で扱う。`lake build NLisp.GlobalIR` 成功。global call、getter結果、任意Surface式への一般化は未完了。

2026-11-25追記: `GlobalSourceLowering.readClosedInitializer_valueReference_runtime_type_safe_or_early_read` を追加した。source-visible value identityのdecode、混在entry layout、実行definition tableのgetter、store型とslot数を接続し、GlobalIR評価結果がslot型を持つか、該当slotの`beforeInitialization` faultになることを示す。`lake build NLisp.GlobalSourceLowering` 成功。これはglobal値参照atomの局所結果で、任意initializer評価・Cのstep-by-stepシミュレーション・全体source-to-GlobalIR意味定理は未完了。

2026-11-25追記: `GlobalProgramEntry.toDefinitions_function_of_layout` と `GlobalSourceLowering.readClosedInitializer_sourceVisibleFunctionReference_runtime_evaluates` を追加した。source-visible function identityから得たmixed-table indexがruntime `Definition.function` indexと一致し、erased global referenceが任意store上で同じ`.global index`値へ評価される。`lake build NLisp.GlobalSourceLowering` 成功。関数本体の適用評価simulationやCのstep全体との対応は未完了。

2026-11-25追記: `readClosedInitializer_sourceVisibleFunctionReference_runtime_typed` を追加した。混在`compiledLayout`から得る関数signatureを`GlobalProgramEntry.signatures`の同じindexへ射影し、runtime参照評価の結果をその型の`ValueTyped`へつなぐ。`lake build NLisp.GlobalSourceLowering` 成功。実際の関数適用、generic specialization後のcall結果、C評価step全体とのsimulationは未完了。
2026-11-25追記: `globalIndexOf_get?_unique` と `mixed_value_identity_and_getter_index` を追加した。binding identityが一意な混在entry列では、宣言位置からのidentity lookupとGlobalIR getter mappingが同じsource indexを返す。`lake build NLisp.GlobalProgramEntry` 成功。C側の共有binding node・実際のname lookup/evaluation stepとのシミュレーション、およびdecode成功からの実行layout/initializer条件構成と全体意味保存は未完了。
2026-11-25追記: `decodeTopLevelProgram_layout_and_initializer_conditions` はdecode成功から実際の混在header layoutを存在証明として取り出し、返却されたslot型列がheader値宣言の型列と一致すること、initializer数がslot数と一致すること、関数本体のprogram well-scopedと各initializerのlet-layout整合を一つの補題で得る。`GlobalSourceLowering.decodedTopLevelProgram_checkedRows_globalIR_layout` はこのdecode由来条件と、Entry表の型slot列一致・initializer checker scan成功から、`TypedInitializerRows`および実際の`toRuntimeProgram`に対する`GlobalIR.InitializerTypesAgree`を同時に構成する。`lake build NLisp.NamedDecoder`、`lake build NLisp.GlobalSourceLowering`、全44ターゲットの`lake build NLisp`が成功。decode済みNamed initializer列からGlobalProgramEntryのSurface initializer列への同一性・変換証明と、C境界の意味保存はまだ仮定・未接続。
2026-11-25追記: `sourceValueSlotOrdinal_initializer_lookup` はCの混在Program添字からdense value slotへ変換した結果が、GlobalIRのinitializer列において同じ宣言由来のerase済みinitializerを指すことを証明する。関数宣言を飛ばす場合と先行valueを数える場合を帰納的に処理した。`lake build NLisp.GlobalProgramEntry` 成功。Cの実行step全体と値cell更新のシミュレーションは未接続。
2026-11-25追記: `sourceValueSlotOrdinal_successful_initialization_populates` は上記initializer添字対応をGlobalIRの逐次初期化成功へつなぎ、Cの混在宣言添字で選んだ値宣言に対応するdense slotが初期化後に値を保持することを示す。`lake build NLisp.GlobalProgramEntry` 成功。Cの実コードstep遷移・共有RBind cellとの完全シミュレーションは未完了。
2026-11-25追記: `sourceValueSlotOrdinal_successful_getter_reads` は混在Program添字から生成layout内のgetter entryを特定し、対応slotの初期化後store値を同じ添字の0引数GlobalIR getterが返すことを証明する。initializer列での宣言対応、初期化後のstore存在、getter table位置を合成した。`lake build NLisp.GlobalProgramEntry` 成功。Cの実`rfind`・`eval`ステップとGlobalIR評価のsimulationは未完了。
2026-11-25追記: `CNameResolution.readName_after_other_cell_write` と `captured_environment_other_cell_write` は、Cのfront-first name searchで選ばれたbinding identityとは別の共有RBind cellを更新しても、捕捉環境からその名前で読む値が変わらないことを証明する。`lake build NLisp.CNameResolution` と全44ターゲットの `lake build NLisp` 成功。実Cの命令遷移とGlobalIR全体store間のsimulationは未完了。

2026-11-25追記: `readClosedInitializer_sourceVisibleTypeAppFunction_runtime_typed` を追加した。C構文上の明示type-appのdecode、mixed-table関数layout、erased runtime global評価、呼び出し側assignment下で型引数をinstantiateした関数の`ValueTyped`を結ぶ。型引数arityとsignature well-formednessはlayout条件として明示する。`lake build NLisp.GlobalSourceLowering` 成功。引数評価を含むcall全体とC `check_call` state simulationは未完了。

2026-11-25追記: `evaluate_contextual_zero_arity_global_call_preserves_type` を追加した。GlobalIR table entryが0引数functionであり、bodyがglobal referenceも許すcontextual arithmetic fragment内にある条件で、body評価からゼロ引数call評価を合成して結果型を保存する。十分なfuelを前提に明示した。`lake build NLisp.GlobalIR` 成功。任意arity・一般Surface body・全評価器の型安全性は未完了。

2026-11-25追記: `ContextualGlobalArithmeticTerms` と `evaluate_contextualGlobalArithmeticTerms_preserves_type` を追加し、global function referenceを含む任意個の引数評価から値列の型を導く。`evaluate_contextual_global_call_preserves_type` はこの結果をbodyのcontext typingへつなぎ、十分なfuel・arity一致・typed fragment bodyの下で任意arity GlobalIR callの結果型を保存する。`lake build NLisp.GlobalIR` 成功。任意Surface body・getterを含むcall全体・GlobalIR一般評価器の型安全性は未完了。


## 次に進める実装順

1. **ビルドを安定させる**: 2026-11-24の最新作業ツリーではLean 4.8の全42ターゲットビルドが成功している。後続の証明追加ごとに全体ビルドを再実行し、通過を確認するまでは関連する残課題を完了扱いにしない。
2. **トップレベル値とGlobalIR**: decode結果からtyped runtime table/store条件を構成し、initializerの評価型を導出する。GlobalIR評価器の型保存とsource/Cとの意味対応を個別に進める。
3. **Named意味論の反映と総合定理**: decoderが保証するbinder/layout条件を使い、評価全体の逆向き反映を合成する。その後にエラー・発散の対応と有限展開証書を含む主定理を組み立てる。
4. **残る型保証**: C型引数推論とLean制約モデルを一般対応付けする。Float/String/Characterおよび全組み込み関数の仕様・評価・型安全性を拡張する。
5. **macro copyのC対応**: Leanのcopy状態遷移とC `copy_template`の一段シミュレーションを定義し、binder freshnessと非捕捉を全構文へ合成する。
6. **停止性・独立検査の統合**: template callsiteから次の実macroStepまでのシミュレーションを完成させて終了性を示す。freshness・型保存・構文対応の健全性定理を統合し、コストモデルを証書byte長へ接続する。

順序は、現時点の依存関係と直近のビルド阻害要因に基づく。各保証はLean証明・C対応・文書の証拠が揃った範囲だけ完了にする。


## 現在の到達点

2026-11-25追記: `CTypeNode` にC runtimeの`.floating`・`.string`・`.character`型constructorを追加し、それらをLean `Ty.float`・`Ty.string`・`Ty.character`へdecodeする定義を整合させた。well-formedness、C substitution対`Ty.instantiate`、monotype判定、型比較のdecode一致および制約器の反射性を拡張し、`lake build NLisp.CTypeArguments` 成功。これはTask 5の型表現部分とTask 3のC/Lean型ノード対応の前進であり、Cの全constraint walkとLean推論器の一般シミュレーションは未完了。
2026-11-25追記: `CPrimitiveType` と `cMatchType_primitive_simulation` を追加した。Cのboolean/integer/float/string/character/unit制約は、成功時に代入状態を変えず、C構造比較のdecode一致からLean `collectArgument` も同じ型でno-op成功する。`lake build NLisp.CTypeArguments` 成功。quantified variableのcapture/repeat/conflict、List/Option/Functionの再帰制約を含む全constructorの局所step合成はまだ未完了。
2026-11-25追記: `cMatchType_variable_state_simulation` はdecode済みscheme変数に対するC matcher成功を、Leanの同一de Bruijn slot制約へ一般に対応づける。空slotの初回captureと既存slotのrepeatを分け、`CSubstitutionStateAgree`を両ケースで保存する。`lake build NLisp.CTypeArguments` 成功。List/Option/Functionの再帰stepと全constructorの関数引数列シミュレーションは未完了。
2026-11-25追記: `CAtomicConstraintPattern` と `cMatchTypes_atomic_state_simulation` を追加した。型引数parameterがprimitive leafまたはquantified variableだけからなる場合、Cの成功した左から右の引数matcherをLean `collectArguments` と状態不変条件へ合成し、単一step前提を不要にした。`lake build NLisp` 全45ターゲット成功。List/Option/Functionでネストしたparameterに対応する一般simulationは未完了。
2026-11-25追記: `cMatchType_list_atomic_state_simulation` と `cMatchType_option_atomic_state_simulation` はprimitive/quantified leafを一段包むListまたはOption制約についてC成功matcherからLean collectorへの型・状態simulationを構成する。`lake build NLisp.CTypeArguments` 成功。任意深さの相互再帰とFunction型引数列を含む完全対応は未完了。
2026-11-25追記: `cMatchType_and_types_state_simulation` は単一型matcherと型列matcherをfuelについて相互帰納し、primitive、変数capture/repeat、任意深さList/Option、Function引数列と結果型について、成功するC制約走査からLean collector成功と`CSubstitutionStateAgree`保存を導く。C/Lean型decode成功を前提として全C型形状を扱う。`lake build NLisp` 全45ターゲット成功。C `check_call` の未代入slot拒否、呼出元型変数、結果型置換まで含む決定手順の統合定理は引き続き接続中。

| 課題 | 検証・実装済み | 主な残り |
| --- | --- | --- |
| 1. 展開後構文からIRへの意味保存 | 元構文とIRの独立照合、束縛ID意味論からIRへの有限評価の前向き保存 | well-scopedソース条件付きの逆向き評価反映、エラー・発散の対応 |
| 2. 新多相モデルの型安全性 | 評価結果の型保存、参照切れ・引数個数違い・形状違いの排除、型検査器の受理結果との接続 | 小ステップProgressを主張する場合の簡約関係と証明、拡張モデルへの適用 |
| 3. 一方向型引数決定 | Lean推論器の成功結果の健全性・一意性、Surface型検査器の十分fuel下の完全性と計算可能な構造上界、候補条件下の型引数決定完全性、C型matcherからLean collector・代入状態・戻り値instantiateへの抽象全constructor成功simulation | C実`Type*` / `check_call`メモリ状態との対応、Lean成功からC matcher成功への完全性、候補条件なしの型引数決定完全性 |
| 4. トップレベル値・初期化 | Cの共有セルと脱出クロージャの修正、注釈付きdefineのGlobalHeader読み取り、GlobalIR実行モデル、初期化セルの保存・充足の証明 | defineのpoly証書・GlobalIR経路への接続、変換の意味保存、GlobalIRの型安全性、C対応 |
| 5. 全型・組み込み関数 | C処理系と旧型付けモデルは全26組み込み関数に対応 | 新評価モデルへのFloat/String/Character・演算の追加と証明 |
| 6. マクロ展開全体の終了性 | 名前・arity一致の全直接候補と穴頭位置の同arity候補辺の整礎性・呼び出し鎖上界、成功する有限fuel走査の抽出網羅性、全規則行を含むgraphへの保存と証書順位の減少、候補生成作業の予算制限 | 実際のmacroStep列との対応、展開アルゴリズム全体へのシミュレーション・終了性の接続 |
| 7. 独立検査器の保証・計算量 | C展開器を起動しない検査、個別の構文・束縛・型付け・意味保存の検査、整数の数値に依存しない型消去尺度、局所展開証書の区間非重複検査、区間内counter/token非衝突、連続binder呼び出しのtoken一意性、単一binderとsource tokenの非衝突、`copyParameters`・`copyPattern`と空マクロ集合かつ`CounterSafeInitializer`条件下の`copyBindings`のtoken列一意性・source token非衝突・fresh区間内所属、別々の受理済み区間に属するこれらの出力間の非衝突、任意マクロ集合のatom・制限付きatom-only list・binder特殊headを含まない任意ネスト木のcounter保存、`MacroCounterSafeBindingInputs`条件下のtoken列一意性・source-token分離・区間所属および受理済み証書区間間の非衝突、initializerのcounter保持条件からbinding列へfreshnessを合成する一般定理、要素別前提から任意の`copyMany`走査へcounter保持を合成する定理、counter-preserving case body条件下の`copyCases` pattern token列・一意性・source-token分離・区間所属・証書区間間非衝突、`MacroCounterSafeCases`条件下の区間分離 | binderを含むinitializerを含む全構文への拡張、case bodyのcounter保存を導く構造的証明、全体`copy`の結果への合成、C `copy_template`とのシミュレーション、counter境界の全体統合、入力識別子との非衝突のcopy全体への合成、全検査過程の合成的健全性、証書のビットサイズに対する計算量上界 |

新しい意味保存・型安全性・型検査器の完全性の対象型は、Boolean、Integer、Unit、関数、List、Optionである。C実行器全体の正しさを証明したとは扱わない。


## 1. 展開後構文からIRへの意味保存

実装済み: `ExpansionLowering.lean`、`NamedSemantics.lean`、`NamedDecoder.lean`、`NameLowering.lean`。

- [ ] デコーダ／型検査が保証するwell-scopedソース条件（特にletManyのbinder数）と、プログラム・捕捉環境内closureの不変条件を明示した上で、型付きIRの終了評価からNamed評価を構成する一般逆向き定理を証明する。
- 2026-11-25追記: `ArithmeticFragmentRows` と `arithmeticFragmentRows_arguments_reflected` は各initializerのfragment証拠から任意長の引数評価列をNamed評価列へ反映する。`arithmeticFragment_letMany_evaluation_reflected` はこれを任意binder数のletManyへ合成し、識別子・initializer数一致と各initializer/bodyのfragment条件の下でIRの有限評価導出からNamed導出を構成する。`decodeExprChecked_arithmeticFragment_letMany_evaluation_reflected` はさらにchecked decoder成功からbinder数一致を取り出し、追加arity前提なしで同じNamed導出を構成する。`lake build NLisp.NamedArithmeticReflection` 成功。`decodeExprChecked_arithmeticFragment_letMany_termination_iff` / `_divergence_iff` はchecked decodeを前提に、有限big-step終了および有限導出不存在としての非停止を同じfragmentで両方向に対応させる。対象モジュールbuild成功。これは`letMany`一構文を含むfragment限定定理で、decode済み一般式・任意構文への逆向き定理は未完了。`NamedDecoder.programWellScoped` と再帰的な `ValueWellScoped` / `EnvironmentWellScoped` を定義し、decode成功からプログラム不変条件を得る `decodedProgram_wellScoped`、top-level混在宣言から関数・initializer双方の整形式性をまとめる `decodeTopLevelProgram_wellScoped`、lambda closure生成の不変条件、binding/捕捉環境結合の `environmentWellScoped_bind_append`、環境lookupによるclosure不変条件の保存を示す `environmentWellScoped_lookup` を追加した。`evaluation_preserves_valueWellScoped`はwell-scoped環境とlet layout整形式性の下でNamed有限評価が返すclosureを含む値の不変条件を保存する。`decodeProgram_body_evaluation_preserves_valueWellScoped`と`decodeTopLevel_initializer_evaluation_preserves_valueWellScoped`はdecode成功から取り出した関数本体・initializerを有限評価した結果へ不変条件を接続する。`program_lookup_body_wellScoped`はwell-scoped programのlookup済み定義本体へ整形式性を射影し、`closureApplication_environment_wellScoped`はclosure本体の整形式性と、引数評価値・captured environmentから適用時環境の整形式性を合成する。`letLayoutsAlignedList_mem` と `letLayoutsAligned_{app_parts,lam_body,ite_parts,letMany_parts,begin_parts,add_parts,sub_parts,mul_parts,le_parts,intEq_parts,cons_parts,some_body,matchList_parts,matchOption_parts}` も追加し、式リスト要素・再帰子式・letMany binder数の条件を評価反映の再帰ケースへ射影できるようにした。さらに`expressionChildren` / `letLayoutsAligned_children`を追加し、全Named Expr constructorについて、即時子式への整形式性伝播を一つの定理にまとめた。これらは一般評価反映への接続前の基礎補題であり、逆向き定理は未証明。binder ID数が不一致の任意Exprにはこの主張は成立しない。
2026-11-25追記: `IdentityScoped` / `IdentityScopedList` でNamed identity式の字句binder scopeを全constructorにわたって定義した。`position_eq_length_of_not_mem` と `position_lt_length_of_mem` は、binder identityが存在しないときに下げ先が環境長になり、存在するbinderなら有効な添字となることを示す。`ValueIdentityScoped` / `EnvironmentIdentityScoped` はcaptured environment identityに対するclosure body scopeを表し、binding/captured environment結合の保存とlambda closureへの構成補題も追加した。CBindingWalkの受理証書・decoder成功からこれらのscope関係を導く補題、およびIdentityScopedを使った一般評価反映への接続は未完了。
2026-11-25追記: `CBindingWalk.accepts_selected_identity_in_caller` から、受理済み参照siteのselected identityがcaller binding identity列に属することを示し、`acceptedSite_variable_identityScoped` でそのsiteが表す単独変数Exprの`IdentityScoped`証明を構成した。node tree全体をwalk resultと対応させてscope証明を合成する定理、およびdecode成功からNamed定義/initializer全体へ接続する定理は未完了。
2026-11-25追記: `CBindingWalk.check_selected_identities_in_caller` は成功した全体scope checkからreferencesの成功結果を保持し、抽出されたすべてのreference siteについてacceptanceとselected identityのcaller membershipを一括して与える。`acceptedCheck_reference_sites_identityScoped` はこの結果を各siteのNamed variable leafへ変換する。これはsite一覧の健全性であり、対応する各Nodeからdecodeされた複合Exprのbinder scope全体を構成する証明は未完了。
2026-11-25追記: `CompositionalReflectionFragment` を追加し、Arithmetic、任意arity application、任意長begin、arity整合済み任意長letManyの既存反映補題を `compositionalReflection_evaluation_reflected` に統合した。これにより同fragment上の終了同値と有限big-step導出不存在としての非停止同値も一つの定理から得られる。さらにwell-scoped program/environmentとlet layout整合性の前提を加えた `compositionalReflection_evaluation_reflected_scoped` は、反映されたNamed結果がclosureを含む `ValueWellScoped` を満たすことを示す。対象モジュールbuild成功。fragmentはなお全Expr構文を覆わず、decode成功から任意式のIdentityScoped証拠を構成して一般反映へ接続する課題は残る。
2026-11-25追記: `CheckedCompositionalInitializer` と `checked_compositional_initializer_main` / `_with_value` を追加し、上記fragmentに属する任意のトップレベルinitializerについて、decode由来のprogram/let-layout不変条件を反映条件へ渡して、読取・有限展開・freshness・束縛対応・型付け済みinitializer一覧・終了/非停止同値を一つの証書の主定理に統合した。値を得る場合はclosure scope safetyも返す。`lake build NLisp.CertifiedArithmeticReflection` 成功。この統合も現在証明済みのfragment範囲に限られ、一般Named式やGlobalIR初期化状態への意味シミュレーションを証明したものではない。
- [ ] Fault対応を元C構文の読取・有限展開・Named identity loweringを通したsource-to-GlobalIR定理へ接続し、top-level initializer faultも統合する。現状の証明範囲はSurfaceからerasure IRまでであり、C境界とGlobalIR初期化経路は未接続。
- 2026-11-25追記: `GlobalIR.run_reports_initializer_fault` は初期化列で返ったfaultがentry function評価より前にprogram実行結果へ伝播することを示す。`lake build NLisp.GlobalIR` 成功。これはGlobalIR内のfault伝播だけで、Surface/Named/Cのinitializer faultを同じfaultへ対応付ける証明は未接続。
- 2026-11-25追記: `GlobalIRErrorCorrespondence.unbound_variable_fault_corresponds_to_globalIR` は、source環境とそのerase済み値環境の双方で同じlocal indexが欠落する条件から、Surface evaluatorの`.unbound`とGlobalIR evaluatorの`.core .unbound`が同値であることを示す。`eraseValues_lookup_none` が欠落indexを値erasure越しに保存する。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。これはlocal variable一構文のfault対応で、global/app/shape/arity fault、Named/C変換、initializer faultとの統合は未完了。
- 2026-11-25追記: `functionTable_globalIR_leaf_commutes` はfunction-only tableのPolyIR/GlobalIR間でleaf項の評価を任意fuel・environment・storeについて対応させる。対象はlocal/global lookup、Boolean/Integer/Float/String/Character/Unit、lambda、Nil/Noneで、out-of-fuelとunbound faultも`.core` wrapper越しに一致する。`functionTable_map_lookup` がfunction definitionへのlist mappingでglobal indexを保存する。対象モジュールbuild成功。再帰的constructor、ArgumentsEvaluate/SequenceEvaluateおよびmixed getter layoutの全体simulationは未完了。
- 2026-11-25追記: `application_function_fault_propagates_to_globalIR` と `application_arguments_fault_propagates_to_globalIR` は、対応する関数評価faultまたは関数成功後の引数列faultがapplication全体へ伝播し、GlobalIR側では`.core` faultとなることを証明する。対象モジュールbuild成功。関数/引数子評価のsource/runtime対応は前提であり、一般評価の再帰simulationとC/initializer接続は未完了。
- 2026-11-25追記: `global_function_wrong_arity_fault_corresponds_to_globalIR` はsource global signatureとruntime functionのarity一致、および関数・引数評価のerasure対応から、成功した引数列のarity不一致に対するSurface/GlobalIR fault同値を示す。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。C/Named変換からこれらの評価対応を導く全体simulationとinitializer接続は残る。
- 2026-11-25追記: `unbound_global_reference_fault_corresponds_to_globalIR` はsource/GlobalIR双方の宣言表で同じglobal indexが欠ける条件の下、Surface `.global` とerased GlobalIR `.global`の`.unbound`を同値にする。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。値globalのgetter変換と全体のNamed/C fault simulationは別途未接続.
- 2026-11-25追記: `add_wrong_shape_fault_corresponds_to_globalIR` は、左右子式のSurface評価とGlobalIR評価がerase値で対応し、結果が両方とも整数ではないとき、加算のSurface `.wrongShape` とGlobalIR `.core .wrongShape`を同値にする。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。左右子式の評価対応が明示前提で、一般式・ほかの演算・Named/C変換への統合は残る。
2026-11-25追記: `floatBin_wrong_shape_fault_corresponds_to_globalIR` はFloat加減乗除すべてで、対応する子評価とnot-both-floats条件からSurface/GlobalIRのshape faultを一致させる。`readClosedInitializer_floatBin_wrong_shape_fault_corresponds_to_globalIR` は実際のannotated node readerを通してこの結果へ接続する。全45ターゲット `lake build NLisp` 成功。子評価対応は前提であり、C実行器およびinitializer fault全体とのsimulationは未接続。
2026-11-25追記: `sub_wrong_shape_fault_corresponds_to_globalIR` を追加し、整数減算についても対応する子評価と「両方とも整数ではない」条件からSurface/GlobalIRの`.wrongShape`一致を証明した。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。一般の式意味対応と残り整数演算への統合は未完了。
2026-11-25追記: `mul_wrong_shape_fault_corresponds_to_globalIR` を追加し、整数乗算にも同じ限定条件で`.wrongShape`対応を証明した。対象モジュールのLean build成功。比較・整数等値・一般faultシミュレーションは未完了。
2026-11-25追記: `le_wrong_shape_fault_corresponds_to_globalIR` を追加し、整数以下比較でも両オペランドのshape不一致時のfault対応を証明した。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。整数等値と一般式への合成は引き続き未完了。
2026-11-25追記: `intEq_wrong_shape_fault_corresponds_to_globalIR` を追加し、整数等値を含む整数二項演算5種類すべてに、子評価対応を仮定したshape fault同値を用意した。対象モジュールbuild成功。成功値・子fault・呼出し/arity faultを含む評価器全体のシミュレーションとC・initializer接続は未完了。
2026-11-25追記: `closure_wrong_arity_fault_corresponds_to_globalIR` はSurface/GlobalIRで関数と引数列がerase越しに対応して評価され、関数が同じclosure body・captureを持ち、arityが不一致の場合に、両評価器の`.wrongArity` faultが同値であることを証明する。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。任意function kind、呼出し元評価対応の導出、一般意味シミュレーションおよびC/initializer統合は未完了。
2026-11-25追記: `readClosedInitializer_intEq_wrong_shape_reports_run_fault` は、reader出力がbool/intを比較するinitializerである場合、そのSurface評価の`.wrongShape`と、GlobalIRの最初のinitializer faultおよび`run`結果を接続する。`lake build NLisp.GlobalSourceLowering` 成功。readerの成功結果は前提として与え、C字句入力からの具体的読取証明、任意initializer列への一般化、Named評価は未接続。
2026-11-25追記: `readClosedInitializer_intEq` はannotated nodeのbuiltin ID 24・`integer=`名・operandの読取・可視function未解決条件からSurface `intEq`構文を構成する。`readClosedInitializer_intEq_builtin_wrong_shape_reports_run_fault` はこのreader規則をfault/run定理へ直接合成する。対象モジュールbuild成功。C source bytesのparseからのreader前提導出や、一般fault・initializer列への一般化は残る。
2026-11-25追記: `FunctionTableIntegerBinary` と `functionTable_globalIR_integerBinary_commutes_of_pointwise` を追加し、function-only table上のPolyIR/GlobalIR実行対応を加算だけでなく減算・乗算・整数比較・整数等値へ一括一般化した。左右子評価の対応から、成功値・wrong-shape fault・child faultを含む式全体の結果同値を導く。`.tools/lean-4.8.0/bin/lake build NLisp.GlobalIRErrorCorrespondence` 成功。これはPolyIR-erased termとfunction-only GlobalIR table間の条件付き補題で、Surface/Named/C入力の評価対応を導くものではなく、mixed getter tableにも未接続。
- [ ] 非停止を有限big-step評価導出が存在しないこととして `SourceDiverges` / `LoweredDiverges` に定義した。`termination_preserved_and_reflected` と `divergence_preserved_and_reflected` は評価反映を仮定すれば終了・非停止が同値であることを示す。さらに `typed_closed_divergence_iff_fuel_exhaustion` は、閉じた型付きSurface式では有限評価導出がないことと、全てのfuelで `.outOfFuel` となることを同値にした。`arithmeticFragment_termination_preserved_and_reflected` と `arithmeticFragment_divergence_preserved_and_reflected` は前向きerasure simulationと逆向きfragment反映を合成し、Named算術fragmentの有限終了・非停止を両方向に対応させる。`CertifiedArithmeticReflection.checked_initializer_main`はsource読取・展開・scope証書とこの有限終了/非停止対応をclosed arithmetic top-level initializerについて統合する。追加の`CheckedGlobalCallInitializer` / `checked_global_call_initializer_main` は、decode済みinitializerがfragment条件を満たすglobal関数を呼ぶ場合、任意arityのcallについて同じsource読取・有限展開・scope correspondence・freshnessと有限終了/非停止同値を一つの証書主定理へまとめる。`checked_global_call_initializer_value` は有限評価反映と返却closureのwell-scoped性も得る。対象モジュールbuild成功。一般Named評価反映 `EvaluationReflection` 自体の証明、well-scoped decoded source全体への一般化、GlobalIR初期化器との非停止対応は未完了。

完了条件: 展開後構文からIRまで、値・終了・対象とするエラー・非停止の対応を、保証範囲を限定した一般定理で説明できること。



### 既存証明の適用範囲として残る課題
  - いずれも限定fragmentの範囲であり、一般EvaluationReflection、C top-level define/initializerとの統合、decode・型付けwell-scoped条件からの一般化は未完了。
  - これは変数ケースだけであり、評価全体の反映は未証明。
  - IR評価全体の逆向き定理は未証明。
  - クロージャ適用を含む一般の評価反映は未証明。
  - これらを使うクロージャ適用の評価反映は未完了。
  - これは個別の演算子ケースであり、全式の逆向き定理は未証明。
  - 演算子ケースの補題であり、全式の逆向き定理は未証明。
  - これは条件分岐ケースであり、全式の逆向き定理は未証明。
  - リスト・オプションcase分析やクロージャ適用を含む全式の証明は未完了。
  - 任意要素の反映証明を前提とする補助定理であり、全式の逆向き定理は未証明。
  - IRがbinder ID数を消去するためこの整形式条件を明示しており、これを含む一般の全式定理は未証明。
  - matchOptionと全式の逆向き定理は未証明。
  - 全式の逆向き定理は未証明。
  - これは相互帰納法のアプリケーション各ステップであり、`EvaluationReflection` 自体の証明は未完了。
  - ネストしたdecode結果のwell-scoped性および逆向き評価定理との接続は未完了。
  - 全構文の逆向き評価反映への統合は未完了。
  - 一般式構文、runtime error、GlobalIR初期化runとの一体化はこの限定主定理に含まれず、課題1.1〜1.2および課題4に残る。
  - 任意arityのlambdaは`lambda_application_evaluation_reflected_of_fragments`で扱うが、fragmentの主定理自体は依然として構文限定であり、一般EvaluationReflectionへの接続は未完了。

## 2. 新多相モデルの型安全性

実装済み: `PolymorphicSafety.lean`。`evaluator_type_safe`、`evaluation_preserves_type`、`evaluation_no_type_error` を型検査器とpoly証書へ接続した。

- [ ] GlobalIRおよび課題5の拡張型・演算に対して型安全性を証明する。GlobalIRの整数加減乗・比較・整数等値について、整数の子評価から結果値と `PolyIR.ValueTyped` を同時に得る `evaluate_{add,sub,mul,le,intEq}_typed_of_children` を追加した。`ArithmeticTerm` と `evaluate_arithmetic_preserves_type` はBoolean/Integer/Float/String/Character/Unit、Nil/None/Some/Cons、型の合うif式・List/Option match、整数演算および4種類のFloat二項演算を含み、任意fuel・環境で成功した結果の型を構造帰納法で保存する。 今回`ArithmeticTerm.letManyClosed`を追加し、initializer列は任意長・任意のGlobalIR項でもよく、bodyがこのfragmentに属する場合に成功評価の結果型を保存する。GlobalIRのletMany評価がinitializer列を評価後、結果値を参照しない型付きbodyへ渡す経路を評価器のfuel分割込みで証明した。`lake build NLisp.GlobalIR` 成功。Floatは`floatBinValue`/`evaluate_floatBin_typed_of_children`経由で結果を`.float`とする。matchでは評価済みscrutinee型から有効な枝を選び、枝の型保存を返す。`ArithmeticSurfaceExpr.hasType`と`.erase`は同じ部分式群のSurface型付け・GlobalIR保存を接続する。これらの断片はOption返却演算を含まない。また一般関数適用・closure・getterを含むGlobalIR全評価器の型安全性も未完了。`evaluate_var_preserves_type`は局所lookupの型保存を示し、`evaluate_typed_var_preserves_type`はSurface `.var`導出を接続する。`evaluate_global_value_preserves_type`はtyped tableからのglobal関数値参照を扱う。`evaluate_typed_lambda_preserves_type`は型付きlambdaのclosure生成を扱う。`evaluate_identity_application_preserves_type`はidentity lambdaの一例を、`evaluate_letOne_variable_preserves_type`は1要素letのbodyが`.var 0`を読む一例を証明する。`ContextualArithmeticTerms`/`evaluate_contextualArithmeticTerms_preserves_type`はparallel-letの任意長initializer列を、`evaluate_contextualLetMany_preserves_type`はその列とbodyの型保存を合成する。`ContextualArithmeticSequence`と`evaluate_contextualBegin_preserves_type`/`evaluate_contextualBegin_empty_preserves_type`はbeginの式列を扱う。`ContextualGlobalArithmeticTerm`と`evaluate_contextualGlobalArithmeticTerm_preserves_type`はglobal function referenceを含む限定fragmentの型保存を示す。 `evaluate_contextual_lambda_application_preserves_type`は任意arityのsyntactic lambda applicationについて、型付き引数列・arity一致・captured environment・body fragmentの成功評価から結果型を導く。 `evaluate_contextual_closure_application_preserves_type`は呼出し元と独立したcaptured environmentを持つ評価済みclosureに一般化し、capture列・argument列を別々に型付けしてbody評価からcall評価結果と結果型を同時に導く。fragment対象外の一般Surface式、一般の関数適用、Option返却演算、getterを含む全評価器定理は未完了。対象モジュールと全体45ターゲットの`lake build NLisp`を確認済み。
2026-11-25追記: `GlobalIR.ArithmeticTerm` と `ArithmeticSurfaceExpr` にString/Character literalを追加し、Surface型付け・erasure・GlobalIR算術fragment型保存まで接続した。String/Character一般操作、Option返却演算、一般関数適用/closure/getterを含む全GlobalIR評価器の型安全性は未完了。

完了条件: 採用する意味論に対する型安全性の主張と証明が一致すること。旧単相コアのProgressを新多相モデルの証明として流用しない。


### 既存証明の適用範囲として残る課題
  - 評価器自体の型安全性、関数評価、拡張型への一般化は未完了。
  - これは実行時faultのGlobalIR内伝播だけで、ソース評価との全体的なエラー対応は未完了。

## 3. 一方向型引数決定と型検査

実装済み: `TypeArguments.lean` の収集・検査アルゴリズムと成功結果の証明。`CheckerCompleteness.lean` の `inference_eventually`、`elaborate_eventually` と `type_unique`。`elaborate_eventually` は任意の `HasType` 導出に対し、十分なfuel以降で型検査付きelaborationが成功することを示す。

`checkerTypeFuel` / `checkerTypesFuel` は型木および関数型引数リストから整形式性検査のfuelを計算し、`checkWF_sufficient` / `checkTypesWF_sufficient` が十分性を証明する。`checkerSignatureFuel` / `checkSignatureWF_sufficient` はその境界をシグネチャのparameter・result両方へ合成する。`checkerExprFuel` / `checkerExprsFuel` は式・式列・注釈・全global signatureから計算可能な境界を返し、各構文ケースで注釈・子式のfuelを親fuel内に収める。`inference_structural_fuel` はその式fuelから`infer`の成功を証明する。`CTypeArguments.lean` はC型ノードのpointer identity・順序付きscheme identity配列・identity検索によるslot化、欠落identityの拒否、forall型のmonotype/decode拒否をモデル化する。`cPointerIndex_result_is_identity`は検索成功位置が実際に同じidentityを指すことを示し、`cPointerIndex_result_lt_length`は返却位置がscheme配列範囲内であることを示す。`decodeCType_variable_wellFormed`がこの範囲性をLeanの型変数スコープ条件へ接続し、`decodeCType_wellFormed`は成功した複合C型全体のdecodeについてList/Option/function引数・戻り値を含めて同じscope性を証明する。`decodeCType_variable_iff_pointer_slot`が重複のないscheme pointer列でC identity nodeとLeanのindex nodeの表現を双方向に特徴付ける。`cPointerIndex_has_slot_iff_mem`は検索が成功することとidentityがscheme配列に含まれることの同値を示す。`CNoDuplicatePointers`の仮定下では`cPointerIndex_matches_unique_slot`と`decodeCType_variable_at_unique_pointer`が配列位置とLean scheme indexの一致を証明する。`CTypeArguments.cMatchType` / `cMatchTypes`はC `match_type`のfuel付き構造モデルとしてscheme pointerによる柔軟変数選択、実引数型の代入、再出現時の一致判定、List/Option/Function再帰、monotype条件を記述する。`cMatchTypes_arity_mismatch`は型引数列長の不一致が失敗することを示す。`cMatchType_matches_Lean_variable_capture`は、pointer lookup成功・空assignment slot・decode済み実引数の下でCとLeanの初回型変数制約が同じindexを更新し、caller scope well-formednessも保つ。`cTypeEq_decode_agreement`はfuel付きC構造比較の受理からdecode先Lean型/型列の等値を相互帰納で導く。`cMatchType_matches_Lean_variable_repeat`はこれを使ってdecode後の型一致を導出し、Lean collectorとの再出現受理を合成する。`cMatchType_rejects_Lean_variable_conflict`はC比較拒否とdecode後不一致を前提としてLean側拒否も示す。`cTypeEq_reflexive_of_cost`は型木の構造コストを超えるfuelの下で同一monotype C木が比較受理されることを示す。異なるC木が同じdecode型を表す場合の比較完全性、比較fuelのC再帰との一致、複合型制約走査とassignment列全体のsimulation、C実データ構造からdistinct pointer条件を導く証明、Cメモリ状態を含む`check_call`全体simulationは未完了。

- [ ] Cの型引数決定と、Leanの制約・代入・呼び出し側の型変数の扱いを一般的に対応付ける。進捗: `Ty.instantiate_wellFormed` は明示した`Ty.rec`の型・型リストmotiveを使い、well-formedな候補列による量化prefix置換が関数parameter列・result・List・Optionの全構造でcaller scopeを保つことを証明する。`TypeArgumentSolution.instantiated_result_wellFormed` は推論済みsolutionとscheme result型のwell-formednessから、C `check_call`が`substitute_type`で作る戻り値型のscope安全性を導く。`inferTypeArguments_complete_from_candidate` はcaller scope内の型変数を含む候補も一方向照合で回収する。C `match_type`（`src/nlisp.c:1343`）の変数記録・再出現比較・List/Option/Function再帰、関数arity guard（1354行）、`check_call`の引数順走査と未決定変数拒否（1498–1528行）にはLean側の対応する局所soundness/completeness・arity・caller-variable保持補題がある。C `monotype`（1332行）はforallを含む実引数を拒否するが、Lean `Ty`にはforall constructor自体がなく、C pointer identityをscheme indexへ写す一般表現関係もまだ定義していない。したがってCの`Type*`状態とLean substitutionを結ぶ1呼び出し全体のシミュレーションは未証明。`collectArguments_keeps_first_caller_variable_capture`は最初の変数制約がcallerの`Ty.var`をそのまま代入し、残りの引数走査後も同じslot値を保持することを示す。

完了条件: 期待する戻り値型を使わないこと、呼び出し側の型変数を固定して扱うこと、未決定変数へ既定値を入れないことを維持し、成功・失敗・資源超過の保証を整理すること。


### 既存証明の適用範囲として残る課題
  - これはcollector局所の規則一致で、Cのpointer identity・monotype検査・全呼び出しとの一般シミュレーションは未証明。
  - これはC `match_type` の変数分岐の局所的な逆方向性を与えるが、複合型・引数列・`check_call`全体への合成は未完了。
  - これはLean collector内の一般的な制約→代入意味対応であり、C `Type*`ポインタ同一性、`monotype`、C `check_call`メモリ状態とのシミュレーションは未完了。
  - C `Type*`グラフとの一般的な表現関係・monotype検査・pointer identityを含む呼び出し全体のシミュレーションは未完了。
  - C `Type*` pointer identityとLean indexの表現関係・メモリ状態simulationは未完了。
  - C allocator/`Type*`グラフからこれらの前提を導く`check_call`実メモリ状態シミュレーションは未完了。
  - C実コードの`Type*`メモリ配置、allocator、実`check_call`状態から抽象前提を導くsimulationと、Lean成功からC matcher成功を導く完全性は未完了。

## 4. トップレベル値・初期化・捕捉

2026-11-25 継続作業: `decodedTopLevelProgram_checkedRows_executable_layout` を追加した。decode成功・value slot型列とsource-order `Entry`の一致・initializer-row checker受理から、mixed header/layout・initializer長とlet-layout整合・Named function well-scoped性に加え、実際の`toRuntimeProgram`定義数/initializer数、typed initializer rows、GlobalIR `InitializerTypesAgree`を一つの結論へ得る。`.tools/lean-4.8.0/bin/lake build NLisp.GlobalSourceLowering`と全46ターゲットの`lake build NLisp`が成功。initializerの評価意味保存、checker受理rowsのC/source decodeのみからの自動構成、初期化runの一般型安全性は引き続き未完了。
2026-11-25 継続作業: `decodedTopLevelProgram_arithmeticRows_initialization_supports_typed_getter_call` を追加した。成功decode・value slot型列とEntry tableの一致・算術initializer row proof・成功したGlobalIR初期化runから、checker fuel/受理証拠、実行layoutとinitializer型合意、および初期化後getterの宣言型を一つの定理で構成する。算術fragmentからinitializer評価型保存を導くため、別途per-evaluation型保存前提を要求しない。`lake build NLisp.GlobalSourceLowering` と全46ターゲットの`lake build NLisp`が成功。Named sourceからGlobalIRへのinitializer評価自体の意味保存、任意initializerへの拡張、C checker/result連携は未完了。
2026-11-25 継続作業: `decodedTopLevelProgram_arithmeticRows_initialization_preserves_store` を追加した。成功した混在top-level decode・value slot型一致・算術initializer row証明・実際のGlobalIR初期化runから、checker受理、header/layout条件、`InitializerTypesAgree`、初期化後の`StoreWellTyped`・store長・各slotの型付き値存在をまとめて構成する。算術initializerの評価型安全性は既存row証明から導き、別の全評価器型保存仮定を置かない。`.tools/lean-4.8.0/bin/lake build NLisp.GlobalSourceLowering` 成功。Named initializer評価とGlobalIR評価の意味保存、任意initializerとC実行器への接続は未完了。

poly生成器接続の実装条件を確認した。`PolyExporter.globals` は関数・値を元宣言順に保持するため、値宣言を単に許可して関数のみのPolyIR証明を再利用することはできない。initializer内の値global参照はSurface/GlobalIR上でゼロ引数getter呼び出しとして出力し、混在宣言を `GlobalProgramEntry.Entry` に変換して `valueTypes`・`TypedInitializerRows`・`toRuntimeProgram` に結び付ける必要がある。GlobalIR関数bodyも同じ混在global indexと `lowerGlobalReads` getter semanticsで型付けする。現在のfunction-only exporterはこの接続を生成していないため、この項目は未完了。


実装済み: C実行器の共有セル、初期化前読み出しの診断、`GlobalIR.lean` と初期化の不変条件。

追加済みの補助定理: `evaluate_lambda_store_independent`、`getter_call_reads_current_store`、`getter_call_reports_early_read`、`initializeValues_stops_on_error`、`initializeValues_commits_head`。IR上でクロージャ作成がストアに依存せず、getter呼び出しは呼び出し時のストアを読むこと、未初期化セルのエラー、初期化式の失敗時に後続へ進まないこと、成功した値をセルへ確定してから次へ進むことを証明する。さらに`Diverges`を全ての正のfuelでfuel切れとなる性質として定義し、再帰呼び出しの例と、発散するinitializerが初期化列をfuel切れにすることを証明した。これらはソース変換、GlobalIRの型安全性、C実装とのシミュレーションを証明するものではない。

- [ ] poly証書生成経路へ接続する。`PolyExporter`は混在top-level宣言をdecodeし、値宣言を含む場合に`GlobalProgramEntry.Entry`列を生成する機能を追加した。`checkInitializer_sound` はcheckerの成功から型付け・source保持・erasure一致を取り出し、`TypedInitializerRows.value_of_checkInitializer` はその結果とslot対応を一行証明へ組み立てる。`LoweredClosedValue` にも `checkInitializer = some initializer` の証拠を保持し、raw initializerのdecode結果・型付け・checker成功を同一certificateへ結んだ。実行可能な `checkInitializerRows` と `checkInitializerRows_iff` は走査の成功とproof-carrying row invariantが同値であることを証明する。これにより全value行の受理証拠・slot対応から `TypedInitializerRows` を構成できる。`checkInitializerRows_initialization_supports_typed_getter_call` は成功scanをGlobalIR初期化後のgetter型安全性へつなぐ。`globalIR_types_agree` / `toRuntimeProgram_types_agree` は同じchecker証拠からslot型整合も直接導く。`InitializerCheckerRows.toRuntimeProgram_initialization_preserves_store` と `_supports_typed_getter_call` は、実行tableの初期化後store型安全性・slot数・getter型安全性を導き、一般initializer評価の型保存を明示前提として残す。今回、`BodiesHaveTypes.signature_valid_at` を追加し、poly証明生成で各関数signatureのwell-formednessを型付き関数列から射影できるようにした。poly証書に値宣言がある場合、ソースからの値置換・initializer行受理・slot型整合・GlobalIR初期化成功を結ぶコードを追加し、`(define (answer Integer) 42)` と`main`を含む生成証書でLean検査成功を確認した。initializerは生成されたソース式から`lowerAndReplaceValues`で実際に読み替える。initializerを含まない多相例の再検査はLean status 137で終了したため、退行なしの確認は得ていない。関数本体からトップレベル値を参照する意味保存、全value行に対する一般証書の型付け・評価意味対応、初期化後の一般store型安全性、C実行対応は未完了。`CertifiedValueReplacement.initializer_at_slot` は置換後initializerの型付けとidentity由来getter slotを束ね、`CertifiedValueTrace.typedInitializers` はtrace全体のinitializer型付けを最終signature表へ移す。
- [ ] `ExpansionLowering.readProgramHeaders` は混在したdefun/define列をそれぞれの順序を保って読み取る。`NamedDecoder.decodeTopLevelProgram` は関数headerの後にvalue headerを並べ、関数bodyとinitializerのglobal参照をcombined indexでdecodeする。`globalIndex_value_reference` はbinder IDから値globalの `functionCount + slot` への対応を証明し、`decodeGlobalInitializers_length` / `decodeProgramWithGlobals_layout` / `decodeTopLevelProgram_layout` はslot型と初期化式の件数一致を示す。`GlobalIR.assembleNamedProgram` / `programOfNamed` はdecoded functionとinitializerからgetter付き実行table・初期化列を構成する。`assembleNamedProgram_length` / `programOfNamed_definition_count` はruntime tableの関数prefix・slot getter suffixの全長を、`programOfNamed_getter_lookup` はslot番号からgetter entryの位置を示す。追加した`decodedProgram_layout`はdecode成功時にruntime table全長・initializer数・値slot getter位置をまとめて示す。`decodedProgram_successful_initialization_populates_slot`は、そのdecode由来layoutとGlobalIR initializer列の成功実行から任意slotのstore値存在を導く。`decodedProgram_successful_initialization_getter_reads_slot`はさらにcombined getter indexをdecode由来layoutから取得し、初期化後に同じslot値を返す評価まで合成する。型付きstore保証や任意initializerのソース意味対応は別前提・未完了である。`decodedInitializer_arithmetic_evaluation_reflected`はdecode済み混在programから選んだ算術fragment initializerについて、Named評価の反映と返却closure値のscope不変条件を示す。ただしこれをGlobalIR実行tableへ運ぶ意味保存・poly型付け証明・初期化後の型安全性は未証明。
- 2026-11-25追記: `decodedTopLevelProgram_checkedRows_initialization_preserves_store` は混在top-level decode成功・全initializer行のchecker受理・生成された実GlobalIR program上の初期化成功を合成し、ソースinitializer数とruntime initializer数の一致、およびinitializer評価の値型保存仮定の下でtyped storeとslot layout長を導く。`lake build NLisp.GlobalSourceLowering` 成功。一般GlobalIR評価の型安全性とソース意味対応はなお前提・未接続であり、この定理は課題4全体を完了しない。
- 2026-11-25追記: `decodedTopLevelProgram_checkedRows_initialization_supports_typed_getter_call` はdecode成功・checker受理・initializer成功を、生成runtime program上の初期化後getterの宣言型読み出しへ接続する。GlobalProgramTypedとinitializer評価型保存は明示前提のままで、一般initializer意味保存やpoly証書経路は未接続。`lake build NLisp.GlobalSourceLowering` 成功。
- [ ] Cの表現対応を`src/nlisp.c:628-633, 1768-1788, 2037-2064`に明記した。`Program.data`と`value_slots`は混在宣言添字を使い、`value_slots[i]`は初期化時に作った同一の`RBind`セルを指し、`NULL`から値への更新後も関数closureがそのセル列を捕捉する。GlobalIR側の`sourceValueSlotOrdinal` / `sourceValueSlotOrdinal_layout`は混在宣言添字からdense slot ordinalとgetter layoutへの対応を証明し、`sourceValueSlotOrdinal_matches_identity_lookup`は一意なbinding identityについてordinalがidentity検索結果と一致することを示す。`sourceValueSlotOrdinal_refersToValueDeclaration`は成功添字が値宣言を指すことを示し、`sourceValueSlotOrdinal_complete`はgetter layoutからordinalを復元する。`CNameResolution.CellStore` / `writeCell` / `readName_after_cell_write` は固定名前環境で更新後の値が読めることを示す。今回CellStoreのpayload型を任意型に一般化し、`identityCellStore`でGlobalIR storeをbinding identity経由のcell storeとして解釈し、`resolvedCellName_reads_globalIR_slot`で名前検索成功・identity-slot対応・初期化済みstore値から同じ値の取得を導き、`resolvedValueName_reads_declared_globalIR_slot`が一意な混在Entry table上の宣言添字・dense slot ordinalを同じ名前解決結果へ接続する。`identityCellStore_update_matches_C_cell_write`はslot写像の単射性とslot存在条件の下でGlobalIRの`List.set`とC共有cell更新の一致を示し、`declaredValueCell_update_matches_C_cell_write`は混在Entryの一意性とsource ordinalから単射性を導いてこの一致を適用する。`resolvedCValueName_agrees_with_compiled_globalIR_getter`はC風の名前検索・mixed declaration添字・dense slot・初期化済みstore・GlobalIR getter評価を一つの結果に結び、`resolvedCValueName_uninitialized_matches_globalIR_early_read`は空cell読出しとGlobalIRの`.beforeInitialization`を対応させる。実Cの`rfind`文字列名検索、`eval`の個別step、およびC実装とGlobalIR抽象store間の全体シミュレーションは未証明。

完了条件: 先に作ったクロージャが後から初期化された大域値を正しく参照し、実際の初期化前読み出しは初期化エラーとなること。未使用の初期化式も省略しないこと。



### 既存証明の適用範囲として残る課題
  - 型付きinitializer行からStoreWellTypedと全slot充填を得る定理と組み合わせられるが、混在プログラムdecodeから条件を構成する証明は未完了。
  - 任意位置の宣言・initializer列、poly証書生成、正常なinitializer列全体とC実行器のシミュレーションは未完了。
  - initializer評価の型保存、decode/exporterからの行証明生成、全体のソース意味保存は前提または未接続のまま。
  - poly型付け・initializer評価・GlobalIR初期化意味対応は別途残る。
  - これで生成器単体のdecode・型検査結果が明示されるが、poly証書生成器や全value行の自動構成へは未接続。
  - 条件・選択branch評価と初期化成功は前提であり、一般再帰initializer評価・poly exporterからの行証明生成には未接続。
  - 全宣言列をpoly exporterから構成する経路とsource-to-GlobalIR意味保存は未完了。
  - ソース/Cとの実行シミュレーションは未接続。
  - 全構文への拡張、元ソースとGlobalIRの意味保存、全initializerの型付き初期化、poly証書生成経路への接続は未完了。
  - initializer列全体の意味保存・型安全性は残る。
  - initializer評価の型付き前提の導出とGlobalIRの一般fuel付き評価器の型保存は未完了。
  - decode成功から行証明を自動構成する接続とinitializer評価の一般型安全性は未完了。
  - 任意Surface initializerやdecode/poly証書からの一般生成経路は未接続。
  - decode成功から型付き行を作る経路、initializer評価型安全性の一般化、poly exporter接続は未完了。

## 5. 全型・全組み込み関数

- [ ] 新Surface・IR・値・評価器・型付けへFloat、String、Characterを追加する。2026-11-25進捗: `Surface.Ty.float` と `Surface.Expr.float` を追加し、Surface評価値、PolyIR項・値・評価関係・実行器、erasure、型推論と型安全性をFloat literalまで接続した。`TypeArguments`の型再帰補題、チェッカー完全性、構文サイズモデルもFloatを扱い、`floatBits`は64-bit literal payloadを数える。さらに `FloatBinOp` の加減乗除をSurface・PolyIR・GlobalIRの項と評価器、型検査、Surface/PolyIRの意味規則、型安全性、評価完備性へ接続した。Named側にもFloat式・値・四則演算の評価規則、lowering、`float_evaluation_reflected`、`floatBin_evaluation_reflected`を追加し、`ArithmeticFragment`の有限IR評価反映へFloat literalと加減乗除を含めた。`evaluation_preserves_valueWellScoped`もFloat結果を扱う。`Lexical.parseFloatLiteral`を追加してASCII decimal significand・符号・10進スケールを読み、桁順が±400の外ではCと同じ符号付きゼロ/無限大へ分岐させた。Named decoderとSurface checkerもこのparserを参照する。今回 `Surface.Ty` / `Surface.Expr` / Surface値・評価関係・実行器、PolyIR/GlobalIR項・値・評価器、erasure、型checkerと型安全性へString・Character leaf constructorsを追加した。`TypeArguments`の型照合、checker完全性、構文サイズ/コストモデルのprimitiveケースも更新し、全45ターゲットの `lake build NLisp` 成功。ただし文字列・文字とC readerとの完全対応、文字列操作は未証明。Floatも`Float.ofScientific`とC `decimal_to_binary64`の全binary64結果一致、極端な有効桁列を含む丸め一致は未証明。
- [ ] 全26組み込み関数について型と評価規則を対応付ける。
2026-11-25追記: `CBindingWalk.builtinEnvironment_all_ids` がCのBuiltinSpec列にある全26名（整数/Boolean/Float/String/Character演算と変換）のname-resolution identityを個別に確定し、C annotated-tree側lookupへ固定した。`builtinPrimitive` と `builtinEnvironment_primitiveRows` は各名前/identityを `TypedExpansion.Primitive` へ結び、`builtinEnvironment_primitiveTypeRows` は全26件の`Primitive.type`を展開したsignature表と照合する。Lean側のname/identity/type表は網羅したが、C enum/BuiltinSpecとの機械抽出による一致証明、および多相IRの評価規則・型安全性への接続は未完了。
- [ ] binary64の丸め、NaN・無限大・符号付きゼロ・サブノーマルを仕様と整合させる。
- [ ] UTF-8、Unicode scalar、埋め込みNUL、文字列操作をモデルと対応付ける。
2026-11-25追記: `Lexical.readStringLiteral` と `readCharacterLiteral` を実装し、Named decoderが引用文字列、newline/space/tab、標準escape、Unicode scalar `\u{...}` をNamed String/Characterへ変換するようにした。hex Unicodeは6桁以内かつscalar範囲（surrogate除外）を検証し、String結果はU+0000を保持できるLean Stringで構築する。Named評価からPolyIRへのString/Character literal反映定理も追加。`lake build NLisp.Lexical`, `lake build NLisp.NameLowering`, `lake build NLisp.NamedDecoder` が成功した。C実装との全入力一致（とくにUTF-8妥当性、NULを含むatom保持）、builtin string operationの意味・型保存は未証明。
- [ ] 整数除算・余り・数値変換のOption結果を含め、型安全性・意味保存を拡張する。
2026-11-25追記: `TypedExpansion.truncQuotient` と `integerOptional` を追加し、C/GMP `mpz_tdiv_q` のゼロ方向丸めと、`mpz_tdiv_r` と同じ `left - quotient * right` による余りをLean上に定義した。除数0では`none`、非0では商・余りが定義されることを証明した。`.tools/lean-4.8.0/bin/lake build NLisp.TypedExpansion` と全46ターゲットの `.tools/lean-4.8.0/bin/lake build NLisp` が成功。これは値関数の仕様化までであり、Surface/PolyIR/GlobalIR評価器、Option値の型安全性、Cとの実行意味対応には未接続。
2026-11-25追記: `integerOptional_division_equation` を追加した。任意の非zero divisorについて`quotient`と`remainder`がそれぞれ`some`を返し、`left = quotient * right + remainder`を満たすことを構成した。`lake build NLisp.TypedExpansion` と全46ターゲットの`lake build NLisp`成功。GMP/Cとの丸め結果同値、剰余の絶対値上界、Surface/IR evaluatorへの接続は未証明。
2026-11-25追記: `GlobalIR.evaluate_floatBin_of_children` と `evaluate_floatBin_typed_of_children` を追加し、左右子式がFloatへ評価される条件で、4種のFloat二項演算の結果値と`PolyIR.ValueTyped .float`を同時に導く。Lean 4.8の`readClosedInitializer_floatBin_builds_typed_row` は、この読取・左右評価の証拠から混在宣言のFloat initializer rowを`TypedInitializerRows`と`ArithmeticInitializerRows`の両方へ組み立て、同じinitializerのGlobalIR評価結果を保つ。`readClosedInitializer_floatBin_initialization_preserves_store` は実際の生成GlobalIR programの成功initializer runを受け、decoded floatBin式の型付き行から初期化後の`StoreWellTyped`を導く。全45ターゲット `lake build NLisp` 成功。C binary64丸めとの一致、NaN等の網羅、String/Character、任意式のGlobalIR型安全性には拡張していない。 `GlobalSourceLowering.readClosedInitializer_floatBin_evaluates` は、Float二項演算のdecode結果と左右のGlobalIR評価から、結果値・PolyIR値型・ArithmeticSurfaceExpr・Surface型付けを合成する。readerへfloat+/-/*//の分岐をC builtin identity 39/42/45/48で追加し、`CBindingWalk.builtinEnvironment_floatArithmetic_ids`でLean builtin environmentのlookup IDを確認した。`readClosedInitializer_floatBin`は、左右nodeのdecode成功とbuiltin binding IDから実reader結果のSurface `.floatBin`式を導く。`readClosedInitializer_floatBin_builds_typed_row` は、この読取・左右評価の証拠から混在宣言のFloat initializer rowを`TypedInitializerRows`と`ArithmeticInitializerRows`の両方へ組み立て、同じinitializerのGlobalIR評価結果を保つ。`readClosedInitializer_floatBin_initialization_preserves_store` は実際の生成GlobalIR programの成功initializer runを受け、decoded floatBin式の型付き行から初期化後の`StoreWellTyped`を導く。全45ターゲット `lake build NLisp` 成功。C binary64丸めとの一致、NaN等の網羅、String/Character、任意式のGlobalIR型安全性には拡張していない。

完了条件: 旧型付けモデルやC実装で対応している事実だけでなく、新しい評価モデルで全演算の意味と保証を説明できること。


### 既存証明の適用範囲として残る課題
  - 旧コアの26組み込み関数との対応、新多相モデルへの追加、浮動小数点・文字列・文字の保証は未対応。

## 6. マクロ展開処理全体の終了性

- [ ] 展開された親規則のtemplateから次の実行macroStepへ、同じ `StaticCall` 辺を追跡し、各遷移の親・子rule indexで順位が減ることを証明する。リテラルheadでは `root_template_call_to_next_macro_step` / `root_next_macro_step_rank_decreases` が任意arityを扱う。`copyManyWithMacros_extract_element` は任意位置の要素copyと前後のcopy走査を分解し、`literal_call_at_list_index_to_next_macro_step` は通常のコピー対象リストの任意の兄弟位置にあるリテラルcallを、対象引数のcopy/match条件下で静的辺へ接続する。再帰的な `LiteralCallSite` と `SubstitutedHeadCallSite`、対応する `*_to_next_macro_step` / `*_rank_decreases` 定理は各中間list headの中立性を前提として、任意深さの通常リスト経路にあるリテラルheadと、parameter/hole名が一致する非特殊フォームの置換headを、実match条件下で同じtemplate `StaticCall` と順位減少へ接続する。`copyWithMacros_lambda_parts` / `lambda_body_call_site_to_next_macro_step` と `copyWithMacros_let_parts` / `let_copy_body_call_site_to_next_macro_step` は、それぞれ通常dispatcherで成功したlambda/let全体copyから専用binding処理とbody copy結果を抽出し、body内callをtemplate edgeへ接続する。さらに `BindingRows` / `copyBindingsWithMacros_extract_initializer` / `let_initializer_call_to_next_macro_step` / `let_initializer_call_rank_decreases` は、有効なbinding prefixの後にある任意initializer内の任意深さの通常リストcallを接続する。`CaseRows` / `copyCasesWithMacros_extract_default` / `copyCasesWithMacros_extract_pattern` は、case列の有効なprefixの後の任意位置からdefault/pattern caseのコピーを抽出し、pattern fresheningで更新された開始counterも返す。default/pattern caseの任意位置のbody callやmatch scrutineeの接続もある。特殊フォームの一部については、root位置の `lambda_hole_head_copy_rank_decreases` / `let_hole_head_copy_rank_decreases` / `match_hole_head_default_copy_rank_decreases` / `match_hole_head_cases_copy_rank_decreases` が実matchからtemplate `StaticCall` と順位減少を導く。特殊フォームを含む任意callsite、実行macroStep列全体と構文走査を合成する定理は未証明。
- [ ] 順位の減少と構文処理の進行から、展開処理全体の終了を導く。
2026-11-25追記: `ExpansionProgress := Prod.Lex Nat.lt Nat.lt` と `macroExpansionProgress_decreases` / `syntaxTraversalProgress_decreases` / `expansionProgress_wellFounded` を追加した。マクロ展開が生成構文を大きくしても第1成分のrule rankが下がり、通常走査では同rankの下で構文node数が下がるという抽象二相測度は整礎である。`lake build NLisp.MacroTermination` 成功。実copy/macroStep列およびC展開ループの各遷移がこの抽象関係を満たすことの接続は未証明なので、全体終了性項目は未完了。
2026-11-25追記: `ProcessCertificate.source_static_call_expansion_progress` を追加し、`CheckedStaticTermination`の受理済み`GraphCall`から辞書式測度のmacro component減少を直接導くようにした。`lake build NLisp.ProcessCertificate` 成功。静的template callsiteが実copy後の次macroStepになるシミュレーションと、各構文走査でnode数が減る不変条件は未接続。
2026-11-25追記: `CMacroCopy.TreeChild` と `treeChild_nodeCount_decreases` は、Tree直下のList要素についてconstructor node数が必ず減ることを証明する。`MacroTermination.treeChild_expansionProgress_decreases` でこの事実を辞書式測度の構文成分へ接続した。`lake build NLisp.CMacroCopy` と `lake build NLisp.MacroTermination` 成功。現時点の`TreeChild`はList要素だけを形式化し、コピー各段階や全構文分岐を処理する実走査状態との対応は未完了。 `TreeChild`から辞書式syntax-progressを導く`treeChild_expansionProgress_decreases`も追加した。 `treeListNodeCount_cons_tail_decreases` と `treeList_tail_expansionProgress_decreases` も追加し、`copyMany`系の残tail走査で要素を一つ消費する進行を同じ二相測度へ接続した。`lake build NLisp.MacroTermination` 成功。個別special-form処理で生じる再帰呼出し全体との対応は未証明。
- [ ] Cの展開処理との対応を示す。
- [ ] より精密な動的呼び出し解析や、利用者指定の一般的な構造的減少を別の十分条件として設計する。構文穴の呼び出し先については、同じ引数個数を持つ全マクロ規則を候補辺へ加える保守的解析を実装済み。

完了条件: 呼び出しグラフの整礎性を、展開器全体の終了性と取り違えないこと。証明不能はUnknownとし、非停止や入力不正とは判定しないこと。展開サイズ・時間の上界は別に扱う。

追加済みの前提補題: `successful_match_has_signature` は成功した`matchRule`から規則signature・呼び出しhead名・引数数の一致を取り出す。`macro_step_input_is_static_candidate` はrule membershipも仮定して、その実呼び出しをsome targetへの`StaticCall`として導く。`call_chain_length_bounded` / `no_infinite_call_chain` は受理済みranked graph上の有限prefix上界と無限call chainの不存在を示し、`ProcessCertificate.source_static_call_chain_length_bounded` / `_terminates` は同じ結果をsource process証書へ接続する。実際のmacroStep列からそのgraph relationへの合成は未証明のため、展開器全体への終了性接続は未完了。


### 既存証明の適用範囲として残る課題
  - 実際の次macroStepがそのtemplate call siteから来たことの証明は未完了。
  - 非空pattern caseの複数case位置は未対応。
  - 内側list headの中立性が必要で、3段以上・特殊フォーム・展開列全体への一般化は未完了。
  - 中間list headの中立性が必要で、四段以上・特殊フォーム・展開列全体への一般化は未完了。
  - 各中間list headの中立性が必要で、五段以上・特殊フォーム・展開列全体への一般化は未完了。
  - 特殊フォームheadや展開列全体への一般化は未完了。
  - これは複数caseの走査分解までであり、match構文内callsiteとtemplate edgeを結ぶ一般定理は未完了。
  - 特殊フォームhead、展開列全体の停止性も未完了。
  - 特殊head内の任意callsiteを網羅する定理、実macroStep列全体と構文走査を合成する定理、全展開終了性は未完了。
  - ほかの全構文callsiteを実行macroStepへ網羅する定理、展開全体の終了性は未完了。

## 7. 独立検査器の保証・計算量


- [ ] 受理から得られる構文対応・freshness・非捕捉・型保存を、一つの合成的健全性定理へまとめる。
  現在の部分結果: `ExpansionCertificate.checkFresh_sound_with_intervals` は単一の受理判断から有限展開と記録区間の非重複を同時に導く。`ProcessCertificate.CheckedExpansion` は元ソース、正規化、同じ入力・出力へ結び付いた受理済み局所証書、scope correspondencesを一つのレコードへ保持し、`source_expands_with_scopes_and_freshness` が読取・有限展開・区間分離・scope対応を合成する。`verify_lean.py` のproof generatorがこのrecordを構成する経路は `examples/polymorphism.nlisp --mode poly` の生成証書で再実行し、Lean検査成功を確認した。生成binder全体のfreshness・非捕捉・型保存・実process artifactとの対応は残るため、この項目は未完了。
- [ ] `copy`、`copyMany`、`copyParameters`、`copyBindings`、`copyPattern`、`copyCases` の結果について、上記のbinder性質を構造的に合成し、全生成識別子がcounter境界内かつ相互に異なることを示す。入力識別子との非衝突と合わせて全体のFreshnessを導く。
  追加進捗: `CMacroCopyBinderComposition.copyBinderPhases_freshness` は、任意のmacro-name集合とcounter-preserving条件の下でパラメータ・let binding・match pattern・match caseの4段階copyを合成し、出力binder tokenの相互非衝突、予約source-token剰余類との非衝突、最終counter区間への所属を同時に導く。`copyBinderPhases_disjoint_source` はsource token一覧の全要素が予約剰余類に属する場合の非衝突を導く。initializer/case条件を外した一般binder処理、全構文の`copyMany`合成、実ソース全体との非衝突前提の構成は未接続。
- [ ] マクロ契約の型付けと、実際の置換・展開証書の型情報を同一モデルへ接続する。
- [ ] 検査手続きのコストモデルを定義し、構文走査・環境探索・型照合・局所証書検査の上界を証明する。`checkerTypeFuel_le_typeBits` / `checkerTypesFuel_le_typeListPayload` / `checkerTypesFuel_le_typeListBits` は型WF checkerの構造的fuelを単体・型列の符号長以下にし、`checkerSignatureFuel_le_signatureBits` / `checkerSignaturesFuel_le_signatureListBits` はsignature単体・列へ合成する。`typedProgramSignatureValidationAndScanCost_le_bits` はglobal signature表のWF fuelとトップレベルsignature/body行走査を合成し、全program bit長の2倍以下とする。`lake build NLisp.CertificateSize` と全44ターゲットの `lake build NLisp` が成功。式全体のchecker fuel、構文全走査、copy処理、環境探索との合成を含む総コスト上界は未証明。
- 2026-11-25追記: `checkerGlobalExprFuel_le_scaled_expressionBits` は、任意のglobal参照式について型引数checker fuelと参照ごとのglobal signature表再走査を、式符号長×(`checkerSignaturesFuel globals + 2`)以下へ抑える。atomic literal/variable、unit、型注釈付きnil/noneについても `checkerSimpleLeafExprFuel_le_scaled_expressionBits` / `checkerNilExprFuel_le_scaled_expressionBits` / `checkerNoneExprFuel_le_scaled_expressionBits` で個別の上界を証明した。`CheckerLeafExpressions` と `checkerLeafExpressions_fuel_bound` はこれらとglobal参照のみからなる任意長の式列へ、pointwise前提なしで式列境界を合成する。さらに `checkerLeafExpressions_fuel_plus_one_bound` は終端list dispatch分まで含めて同じ列のchecker fuelを抑え、application合成に使える形を与える。`expressionBits_add/sub/mul/le/intEq/floatBin` の符号長等式と `CheckerBinaryTreeExpression` / `checkerBinaryTreeExpression_fuel_bound` により、これらの整数・Float二項演算を任意深さで組み合わせた式木も上界内となる。`checkerTypeFuel_le_scaled_typeBits` を加え、`some`/`cons`の注釈と子式のfuelを合成し、型付きlist/option構築、3枝条件式`ite`、lambdaの型引数列・結果型・本体、ゼロ引数application、空initializer・一つ・二つ・三つ・四つのinitializerを持つ`letMany`、空rest・一要素rest・二要素restの`begin`、`matchList` / `matchOption`を含む式木まで拡張した。`CheckerBinaryTreeExpressions` / `checkerBinaryTreeExpressions_fuel_bound` はそれらの式木だけからなる任意長の式列へ、list walker込みの境界を合成する。`lake build NLisp.CertificateSize` 成功。五つ以上のinitializer letMany・非空引数application等のほかの再帰constructor、任意構文列、入力全体の検査器総コストは未完了。
2026-11-25追記: `checkerBinaryTreeExpressions_fuel_plus_one_bound` を追加し、上記の再帰式木で構成された任意長のinitializer列について、列終端のwalker dispatchを含むfuel境界を証明した。initializerを持つ式への合成に利用する補題で、`lake build NLisp.CertificateSize` 成功。一般長`letMany`のサイズ境界には、`Surface.Expr.rec`が生成する相互再帰の式列サイズと明示foldサイズの一般一致補題が別途必要であり、今回の試行では確立できなかったため、未完了のままとする。
2026-11-25追記: `expressionBits_letMany_five` と `CheckerBinaryTreeExpression.letManyFive` を追加し、5 initializerのparallel letについてもfuel境界を証明した。`lake build NLisp.CertificateSize` 成功。これは固定arityをもう一つ追加した結果であり、任意長initializer列のサイズ整合は依然未完了。
2026-11-25追記: initializer列の一般長境界を調査し、Lean生成の`Surface.Expr.rec`（式を主項とするrecursor）と`Surface.Expr.rec_1`（`List Expr`を主項とするrecursor）が別の計算定数として現れることを確認した。`expressionBits`の`letMany`分岐に含まれる相互再帰列サイズと、`foldr expressionBits`で定義した`expressionListPayloadBits`の一致は単なる`rfl`/`simp`では閉じず、recursor間の対応補題が必要。誤った一般化を残さないよう試作は撤回し、既存のCertificateSize build成功を再確認した。

補足: `certificateEndpointPayloadNodes` と `certificateMaxEndpointNodes_le_payload` を追加し、証書から再構成される全endpointの構文nodeを集計する尺度を導入した。`CertificateSize`では最大endpoint node数をモデル上の`certificateBits`へ抑えた。実際のシリアライズbyte長との関係、payload比較のbit費用、copy本体は未完了。

完了条件: 「今回検査できた」「予算付きで動く」「構文ノードだけなら線形」を、検査器全体の多項式時間保証として扱わないこと。元ソースに対して証書が大きくなり得ることと、証書サイズに対する検査時間を区別すること。


### 既存証明の適用範囲として残る課題
  - 任意binder body、nested initializerおよび全体copyへの合成は未完了。
  - `copyBinderPhases_freshness` の4 phase列を入力できるが、証書受理から一般 `copy` 全構文の区間所属を構成する定理は未完了。
  - 任意initializer/case本文を含む全`copy`構文への拡張は未完了。
  - 構文一般の`copy`へ広げる証明は未完了。
  - 比較の早期不一致を無視した保守的モデルであり、構文走査・型照合・copy処理を含む検査器全体のコスト上界は未完了。
  - CBindingWalkの構文走査・scope集合処理費用はモデル外で、全checker上界は未完了。
  - 実ファイル直列化との大小関係、atom payload比較のbit costは未完了。
  - 両方の長さ成分だけを結んだ補題で、マクロ仮引数総数や照合全体の費用上界には未接続。
  - 実ファイルbyte長との符号化対応、copy本体・atom payload bit costは未完了。
  - 実ファイルbyte長との対応・copy本体・atom payload bit costは未完了。

## 追加の研究・仕上げ作業


2026-11-24追記: `TypedInitializerRows.toRuntimeProgram_initialization_preserves_store` は、混在Entry列の全initializer行証明と各評価結果の型保存前提から、生成GlobalIRプログラム自身のinitializer列を実行した後の`StoreWellTyped`とslot数保持を導く。さらに`toRuntimeProgram_initialization_supports_typed_getter_call`は、初期化後の任意getter結果が対応slot型を持つことを導く。一般GlobalIR評価器の型安全性が未証明のため、評価型保存は明示前提であり、poly exporterからの証書自動生成、decode成功からtyped layoutを得ること、ソース意味保存は未接続。

2026-11-25追記: `CSubstitutionStateAgree` を使う部分代入対応について、`cMatchType_repeated_preserves_substitution_state` を追加した。quantified variableの既存C/Lean代入がdecode対応し、C構造比較が成功する場合、C matcherとLean constraint collectorが各々入力配列を返すため、全slotの部分対応不変条件も維持される。`lake build NLisp.CTypeArguments` 成功。これは単一の反復制約を扱う補題で、再帰的な引数列全体のC `check_call` とLean収集・代入シミュレーションは未完了。
2026-11-25追記: `cMatchTypes_state_simulation_of_steps` は単一型制約ごとのC matcher/Lean collectorシミュレーションと `CSubstitutionStateAgree` 保存を前提に、`cMatchTypes` と `collectArguments` の任意長・左から右の走査へ合成する。`decodeCTypes_map_getD` と `_state_simulation_of_steps_decoded` はdecode成功から失敗時fallbackを取り除き、C parameter/actual型列をLeanのdecode型列そのものへ接続する。`lake build NLisp.CTypeArguments` 成功。前提である全型構造の単一制約シミュレーション、C `check_call`の引数型配列decode・最終代入、実C状態との接続は引き続き未完了。
2026-11-25追記: `cMatchType_variable_capture_preserves_substitution_state` は既存の空slot capture対応とslot更新不変条件を合成した。C pointer検索からscheme slot範囲を導き、C側actual型がdecodeされ、C/Lean双方で同じslotが空なら同じ値を格納して全slotの `CSubstitutionStateAgree` を維持する。`lake build NLisp.CTypeArguments` 成功。これはvariable-patternの初回capture分岐であり、既存値・構造constructor・一般の引数列からstate対応を導く未解決部分は残る。
2026-11-25追記: `cMatchType_captures_rigid_caller_variable_preserves_state` はscheme/caller双方のdistinct pointer列から型変数identity検索をLean slotへ対応させ、初回captureによる代入状態不変条件の保存まで合成する。`lake build NLisp.CTypeArguments` 成功。これは実引数がcaller型変数の初回captureに限られ、一般C型構造のsingle-step simulationと`check_call`全体は未完了。

2026-11-25追記: Float atom読取を `Lexical.readFloatLiteral` に統合し、字句判定と数値変換を同じAPIで行うようにした。`readFloatLiteral_lexical` はreaderが値を返すならC共通のFloat字句文法を満たすことを示す。Named decoder、Surface checker、GlobalSourceLoweringで共有し、`lake build NLisp.GlobalSourceLowering NLisp.ExpansionLowering` が成功。全44ターゲットのビルドも再確認済み。これは字句受理の性質であり、Cとのbinary64値一致は依然未証明。


### 既存証明の適用範囲として残る課題
  - `RESEARCH_FORMALIZATION.md`で総合健全性式を未達の研究目標と明記し、確認済みの有限展開・区間分離・条件付きcopy freshness・静的候補グラフと、未証明の全体freshness/非捕捉/型保存/C対応を区別した。

## 作業上の注意

- 予算切れは非停止の証明ではない。
- 型が合う出力を生成できることだけでは、元プログラムとの意味保存にならない。
- 証明済みという記載は、本体のLeanファイルと公理監査を確認して更新する。
- モデル更新後の証書は再生成する。古い環境ハッシュの証書を黙って受理しない。
- 今回の追加修正には未ステージのファイルがある。Gitのステージ・コミット・アップロードはユーザー側で行う。

2026-11-25追記: `GlobalIRErrorCorrespondence.functionTable_globalIR_leaf_commutes` は、function-only definition tableをGlobalIRへ写したとき、PolyIR/GlobalIRのleaf項評価が任意fuel・environment・storeで一致することを証明する。対象はlocal/global lookup、Boolean/Integer/Float/String/Character/Unit、lambda、Nil/Noneで、`.core` fault wrapper越しにfaultとout-of-fuelも対応する。`functionTable_map_lookup` がglobal indexを保つ。引数列・再帰構文・mixed getter layout・Named/C変換の一般simulationは未完了。
2026-11-25追記: `functionTable_globalIR_arguments_commutes_of_pointwise` は、各引数式の任意fuel評価がPolyIR評価の`.core` wrapperと一致するなら、引数列評価も一致することを証明する。子項には親より1小さいfuelが渡る点を含めて列帰納を行う。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。各項評価の一般シミュレーションを前提とする補題であり、再帰構文・sequence・mixed getter layout・C境界への合成は未完了。
2026-11-25追記: `functionTable_globalIR_sequence_commutes_of_pointwise` は、各sequence要素のPolyIR/GlobalIR評価対応からsequence全体の結果対応を列帰納で導く。現在の累積値をtail inductionへ渡し、先頭式の成功・fault双方を処理する。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。一般の式評価simulationおよびmixed getter/C実行との接続は未完了。
2026-11-25追記: `functionTable_globalIR_begin_commutes_of_pointwise` は、`.begin first rest`についてfirstの評価対応とrest要素のpointwise評価対応から、GlobalIR/PolyIRの全体評価結果の一致を導く。firstのfault伝播と、成功時に得た値をsequence初期値にする場合を分ける。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。一般式再帰シミュレーションとmixed getter/C境界は未接続。
2026-11-25追記: `functionTable_globalIR_ite_commutes_of_pointwise` は条件・両枝の任意fuel評価対応からif式全体の対応を導く。条件fault、非Boolean条件のshape fault、選択された枝の評価を分け、未選択枝は評価しないことも一致させる。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。一般再帰式simulationとmixed getter/C境界への統合は未完了。
2026-11-25追記: `functionTable_globalIR_ite_commutes_of_pointwise` は条件・両枝の任意fuel評価対応からif式全体の対応を導く。条件fault、非Boolean条件のshape fault、選択された枝の評価を分け、未選択枝は評価しないことも一致させる。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。一般再帰式simulationとmixed getter/C境界への統合は未完了。
2026-11-25追記: `functionTable_globalIR_add_commutes_of_pointwise` は、加算の左右子項について任意fuelで評価が対応するなら、加算結果またはwrong-shape faultを含む式全体の評価が対応することを証明する。`lake build NLisp.GlobalIRErrorCorrespondence` 成功。ほかの二項演算、再帰的子項simulation、C/initializer接続は未完了。
2026-11-25追記: `functionTable_globalIR_ite_commutes_of_pointwise` は条件・両枝の任意fuel評価対応からif式全体の対応を導く。条件fault、非Boolean条件のshape fault、選択された枝の評価を分け、未選択枝は評価しないことも一致させる。`functionTable_globalIR_add_commutes_of_pointwise` は加算の左右子項の対応から、加算結果・wrong-shape faultを含む評価一致を導く。全体 `lake build NLisp` 成功。一般再帰式simulationとmixed getter/C境界への統合、ほかの二項演算は未完了。
2026-11-25追記: `lambda_application_termination_preserved_and_reflected` は、任意個のlambda parameter/argumentに対し、bodyと各argumentが`ArithmeticFragment`なら有限終了の保存・反映を証明する。`lambda_application_divergence_preserved_and_reflected` は同条件で有限big-step導出の不存在も両方向に対応させる。既存の`lambda_application_evaluation_reflected_of_fragments`を使い、引数個数上限を置かない。`lake build NLisp.NamedArithmeticReflection` 成功。lambda適用bodyを任意Named式へ広げる一般反映定理とC/展開証書の接続は未完了。
2026-11-25追記: `ContextualArithmeticTerm.floatBin` とその評価保存caseを追加し、Floatの四則演算がcontext-indexed environmentで、Float局所変数やそれ以前に導入されたbinderを使う場合もGlobalIR評価後に`.float`型を保つことを証明した。既存`evaluate_floatBin_of_children`の算術意味を使うため、NaN/無限大/丸めのC対応は対象外。`lake build NLisp.GlobalIR` 成功。GlobalIRの一般項型安全性、混在getter/callや全Builtinとの合成は未完了。
2026-11-25追記: `lambda_application_termination_preserved_and_reflected` と `lambda_application_divergence_preserved_and_reflected` は、任意arityの明示lambda適用についてbody/argument fragment条件の下で有限終了・有限導出不存在の両方向対応を示す。`lake build NLisp.NamedArithmeticReflection` 成功。
2026-11-25追記: `cSubstitutionStateAgree_initial_empty` は、C `check_call`の`calloc`で初期化されるscheme変数slot列とLean assignment列を、全slot emptyの状態不変条件へ対応付ける。`replicate_lookup_eq_some` が各slotのpointwise empty証拠を与える。`lake build NLisp.CTypeArguments` 成功。このabstract初期状態はC allocatorを形式化したものではなく、実Type* arrayからの対応・check_call全step simulationは未完了。
2026-11-25追記: `cMatchTypes_success_substitutes_result_like_Lean_from_empty` はC `check_call`の初期empty substitution列から制約matcher成功を開始し、全slot割当条件（Cの未決定型引数拒否に相当）・C/Lean partial-state simulation・結果型のC substitutionからLean `Ty.instantiate` decode一致までを合成する。`lake build NLisp.CTypeArguments` 成功。引数式のC型付け結果や実Type* memory layoutをLean条件へ導くcheck_call全体のステップsimulationは未完了。
2026-11-25追記: 上記の呼出し結果対応を含め、全45ターゲットの `lake build NLisp` を再実行して成功を確認した。今回試した「全slot割当からassignment列をcandidate列へ等置する」補題はLeanリスト添字の証明が未完了のため取り下げ、未検証の主張としては記録しない。22件の完了数に変更はない。
2026-11-25追記: `LambdaApplicationFragment` を定義し、bodyと任意長のargument listが`ArithmeticFragment`に属するlambda適用について、`lambdaApplicationFragment_evaluation_reflected`、有限終了の保存・反映、および「有限big-step導出が存在しない」と定義した非停止の保存・反映を追加した。`lake build NLisp.NamedArithmeticReflection` 成功。任意のwell-scoped型付きIR式への一般定理ではなく、fragment前提とlowered PolyIR evaluatorに限るため、課題1の主定理は未完了。
同変更後の全体 `.tools/lean-4.8.0/bin/lake build NLisp` も全45ターゲット成功。
2026-11-25追記: `collectArguments_complete_assignments_eq_candidate` は、候補型引数がparameter列で全slot出現し、候補置換が実引数列を与えるとき、collector完了後のassignment配列を`candidate.map some`へ等置する。`inferTypeArguments_complete_from_candidate` の証明をこの補題で置き換え、inferrable条件から全slot出現を導く経路を明示した。`lake build NLisp.CheckerCompleteness` 成功。C側matcher状態との対応やC `check_call`全体simulationは未完了。
同変更後の全45ターゲット `.tools/lean-4.8.0/bin/lake build NLisp` 成功。
2026-11-25追記: `cMatchTypes_success_infers_arguments_and_substitutes_result` は、初期empty substitution列から始まるC/Lean制約走査simulationと、C側の全scheme slot割当条件から、Lean側assignmentの充足を導いて型引数列を構成し、decode済みparameter列を実引数型列へinstantiateすること、およびC `substitute_type`結果のdecodeが同型引数列によるLean result `Ty.instantiate`と一致することを示す。`decodeCTypes_wellFormed` はC型配列の成功decodeからparameter型の量化変数scopeを導き、Lean collector soundnessへ供給する。別個のassignment対応・型引数列を仮定しない形でmatcher/引数制約soundness/戻り値型置換を合成した。`lake build NLisp.CTypeArguments` 成功。Cの実Type* arrayからpointer列・decode・monotype・slot完備条件を構成する証明と、call-site式型検査を含むC `check_call`全体のstep simulationは残る。
同変更後の全体 `.tools/lean-4.8.0/bin/lake build NLisp` は全45ターゲット成功。
2026-11-25追記: `CTypeArgumentInference.cMatchTypes_success_agrees_with_inferTypeArguments` を追加し、C matcher成功・slot完備から構成したLean型引数を、対応するheaderのparameter列を使う`inferTypeArguments_complete_from_candidate`へ入力して、Lean推論器の成功と戻り値型置換一致を結んだ。前提としてC/Lean scheme arityとparameter型列の一致、`inferrable`、collector fuel、推論候補長に対するchecker fuel上界を明示する。`lake build NLisp.CTypeArgumentInference` 成功。Cの実memory/type-pointer列からこれらのdecode・monotype・scope・fuel premisesを導くC `check_call`全体simulationは未完了。
同変更後の全体 `.tools/lean-4.8.0/bin/lake build NLisp` は新しいtargetを含む全46ターゲット成功。
同変更後の全体 `.tools/lean-4.8.0/bin/lake build NLisp` は全45ターゲット成功。
