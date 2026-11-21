# NLisp-Core C参照処理系

このディレクトリには、`SPECIFICATION.md` の組み込み関数と型付き関数・マクロを実行するC17処理系を置く。Leanコアの保証範囲は `LEAN_FORMAL_SPECIFICATION.md` を参照する。

## 対応機能

### 2026-11-19 追補: 構文照合と束縛ID意味論

`ExpansionLowering.lean` は、CBindingWalkが検査した同じ注釈付き構文と、提案されたSurfaceの各ノードを独立に照合する。シグネチャ、型注釈、束縛IDから局所添字への対応、引数順、並列let、match節、組み込み関数の固定表現を検査する。省略した型引数を持つ呼び出しは、全型変数が仮引数型に現れる場合に限る。型整合性は別途SurfaceCheckerが検査する。mainの宣言名・シグネチャと整数エントリーポイントも照合する。`readGlobalHeader` / `readGlobalHeaders` は注釈付きdefineから型、束縛ID、初期化式と元宣言位置を読み取る。これは後続形式へまだ変換・接続していない。

`NamedSemantics.lean` は、局所変数を束縛IDで参照し、環境をIDと値の対応列として扱う独立した有限評価意味論である。`NamedDecoder.lean` は元の注釈付き構文からこの操作的構文を読み取る。型注釈・型適用は操作的構文では実行しないが、元構文と型付きIRの注釈対応を上記の照合器で検査する。

`NameLowering.evaluation_preserved` は任意の有限のNamed評価を、位置添字を使う実行用IRの評価へ移す一般定理である。クロージャ、共有された再帰関数表、並列let、List/Option照合を含む。poly証書は元構文の読み取り、生成IRとの型消去後の一致、`source_evaluation_preserved` を入力ごとにカーネル検査する。単に型が合う別の出力を提示しても受理されない。

逆向き評価証明の基礎として `lookup_lowered_reflects` と `variable_evaluation_reflected` を追加した。lowered environmentの位置lookupが値を返すなら、元のNamed環境で同じbinder identityをlookupして対応する値を得られ、IRの変数評価導出をNamed側へ反映できる。`definitions_lookup_reflects` / `global_evaluation_reflected` は大域参照を、各リテラル反映補題は定数評価をNamed側へ戻す。`lambda_evaluation_reflected` はIRのclosure生成導出をNamedのラムダ評価へ戻し、クロージャ値のlowering一致まで示す。`add_evaluation_reflected`、`sub_evaluation_reflected`、`mul_evaluation_reflected`、`le_evaluation_reflected`、`intEq_evaluation_reflected`、`ite_evaluation_reflected`、`some_evaluation_reflected`、`cons_evaluation_reflected` は子式の反映を入力として算術・比較・分岐・Option構築・List構築の評価を合成する。さらに `arguments_evaluation_reflected` と `sequence_evaluation_reflected` は各要素の反映証明を受けて列の評価を合成し、`begin_evaluation_reflected` はその補題を使ってbegin評価を反映する。対応する構成子の例を `tests/NameLowering.lean` で検査し、モジュールのLeanビルドも成功した。これらは構成子ごとの部分結果であり、クロージャ適用や他の複合式を含む評価全体の逆向き定理は未証明。

クロージャ適用の環境対応を支える補題として、`lowerEnv_bind_append` は引数をbindしたNamed環境をlowerするとIRの引数値列と捕捉環境の連結になることを示し、`identities_bind_append` と `lower_call_body` はその環境のbinder ID列および本体のloweringを `ids ++ identities env` と一致させる。具体例を `tests/NameLowering.lean` で検査した。クロージャ適用の逆向き評価証明そのものは未完了。

`letMany_evaluation_reflected` は、初期値数がbinder ID数と一致する整形式条件の下で、IRの初期化列と本体評価の反映証明からNamed側のletMany評価を構成する。IRはletManyのbinder ID数を消去するため、この前提をIR評価だけから導けるとはしていない。単一binderの変数参照例を `tests/NameLowering.lean` で検査した。全式の逆向き定理やこの整形式条件を元ソース証書から得る接続は未完了。

`matchList_evaluation_reflected` は、target/empty branchの反映と、cons branchに追加されたhead/tail値に対応する環境での本体反映を入力として、list match評価をNamed側へ戻す。`matchOption_evaluation_reflected` もnone/someの分岐を同じ方法で反映し、some branchではpayloadを追加した環境の本体評価を使う。各caseの具体例を `tests/NameLowering.lean` で検査した。各ケース補題を単一の一般評価反映定理へ統合する帰納証明は未完了。

`EvaluationReflection` はNamed環境・binder ID列・IR環境・lowered式の対応を保つ相互帰納法のmotive候補として定義した。`appClosure_evaluation_reflected` はこのmotiveから関数、引数列、本体評価を反映し、引数bind後の環境・arity・body loweringを接続する。`appGlobal_evaluation_reflected` は大域関数lookupを逆向き定義lookupへ接続し、引数環境で本体を反映する。`app_evaluation_reflected` はIRの二つのapplication規則をこの補題へ振り分ける。これらは帰納ステップの補題であり、motive自体を成立させる全constructorの相互帰納証明はまだ完了していない。

逆向き評価の無条件主張には反例がある。`letMany`のbinder IDリストはIR loweringで消えるため、ID数0・初期値1個のNamed式はIR上では評価成功するが、Named側はarity条件により評価できない。この反例を `tests/NameLowering.lean` で検査した。したがって一般定理には、デコーダ／型検査が保証するletMany arity、ソースのwell-scoped性、およびプログラム・環境に入るclosureの不変条件を入力へ明記する必要がある。これらの条件と全式反映の統合は未完了。

`NamedDecoder.letParts_lengths` は成功したlet binding走査でbinderとinitializerの件数が等しいことを示し、`decodeExprs_length` は成功した式列decodeがNode件数を保つことを示す。decodeExprのlet分岐を `decodeLetMany` に集約し、`decodeLetMany_lengths` で実際のlet decode成功結果についてもbinder数とinitializer数が等しいことを証明した。さらに`letLayoutsAligned` が全式木中のlet件数を検査し、`decodeExprChecked` / `decodeFunctions` はこの条件を満たす関数本体だけを返す経路を定義する。`decodeExprChecked_spec` と `decodeExprChecked_letMany_lengths` はchecked decode結果からletのbinder/initializer長さを取り出し、`decodeFunctions_letLayoutsAligned` / `decodeProgram_letLayoutsAligned` はdecodeProgram出力の全ネストletに対する保証を述べる。`definitionsLetLayoutsAligned_mem`、`decodeProgram_member_letMany_lengths`、`decodeProgram_lookup_letMany_lengths` はその保証を出力定義の任意のletとindex lookupへ適用し、`decodeExprChecked_letMany_evaluation_reflected` はchecked decodeから `letMany_evaluation_reflected` へ長さ条件を渡す。評価反映の帰納仮定自体を構成する一般定理は未完了で、Leanビルド確認も残る。
`definitions_lookup_reflects` と `global_evaluation_reflected` も加え、lowered定義表の要素から元の定義を復元し、IR global評価をNamed側へ反映する。テストでは一要素の関数表に対するglobal評価を確認した。これらの補題はlookupと二つの原子ケースだけを扱い、関数適用・クロージャを含む評価全体の反映は未証明。
bool、int、unit、nil、noneの評価規則についても対応する `*_evaluation_reflected` 補題を追加し、Named側の値を構成してIR値へのlowering一致を証明した。関数適用、条件分岐、再帰データ値やクロージャを含む一般評価の反映は未証明。

この定理は有限評価の前向き保存であり、逆向きの評価反映、Named意味論とC実行器の対応、新多相モデルの型安全性、検査器全体の多項式時間を追加で保証するものではない。保証範囲の `formal_semantic_preservation` は処理系全体の保証ではないためfalseを維持し、polyのkernel_checksに上記の部分保証を列挙する。

名前変換は数値IDを含むsizeOfによる再帰から、構文の入れ子帰納原理へ変更した。Lean 4.8のネイティブコード生成がこの帰納原理に未対応のため、この証明用変換はnoncomputable指定だがカーネル内では簡約できる。Cの実行器と既存の実行可能な型消去関数は維持する。これは検査器全体の計算量上界の証明ではない。

`TypeArguments.lean` は一方向の型引数収集アルゴリズムと証明付き結果を追加する。戻り値の期待型を入力にせず、呼び出し側の型変数を固定した構文として扱い、未決定変数や競合する制約を拒否する。成功値は型引数個数、呼び出し側での整形式性、仮引数型の具体化と実引数型の一致、一意性を保持する。`inferred_arguments_unique` は、全量化変数が仮引数型に現れるという判定の受理から、任意の二つの整合する型引数列が等しいことを証明する。`collectorTypeFuel` / `collectorTypesFuel` は制約走査の計算可能な構造fuelを定める。`CheckerCompleteness.inferTypeArguments_complete_from_candidate` は、整形式かつ仮引数と実引数に整合する候補について、全量化変数の出現とcollector・型検査両方の構造fuelを前提に推論器がその候補を返すことを証明する。`inferTypeArgumentsCandidateFuel` は二つの計算可能なfuel境界の最大値を返し、`inferTypeArguments_complete_at_candidate_fuel` はその上界で完全性を示す。Cの推論器との一般的な対応と、新多相モデルの型安全性は別課題である。

### 2026-11-19 追補: 多相評価器の型安全性

`PolymorphicSafety.lean` は、型変数の解釈、型付きの実行時値・環境、共有された全関数本体の型付け条件を定義する。`evaluator_type_safe` はfuelに関する帰納法で、式・引数列・begin列の評価が、型に合う値またはoutOfFuelに限られることを同時に証明する。`evaluation_preserves_type` は成功結果の型保存、`evaluation_no_type_error` はunbound/wrongArity/wrongShapeが起きないことの系である。汎用本体を一つだけ保持し、多相再帰で変わる型引数は証明中の解釈だけで扱う。

`elaborateProgram_programTyped` はSurfaceCheckerの成功から全ソース本体の型付け条件を導く。証明付き項を生成した事実だけでなく、その項のexpressionが元の入力本体と同じであることも証明する。poly証書に `program_typed` と `entry_has_no_type_error` を追加し、型検査済みの実際のエントリーポイントへ接続した。`tests/PolymorphicSafety.lean` は汎用identityと型が成長する多相再帰を扱い、依存公理は標準3公理のみ。

対象は新SurfaceモデルのBoolean/Integer/Unit/関数/List/Optionである。これは有限予算の評価器に関する意味的な型安全性であり、別途定義した小ステップ関係に対する構文的Progress定理やC実行器全体の正しさと同一視しない。初期実装記録にある新多相モデルの「型安全性未証明」は、この評価器と対象型の範囲について更新された。

### 2026-11-19 追補: 大域値を捕捉するCクロージャ

C実行器で、大域値の初期化前に生成したクロージャが、後から初期化された同じ束縛を参照できない例を修正した。全大域値に未初期化の共有セルを先に確保し、ソース順に各初期化式を実行してセルを一度だけ埋める。関数・ラムダは同じセルを参照する。未初期化セルを実際に読むと、内部のunboundではなく「before its initialization」の初期化エラーを返す。局所束縛やマクロ定義位置のスコープは維持する。

CとGlobalIRの状態表現には次の対応がある。Cの`RBind.value == NULL`はGlobalIRのstore slotの`none`、初期化後の`RBind.value == v`は`some v`に当たる。Cの`value_slots[i]`は各`D_VAL`宣言に対応する共有`RBind`ノードを指し、初期化ループはこの同じノードの`value`を書き換える。GlobalIRでは同じslotをstore listのindexで表し、getter定義が呼出し時のstoreから読む。Cの`Program` indexからdefine ordinalへの対応、文字列名検索とNamed binder IDの対応を保つ状態関係およびC実行ステップとのシミュレーション定理は未実装であり、この表現上の対応だけを形式証明済みとは扱わない。

`tests/global_initialization.py` は、後から初期化されるセルを参照する脱出クロージャ、局所シャドーイング、初期化中の読み出し、未選択分岐、未使用でも実行する初期化式、マクロの定義位置を確認する。Cの修正と規範仕様の明確化であり、polyモードへのdefineの変換と初期化・捕捉の意味保存証明はまだ実装していない。

`GlobalIR.lean` はこの変換を接続するための実行可能な基礎モデルである。大域値は未初期化/初期化済みのストアに保持し、内部の0引数getterが呼び出し時のストアを読む。クロージャの局所環境へ古い大域値を固定せず、初期化式をソース順に実行してからエントリーポイントを実行する。`initialization_length`、`initialized_prefix_unchanged`、`initialized_cells_present` により、成功した初期化はセル数を変えず、先行セルを上書きせず、処理した範囲を初期化済みにすることを証明した。さらに`evaluate_lambda_store_independent`はクロージャ作成がストアに依存しないことを、`getter_call_reads_current_store`と`getter_call_reports_early_read`はgetter呼び出しが現在のストア値を返すことと未初期化時の専用エラーを証明する。`initializeValues_stops_on_error`と`initializeValues_commits_head`は、初期化式の失敗で処理を止め、成功時はその値をセルへ格納してから次へ進むことを示す。これらのgetter呼び出し定理は評価fuelを2以上とする。`tests/GlobalIR.lean` はCと同じ脱出クロージャの例を実行し、上記の定理の公理依存も出力する。このモデルの入力はIRであり、元ソースのdefineからの変換・型安全性・C実行器との対応を証明したとは扱わない。
`StoreWellTyped` は初期化済みセルを型付きとする条件を定義し、`StoreWellTyped.set` は型付き値をセルへ書き込んでもこの条件が保たれることを示す。`initializeValues_preserves_typed` は初期storeが型付きで、各slotの型対応があり、各initializer評価が型付き値を返し、列がstore範囲内に収まるなら、成功後のstoreも型付きであることを示す。`readGlobal_preserves_type` と `getter_call_preserves_type` はその条件下でgetter読み出しの返値型を保存する。GlobalIR評価器の型安全性からinitializer評価の前提を導く証明、通常関数評価と拡張型への一般化は未完了。

`GlobalProgramTyped` は明示的な `functionSources` 対応表を取り、combined runtime table indexとsource function definition indexを分けてfunction entryを元のchecked source body・signatureへ結ぶ。`functionSourcesFor` は関数prefixの同一index対応を生成し、`mem_functionSourcesFor_iff` はその範囲を特徴付ける。`functionEntries` は関数本体をeraseしてgetter参照を書き換え、`assembleProgram` はその関数列の後ろへslot getter列を連結する。`assembleGlobals` は対応するsignature列を作り、`assembled_function_source_layout` / `assembled_getter_layout` は関数・getterのruntime indexをsource signatureやslot typeへ対応づける。`AssembledSourceTyped` の仮定から `assembleProgram_typed` がこのtableの `GlobalProgramTyped` を構成する。`getterMappings` / `getterFor_getterMappings` と `lowerGlobalReads_global_value_getter` は関数prefix後のglobal value indexをgetter callへ接続する。`ExpansionLowering.globalValueIndex` / `globalValueReferenceIndex_sound` と `NamedDecoder.globalIndex_value_reference` はGlobalHeaderのbinder IDからslot index・function-prefix込みglobal indexへの対応を示す。`ExpansionLowering.readProgramHeaders` / `NamedDecoder.decodeTopLevelProgram` は混在した関数・値global列をそのindex規約でdecodeし、slot型・initializer数の一致を証明する。`GlobalIR.assembleNamedProgram` / `programOfNamed` はdecoded function bodyとinitializerをgetter付きtable・store初期化列へ変換する。`assembleNamedProgram_length` / `programOfNamed_definition_count` はruntime definition tableの全長が関数数+slot数になることを示し、`programOfNamed_getter_lookup` はcombined indexで各slotのgetter entryを特定する。`decodedProgram_layout` はdecode成功からruntime table全長・initializer数・値slot getter位置を一つの結論へまとめる。decode結果から型付きlayoutを導く型証明と、実行時のソース意味保存およびGlobalIR評価規則全体の型不変条件はまだ証明されていない。Leanビルド確認は未完了。
`empty_store_well_typed` と `initializeValues_from_empty_preserves_typed` は初期化開始時の全slotが未初期化である実際のstore形状から同じ型不変条件を保つ。各initializer評価の型付き性は依然として前提であり、それをGlobalIR評価器から導く型安全性証明ではない。Leanビルドでの確認は未完了。

`InitializerTypesAgree.slot_type_at` は、この合意条件の下でinitializer列内の各offsetから対応slot型を取り出す。これは初期化列をslot型列と照合する補題であり、initializerを実行した値の型保存を単独では証明しない。
`lowerGlobalReads`は値定義indexとgetter定義indexの対応表を受け取り、値位置のglobal参照を零引数getter呼び出しへ書き換える。適用先がgetter対応表にある場合はgetterで値を取り出してから引数を適用し、対応表にない関数参照と局所変数は保持する。このIR上の書き換えを確認したが、source binder IDと大域表indexから対応表を構築する変換や、その意味保存は未証明である。
`Diverges`は任意の正のfuelで評価がfuel切れになる性質として定義した。自己再帰関数の例で発散を示し、発散するinitializerが後続の初期化式へ進まないことを証明した。これはこのfuel付きGlobalIR評価器の意味であり、C評価器やソース評価との非停止対応ではない。

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

`SurfaceChecker.lean` は全Surface構文の実行可能な型検査と証明付きIR構築を行う。`elaborateProgram` は共有された全シグネチャの下で各汎用本体を一度検査し、再帰・相互再帰・多相再帰を具体化なしに受理する。成功値自体に `HasType` の証明を保持する。明示的型引数を持つ展開後構文が入力であり、Cの一方向型引数推論の正しさはまだ接続していない。checkerの深さ予算超過と型不適合はともにnoneとなるため、noneは不適合の証明として使わない。C CLIでは深さ・作業予算超過を `NLISP_UNKNOWN`、型不適合を `NLISP_TYPE_ERROR` として区別する。`CheckerCompleteness.lean` の `checkerTypeFuel` / `checkerTypesFuel` は型木と関数型引数列から整形式性検査用fuelを直接計算し、`checkWF_sufficient` と `checkTypesWF_sufficient` が十分性を証明する。`checkerSignatureFuel` / `checkSignatureWF_sufficient` はシグネチャの全parameter型とresult型をこの境界で検査できることを示す。計算可能な `checkerExprFuel` / `checkerExprsFuel` は式と式列の子fuel・注釈・参照対象の全global signatureを合成し、`inference_structural_fuel` は得られた上界以上のfuelで`infer`が証明付き結果を返すことを示す。C推論器との対応と候補条件に依存しない型引数決定完全性は未完了。一般的な型保存・Progressも未証明。

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

Cの`match_type`は型変数を宣言中の`Type*` identityで識別し、Leanの`collectArgument`は局所de Bruijn indexで識別する。どちらも実引数型を一度だけ記録し、再出現時は完全一致を要求して、List/Option/関数型の内部を再帰する。`collectArgument_first_variable_capture` はcaller側の `Ty.var` を再帰的に解かずそのまま格納し、`collectArgument_repeated_variable_same` / `_conflict` は同じ制約の一致・不一致をCと同様に分ける。Leanの成功結果の健全性・一意性はカーネルで証明済みだが、C側のpointer identity・monotype検査・配列代入を含む一般シミュレーション、収集器の完全性、式全体の構造的fuel上界は未証明である。比較表と条件は`RESEARCH_FORMALIZATION.md`に記録する。

Cの照合ステップに対応して、`AssignmentsAgree.set` は既存制約と候補型引数列の一致を更新後も保ち、`collectArgument_first_variable_agrees` / `collectArgument_repeated_variable_agrees` は型変数の単一出現・再出現をこの不変条件へ接続する。複合型木とparameter列全体に対する帰納的collector完全性にはまだ接続していない。

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

CMakeはPythonベースのテストで`PYTHONUTF8=1`を設定する。Windowsのシステムロケールが日本語でも、UTF-8のJSON・Lean証明項をCP932として読み書きしないためである。

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

`ExpansionCertificate.checkWithTraversalCost` は、局所証書のコンストラクタを1件1単位として走査コストを返す。`checkWithTraversalCost_result` で通常の `check` と結果が一致し、`checkWithTraversalCost_le_nodes` でコストが証書コンストラクタ数以下であることを示す。このコストモデルは証書木の制御構造だけを扱い、macroStep内の `matchRule`・`copyWithMacros`、環境探索、型照合のコストを数えない。したがって検査器全体の上界や多項式時間保証にはならない。

`--verify-certificate ... --independent` はC処理系を起動しない。元ソースと展開導出の証拠、変換記録から本文を再構成し、読み取り・正規化・局所展開・束縛対応をLeanカーネルで検査する。存在しない `--nlisp` を指定して数学マクロの実証書を検査する統合確認に成功した。通常の再実行方式も残す。

JSON内の重複キー、不正なBase64、ダイジェスト不一致、別のLean環境、再現できない入力・規則適用・変換・本文はエラーとする。暗号署名はなく、保証範囲のフィールドにもその旨を明記する。検査器全体の正しさと多項式時間上界の一般証明は残る。証書のassurance内のprocess欄は生成時の記録方式であり、再検査にCを起動したかは選択した検査モードによる。

元ソース・証明書の読み込みとC過程出力の取り込みにも証明書のバイト上限を適用し、上限を超えた出力をメモリへ無制限に取り込まない。上限超過時は自分が起動したC子プロセスを終了して回収し、Unknownを返す。証明書自体の改行はLFに固定し、同梱する元ソースの改行・UTF-8バイト列はそのまま保持する。

### 入力サイズと計算量の範囲

独立検査器の入力サイズを、検査する単一証明書の実ファイル長 `B` バイトに対する `N = 8B` ビットと定義する。証明書には元ソース、構文、型、識別子、数値、過程記録、Lean本文がそれぞれの実際の符号化で含まれるため、Base64・JSON・10進整数・Lean本文の表記長も `N` に数える。元ソースを証明書外から別途渡す方式を測る場合は、そのファイル長も加算する。

証明書形式は構文木をJSON配列の木として直列化し、参照共有をポインタやDAG参照として符号化しない。C側でマクロ引数の構文を共有しても、証明書では出現ごとに直列化される。再検査時は各出現を個別に検査し、ノード間の結果キャッシュは使わない。したがって `N` は展開で複製された構文と証明本文のサイズも含むが、Lean本文の生成・精緻化・カーネル検査の計算量上界は別途証明が必要である。

Lean側では `checkWithTraversalCost` が局所証書コンストラクタ走査を1ノード1単位で上から数え、`checkWithTraversalCost_le_nodes` が証書ノード数以下を示す。`freshIntervalCount_le_nodes` はfresh区間数も同じノード数で抑え、`intervalPairComparisonCost_le_square` は重複検査の区間pair比較回数を区間数の二乗以下に抑える。`checkFreshStructuralCost_polynomial` は両工程を合成し、ノード数を `n` とした部分コストが `n + n²` 以下と示す。これはpair述語の呼び出し回数であり、任意精度Natの比較に必要なビット演算は数えない。また `macroStep` 内の規則探索・構文照合・`copyWithMacros`、型検査とLeanカーネルのコストも含まないため、独立検査器全体の多項式上界を示すものではない。

`CMacroCopy.lookupWithCost` は連想リストのlookupで検査したキーごとに1単位を数え、結果が通常の `lookup` と一致し、費用が環境リスト長以下となる構造モデルを定義する。失敗lookupは全キーを検査するため、`lookupWithCost_miss_scans_all` で費用が環境長と等しいことを示す。`binderWithLookupCost` はbinder処理のlookup部分へこの計数を接続し、lookupを含む結果の一致と同じ長さ上界を置く。`copyParametersWithLookupCost`、`copyPatternWithLookupCost`、`copyBindingsWithBinderLookupCost` は列走査とhole lookup費用を合成し、通常の各copy操作との結果一致および列長×(hole環境長+1)+1の上界を示す。最新のWSL Lean 4.8ビルドで`NLisp.CMacroCopy`は`Built`となり、これらの定理を含むファイルのコンパイルを確認した（unused-variable警告あり）。これは文字列比較を1単位とみなすモデルであり、文字列長に応じた比較コスト、fresh token文字列生成、Nat演算、initializer内部やcopy全体の構文走査・型照合は含まない。

`copyParametersWithLookupCost` はparameter-binder列の各要素に1単位、実行したhole lookupのキー比較ごとに1単位を課し、通常の`copyParameters`との結果一致と「列長×(hole環境長+1)+1」の上界を与える。WSL Lean 4.8ビルドで確認済み。型payload検査やlambda全体の他のcopy処理は含まない。

`copyPatternWithLookupCost` は任意マクロ集合のmatch pattern binder列にも同じ走査・lookup費用を与え、`copyPatternWithMacros`との結果一致と同じ列長上界を定義する。WSL Lean 4.8ビルドで確認済み。patternの構造検査とcase body copyはこの部分モデルの対象外である。

`copyBindingsWithBinderLookupCost` はlet binding列の各binder lookupと行走査を計量し、`copyBindingsWithMacros`との結果一致と列長上界を与える。WSL Lean 4.8ビルドで確認済み。initializerの通常copyを呼び出すが、その内部費用は明示的に計量対象外とするため、let全体のcopy費用ではない。

`CExpansion.holeEntriesWithCost` は、マクロ呼び出しの仮引数と実引数の対応付けに対し、各対応要素と終端または形状不一致を1単位として数える。通常の `holeEntries` と同じ結果で、費用は仮引数列の長さに1を足した値以下となる。これは `matchRule` の浅い形状・名前比較、文字列長依存の比較、リスト割当、後続の `copyWithMacros` を含まないため、局所的な引数対応付けの上界である。Leanビルドでの確認は未完了。

最新のWSL `lake build` では `NLisp.CMacroCopy` はwarningのみでビルド成功した。`NLisp.CExpansion.holeEntriesWithCost_result` はOption mapとdo記法のbindの一致で失敗し、修正を追加した。`NLisp.ExpansionLowering.globalValueIndex_lookup_sound` ではslot indexの等式方向とcons後のlist lookup条件で失敗し、両方を補題で明示する修正を加えた。これらの修正は次回ビルドでの確認待ちである。

`matchRuleWithCost` はこの対応付けモデルに浅い規則・呼び出し形状とhead名の判定を1単位で加え、通常の `matchRule` と同じ結果および仮引数数+2の上界を定義する。文字列比較のbitコストや固定形状パターンマッチ内の各constructor検査を個別には数えない。このモデルも証明書の `macroStep` 全体や `copyWithMacros` の計算量上界ではない。Leanビルドでの確認は未完了。

`ExpansionCertificate.membershipWithCost` は規則一覧の所属探索で実際に調べた各要素を1単位として数え、比較回数が一覧長以下であることを示す。`checkStepWithMatchCost` はこの探索費と規則照合費を局所証書stepへ接続し、通常の `checkStep` と同じ真偽値を返す。その上界は仮引数数 + 規則一覧長 + 2 である。`copyWithMacros` の判定は実行するが内部費用はこのモデルから除外するため、検査step全体の上界を与えるものではない。Leanビルドでの確認は未完了。

`checkWithMatchTraversalCost` はこの局所費用を `refl` / `congList` / `macroStep` / `trans` に再帰的に合成し、`trans` の接続点等値判定呼び出しとその左endpointの構文node比較費を数える。`checkWithMatchTraversalCost_result` は通常の `check` と判定が一致すること、`checkWithMatchTraversalCost_le_bound` は `certificateMatchCostBound rules` 以下となることを示す。各macroStepの上界は埋め込みruleの仮引数数 + 規則一覧長 + 2 である。`certificateMatchCostBound_eq_components` の費用成分には証書node数、仮引数総数、macroStep数×(規則一覧長+1)、trans数、endpoint比較node数の合計を含む。`treeNodeCount` は構文木のconstructor数を数え、`treeEqWithWorstCaseCost` は左endpoint全体を課金する保守的な費用を返す。証書内の構文payloadを含む入力バイト長への上界、atom payloadのbit費用、copy本体の費用はまだ示しておらず、全検査器の多項式時間保証ではない。変更後のLeanビルド確認は未完了。

`CMacroCopy.treeNodeCount` はatom payloadの大きさに依存せず構文木のconstructor数を数える。`treeEqWithWorstCaseCost` は等値判定の結果を保ち、左operandの全constructor数を課金する保守的な比較費用を返す。`certificateTransComparisonCost` はこの比較費を証書のtransノードすべてに合成する。証書byte長への上界接続とatom名・整数tokenなどpayloadのbit費用は対象外で、Leanビルド確認も未完了。

`separatedManyWithCost` と `disjointIntervalsWithCost` は、fresh区間検査における端点検査と区間pair比較を短絡評価に合わせて計量し、通常の `disjointIntervals` と同じ結果を返す設計である。`checkFreshWithMatchCost` はこの費用と規則照合費を合成する。証書ノード数を `n` とすると、部分費用の上界は `certificateMatchCostBound rules + n² + n` となる。copy本体、構文payload、Nat比較のbit費用は除外する。Leanビルドでの確認は未完了。

`certificateMatchCostBound_eq_components` は、照合・接続点判定とendpoint比較の累積境界を証書node数、各macroStep規則の仮引数数の合計、macroStep数×(規則一覧長+1)、trans数、endpoint比較node総数へ分解する。これは部分モデルの費用内訳であり、構文payload上のbit費用やcopy本体を含む実際の実行時間の主張ではない。費用式変更後のLeanビルド確認は未完了。

`certificateMacroStepCount_le_nodes` と `certificateTransCount_le_nodes` によりmacroStep数・trans数は証書node数以下となる。`certificateTransComparisonCost_le_count_mul_max` は比較node総数をtrans数×最大endpoint構文node数に抑え、`certificateMatchCostBound_le_endpoint_polynomial` と `checkFreshWithMatchCost_le_endpoint_polynomial` は照合・endpoint比較・freshness費用を証書node数、規則一覧長、仮引数総数、最大endpoint構文node数の多項式で抑える。最大endpointサイズを証書byte長へ抑える証明は未完了のため、証書byte長に対する計算量保証はまだ主張しない。copy本体・atom payload bit操作も対象外で、Leanビルド確認は未完了。

`certificateEndpointPayloadNodes` は、各証書nodeのsource/target endpoint、trans接続点の左endpoint、およびその子証書のendpoint syntax nodeを合計する。`certificateMaxEndpointNodes_le_payload` と `checkFreshWithMatchCost_le_payload_polynomial` により、最大endpoint構文node数をこの集計値で置き換えた構造サイズ上界を追加した。この値を実際のJSON/Lean証書byte長へ結ぶ符号化定理はまだなく、byte-size計算量保証ではない。Leanビルド確認も未完了。

2026-11-20の探索的比較を `tools/benchmark_certificates.py` で行った。各例1回、Windows上で、証明書なしの `run`、証明書生成、C再実行付き再検査、Cを使わない独立再検査を計測した。展開結果サイズは `nlisp expand` の出力バイト数、証明書サイズは最終Leanファイルのバイト数である。メモリは親子プロセスのRSSを10ms間隔でサンプルしたピーク値であり、厳密な最大値ではない。

| 例 | 入力 / 展開 / 証明書 bytes | 実行 秒 / MiB | 生成 秒 / MiB | 再実行検査 秒 / MiB | 独立検査 秒 / MiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| factorial | 141 / 122 / 82,082 | 0.026 / 2.0 | 10.14 / 476 | 9.78 / 475 | 9.78 / 475 |
| macros | 963 / 302 / 225,248 | 0.024 / 2.0 | 23.52 / 555 | 23.80 / 558 | 23.88 / 557 |
| polymorphism | 611 / 463 / 186,505 | 0.024 / 2.0 | 35.52 / 551 | 34.89 / 552 | 35.44 / 551 |

これは統計的な性能評価ではなく、各条件1回の観測である。使用した既存C実行ファイルは基準コミット `9a0f9f8` 相当で、現HEADに含まれる後続の大域初期化修正と今回のID上限ガードを含まない。対象例での目安に限り、現HEADの再ビルドを使った再計測が残る。生成・検査時間はLean検査が主で、これらの例では再実行と独立検査の差は小さかった。この観測から漸近計算量の主張は導かない。


## 束縛環境の形式モデル

`NLisp/ScopedSyntax.lean` は全実行時型の型付けモデルに、束縛IDを持つ環境、所属環境付き構文、定義位置・呼び出し位置からの別々の埋め込みを追加する。埋め込みには型保存だけでなく束縛ID保存の証明を要求する。重複IDの環境は許可しない。テンプレートの穴と捕捉変数を別の代入領域として定義し、導入した束縛子の下では既存参照を持ち上げる。

C処理系は一意化した内部名、定義位置の環境スナップショット、Macro.originに加え、アトムのトークンID・実際に選んだ束縛ID・型タグ・名前解決に使用した環境を記録する。通常の証明書は、有限の展開に関する衛生的置換と束縛IDをLeanで照合する。証明書は使用した各Leanモデルのハッシュも記録し、異なるモデルに対する過程記録を黙って受理しない。C全体の機械意味論と形式モデルの一般的な対応証明は含まない。


## 2026-11-18追加: C展開とスコープの証明書検査

識別子IDは組み込みが `3*(index+1)`、元の字句が `3*(tokenIndex+1)+1`、生成した束縛名が `3*freshCounter+2` である。Cのfresh counterはこのIDを`size_t`で表現できる範囲に制限し、範囲を使い切ると `Unknown` を返す。名前の文字列比較による実際の探索境界で、要求名・選択した束縛・環境・定義位置を観測する。型タグはCの型オブジェクトの識別用であり、型意味論の証明済み符号化とは扱わない。

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

## 2026-11-20 追加作業: WindowsビルドとGlobalIR

UCRT64 GCCのCMakeビルドではコンパイラ子プロセス`cc1.exe`が起動できず、変更したCソースが再コンパイルされないことを確認した。Visual Studio同梱Ninja、MSYS2 Clang、静的GMPを明示してCMakeを構成し直し、`nlisp.exe`を再生成した。生成物を`build-ucrt/nlisp.exe`、`build/Debug/nlisp.exe`、`build/Release/nlisp.exe`へ反映し、factorialが120を返すことと組み込み・構文・大域初期化のCテストを確認した。

全体CTestで日本語Windowsの既定文字コードによりPythonがUTF-8証明データをCP932として扱う問題を再現したため、CMakeのPythonテストに`PYTHONUTF8=1`を設定した。これによりlean_bridge、macro_termination、source_reader、poly_bridgeをそれぞれ再実行し、修正済みの停止性期待とマクロ宣言専用例の対象範囲を反映して成功を確認した。GlobalIRには正の全fuelでfuel切れとなる`Diverges`定義、再帰関数の例、および発散initializerが後続初期化を止める定理を加え、`tests/GlobalIR.lean`でカーネル検査した。これらの作業は残るマクロ全体の終了性、ソースからGlobalIRへの意味保存、CとLeanの一般シミュレーションを完了するものではない。

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

任意のマクロ集合に対する `MacroCounterSafeInitializer` / `MacroCounterSafeBindingInputs` は、atom、atom一個・二個listに加えて、先頭が`match`でない任意長のatom-only listを表す。`atomList` constructorのcounter保存は `copyWithMacros_atomTrees_keeps_counter` で示す。さらに `singletonWrapped` constructor と `copyWithMacros_singleton_child_preserves_counter` により、同条件を満たす子を単一要素listで包んだinitializerを任意の深さで構成できる。`pairChild` / `copyWithMacros_pair_child_preserves_counter` はatom headの二要素listにもcounter-preservingな子を許す。`tripleChildren` / `copyWithMacros_triple_children_preserves_counter` はheadが`match`・`let`でなく、第2要素がatomの場合に第3要素へcounter-preservingな子を許す。`quadrupleChildren` / `copyWithMacros_quadruple_children_preserves_counter` はheadが`match`でない4要素listの第4要素へ同条件の子を許す。さらに `CounterNeutralTree` / `counterNeutralTree_preserving` は、全てのリストheadがマクロ名および `match` / `let` / `lambda` 以外である任意深さのネスト木を構造帰納法で扱う。このconstructorは `MacroCounterSafeInitializer.neutralTree` としてbinding列のfreshness合成へ接続されている。いずれの条件もbinder特殊形式やマクロ展開を含む任意initializerを網羅しない。counter保存証明を `CounterPreservingBindings` に変換でき、一般定理からbinder token列の一意性、source-token分離、fresh区間所属を導く。`checkFresh_separates_macro_counter_safe_binding_tokens` はその出力を別証書区間間の非衝突へ接続する。

`tests/CMacroCopy.lean` は、三段のsingleton wrapper、atom headの二要素list、制限付き三要素listを含むinitializer、およびbinding列への合成をLeanで検査する。

`CounterPreservingCases` は、match case列の各bodyがcounterを保持する前提を表す。`copyCasesWithMacros_preserving_counter` はpattern中のbinder数だけcounterが進み、それ以外のbody/tail走査はその前提の下でcounterを追加消費しないことを証明する。`copyCasesWithMacros_preserving_token_sequence` は各出力pattern binder tokenを連続counter列に同定し、派生補題が一意性・source-token分離・区間所属を導く。`checkFresh_separates_case_copy_tokens` は別々の証書区間間の非衝突を示す。これらはcase bodyのcounter保存を前提とし、C実装との対応は未証明。

`MacroCounterSafeCases` は各case bodyに `MacroCounterSafeInitializer` 条件を与える構成的な入力型であり、atom、短いlist形状、または先頭が`match`でない任意長atom-only listを扱う。`macroCounterSafeCases_preserving` により抽象case条件へ変換でき、`checkFresh_separates_macro_counter_safe_case_tokens` はこの条件付き入力に対する区間間非衝突を直接導く。

`counterTokens_within_interval` は生成token列の各要素から対応counterを復元し、開始値より大きく、開始値と操作内binder数の和以下であることを示す。これを `copyParameters_tokens_within_interval` と `copyPattern_tokens_within_interval` へ接続し、出力tokenをfresh区間内のcounterへ対応付けた。証書に記録された任意の `copy` 区間との対応には、構造全体のcounter合成がなお必要である。

`ExpansionCertificate.checkFresh_separates_parameter_copy_tokens` と `checkFresh_separates_pattern_copy_tokens` に加え、`checkFresh_separates_case_copy_tokens` と制限付き `checkFresh_separates_macro_counter_safe_case_tokens` は、局所copy出力の区間所属を証書全体の受理済みfresh区間へ接続する。記録区間が異なる場合、対象操作の出力tokenが一致しないことを導く。任意のC展開証書の全生成tokenを列挙し、すべてのcopy分岐を含める完全なfreshness定理は未完了である。

`CounterSafeInitializer` は空マクロ集合の下でatom、atom一個・二個のlist、または先頭atomが`match`でないatom三個・四個のlistを表し、`AtomicBindingInputs` はこの条件を満たすlet binding listを表す。この条件の下で `copyBindings_atomic_counter` は最終counterがbinding数だけ進むことを示し、`copyBindings_atomic_token_sequence`、`copyBindings_atomic_tokens_unique`、`copyBindings_atomic_tokens_avoid_source`、`copyBindings_atomic_tokens_within_interval` がbinder token列の順序、一意性、source-token非衝突、区間所属を導く。`checkFresh_separates_atomic_binding_tokens` は区間非重複へ接続する。initializerがさらに深い式や束縛子を含む一般のletについては、initializerコピーが消費するcounterとの合成が残る。

`AtomicTrees` と `copyMany_atomic_counter` は空マクロ集合で、atomだけからなる子リストを順にコピーしてもcounterが変わらないことを証明する。`copy_single_atom_list_keeps_counter`、`copy_two_atom_list_keeps_counter`、`copy_three_atom_list_keeps_counter`、`copy_four_atom_list_keeps_counter` は、記載した制約内の短いlist構文全体でもcounter保存を示す。任意長リストのマクロ集合付き結果は `MacroCounterSafeInitializer` の節を参照。

`call_extraction_complete` は、有限fuelの`calls`/`callsMany`が成功すれば、構文木中の任意の深さにある直接呼び出しと穴頭位置の候補呼び出しが抽出結果に含まれることを帰納法で示す。`graphRows_static_call_edge` はその抽出結果が行の辺として保存されることを導き、`GraphCall` と `graphRows_contains_static_calls` は全規則行を走査したグラフにも各行の辺が残ることを示す。`ProcessCertificate.source_static_calls_decrease` はこの結果を一般の受理済み停止性証書から取り出す定理であり、生成証明書の `every_static_rule_call_decreases` も同じ接続を確認する。root呼び出し補題`calls_direct_macro_complete`と行保存補題`graphRows_dependency_edge`は構成要素である。さらに `MacroTermination.macroStep_has_static_call` は実行redexを名前・arity候補へ結ぶが、展開中の親規則templateからそのredexへの文脈・置換を追跡しておらず、実際に隣接するmacroStep間の順位減少は未証明である。

`CMacroCopy.copyWithMacros_preserves_zero_arg_macro_call` は、template中のリテラル0引数マクロ呼び出しについて、headがholeで置換されない場合にコピー後も同じマクロheadが残ることを示す。`copied_zero_arg_template_call_preserves_static_candidate` はコピーの結果とこの局所補題を組み合わせ、templateにあった同じ `StaticCall` 候補をコピー結果にも保存する。これはtemplate callsiteからコピー済みredexへの限定的な接続である。候補先と実際に選ばれた子ruleの同一性、引数を持つ呼び出し、穴置換、任意の入れ子文脈を扱う一般補題や、そこから展開全体の終了性を導く証明は未完了。

`zero_arg_template_call_to_next_macro_step` はコピー結果に続く実際のrule matchから候補先を取り出し、template上の同じ0引数呼び出しへ戻す。`zero_arg_next_macro_step_rank_decreases` はその候補を受理済みgraph rowへ結び、親rowから順位が下がることを証明する。この接続はrootのリテラル0引数呼び出しに限り、一般の引数、穴置換、入れ子文脈、展開列全体の停止性は未証明。

`copyManyWithMacros_preserves_length` と `copyWithMacros_preserves_root_macro_call` により、リテラルmacro headが置換されないroot呼び出しでは、任意個数の引数をコピーしてもarityとhead名が保たれる。`root_template_call_to_next_macro_step` はそのコピー結果で実際の次macroStepが成功する場合にtemplate上の同じ候補を導き、`root_next_macro_step_rank_decreases` は受理済み親rowから順位が下がることを示す。穴headと任意の入れ子template文脈を扱う展開全体のシミュレーションは未完了。

`copyWithMacros_substituted_head_uses_copyMany` は、特殊フォームheadを除いたhead-holeの通常コピー分岐について、`copyWithMacros` の成功からwhole-list `copyMany` の成功を抽出する。`lookup_isSome_of_mem_keys` がtemplate parameter名とcopy hole名の対応を接続する。これらを使う `substituted_head_template_call_to_next_macro_step` と `substituted_head_next_macro_step_rank_decreases` は、実際の次rule matchのarityを元template引数数へ結び、`targetsOfArity` の全候補辺からrank減少を得る。特殊フォームとして解釈されるhead holeと入れ子文脈で子を追跡する証明は未完了。

`copyManyWithMacros_cons_parts` と `copyWithMacros_root_macro_call_parts` を合成した `nested_literal_call_to_next_macro_step` は、通常のコピー対象リストの先頭要素にあるリテラルmacro callを、1段のリスト文脈越しに実際の次stepへ接続する。この結果も任意深さの文脈、穴headの文脈、複数step列の順位減少には一般化されていない。

`copyManyWithMacros_extract_element` は、先行要素数に応じたfuelを明示して、成功した `copyMany` から任意位置の要素copyと後続走査を抽出する。`literal_call_at_list_index_to_next_macro_step` はこれを使い、兄弟要素を持つ通常リスト内のリテラルhead callについて、実際に次ruleがそのコピー済みcallへmatchする条件の下で元templateの `StaticCall` を得る。先行要素が進めたfresh counterも対象callの開始値として引き継ぐ。これでも任意深さに積み重なるリスト文脈、特殊フォームの専用copy経路、穴head、各macroStep遷移から展開全体の順位減少を合成する証明は含まない。

`list_index_next_macro_step_rank_decreases` は、この一段の兄弟位置対応に受理済み親template行の順位減少を合成する。子引数の再コピー結果が次のruleにmatchすることを前提とする。全深さの構文文脈にわたるシミュレーションや、これらの局所順位減少を展開実行列全体へ持ち上げる定理は未証明である。

`nested_literal_call_at_two_list_indices_to_next_macro_step` は、外側リストの任意要素を抽出し、そこから内側リストの任意要素を抽出する二段のcopy走査を合成する。通常の内側リスト（headがマクロ名でも `match` / `let` / `lambda` でもない）中のリテラルhead callについて、コピー後に実際の子ruleがmatchする条件下で、元templateの同じ `StaticCall` 候補を得る。`nested_two_indices_next_macro_step_rank_decreases` は受理済み親rowの順位減少へ接続する。三段以上の任意深さ、binder等の特殊フォーム、穴headの文脈、macroStep列全体の順位減少は未証明である。

`nested_literal_call_at_three_list_indices_to_next_macro_step` は、その二段対応を一段外側へ合成する。三つの選択位置はそれぞれ任意の前後兄弟を持てる。二つの中間リストheadが通常copy経路を使う中立性条件の下で、copy結果の実matchから元template callsiteを構成する。`nested_three_indices_next_macro_step_rank_decreases` はこれを受理済み親rowの順位減少へ接続する。四段以上、特殊フォームheadやhole headを含む任意文脈、実行macroStep列全体の停止性は未証明である。

`nested_literal_call_at_four_list_indices_to_next_macro_step` は三段の証明結果を外側の通常リストで包み、四段の選択位置で同じcopy/matchから `StaticCall` を構成する。全中間リストでhead中立性を要求し、`nested_four_indices_next_macro_step_rank_decreases` が受理済み親rowの順位減少を示す。五段以上の一般深さや展開列全体への合成は未証明である。

任意段数を扱うため、`LiteralCallSite` は通常リストの選択位置を帰納的に記述し、各段の前置兄弟数とlist copy overheadから必要fuelを定める。`literal_call_site_to_next_macro_step` はlist copyを `copyMany` へ分解して経路を帰納的にたどり、実際の子rule matchを前提として元template上の同一 `StaticCall` を得る。`literal_call_site_rank_decreases` は受理済み親rowの順位減少へ合成する。この一般化は各中間list headがcounter-neutralで、call headがテンプレート穴に置換されないリテラルatomである場合に限る。特殊フォーム経路、穴headの任意文脈、複数の展開step全体のシミュレーション・停止性は未証明である。

`literal_call_at_list_index_to_next_macro_step` とLiteralCallSite系の再帰定理は、copyのrename環境を空に固定せず任意の `Renames` を受け取る。`copyWithMacros_lambda_parts` は、macro名・hole名に衝突せずparameter列が有効なlambdaの成功copyから、parameter copy、freshened rename環境、次counter、body copyの結果を分解する。`lambda_copy_body_call_site_to_next_macro_step` はこの分解結果を使い、counter-neutralなbody list内で子ruleがmatchするcallsiteをlambda template内の同じ `StaticCall` へ接続し、`lambda_copy_body_call_site_rank_decreases` がwhole-lambda copyから順位減少を導く。`copyWithMacros_let_parts` と `let_copy_body_call_site_to_next_macro_step` / `let_copy_body_call_site_rank_decreases` は有効なbinding列を持つ通常let branchのbodyを同様に接続する。さらに `copyBindingsWithMacros_cons_parts` は各binding scan headをbinder・initializer・tail operationへ分解し、`BindingRows` / `copyBindingsWithMacros_extract_initializer` は形状が有効なprefixを帰納的に走査して、選択したinitializerの実rename環境とcounterを取り出す。`let_initializer_call_to_next_macro_step` / `let_initializer_call_rank_decreases` は、その任意initializer内にあるcounter-neutralなlist callをtemplate edgeと順位減少へ接続する。`copyCasesWithMacros_default_parts` / `copyWithMacros_match_default_parts` は空pattern case bodyのcopyを分解する。`copyCasesWithMacros_pattern_parts` は非空pattern caseのpattern freshening、freshened renameでのbody copy、tail scanを分解し、`match_pattern_body_call_site_to_next_macro_step` / `match_pattern_body_call_site_rank_decreases` がそのbody callをtemplate edgeと順位減少へ接続する。複数caseの一般走査、特殊フォームとして解釈される穴head、複数step全体のシミュレーションは未証明である。

置換head用に `SubstitutedHeadCallSite` と `substituted_head_call_site_to_next_macro_step` / `substituted_head_call_site_rank_decreases` も定義した。parameter名とcopy hole名の一致、置換headが `lambda` / `let` / `match` 以外、中間リストheadのcounter-neutral性を条件として、任意深さの通常リスト文脈で、実matchから元template callsiteの順位減少を導く。特殊フォームheadがコピー時に専用処理へ分岐する場合と、macroStep列全体のシミュレーション・停止性は未証明である。

この追加後に `examples/math_macros.nlisp` の `--mode termination` 証明書を生成し、Lean検査した。これは既存のグラフ再計算・順位検査の確認であり、新しい局所補題を使った実展開シミュレーションではない。

2026-11-20追補: `MacroCounterSafeInitializer.atomList` と `copyWithMacros_atomTrees_keeps_counter` により、任意長で先頭atomが`match`でないatom-only list initializerのcounter保存を任意マクロ集合で証明し、binding列・case bodyのfreshness合成へ接続した。`singletonWrapped` はcounter-preserving initializerの単一要素list wrapperを任意の深さまで合成し、`pairChild` は二要素listの第2要素、`tripleChildren` はheadが`match`・`let`でなく第2要素がatomの場合の三要素listの第3要素にcounter-preserving initializerを置けるようにした。Lean 4.8.0同梱の `lake build` と `tests/CMacroCopy.lean` の検査に成功した。`examples/macros.nlisp` のcore証明書と `examples/dynamic_macro_head.nlisp` の停止性証明書を現行ソースから生成し、どちらも独立再検証に成功した。候補解析の作業予算診断に試行量・上限値を加え、小さな直接呼び出しで上限12の13操作目がUnknownになることを確認した。実CLIの上限0では34ノードの入力が証明書なしのUnknownになることも確認した。CMakeの `nlisp_core` と `nlisp` もビルド成功。対象外はより一般的な複数要素のネストinitializer、binderを含むinitializer、先頭`match`の任意長list、およびC `copy_template`との一般シミュレーションである。CTestはこの追補では実行していない。

2026-11-21追補: `MacroCounterSafeInitializer.quadrupleChildren` と `copyWithMacros_quadruple_children_preserves_counter` を追加した。先頭が`match`でない4要素の通常listに限り、第4要素へcounter-preservingな子initializerを置ける。この条件は `macroCounterSafeInitializer_preserving` で既存の`CounterPreservingInitializer`へ変換されるため、`MacroCounterSafeBindingInputs`・`CounterPreservingBindings`の一般合成からbinder tokenの一意性、source-token分離、counter区間所属へつながる。Leanファイル単体の検査は成功。binder initializer一般やcopy全体のFreshnessは未完了。
2026-11-21追補: `CounterNeutralTree` と `counterNeutralTree_preserving` を追加し、binder特殊headやマクロ呼び出しを含まない任意のネスト木についてcounter保持を構造帰納法で証明した。`MacroCounterSafeInitializer.neutralTree` を通してbinding列のtoken freshness合成へ渡せる。Lean 4.8.0で `NLisp/CMacroCopy.lean` の直接検査に成功。binderを含む任意initializerや全体`copy`のfreshnessは引き続き未完了。

2026-11-21追補: CaseRows と copyCasesWithMacros_extract_default / copyCasesWithMacros_extract_pattern により、有効なcase prefix後の任意位置からcase body copyと開始counterを抽出する。copyWithMacros_match_cases_parts は2件以上のcase走査を分解し、match_default_body_call_site_at_index_to_next_macro_step / match_default_body_call_site_at_index_rank_decreases と match_pattern_body_call_site_at_index_to_next_macro_step / match_pattern_body_call_site_at_index_rank_decreases は有効なprefix後の任意default/pattern case bodyのcounter-neutral callを、元matchのtemplate StaticCall と受理済み順位減少へ接続する。match_scrutinee_call_site_at_index_to_next_macro_step / match_scrutinee_call_site_at_index_rank_decreases も複数case matchのscrutinee callを接続する。 match_scrutinee_call_site_to_next_macro_step / match_scrutinee_call_site_rank_decreases は単一case形式も扱う。特殊フォームとして解釈される穴headと展開step列全体の停止性は未証明。Lean全体の lake build に成功。

2026-11-21ビルド追記: WSL Lean 4.8の再ビルドでは`CMacroCopy`がリプレイ成功し、`CExpansion.holeEntriesWithCost_result`と`ExpansionLowering.globalValueIndex_lookup_sound`の証明で失敗した。前者はOptionのmap/bind補題適用前に再帰定義`holeEntries`を明示簡約し、後者は`getElem?`の定義展開を避けてリストcons/successorの簡約を使うように修正した。これらはログ後の作業ツリー変更であり、再ビルド確認待ち。こちらのWindows実行環境からは`wsl.exe -l -v`が終了コード1でディストリビューションを検出できず、WSL検証は利用者側のログに依存する。

2026-11-21ビルド追記2: 利用者の次のWSL `lake build` では`CExpansion`の失敗が解消し、失敗対象は`ExpansionLowering`と`ExpansionCertificate`のみになった。これを根拠に`holeEntriesWithCost`と`matchRuleWithCost`の項目はLean 4.8で検証済みに更新した。新たに確認された問題は、global slot lookup結果を`getElem?`へ移す式の簡約と、証書費用モデルの等価性・構造上界証明である。`ExpansionLowering`では有効範囲を明示して添字簡約する形へ変更し、`ExpansionCertificate`では非計算可能な構文node countを参照する測度を非計算可能定義にし、membership・cost accumulator・区間走査の証明をログの失敗点に沿って修正した。後者はまだ再ビルド未確認。
