# 型付き衛生マクロ展開の局所証書に関する形式化と研究課題

## 1. 研究対象と結論

NLisp 0.2 は、正格・左から右評価の明示型付きLispに、定義位置と呼び出し位置を区別する型付き衛生テンプレートマクロを加えた言語である。現在の実装は、個別の有限入力について、元ソースの読み取り、正規化、実在するマクロ規則による展開、生成束縛のfreshness、最終構文の名前解決をLeanで独立に照合できる。

本研究の中心課題を次の問いに定める。

> 信頼しないマクロ展開器が生成した各展開ステップについて、規則照合、衛生的置換、freshness、非捕捉および型保存を、局所的かつ合成的に検査できる有限証書を設計し、その独立検査器の受理が展開全体の健全性を含意することをLeanで証明できるか。

この問いに対する主要成果は、一般的なマクロ展開器の正しさではなく、次の健全性主張である。

\[
  \operatorname{check}(P,e,e',C)=\mathsf{true}
  \Longrightarrow
  \operatorname{Expands}_P(e,e')
  \land \operatorname{Fresh}(C)
  \land \operatorname{NonCapture}(e,e',C)
  \land \operatorname{TypePreserving}(e,e').
\]

展開器と証書生成器は信頼しない。検査器が拒否した場合は、入力が不正であるとは限らず、証書が不足または不適合であることだけを意味する。

## 2. 基本言語

### 2.1 型

実装全体の型を次で表す。

\[
\begin{aligned}
\tau ::= {}& \mathsf{Boolean}
 \mid \mathsf{Integer}
 \mid \mathsf{Float}
 \mid \mathsf{String}
 \mid \mathsf{Character}
 \mid \mathsf{Unit} \\
&\mid \mathsf{List}\;\tau
 \mid \mathsf{Option}\;\tau
 \mid (\tau_1,\ldots,\tau_n)\to\tau
 \mid \alpha, \\
\sigma ::= {}& \forall \alpha_1\ldots\alpha_k.\,(\tau_1,\ldots,\tau_n)\to\tau.
\end{aligned}
\]

`forall` はトップレベル関数シグネチャの外側にのみ現れる。`let` 一般化は行わない。型引数は明示的な `type-app` または実引数型からの一方向照合で決定する。

マクロ契約にのみ現れる構文型を次で表す。

\[
  \mathsf{Syntax}[\Gamma,\tau]
\]

ここで \(\Gamma\) は構文が所属する束縛環境であり、単なる型 \(\tau\) だけでなく各自由識別子の束縛identityを保持する。

### 2.2 式

マクロ展開後の主要な表層式を次で表す。

\[
\begin{aligned}
e ::= {}& x \mid c \mid (e\;e_1\ldots e_n)
 \mid \lambda((x_1:\tau_1)\ldots(x_n:\tau_n)): \tau.\,e \\
&\mid \mathsf{if}\;e\;e\;e
 \mid \mathsf{let}\;((x_1:\tau_1)=e_1,\ldots,(x_n:\tau_n)=e_n)\;\mathsf{in}\;e \\
&\mid \mathsf{begin}\;e_1\ldots e_n
 \mid \mathsf{match}\;e\;\overline{p\Rightarrow e}
 \mid \mathsf{typeApp}\;e\;\overline{\tau}.
\end{aligned}
\]

定数 \(c\) はリテラル、データ構築子、組み込み関数を含む。評価はcall-by-value、正格、左から右である。並列 `let` の各右辺は元の環境で評価され、全結果を得た後に本体で同時に束縛される。

### 2.3 束縛環境

束縛を型と自然数identityの組として定義する。

\[
  b = \langle \operatorname{id}(b),\operatorname{ty}(b)\rangle,
  \qquad
  \Gamma = [b_1,\ldots,b_n].
\]

有効な環境はidentityが重複しない。

\[
  \operatorname{Valid}(\Gamma)
  \iff
  \forall i\ne j.\;\operatorname{id}(b_i)\ne\operatorname{id}(b_j).
\]

環境埋め込み \(\iota:\Gamma\hookrightarrow\Omega\) は型付き変数の名前変更であり、型だけでなくidentityを保存する。

\[
  \forall x\in\Gamma.\quad
  \operatorname{ty}(\iota(x))=\operatorname{ty}(x)
  \land
  \operatorname{id}(\iota(x))=\operatorname{id}(x).
\]

この条件により、同じ型を持つ別の束縛へのすり替えを禁止する。

## 3. 型付き衛生マクロ

### 3.1 マクロ規則

固定引数のマクロ規則を次で表す。

\[
  \rho =
  m(x_1:\mathsf{Syntax}\;\tau_1,\ldots,x_n:\mathsf{Syntax}\;\tau_n)
  \Rightarrow t : \mathsf{Syntax}\;\tau.
\]

反復パターン、束縛名の穴、型の穴、手続き的マクロ、意図的捕捉は現在の対象外である。各 \(x_i\) は式構文全体の穴を表す。

定義位置を \(\Gamma_d\)、呼び出し位置を \(\Gamma_c\)、穴の型列を \(H=[\tau_1,\ldots,\tau_n]\) とする。テンプレートと実引数は次の型を持つ。

\[
  t : \operatorname{Template}[\Gamma_d;H;\tau],
  \qquad
  a_i : \mathsf{Syntax}[\Gamma_c,\tau_i].
\]

展開先 \(\Omega\) には、互いに独立したidentity保存埋め込みを要求する。

\[
  \iota_d:\Gamma_d\hookrightarrow\Omega,
  \qquad
  \iota_c:\Gamma_c\hookrightarrow\Omega.
\]

### 3.2 抽象的な型付き展開

穴代入を \(\theta=[x_1\mapsto a_1,\ldots,x_n\mapsto a_n]\) とする。展開は、穴を呼び出し位置から、テンプレートの自由変数を定義位置から移送する。

\[
  \operatorname{expand}(t,\theta,\iota_d,\iota_c)
  = t[
      x_i\mapsto\operatorname{rename}(a_i,\iota_c),
      y\mapsto\iota_d(y)
    ].
\]

抽象モデルでの型保存は構成により得られる。

\[
\frac{
  t:\operatorname{Template}[\Gamma_d;H;\tau]
  \quad
  \theta:H\Rightarrow\Gamma_c
  \quad
  \iota_d:\Gamma_d\hookrightarrow\Omega
  \quad
  \iota_c:\Gamma_c\hookrightarrow\Omega
}{
  \operatorname{expand}(t,\theta,\iota_d,\iota_c)
  :\mathsf{Syntax}[\Omega,\tau]
}.
\]

現在の `ScopedSyntax.Macro.expand` はこの層に対応する。

### 3.3 実装上の識別子領域

実際の有限証書ではidentityを次の互いに素な領域へ分ける。

\[
\begin{array}{ll}
\text{組み込み識別子} & 0 \pmod 3,\\
\text{元ソースの字句識別子} & 1 \pmod 3,\\
\text{マクロが生成した束縛子} & 2 \pmod 3.
\end{array}
\]

生成カウンター \(k\) に対する新しいidentityを

\[
  \operatorname{freshId}(k)=3k+2
\]

とする。各マクロ適用が使用するカウンター区間 \((l,u]\) は、他の適用の区間と交差してはならない。

\[
  \operatorname{Disjoint}((l_1,u_1],(l_2,u_2])
  \iff u_1\le l_2\lor u_2\le l_1.
\]

したがって、元ソースと生成束縛の衝突、および異なる展開ステップ間の生成束縛の衝突をそれぞれ局所条件として検査できる。

## 4. 展開関係

マクロ環境 \(M\) は、定義位置indexと元の規則の組の有限列である。

\[
  M=[(d_1,\rho_1),\ldots,(d_k,\rho_k)].
\]

規則照合を次で表す。

\[
  \operatorname{match}(\rho,e)=\operatorname{some}(\theta,t).
\]

衛生的テンプレートコピーを次で表す。

\[
  \operatorname{copy}(M,d,\theta,l,t)
  =\operatorname{some}(e',u).
\]

ここで \(d\) は定義位置、\(l\) と \(u\) はコピー前後のfreshカウンターである。`copy` は次を行う。

1. 穴に遭遇した場合、実引数構文を起源・束縛identityごと変更せず挿入する。
2. テンプレートの自由識別子に定義位置 \(d\) を付ける。
3. `lambda`、`let`、`match` が導入する束縛子へ新しいidentityを割り当てる。
4. 新しい束縛子に束縛される参照だけを同じidentityへ変更する。
5. 値の名前変更によって静的なマクロ名を変更しない。

一段のマクロ展開を次で定義する。

\[
\frac{
  (d,\rho)\in M
  \quad
  \operatorname{match}(\rho,e)=\operatorname{some}(\theta,t)
  \quad
  \operatorname{copy}(M,d,\theta,l,t)=\operatorname{some}(e',u)
}{
  M\vdash e\longrightarrow_{(d,\rho,\theta,l,u)}e'
}.
\]

有限展開関係 \(M\vdash e\Longrightarrow e'\) は、一段展開の反射・推移・S式リスト文脈閉包である。これは現在の `CExpansion.Expands` に対応し、すべてのマクロ展開が停止することは仮定しない。

## 5. freshnessと非捕捉

### 5.1 freshness

展開ステップのfreshnessを次で定義する。

\[
\begin{aligned}
\operatorname{FreshStep}(e,e',l,u) \iff {}&
  \forall z\in\operatorname{Generated}(e').\\
& l<\operatorname{counter}(z)\le u\\
&\land\operatorname{id}(z)\equiv 2\pmod 3\\
&\land\operatorname{id}(z)\notin\operatorname{Ids}(e).
\end{aligned}
\]

展開全体のfreshnessは、各ステップの `FreshStep` と全生成区間のpairwise disjointnessである。

### 5.2 名前解決

名前解決 \(\operatorname{resolve}(\Gamma,n)\) は環境の先頭側にある名前 \(n\) の束縛を選ぶ。参照位置 \(s\) は次を持つ。

\[
  s=\langle n,i,\Gamma_{\mathrm{eff}},\Gamma_{\mathrm{call}}\rangle.
\]

- \(n\): 印字名
- \(i\): 展開結果に記録された選択identity
- \(\Gamma_{\mathrm{eff}}\): 起源を考慮して実際に解決する環境
- \(\Gamma_{\mathrm{call}}\): その参照が現れる呼び出し側環境

参照の局所受理条件を次で定義する。

\[
\begin{aligned}
\operatorname{AcceptRef}(s)\iff{}&
  \operatorname{Valid}(\Gamma_{\mathrm{eff}})
  \land \operatorname{Valid}(\Gamma_{\mathrm{call}})\\
&\land \exists b.\;
  \operatorname{resolve}(\Gamma_{\mathrm{eff}},n)=b
  \land i=\operatorname{id}(b)
  \land b\in\Gamma_{\mathrm{call}}.
\end{aligned}
\]

最後の条件は、定義位置には存在しても呼び出し時点ではまだ利用できないトップレベル値への参照を拒否する。

### 5.3 非捕捉

非捕捉を、単なる印字名の非一致ではなく束縛identityの保存として定義する。

\[
\begin{aligned}
\operatorname{NonCapture}(e,e')\iff{}&
&\forall r\in\operatorname{Refs}(e').\;\operatorname{AcceptRef}(r)\\
&\land\forall r\in\operatorname{HoleRefs}(e').\;
  \operatorname{id}_{e'}(r)=\operatorname{id}_{\mathrm{caller}}(r)\\
&\land\forall r\in\operatorname{TemplateFreeRefs}(e').\;
  \operatorname{id}_{e'}(r)=\operatorname{id}_{\mathrm{definition}}(r)\\
&\land\forall r\in\operatorname{IntroducedBoundRefs}(e').\;
  \operatorname{id}_{e'}(r)=\operatorname{id}_{e'}(\operatorname{binder}(r)).
\end{aligned}
\]

これにより次の二種類の事故を区別して排除する。

1. テンプレートが導入した束縛子が、穴から挿入された自由参照を捕捉する。
2. 呼び出し位置の同名束縛が、テンプレートの定義位置自由参照を奪う。

現在の `CMacroCopy` は起源付与と生成束縛の一意化を計算し、`CBindingWalk` は最終構文から環境を再構成して `AcceptRef` に相当する条件を検査する。ただし、これらを上記の一つの `NonCapture` 定理へ接続することが研究上の主要な未完部分である。

## 6. 局所展開証書

### 6.1 証書構文

証書を展開導出と同型の有限木として設計する。

\[
\begin{aligned}
C ::= {}& \mathsf{refl}(e)\\
 \mid{}& \mathsf{congList}(C_1,\ldots,C_n)\\
 \mid{}& \mathsf{step}(r,d,\theta,l,u,e,e')\\
 \mid{}& \mathsf{trans}(C_1,C_2).
\end{aligned}
\]

`step` の局所証書は少なくとも次を保持する。

- 元規則を識別するindex \(r\) と定義位置 \(d\)
- 展開前の呼び出し \(e\) と展開直後の構文 \(e'\)
- パターン穴と実引数構文の対応 \(\theta\)
- 使用したfreshカウンター区間 \((l,u]\)
- 必要な場合、定義位置・呼び出し位置の境界環境

規則本体、穴代入結果、名前解決結果そのものを無条件には信頼しない。検査器が元ソースの規則と構文から再計算する。

### 6.2 局所検査判断

各証書の検査判断を次で表す。

\[
  M;I\vdash C:e\Longrightarrow e'\triangleright I'.
\]

\(I\) と \(I'\) は部分木の境界インターフェースであり、少なくとも次を含む。

\[
  I=\langle
    \operatorname{FreeIds},
    \operatorname{GeneratedInterval},
    \operatorname{Origins},
    \operatorname{Type},
    \operatorname{ResultHash}
  \rangle.
\]

局所性とは、親ノードの検査が子ノードの内部導出を再検査せず、子の受理済み結論と境界インターフェースだけを使用することと定義する。初期実装ではハッシュを健全性の根拠にせず、構造共有または明示的等式で結ぶ。ハッシュはキャッシュ索引としてのみ使用する。

### 6.3 独立検査器

実行可能な検査器を次の全域関数として定義する。

\[
  \operatorname{check}:
  \mathsf{Program}\to\mathsf{Tree}\to\mathsf{Tree}\to\mathsf{Certificate}\to\mathsf{Bool}.
\]

検査器は次を再計算する。

1. 指定規則が元プログラムのマクロ環境に属すること。
2. 呼び出し名と引数個数が規則に一致すること。
3. 穴代入 \(\theta\) がパターン照合結果と一致すること。
4. 衛生的コピーの結果とfreshカウンター終値が一致すること。
5. 生成区間が他の局所証書と交差しないこと。
6. 展開後の各参照が `AcceptRef` を満たすこと。
7. 子証書の終点と親証書が要求する始点が一致すること。
8. 型付き層へ接続した後は、穴・テンプレート・展開結果の型が契約と一致すること。

検査器はマクロ展開器を呼び出さず、マクロの探索戦略や展開順序を再現する必要もない。証書に記録された有限導出が正当かだけを検査する。

## 7. 証明すべき定理

### 7.1 局所ステップ健全性

\[
\begin{aligned}
&\operatorname{checkStep}(M,e,e',c)=\mathsf{true}\\
&\quad\Longrightarrow
M\vdash e\longrightarrow e'
\land\operatorname{FreshStep}(e,e',c.l,c.u)
\land\operatorname{NonCaptureStep}(e,e',c).
\end{aligned}
\]

### 7.2 証書合成健全性

\[
\begin{aligned}
&\operatorname{check}(M,e,e',C)=\mathsf{true}\\
&\quad\Longrightarrow
M\vdash e\Longrightarrow e'
\land\operatorname{Fresh}(C)
\land\operatorname{NonCapture}(e,e').
\end{aligned}
\]

証明は証書 \(C\) の構造帰納法で行う。`trans` の場合は中間構文の一致、生成区間の非交差、参照identity保存の推移性が主要補題になる。

### 7.3 型保存

型付き表層構文への接続後に、次を証明する。

\[
\frac{
  \Gamma_c;M\vdash e:\tau
  \qquad
  \operatorname{check}(M,e,e',C)=\mathsf{true}
}{
  \exists\Omega,\iota_c.\;
  \iota_c:\Gamma_c\hookrightarrow\Omega
  \land \Omega\vdash e':\tau
}.
\]

展開先 \(\Omega\) はfreshな生成束縛と、必要な定義位置束縛を含み得るため、\(\Gamma_c=\Omega\) を仮定しない。

### 7.4 総合健全性

論文の主定理を次とする。

\[
\begin{aligned}
&\operatorname{checkProgram}(P,P',C)=\mathsf{true}
\land \Gamma\vdash P:\tau\\
&\quad\Longrightarrow
\exists\Omega.\;
  \operatorname{Expands}(P,P')
  \land\operatorname{Fresh}(C)
  \land\operatorname{NonCapture}(P,P')
  \land\Omega\vdash P':\tau.
\end{aligned}
\]

この定理は、展開器の完全性、すべてのマクロの停止性、または展開器が常に証書を生成できることを主張しない。

## 8. 現在のLean実装との対応

| 数理対象 | 現在のLean定義 | 現在の状態 |
| --- | --- | --- |
| 型付き構文と置換 | `TypedExpansion.Expr`, `rename`, `subst` | 実装済み |
| 束縛identity付き環境 | `ScopedSyntax.Binding`, `Scope`, `Valid` | 実装済み |
| identity保存埋め込み | `ScopedSyntax.Embedding` | 実装済み |
| 定義位置・呼び出し位置を分けた展開 | `ScopedSyntax.Macro.expand` | 型付き抽象モデルで実装済み |
| 穴と定義位置参照の分離 | `appendSub_hole`, `appendSub_definition` | 証明済み |
| 生S式の衛生的コピー | `CMacroCopy.copyWithMacros` | 予算付き関数仕様を実装済み |
| 一段・有限展開関係 | `CExpansion.Expands` | 実装済み |
| source/generated identity分離 | `source_and_generated_ids_differ` | 証明済み |
| 生成区間の非交差 | `disjointIntervals`, `separated_fresh_values_differ` | 局所補題まで実装済み |
| 最終構文からの環境再構成 | `CBindingWalk.references` | 実装済み |
| 各参照のidentity対応 | `Corresponds`, `accepts_sound`, `check_sound` | 証明済み |
| ソースから展開・スコープまでの束ね | `ProcessCertificate.CheckedExpansion` | 実装済み |
| 明示的な局所証書データ型 | 未定義 | 研究課題 |
| 局所証書の合成的Boolean検査器 | 部品のみ存在 | 研究課題 |
| freshnessの全展開定理 | 未証明 | 研究課題 |
| `NonCapture`という単一の意味的定理 | 未証明 | 研究課題 |
| 生S式展開と型付き抽象展開の対応 | 未証明 | 研究課題 |
| 証書受理から表層型保存 | 未証明 | 研究課題 |
| 局所再検査量の上界 | 未証明 | 研究課題 |

現在の `CheckedExpansion` は、同じ入力データについて有限展開導出と参照対応を一つのLean構造体へ束ねる。しかし、証書フォーマット自体の局所性、子証書の再利用、freshnessと非捕捉の統合定理、型付き抽象モデルへの接続はまだ研究成果として完成していない。

## 9. 研究課題

### RQ1 局所証書の十分性

各展開ノードについて、どの情報を証書に保持すれば、マクロ変換器を再実行せずに規則適用、freshness、非捕捉を検査できるか。

評価基準は、証書から規則本体や名前解決結果を盲目的に信頼せず、元ソースと境界環境から独立に再計算できることである。

### RQ2 合成的健全性

局所証書の受理を、展開木全体のfreshnessと非捕捉へどのように合成できるか。

主要な技術課題は、生成区間の非交差、部分木間の参照起源、`trans` におけるidentity保存の推移性である。

### RQ3 型付きモデルとの接続

生S式に対する `CMacroCopy` と `CBindingWalk` の検査結果を、`ScopedSyntax.Macro.expand` の型付き展開へどのように対応付けるか。

必要な橋渡しは、型タグを不透明な自然数として扱う現在の対応から、表層型 \(\tau\) と `TypedExpansion.Ty` の意味的対応へ進めることである。

### RQ4 独立検査器の信頼境界

Lean内で定義したBoolean検査器と、実際に配布する検査実行物の間の信頼境界をどこまで縮小できるか。

最低条件は `check = true` から主定理を導くことである。外部JSON変換器や証書生成器は信頼基盤に含めない。実行物まで保証する場合は、Leanコード生成または別の検証済みコンパイル経路を追加課題とする。

### RQ5 局所性と増分再検査

一つのマクロ呼び出しまたはその実引数だけを変更した場合、変更された祖先経路だけを再検査できるか。

局所性の実証では、単に証書が木構造であるだけでなく、次を測定する。

- 全証書サイズと展開結果サイズの比
- 証書生成時間
- 独立検査時間
- 変更ノード数に対する再検査ノード数
- 壊した証書、束縛identity、起源、fresh区間の拒否率

## 10. 論文で扱う範囲

### 必須範囲

1. 固定引数の型付き衛生テンプレートマクロ
2. `lambda`、並列 `let`、`match` の生成束縛
3. 定義位置自由参照と呼び出し位置からの穴構文
4. 局所証書フォーマット
5. 独立Boolean検査器
6. freshness・非捕捉・型保存のLean健全性証明
7. C参照展開器が生成する実証書による評価

### 明示的に除外する範囲

- 任意の手続き的マクロ
- 意図的な変数捕捉
- `syntax-rules` の反復パターン
- すべてのマクロ展開の停止性
- C実行器全体の正しさ
- Float演算やI/Oを含む実行意味論
- コンパイラ全体の意味保存
- 暗号署名による証書発行者の認証

これらを除外しても、展開器を信頼しない局所証書とその健全性という中心成果は成立する。

## 11. 実装計画

### Phase 1 証書計算の固定

- `ExpansionCertificate` をLeanで定義する。
- `refl`、`congList`、`step`、`trans` の各検査規則を実装する。
- 現在の展開履歴から証書データを生成する。
- 証書が保持する情報と検査器が再計算する情報を区別する。

完了条件は、既存の実例が、生成されたLean証明本文ではなく同じ汎用 `check` 関数への証書入力として受理されることである。

### Phase 2 freshnessと非捕捉

- `FreshStep`、`Fresh`, `NonCaptureStep`, `NonCapture` を定義する。
- `copyWithMacros` の成功から `FreshStep` を証明する。
- `CBindingWalk.check_sound` を `NonCapture` へ接続する。
- 証書合成に対するfreshness・非捕捉の保存を証明する。

完了条件は、証書受理から有限展開、freshness、非捕捉を同時に導く定理がLeanで通ることである。

### Phase 3 型保存

- 生S式の型付き解釈関係を定義する。
- 生S式の規則と `ScopedSyntax.Macro` の対応を定義する。
- 衛生的コピーと型付き `Macro.expand` の可換性を証明する。
- 証書受理から展開後の表層型付けを導く。

完了条件は、`checkProgram = true` と展開前の型付けから、展開後に同じ型を持つ項の存在を導くことである。

### Phase 4 局所性の評価

- 代表例と合成的なストレスケースを用意する。
- 証書サイズ、生成時間、検査時間を測る。
- 一部変更時の再検査範囲を測る。
- 規則index、穴代入、起源、identity、fresh区間、子証書を個別に改変する負例を生成する。

完了条件は、検査コストと証書サイズを展開ノード数・生成構文サイズの関数として報告し、局所変更時の再検査削減を実測することである。

## 12. 優先順位

最優先課題は、現在別々に存在する `CExpansion.Expands` と `CBindingWalk.Corresponds` を、新しい局所証書検査器の一つの健全性定理へ統合することである。

次に、生S式と `ScopedSyntax` の対応を証明して型保存を接続する。マクロ停止性、実行意味保存、多相型消去は有用だが、本研究の中心定理には含めず、別課題として扱う。

したがって、論文の最小完成条件は次の三点である。

1. 各展開ステップに対する有限で合成可能な証書形式
2. 展開器から独立した検査器と、その受理からfreshness・非捕捉を導くLean証明
3. 型付き表層モデルへの接続と、証書付き展開の型保存

この三点が完成すれば、研究の主張は「衛生的マクロ展開器を実装した」ではなく、「信頼しない型付き衛生マクロ展開を、局所証書によって独立検査できる」となる。
