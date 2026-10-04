# Z₃ × Z₉ × Z₉ に (243, 121, 60) 差集合は存在しない

*日本語が先、英語は後半にあります。/ Japanese first; the English version follows below.*

## 問題

G = Z₃ × Z₉ × Z₉（元が 243 個のアーベル群）を考えます。G の部分集合 D で、|D| = 121 で、0 以外のどの元 g も差 g = d − d′（d, d′ ∈ D）としてちょうど 60 通りに表されるものはあるでしょうか。

このような集合を **(243, 121, 60) 差集合** と呼びます。

## 出典

- D. M. Gordon, *The La Jolla Difference Set Repository*（ArasuFest 2019 の講演、全 49 枚中の 38 枚目、<https://cargo.wlu.ca/ArasuFest/ArasuFest_talks/Dan_Gordon.pdf>）。このスライドは「アーベル群 G で差集合があるかどうかは exp(G)（群の指数）だけで決まるか？」と問い、「Smallest Open Case（未解決の最小例）」として次の 2 行を挙げています。
  `243 121 60 [3,3,3,9]  No (López and Sánchez)` と `243 121 60 [3,9,9]  Open`。
- La Jolla Difference Set Repository（<https://dmgordon.org/difference-sets/>）。データは <https://github.com/dmgordo/difference-sets> の `ds.json` です。最新のコミット（c089b4d、2026-04-24。2026-10-04 に確認）でも `DS(243,121,60,[3,9,9])` は **Open** のままです。このファイルを表の順に見ると、Open の最初の項目です。

位数 243 のほかの 6 つのアーベル群は決着済みです。Z₃⁵ には差集合があります（Paley 型）。Z₂₄₃ と Z₃ × Z₈₁ にはありません（Lander の定理 4.38）。Z₉ × Z₂₇ にもありません（Arasu–Ma 2001）。Z₃ × Z₃ × Z₂₇ と Z₃ × Z₃ × Z₃ × Z₉ にもありません（López–Sánchez 1997）。

## 答え

**存在しません。** Z₃ × Z₉ × Z₉ に (243, 121, 60) 差集合はありません。

証明は 2 つの部分からなります。1 つ目は古典的な還元で、下にすべて書き出しました（段 1〜5）。これで問いは、変数 64 940 個の有限の充足可能性問題（SAT）に変わります。2 つ目はその SAT の計算です。ソルバー CaDiCaL が「解なし」を示し、その証明書（LRAT 形式）を、それ自体が形式検証された証明検査器 **cake_lpr** と lrat-check が受理しました。

これとは独立な 2 つ目の道として、段 6〜7 で問題を同等な 864 通りに分け、その代表 1 つを同じ方法で証明書つきで確かめました。さらに、対称性の議論に頼らない確認として、864 通りすべてを 1 つずつ解きました。

Gordon の問いについて: Z₃ × Z₃ × Z₃ × Z₉ と Z₃ × Z₉ × Z₉ はどちらも指数 9 で、どちらも答えが「なし」になりました。したがってこの最小の未解決例は、「存在は exp(G) だけで決まる」の反例には**なりません**。

## なぜ（初学者向け）

**差集合とは。** 0, 1, …, 6 の 7 個の数で、7 で割った余りの計算（7 時間で一周する時計）をします。D = {1, 2, 4} を選び、異なる 2 つの元の差をすべて書き出します（行が d、列が d′）。

| d − d′ (mod 7) | 1 | 2 | 4 |
|---|---|---|---|
| **1** | – | 6 | 4 |
| **2** | 1 | – | 5 |
| **4** | 3 | 2 | – |

1, 2, 3, 4, 5, 6 がそれぞれ**ちょうど 1 回ずつ**現れます。つまり {1, 2, 4} は (7, 3, 1) 差集合です。群の元が 7 個、集合の元が 3 個で、どの差も 1 回ずつ現れる、という意味です。今回の問いは、同じことをもっと大きな群で問うものです。G は元が 243 個、D は元が 121 個で、0 以外のどの差もちょうど 60 回ずつ現れてほしい、というものです。G の元は 3 つ組 (a, b, c) で、a は 3 で割った余り、b と c は 9 で割った余りで計算します。

**X 線望遠鏡の符号化開口との関係。** X 線やガンマ線は、レンズや普通の鏡では集光できません。そこで使われる方法の一つが**符号化マスク**です。穴の模様をあけた板を、位置を測れる検出器の前に置きます。空の天体はそれぞれ、マスクの影を少しずつずれた位置に落とします。像は、検出器の画像とマスクの模様の相関をとって復元します。この復元がきれいにいくのは、マスクの自己相関が「平ら」なとき、つまりどのずらし量でも、マスクとずらしたマスクの重なりが同じになるときです。これがまさに差集合の性質です。D を穴の位置の集合とすると、ずらし量 g での重なりは g = d − d′ と書ける組の数で、g ≠ 0 なら常に λ になります。差集合から作ったマスクは URA（uniformly redundant array、Fenimore & Cannon 1978）と呼ばれます。その仲間の MURA などは、実際に X 線・ガンマ線の観測衛星に積まれてきました。今回のような Paley 型（k ≈ v/2、つまり約半分が穴）は、光をたくさん通せるので特に有利です。どの群にこうした集合があるかで、作れるマスクの大きさや形が決まります。Z₃ × Z₉ × Z₉ に (243, 121, 60) 差集合があれば、この種の新しい 243 マスの模様（3 方向に周期 3, 9, 9 で繰り返すもの）になるはずでした。今回の結果は、それが作れないことを示しています。（純粋な数学の結果であり、既存の観測装置に影響するものではありません。）

## 証明

記号: v = 243, k = 121, λ = 60, n = k − λ = 61 とします。パラメータは条件 λ(v − 1) = 60·242 = 14520 = 121·120 = k(k − 1) を満たします。D⁽⁻¹⁾ = {−d} と書きます。群環 Z[G] の中で、D が差集合であることは次と同値です。

  D·D⁽⁻¹⁾ = n·1 + λ·G  (★)

**段 1（61 は乗数）。** 第一乗数定理（巡回群は Hall 1947。アーベル群については例えば Beth–Jungnickel–Lenz『Design Theory』第 VI 章）: 素数 p が p | n、gcd(p, v) = 1、p > λ を満たすなら、どの差集合 D についても pD = {pd} は D の平行移動 D + g になります。ここでは p = 61 = n、gcd(61, 243) = 1、61 > 60 です。

**段 2（61 で固定される平行移動。McFarland–Rice）。** s(D) = Σ_{d∈D} d ∈ G とします。D の平行移動もまた差集合で、s(D + g) = s(D) + k·g です。gcd(k, |G|) = gcd(121, 243) = 1 なので、k 倍は G の全単射です。したがって s(D) = 0 となる平行移動があり、D をそれに取り替えます。61D = D + h とすると、両辺の和をとって 61·s(D) = s(D) + k·h、つまり 0 = k·h なので h = 0 です。よって **61D = D** です。

**段 3（軌道）。** 61 ≡ 1 (mod 3)、61 ≡ 7 (mod 9) なので、x ↦ 61x は (a, b, c) ↦ (a, 7b, 7c) です。7³ ≡ 1 (mod 9) で、7b ≡ b ⇔ 3 | b です。よって固定点は G[3] = Z₃ × 3Z₉ × 3Z₉（27 個）で、残りの 216 個は大きさ 3 の軌道 72 個に分かれます。D はこれら **99 個の軌道**のいくつかの和集合です。

**段 4（巡回商への像）。** φ: G → Z_e を核 H（|H| = 243/e）の全射とし、c_j = |D ∩ φ⁻¹(j)| とします。(★) に φ を施すと次が得られます。

  Σ_j c_j = 121、Σ_j c_j c_{j+s} = 60·|H| + 61·[s = 0]（s ∈ Z_e）、そして段 2 より c_{61j} = c_j。

G の指数は 9 なので e ∈ {3, 9} です。全探索（`ds_cnf.py` の関数 `allowed_vectors`）の結果は次のとおりです。
- e = 3: (c₀, c₁, c₂) は (36, 40, 45) の並べ替え（6 通り）。
- e = 9: ちょうど 12 通り。c₀, c₃, c₆ は 9, 13, 18 の並べ替えで、軌道 {1, 4, 7} と {2, 5, 8} が 12 と 15 を 1 つずつとります。例: (9, 12, 15, 13, 12, 15, 18, 12, 15)。

**段 5（この条件は (★) と同値）。** G の自明でない指標 χ は χ = ψ∘φ と分解できます。ここで φ: G → Z_e は全射（e は χ の位数）、ψ は Z_e の忠実な指標です。すると

  |χ(D)|² = Σ_s (Σ_j c_j c_{j+s}) ψ(s) = 61 + 60|H|·Σ_s ψ(s) = 61

となります。逆に、|D| = k で、χ ≠ 1 のすべてについて |χ(D)|² = n なら、差の個数の関数 N(g) = #{(d, d′) : d − d′ = g} の Fourier 変換は n·δ₀ + λ の Fourier 変換と一致します（k² = n + λv を使います）。よって N = n·δ₀ + λ となり、これは (★) そのものです。指標の核は、G/H が巡回群になる部分群 H とちょうど一致します。G には、指数 3 のものが 13 個（位数 3 の元 26 個 ÷ 2）、指数 9 のものが 36 個（位数 9 の元 216 個 ÷ φ(9) = 6）あります。したがって、段 4 の条件を **49 個の巡回商**すべてで課すことは、D が差集合であることと同値です。プログラムはこの 49 個を指標から計算し直しています。

*段 6〜7 は主証明書（段 8a）には要りません。ずっと小さな SAT で済む 2 つ目の道（段 8b）のためのものです。*

**段 6（G/3G への像）。** G/3G ≅ Z₃³ には大きさ 9 の剰余類が 27 個あります。剰余類 x に入る D の元の個数を E(x) とします。位数 3 の 13 個の商はすべて G/3G を経由するので、E は次を満たします。

  Σ E = 121、s ≠ 0 なら Σ_x E(x)E(x + s) = 540、0 ≤ E ≤ 9。

乗数からはもう 1 つ条件が出ます。大きさ 3 の軌道 {g, 7g, 4g} は 3G の 1 つの剰余類に収まります（7g − g = 6g ∈ 3G だからです）。また、固定点 G[3] は直線 L = {(a, 0, 0)} 上の 3 つの剰余類をちょうど埋めます。よって **x ∉ L なら E(x) ≡ 0 (mod 3)** です。この条件のもとで、像 E はちょうど **864 通り**です。独立な 2 つのプログラムが同じ 864 個の関数を出しました。
- `enum_images.c` は、平面和ベクトルの選び方 6¹³ 通りをすべて調べる完全探索です（13 方向それぞれの平面和は (36, 40, 45) の並べ替えで、E(x) = (Σ_d P_d(d·x) − 484)/9 で E が決まります）。候補はすべて定義に照らして直接確かめています。
- `orbit_check.py` は、mod 3 の条件を使ったずっと小さな探索（3·2¹³ 通り）です。

mod 3 の条件を外すと解は 221 184 通りあります。絞り込みの大部分は乗数によるものです。

**段 7（864 通りはすべて同等）。** G の自己同型と、G[3] の元による平行移動とが生成する群を Γ とします。D が 61D = D を満たす差集合なら、α ∈ Aut(G) と t ∈ G[3] について、α(D) と D + t もまた 61 で固定される差集合です（α(61x) = 61α(x)、61t = t だからです）。よって Γ は G/3G への像の候補を入れ替えます。`orbit_check.py` は G の自己同型を具体的に作り（ランダムな準同型で、全単射であることを確かめたもの）、(1, 0, 0) による平行移動と合わせて使います。これらが G/3G に引き起こす群の位数は 2592 で、864 個の像に**推移的**に作用します（固定部分群の位数は 3）。したがって、差集合が 1 つでもあれば、像が次の代表 E₀ に等しいものもあります。

  E₀ = (3,3,3, 3,3,6, 3,6,6,  4,3,6, 6,3,3, 3,6,6,  6,6,6, 6,3,3, 6,3,6)

（剰余類 (a, b, c) mod 3 の番号は 9a + 3b + c です。）

**段 8（SAT）。** `ds_cnf.py` は次の条件を CNF にします。「D は 99 個の軌道の和集合で、49 個の巡回商のどれへの像も段 4 の許される形のどれかで、|D| = 121」。軌道ごとに Boolean 変数を 1 つ置き、各剰余類の個数は双方向で正確な totalizer で数え、許される形ごとに選択変数を 1 つ置きます。61 で固定される差集合が実際にあれば、それは CNF の解になります（各カウンタに本当の個数を、各選択変数に本当の像を入れればよい）。したがって「充足不能」は「そのような D はない」という意味です。

- **(a) 主証明書（像を固定しない）。** 変数 64 940 個、節 675 931 本です。CaDiCaL 3.0.1 は約 390 秒で（LRAT 証明を書き出しながらだと約 850 秒で）UNSAT を返します。証明（989 MB）は **cake_lpr** が受理し（`s VERIFIED UNSAT`、66 秒）、lrat-check も受理しました。段 1〜5 とこれだけで定理が証明されます。
- **(b) 2 つ目の道。** 「G/3G への像は E₀」を加えます（段 6〜7）。変数 65 723 個、節 679 495 本で、約 10 秒で UNSAT です。LRAT 証明は cake_lpr と lrat-check が、DRAT 証明は drat-trim が受理しました。
- **(c) 対称性を使わない確認。** (b) の問題を **864 通りの像それぞれについて**作って解きました。すべて UNSAT です。

以上より、Z₃ × Z₉ × Z₉ に (243, 121, 60) 差集合は存在しません。∎

## 検証

正確なコマンド、ツールの版、所要時間、チェックサムは `VERIFY.md` にあります。要約:

| 主張 | 確かめ方 | 結果 |
|---|---|---|
| 段 1〜5（還元） | 上の手書きの証明。数値はすべて総当たりで再計算（`reduction_checks.py`） | ALL OK |
| **主 SAT 問題（像を固定しない）** | CaDiCaL → LRAT → **cake_lpr**（形式検証済み）と lrat-check | **VERIFIED UNSAT** |
| G/3G への像 864 通り（段 6） | 独立な 2 つの列挙: C による 6¹³ の完全探索と、Python による 3·2¹³ の探索 | 一致、864 |
| 1 つの軌道（段 7） | G の具体的な自己同型と G[3] による平行移動 | 軌道 1 つ。群の位数 2592 |
| 像 E₀ の問題 | LRAT → cake_lpr と lrat-check。DRAT → drat-trim | VERIFIED |
| 864 通りすべて | それぞれ CaDiCaL で | 864 通りすべて UNSAT（1 つ 6〜24 秒、ソルバー時間は合計 3.0 時間） |
| 対照実験 | 答えが分かっている 14 例と、既知の集合を代入する 2 つのテスト | 決着した例はすべて文献どおり。難しい 2 例は制限時間内に決着しなかった: Z₃⁵（既知: あり。手がかりなしの探索、30 分）と Z₃ × Z₃ × Z₃ × Z₉（既知: なし。90 分）。決着しなかった実行は文献と矛盾しえない |

## 現状

**検証できたこと。** 定理は段 1〜5 と 1 つの SAT 問題の上に立っています。その SAT 問題には、形式検証済みの検査器が受理した証明書があります。答えには別の道（段 6〜7 のあと、E₀ の問題または 864 通りすべて）でもたどり着きました。2 つの道が共有するのは段 1〜5 と CNF 生成器だけです。ここにあるコードはすべて、この確認のために一から書いたものです。結果を最初に示した探索段階のコードは読んでおらず、再利用もしていません。そちらの E₀ の場合の CNF は大きさが違い（変数約 64 000 個・節約 620 000 本。こちらは 65 723 個と 679 495 本）、同じ結論でした。

**まだ信頼に頼っているところ（機械では確かめていない部分）。**
1. 第一乗数定理。教科書にある標準的な定理で、そのまま使っています。
2. 上の段 2〜5 の短い手書きの証明。証明支援系では形式化していません。
3. CNF 生成器 `ds_cnf.py`（Python で約 320 行）。証明が必要とするのは「61 で固定される差集合はどれも CNF を満たす」という性質 1 つです。形式検証はしていません。既知の答えを再現する対照実験と、本物の差集合が CNF を満たすことを見る代入テストで確かめています。
4. cake_lpr。検査のアルゴリズムは HOL4/CakeML で機械語まで検証されています。残る信頼の対象は、HOL4 のカーネル、小さな C のラッパー `basis_ffi.c` とそれをコンパイルする C コンパイラ、そして OS です。
5. 既出の確認。López–Sánchez 1997（紙の雑誌）の本文は直接読めていません。内容は La Jolla の表を通して知っているだけです。2020〜2026 年についてウェブと arXiv を検索しましたが、この群を決着させた論文は見つかりませんでした。

査読は受けておらず、La Jolla の管理者にもまだ報告していません。

---

# No (243, 121, 60) difference set in Z₃ × Z₉ × Z₉


---

## Problem

Let G = Z₃ × Z₉ × Z₉, an abelian group with 243 elements. Is there a subset D ⊆ G with |D| = 121 such that every nonzero element g ∈ G can be written as a difference g = d − d′ (d, d′ ∈ D) in exactly 60 ways?

A set like that is called a **(243, 121, 60) difference set**.

## Source

- D. M. Gordon, *The La Jolla Difference Set Repository*, talk at ArasuFest 2019, slide 38 of 49 (<https://cargo.wlu.ca/ArasuFest/ArasuFest_talks/Dan_Gordon.pdf>). The slide asks: "Does existence in an Abelian group G only depend on exp(G)?" Under "Smallest Open Case" it lists
  `243 121 60 [3,3,3,9]  No (López and Sánchez)` and `243 121 60 [3,9,9]  Open`.
- La Jolla Difference Set Repository, <https://dmgordon.org/difference-sets/>, data at <https://github.com/dmgordo/difference-sets> (`ds.json`). The latest commit (c089b4d, 2026-04-24, checked 2026-10-04) still has `DS(243,121,60,[3,9,9])` with status **Open**. In that file it is the first entry, in table order, whose status is Open.

The other six abelian groups of order 243 are already settled. Z₃⁵ has a difference set (the Paley set). Z₂₄₃ and Z₃ × Z₈₁ have none (Lander, Thm 4.38), nor does Z₉ × Z₂₇ (Arasu–Ma 2001). Z₃ × Z₃ × Z₂₇ and Z₃ × Z₃ × Z₃ × Z₉ have none either (López–Sánchez 1997).

## Answer

**No.** There is no (243, 121, 60) difference set in Z₃ × Z₉ × Z₉.

The proof has two parts. The first is a classical reduction, written out in full below (Steps 1–5). It turns the question into a finite Boolean satisfiability (SAT) problem with 64 940 variables. The second part is the SAT computation. The solver CaDiCaL shows that the problem has no solution. Its certificate (an LRAT proof) was accepted by **cake_lpr**, a proof checker that is itself formally verified, and also by lrat-check.

A second, independent route through Steps 6–7 cuts the problem into 864 equivalent cases. One representative was certified the same way. As a check that does not depend on the symmetry argument, all 864 cases were also solved one by one.

On Gordon's question: Z₃ × Z₃ × Z₃ × Z₉ and Z₃ × Z₉ × Z₉ both have exponent 9, and now both have answer "No". So this smallest open case does **not** give a counterexample to "existence depends only on exp(G)".

## Why (for beginners)

**Difference sets.** Take the numbers 0, 1, …, 6 and do arithmetic modulo 7 (a clock with 7 hours). Pick D = {1, 2, 4}. List all differences of two different elements (row d, column d′):

| d − d′ (mod 7) | 1 | 2 | 4 |
|---|---|---|---|
| **1** | – | 6 | 4 |
| **2** | 1 | – | 5 |
| **4** | 3 | 2 | – |

Each of 1, 2, 3, 4, 5, 6 appears **exactly once**. So {1, 2, 4} is a (7, 3, 1) difference set: 7 elements in the group, 3 in the set, and every difference occurs 1 time. The question asks the same thing in a larger group. G has 243 elements, D should have 121, and every nonzero difference should occur exactly 60 times. Here an element of G is a triple (a, b, c), where a is computed mod 3 and b, c mod 9.

**Coded-aperture X-ray telescopes.** X-rays and gamma rays cannot be focused by lenses or ordinary mirrors. One way to image them is a **coded mask**: a plate with a pattern of holes in front of a position-sensitive detector. Each source in the sky casts a shifted shadow of the mask on the detector. The picture is recovered by correlating the detector image with the mask pattern. That recovery is clean when the mask's autocorrelation is "flat": every nonzero shift should give the same overlap between the mask and its shifted copy. That is exactly the difference-set property. With D as the set of open cells, the overlap at shift g is the number of ways to write g = d − d′, which is λ for every g ≠ 0. Masks built from difference sets are called URAs (uniformly redundant arrays; Fenimore & Cannon 1978). Their relatives, such as MURAs, have flown on X-ray and gamma-ray missions. Paley-type sets like this one (k ≈ v/2, so about half the cells are open) are especially good for throughput. Which groups carry such sets decides which mask sizes and shapes are possible. A (243, 121, 60) set in Z₃ × Z₉ × Z₉ would have been a new 243-cell pattern of this kind (periodic in three directions with periods 3, 9, 9). The result shows that it cannot exist. (The result is pure mathematics. It does not change any existing instrument.)

## Proof

Notation: v = 243, k = 121, λ = 60, n = k − λ = 61. The parameters are admissible: λ(v − 1) = 60·242 = 14520 = 121·120 = k(k − 1). Write D⁽⁻¹⁾ = {−d}. In the group ring Z[G], D is a difference set if and only if

  D·D⁽⁻¹⁾ = n·1 + λ·G.  (★)

**Step 1 (61 is a multiplier).** First Multiplier Theorem (Hall 1947 for cyclic groups; for abelian groups see e.g. Beth–Jungnickel–Lenz, *Design Theory*, Ch. VI): if p is a prime with p | n, gcd(p, v) = 1 and p > λ, then for every difference set D the set pD = {pd} is a translate D + g. Here p = 61 = n, gcd(61, 243) = 1 and 61 > 60.

**Step 2 (a translate fixed by 61; McFarland–Rice).** Let s(D) = Σ_{d∈D} d ∈ G. A translate of D is again a difference set, and s(D + g) = s(D) + k·g. Since gcd(k, |G|) = gcd(121, 243) = 1, multiplication by k is a bijection of G, so some translate has s(D) = 0. Replace D by it. If 61D = D + h, take sums of both sides: 61·s(D) = s(D) + k·h. This gives 0 = k·h, so h = 0. Hence **61D = D**.

**Step 3 (orbits).** 61 ≡ 1 (mod 3) and 61 ≡ 7 (mod 9), so x ↦ 61x is (a, b, c) ↦ (a, 7b, 7c). Since 7³ ≡ 1 (mod 9) and 7b ≡ b ⇔ 3 | b, the fixed points are G[3] = Z₃ × 3Z₉ × 3Z₉ (27 elements). The other 216 elements fall into 72 orbits of size 3. So D is a union of some of these **99 orbits**.

**Step 4 (images in cyclic quotients).** Let φ: G → Z_e be onto with kernel H (|H| = 243/e). Let c_j = |D ∩ φ⁻¹(j)|. Applying φ to (★) gives

  Σ_j c_j = 121, Σ_j c_j c_{j+s} = 60·|H| + 61·[s = 0] (s ∈ Z_e), and c_{61j} = c_j by Step 2.

G has exponent 9, so e ∈ {3, 9}. An exhaustive search (`ds_cnf.py`, function `allowed_vectors`) gives the following.
- e = 3: (c₀, c₁, c₂) is a permutation of (36, 40, 45) (6 vectors).
- e = 9: exactly 12 vectors. c₀, c₃, c₆ is a permutation of 9, 13, 18. The orbits {1, 4, 7} and {2, 5, 8} take the values 12 and 15, one each. For example (9, 12, 15, 13, 12, 15, 18, 12, 15).

**Step 5 (these conditions are equivalent to (★)).** Every nontrivial character χ of G factors as χ = ψ∘φ, where φ: G → Z_e is onto (e = order of χ) and ψ is a faithful character of Z_e. Then

  |χ(D)|² = Σ_s (Σ_j c_j c_{j+s}) ψ(s) = 61 + 60|H|·Σ_s ψ(s) = 61.

Conversely, suppose |D| = k and |χ(D)|² = n for every χ ≠ 1. Then the difference-count function N(g) = #{(d, d′) : d − d′ = g} has Fourier transform equal to that of n·δ₀ + λ (use k² = n + λv), so N = n·δ₀ + λ, which is (★). The kernels of characters are exactly the subgroups H with G/H cyclic. G has 13 such subgroups of index 3 (26 elements of order 3, divided by 2) and 36 of index 9 (216 elements of order 9, divided by φ(9) = 6). So requiring Step 4 for all **49 cyclic quotients** is equivalent to D being a difference set. The program recomputes the 49 quotients from the characters.

*Steps 6–7 are not needed for the main certificate (Step 8a). They give the second route (Step 8b), with much smaller SAT instances.*

**Step 6 (the image in G/3G).** G/3G ≅ Z₃³ has 27 cosets of size 9. Let E(x) be the number of elements of D in coset x. All 13 order-3 quotients factor through G/3G, so E satisfies

  Σ E = 121, Σ_x E(x)E(x + s) = 540 for s ≠ 0, 0 ≤ E ≤ 9.

The multiplier adds a further condition. A size-3 orbit {g, 7g, 4g} lies in a single coset of 3G, because 7g − g = 6g ∈ 3G. The fixed points G[3] fill exactly the three cosets on the line L = {(a, 0, 0)}. Hence **E(x) ≡ 0 (mod 3) for x ∉ L**. With this condition there are exactly **864** possible images E. Two independent programs give the same 864 functions:
- `enum_images.c` runs a complete search over all 6¹³ choices of plane-sum vectors (every one of the 13 directions has plane sums that are a permutation of (36, 40, 45), and E(x) = (Σ_d P_d(d·x) − 484)/9). It then checks every candidate directly against the definition.
- `orbit_check.py` uses a much smaller search (3·2¹³ cases) based on the mod-3 condition.

Without the mod-3 condition there are 221 184 solutions, so the multiplier does most of the work here.

**Step 7 (all 864 images are equivalent).** Let Γ be generated by the automorphisms of G and by the translations by elements of G[3]. If D is a difference set with 61D = D, then for α ∈ Aut(G) and t ∈ G[3], α(D) and D + t are also difference sets fixed by 61, because α(61x) = 61α(x) and 61t = t. So Γ permutes the possible images in G/3G. `orbit_check.py` builds explicit automorphisms of G (random homomorphisms that are verified to be bijective) and the translation by (1, 0, 0). The group they induce on G/3G has order 2592 and acts **transitively** on the 864 images (stabilizer of order 3). Therefore, if any difference set exists, one exists whose image is the fixed representative

  E₀ = (3,3,3, 3,3,6, 3,6,6,  4,3,6, 6,3,3, 3,6,6,  6,6,6, 6,3,3, 6,3,6)

(index 9a + 3b + c for the coset (a, b, c) mod 3).

**Step 8 (SAT).** `ds_cnf.py` encodes these conditions: D is a union of the 99 orbits, its image in every one of the 49 cyclic quotients is one of the admissible vectors of Step 4, and |D| = 121. The encoding uses one Boolean variable per orbit, totalizer counters (exact, both directions) for every coset, and one selector variable per admissible vector. Any actual 61-fixed difference set gives a satisfying assignment: set every counter to the true count and every selector to the true image. So "unsatisfiable" means "no such D".

- **(a) Main certificate, no image fixed.** 64 940 variables, 675 931 clauses. CaDiCaL 3.0.1 reports UNSAT in about 390 s, or about 850 s while writing an LRAT proof. The proof (989 MB) is accepted by **cake_lpr** (`s VERIFIED UNSAT`, 66 s) and by lrat-check. This alone, with Steps 1–5, proves the theorem.
- **(b) Second route.** Add "the image in G/3G is E₀" (Steps 6–7). 65 723 variables, 679 495 clauses. UNSAT in about 10 s. The LRAT proof is accepted by cake_lpr and lrat-check, and the DRAT proof by drat-trim.
- **(c) No symmetry argument.** The instance of (b) was built and solved for **each of the 864 images**. Every one is UNSAT.

Hence no (243, 121, 60) difference set exists in Z₃ × Z₉ × Z₉. ∎

## Verification

See `VERIFY.md` for exact commands, tool versions, times and checksums. In summary:

| claim | how it was checked | result |
|---|---|---|
| Steps 1–5 (reduction) | written proof above; every number rechecked by brute force (`reduction_checks.py`) | ALL OK |
| **main SAT instance (no image fixed)** | CaDiCaL → LRAT → **cake_lpr** (formally verified) and lrat-check | **VERIFIED UNSAT** |
| 864 images in G/3G (Step 6) | two independent enumerations: a complete 6¹³ search in C and a 3·2¹³ search in Python | identical, 864 |
| one orbit (Step 7) | explicit automorphisms of G and translations by G[3] | 1 orbit; group of order 2592 |
| instance with image E₀ | LRAT → cake_lpr and lrat-check; DRAT → drat-trim | VERIFIED |
| all 864 instances | CaDiCaL on each | all 864 UNSAT (6–24 s each, 3.0 h of solver time in total) |
| controls | 14 cases with known answers, plus 2 plug-in tests of known sets | all decided cases agree with the literature; two hard cases were left undecided within the time limit: Z₃⁵ (known: yes; blind search, 30 min) and Z₃ × Z₃ × Z₃ × Z₉ (known: no; 90 min). An undecided run cannot contradict the literature |

## Status

**What is verified.** The theorem rests on Steps 1–5 and one SAT instance. The SAT instance has a certificate accepted by a formally verified checker. The answer was also reached a second way (Steps 6–7, then the E₀ instance or all 864 instances). The two ways share only Steps 1–5 and the CNF generator. All code here was written from scratch for this check. The earlier exploratory code that suggested the result was not read or reused. Its CNF for the E₀ case had a different size (about 64 000 variables and 620 000 clauses against 65 723 and 679 495 here), and it reached the same verdict.

**What is still trusted (not machine-checked).**
1. The First Multiplier Theorem, a standard textbook theorem, used as stated.
2. The short hand proofs of Steps 2–5 above. They are not formalized in a proof assistant.
3. The CNF generator `ds_cnf.py` (about 320 lines of Python). The proof needs one property of it: every 61-fixed difference set satisfies the CNF. It is not formally verified. It is tested by the controls, which reproduce the known answers, and by the plug-in tests, where a genuine difference set satisfies the CNF.
4. cake_lpr. Its checking algorithm is verified in HOL4/CakeML down to machine code. What remains trusted is HOL4's kernel, the small C wrapper `basis_ffi.c` and the C compiler for it, and the operating system.
5. The literature check. The text of López–Sánchez 1997 (a print journal) was not read directly. Its content is known through the La Jolla table. Web and arXiv searches for 2020–2026 found no paper that settles this group.

The result is not peer reviewed, and it has not been reported to the La Jolla maintainers.
