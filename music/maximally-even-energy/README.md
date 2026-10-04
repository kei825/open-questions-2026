# 路と円環でのエネルギーの局所最小（Bushaw–Cody–Leffler の問 5.3）

*日本語が先、英語は後半にあります。/ Japanese first; the English version follows below.*

## 問題

グラフ G として**路** P_n（頂点 0, 1, …, n−1 が一列に並ぶ）か**円環** C_n（同じものの n−1 と 0 を
つないだもの）を考えます。k 個の「電荷」を k 個の頂点に置き、その集合を A とします。A の
**エネルギー**は

  E_g(A) = Σ（A の 2 点の組 {u, v} すべて）g(d(u, v))

です。d はグラフ上の距離（路は |u − v|、円環は min(|u − v|, n − |u − v|)）、g は狭義単調減少で凸な関数で、
例えば **g(r) = 1/r**（反発し合う電荷のようなもの）です。エネルギーが小さいほど点がばらけています。

音楽とのつながり: 円環 C_n（n 平均律の n 個の音と思う）では、エネルギー最小の集合はちょうど
Clough–Douthett の**最大偶数集合**です。12 音から 7 音を選ぶ全音階や 5 音を選ぶペンタトニックがその例です
（Douthett–Krantz。Bushaw–Cody–Leffler が新しい証明を与えた）。

論文の定義:
- A の**摂動**: A の 1 点を、隣の空いている頂点へ動かした集合。
- A が**局所最小**: どの摂動もエネルギーが小さくない。
- A が**（大域）最小**: 同じ大きさのどの集合もエネルギーが小さくない。
- **Descending Local Search**（下降局所探索、DLS）: X = A から始め、X の摂動の一覧を見て、
  エネルギーが小さいものがあれば最初のものに移って繰り返す。なければ X を返す。

**問 5.3。** 路と円環で、局所最小はいつも大域最小か。DLS はいつも最小の集合を返すか。

## 出典

- N. Bushaw, B. Cody, C. Leffler, "Sets of vertices with extremal energy",
  arXiv:2407.18785（v3, 2025-02-04）<https://arxiv.org/abs/2407.18785>、
  Discrete Mathematics 348(7) (2025) 114466。問 5.3 は §5、arXiv の PDF の **22 ページ**。
  定義 1.1・1.2 とアルゴリズムは 2〜4 ページ。
- 原文: *"Suppose g : {1, …, ⌊n/2⌋} → ℝ is a strictly decreasing convex function (or for
  concreteness take g(r) = 1/r) and let G be either a path P_n or a cycle C_n on n
  vertices. Is every local minimizer of E_g on G also a global minimizer of E_g? If A is a set
  of vertices of G, does it follow that Descending Local Search(G, E_g, A) is a minimizer of
  E_g?"* 節の冒頭で "a few specific instances of Question 5.1 that seem approachable, but which
  remain open" の 1 つとして挙げられている。

## 答え

**どちらの問いも否**。路でも円環でも、g(r) = 1/r ですでに反例がある。**狭義の**局所最小
（どの摂動も真に悪い）なのに最小でない集合があり、そこから DLS を始めるとその集合がそのまま返る。

## なぜか（初学者向け）

32 頂点の円環（32 時間の時計）に 4 点を置きます。

```
A = {0, 7, 16, 23}           間隔 7, 9, 7, 9     E = 319/504  ≈ 0.63294
M = {0, 8, 16, 24}           間隔 8, 8, 8, 8     E = 5/8      = 0.62500（最大偶数集合）
```

M のほうが A より良い。A から M へ行くには 2 点を動かす必要があります（7 → 8 と 23 → 24）。
ところが A から **1 点だけ**動かすと、どの動かし方でもエネルギーが上がります。

| 動かし方 | 新しい集合 | エネルギー |
|---|---|---|
| 短い間隔を広げる（例 7 → 8） | {0, 8, 16, 23} | 3191/5040 ≈ 0.63313 |
| 短い間隔を縮める（例 7 → 6） | {0, 6, 16, 23} | 655/1008 ≈ 0.64980 |

7 → 8 がなぜ得にならないのか。変わる距離は 3 つだけです。

| 組 | 前 | 後 | 1/d の変化 |
|---|---|---|---|
| 0–7 → 0–8 | 7 | 8 | −0.017857 |
| 7–16 → 8–16 | 9 | 8 | +0.013889 |
| 7–23 → 8–23 | 16 | 15 | +0.004167 |

間隔 7, 9 を 8, 8 にならすと 0.003968 得をしますが、向かい側の点 23 との距離が 16 から 15 に縮み、
0.004167 損をします。差し引き +0.000198 > 0 です。つまり A はエネルギーの地形の小さな谷にあり、
深い谷 M との間に尾根があります。1 点ずつ動かす局所探索は小さな谷で止まります。

路 P_13 に 7 点を置く場合も同じです。A = {0, 1, 3, 6, 8, 10, 12} のエネルギーは 32195/5544 ≈ 5.8072 で、
1 点だけの動かし方 10 通りはすべて悪くなります（最良で 20137/3465 ≈ 5.8115）。しかし等間隔の
{0, 2, 4, 6, 8, 10, 12} は 223/40 = 5.575 です。

## 証明

以下のエネルギーはすべて厳密な有理数で、断りがなければ g(r) = 1/r。

1. **円環 C_32**、A = {0, 7, 16, 23}: E(A) = 319/504。8 通りの摂動のエネルギーは 3191/5040（4 通り）と
   655/1008（4 通り）で、すべて E(A) より大きい。E({0, 8, 16, 24}) = 5/8 < E(A)。
2. **路 P_13**、A = {0, 1, 3, 6, 8, 10, 12}: E(A) = 32195/5544。10 通りの摂動はすべて大きい
   （最小 20137/3465）。E({0, 2, …, 12}) = 223/40 < E(A)（これが大域最小。`check.py` で全数確認）。
3. **円環の無限族。** すべての x ≥ 8 で、C_{4x} の A_x = {0, x−1, 2x, 3x−1}（間隔 x−1, x+1, x−1, x+1）は
   狭義の局所最小で、最小ではない。
   - E(A_x) − E({0, x, 2x, 3x}) = 4 / ((x−1)x(x+1)) > 0。
   - 短い間隔を広げる 4 通りの動きでエネルギーは (x² − 8x + 3) / (2(x−1)x(x+1)(2x−1)) だけ増える。
     これが正になるのはちょうど x ≥ 8 のとき。
   - 短い間隔を縮める 4 通りの動きでは P(x) / (2(x−2)(x−1)x(x+1)(x+2)(2x−1)) だけ増える。
     P(m+8) = m⁴ + 56m³ + 943m² + 6384m + 15300 > 0。

   （例 1 は x = 8 の場合。x = 5, 6, 7 では局所最小にならない。）
4. **2 つ目の問い（DLS）。** DLS が X を変えるのは、エネルギーが**真に**小さい摂動があるときだけ。
   上の集合から始めるとそのような摂動はないので、DLS はその集合をそのまま返し、それは最小でない。
5. **定義 1.2 の字義どおりの読み。** 論文は「F(A) = min{F(B) : B ∈ pert(A)} のとき A は局所最小」と
   書いている。字義どおり（≤ でなく =）に読むと狭義の局所最小は該当しないが、論文は「最小なら明らかに
   局所最小」とも書き、DLS はすべての i で F(L(i)) ≥ F(X) のときに止まるので、≤ の意図なのは明らか。
   字義どおりの読みでも答えは否定的: P_10 の A = {0, 1, 3, 6, 8, 9} は E(A) = 6599/1260 で、これは 6 通りの
   摂動の最小値に**等しい**（6 → 5 で達成）。一方 E({0, 1, 3, 5, 7, 9}) = 12589/2520 < E(A)。
6. **別の g。** C_8 で g(1), g(2), g(3), g(4) = 57, 31, 10, 0（狭義単調減少・狭義凸）とすると、
   A = {0, 1, 4, 5} は E = 134、4 通りの摂動はすべて E = 139、最大偶数集合 {0, 2, 4, 6} は E = 124。

## 検証

Lean 4 のファイル `MaximallyEvenEnergy.lean`（名前空間 `OpenQuestions.MaximallyEvenEnergy`）、Mathlib v4.33.1。
距離は明示式 `pathDist u v = |u − v|`、`cycleDist u v = min(|u − v|, n − |u − v|)`。隣接は「距離 1」。
`energy g d A = Σ_{A の u < v} g (d u v)`、`inv r = 1/r`。

| 定理 | 内容 |
|---|---|
| `cycle32_counterexample` | C_32 の `{0,7,16,23}` は狭義の局所最小・局所最小で、大域最小でない |
| `path13_counterexample` | P_13 の `{0,1,3,6,8,10,12}` について同じ |
| `cycle_family_counterexample m` | C_{4x}（x = m + 8）の `{0, x−1, 2x, 3x−1}` について、すべての m で同じ |
| `path10_literal_counterexample` | P_10 の `{0,1,3,6,8,9}` は字義どおり（=）の意味で局所最小で、大域最小でない |
| `cycle8_general_g_counterexample` | C_8、g = (57,31,10,0)。g の仮定は `g8_strictAnti`・`g8_strictConvex` で確認 |
| `dls_of_isLocalMin` | 局所最小から始めた DLS（摂動の並べ方は任意、燃料も任意でモデル化）はその集合を返す |
| `cycle32_dls`・`path13_dls`・`cycle_family_dls` | これらの集合からの DLS は最小でない集合を返す |

エネルギーの厳密値も定理として置いた（`energy_A32 = 319/504`、`energy_M32 = 5/8`、
`energy_A13 = 32195/5544`、`energy_M13 = 223/40` など）。具体的な集合は `decide +kernel`（カーネル内の
厳密な有理数計算）で検査し、無限族は記号的に証明した（`omega`・`field_simp`・`ring`・`positivity`）。
無限族の Lean コードは `gen_family.py`（sympy）で生成した。`sorry`・`admit`・`native_decide`・新しい公理は
使っていない。

表の定理の `#print axioms` はすべて `[propext, Classical.choice, Quot.sound]`。

再現（約 30 秒）:
```sh
# from the repository root (after `lake exe cache get`)
lake env lean --threads=2 -DautoImplicit=false -DrelaxedAutoImplicit=false \
  music/maximally-even-energy/MaximallyEvenEnergy.lean
```
詳細は `VERIFY.md`。独立な厳密検算は `python3 check.py`。

## 状況

- **解決（両方の問いに否定。路と円環の両方）。Lean 4 で検証済み**（2026-10-04）。
- 既出の確認（2026-10-04）: 答えは見つからなかった。arXiv は v3（2025-02）のまま。Semantic Scholar では
  被引用が 2 件: 同じグループの "The Wiener index of vertex colorings"（arXiv:2503.18920。末尾の問 5.1〜5.7 は
  彩色についてで、問 5.3 には触れていない）と "Metric general position extensions of classical graph
  invariants and perfection"（arXiv:2601.04351、無関係）。OpenAlex では雑誌版の被引用はなし。姉妹論文
  "The Music and Mathematics of Maximally Even Sets"（arXiv:2407.18768）は局所最小を扱っていない。論文が
  引く Barrett の修士論文（Dalhousie, 2018）の局所探索が失敗する例は、路・円環以外のグラフだけ。
- 注意: (1) 局所最小は意図された読み「どの摂動も小さくない」を使い、字義どおりの読みも反証した（5）。
  (2) 問いは g の定義域を {1, …, ⌊n/2⌋} としているが、路の距離は n−1 まであるので、路では問いが許すとおり
  g(r) = 1/r（すべての正の整数で定義）を使った。(3) 問 5.3 には文面どおり答えたが、局所探索が成功する
  条件の特徴づけはしていない。(4) これらの例を見つけた調査は、円環・g = 1/r では n ≤ 26 に反例がなく、
  k ≤ 6・n ≤ 40 では k = 4 の n = 32, 36, 40 だけと報告しているが、ここでは再確認していない。

---

# Local minimizers of the energy on paths and cycles (Bushaw–Cody–Leffler, Question 5.3)


## Problem

Take a graph G that is a **path** P_n (vertices 0, 1, …, n−1 in a row) or a **cycle** C_n
(the same, with n−1 joined back to 0). Put k "charges" on k vertices; call this set A. The
**energy** of A is

  E_g(A) = ∑ over pairs {u, v} ⊆ A of g(d(u, v)),

where d is the distance in the graph (path: |u − v|; cycle: min(|u − v|, n − |u − v|)) and
g is strictly decreasing and convex, for example **g(r) = 1/r** (like electric charges that
repel each other). Low energy means the points are spread out.

Musical connection: on the cycle C_n (think of the n notes of n-tone equal temperament)
the sets of minimal energy are exactly the **maximally even sets** of Clough and Douthett,
such as the diatonic scale (7 of 12) or the pentatonic scale (5 of 12) (Douthett–Krantz;
new proof by Bushaw–Cody–Leffler).

Definitions from the paper:
- A **perturbation** of A moves one point of A to an adjacent empty vertex.
- A is a **local minimizer** if no perturbation has smaller energy.
- A is a **(global) minimizer** if no set of the same size has smaller energy.
- **Descending Local Search** (DLS): start with X = A; look through the list of
  perturbations of X; if one has smaller energy, move to the first such one and repeat;
  otherwise return X.

**Question 5.3.** On paths and cycles, is every local minimizer a global minimizer? Does
Descending Local Search always return a minimizer?

## Source

- N. Bushaw, B. Cody, C. Leffler, "Sets of vertices with extremal energy",
  arXiv:2407.18785 (v3, 2025-02-04), <https://arxiv.org/abs/2407.18785>;
  Discrete Mathematics 348(7) (2025) 114466. Question 5.3 is in §5, **page 22** of the arXiv PDF.
  Definitions 1.1, 1.2 and the algorithm are on pp. 2–4.
- Quote: *"Suppose g : {1, …, ⌊n/2⌋} → ℝ is a strictly decreasing convex function (or for
  concreteness take g(r) = 1/r) and let G be either a path P_n or a cycle C_n on n
  vertices. Is every local minimizer of E_g on G also a global minimizer of E_g? If A is a set
  of vertices of G, does it follow that Descending Local Search(G, E_g, A) is a minimizer of
  E_g?"* The section introduces it as one of "a few specific instances of Question 5.1 that
  seem approachable, but which remain open".

## Answer

**No to both questions**, for paths and for cycles, already for g(r) = 1/r. There are
**strict** local minimizers (every perturbation is strictly worse) that are not minimizers;
Descending Local Search started there returns them unchanged.

## Why (for beginners)

Look at 4 points on a cycle of 32 vertices (a clock with 32 hours).

```
A = {0, 7, 16, 23}           gaps 7, 9, 7, 9     E = 319/504  ≈ 0.63294
M = {0, 8, 16, 24}           gaps 8, 8, 8, 8     E = 5/8      = 0.62500  (maximally even)
```

M is better than A. To go from A to M, two points must move (7 → 8 and 23 → 24). But every
**single** move from A makes the energy go up:

| move | new set | energy |
|---|---|---|
| widen a short gap (e.g. 7 → 8) | {0, 8, 16, 23} | 3191/5040 ≈ 0.63313 |
| shrink a short gap (e.g. 7 → 6) | {0, 6, 16, 23} | 655/1008 ≈ 0.64980 |

Why does 7 → 8 not help? Only three distances change:

| pair | before | after | change in 1/d |
|---|---|---|---|
| 0–7 → 0–8 | 7 | 8 | −0.017857 |
| 7–16 → 8–16 | 9 | 8 | +0.013889 |
| 7–23 → 8–23 | 16 | 15 | +0.004167 |

Evening out the gaps 7, 9 into 8, 8 gains 0.003968, but the point opposite (23) gets closer
(16 → 15), which costs 0.004167. Net change +0.000198 > 0. So A sits in a small valley of the
energy landscape, separated from the deeper valley M by a ridge; a local search that moves
one point at a time stops in the small valley.

On the path P_13 with 7 points the same happens: A = {0, 1, 3, 6, 8, 10, 12} has energy
32195/5544 ≈ 5.8072, all 10 single moves are worse (the best is 20137/3465 ≈ 5.8115), but the
evenly spaced {0, 2, 4, 6, 8, 10, 12} has 223/40 = 5.575.

## Proof

All energies below are exact rational numbers, g(r) = 1/r unless stated.

1. **Cycle C_32**, A = {0, 7, 16, 23}: E(A) = 319/504; the 8 perturbations have energies
   3191/5040 (four of them) and 655/1008 (four), all > E(A); E({0, 8, 16, 24}) = 5/8 < E(A).
2. **Path P_13**, A = {0, 1, 3, 6, 8, 10, 12}: E(A) = 32195/5544; all 10 perturbations
   are larger (minimum 20137/3465); E({0, 2, …, 12}) = 223/40 < E(A) (this is the global
   minimum; exhaustive check in `check.py`).
3. **Infinite family on cycles.** For every x ≥ 8, A_x = {0, x−1, 2x, 3x−1} on C_{4x} (gaps
   x−1, x+1, x−1, x+1) is a strict local minimizer and not a minimizer:
   - E(A_x) − E({0, x, 2x, 3x}) = 4 / ((x−1)x(x+1)) > 0;
   - the 4 moves that widen a short gap raise the energy by
     (x² − 8x + 3) / (2(x−1)x(x+1)(2x−1)), positive exactly when x ≥ 8;
   - the 4 moves that shrink a short gap raise it by
     P(x) / (2(x−2)(x−1)x(x+1)(x+2)(2x−1)) with P(m+8) = m⁴ + 56m³ + 943m² + 6384m + 15300 > 0.

   (Example 1 is the case x = 8. For x = 5, 6, 7 the set is not a local minimizer.)
4. **Second question (DLS).** DLS changes X only if some perturbation has *strictly*
   smaller energy. Started at any of the sets above, no such perturbation exists, so DLS
   returns the set itself, which is not a minimizer.
5. **Literal reading of Definition 1.2.** The paper writes "A is a local minimizer if
   F(A) = min{F(B) : B ∈ pert(A)}". Read literally (equality, not ≤), a strict local minimizer
   would not count; but the paper also says "clearly every minimizer is a local minimizer"
   and its DLS stops when F(L(i)) ≥ F(X) for all i, so ≤ is clearly meant. The answer is
   negative in the literal reading too: on P_10, A = {0, 1, 3, 6, 8, 9} has E(A) = 6599/1260,
   which *equals* the minimum over its 6 perturbations (attained by moving 6 → 5), while
   E({0, 1, 3, 5, 7, 9}) = 12589/2520 < E(A).
6. **Another g.** On C_8 with g(1), g(2), g(3), g(4) = 57, 31, 10, 0 (strictly decreasing,
   strictly convex), A = {0, 1, 4, 5} has E = 134, all 4 perturbations have E = 139, and the
   maximally even {0, 2, 4, 6} has E = 124.

## Verification

Lean 4 file `MaximallyEvenEnergy.lean` (namespace `OpenQuestions.MaximallyEvenEnergy`),
Mathlib v4.33.1. Distances are the explicit formulas `pathDist u v = |u − v|` and
`cycleDist u v = min(|u − v|, n − |u − v|)`; adjacency is "distance 1";
`energy g d A = ∑_{u<v in A} g (d u v)`; `inv r = 1/r`.

| theorem | content |
|---|---|
| `cycle32_counterexample` | `{0,7,16,23}` on C_32 is a strict local minimizer, a local minimizer, and not a global minimizer |
| `path13_counterexample` | the same for `{0,1,3,6,8,10,12}` on P_13 |
| `cycle_family_counterexample m` | the same for `{0, x−1, 2x, 3x−1}` on C_{4x}, x = m + 8, for every m |
| `path10_literal_counterexample` | `{0,1,3,6,8,9}` on P_10 is a local minimizer in the literal (=) reading and not a global minimizer |
| `cycle8_general_g_counterexample` | C_8 with g = (57,31,10,0); `g8_strictAnti`, `g8_strictConvex` check the hypotheses on g |
| `dls_of_isLocalMin` | Descending Local Search (modelled with an arbitrary ordering of the perturbations and any fuel) started at a local minimizer returns it |
| `cycle32_dls`, `path13_dls`, `cycle_family_dls` | DLS from these sets returns a non-minimizer |

Exact energy values are also stated (`energy_A32 = 319/504`, `energy_M32 = 5/8`,
`energy_A13 = 32195/5544`, `energy_M13 = 223/40`, …). Concrete sets are checked with
`decide +kernel` (exact rational arithmetic in the kernel); the family is proved
symbolically (`omega`, `field_simp`, `ring`, `positivity`); its Lean code was generated by
`gen_family.py` (sympy). No `sorry`, `admit`, `native_decide` or new axioms.

`#print axioms` for all theorems in the table: `[propext, Classical.choice, Quot.sound]`.

Reproduce (about 30 s):
```sh
# from the repository root (after `lake exe cache get`)
lake env lean --threads=2 -DautoImplicit=false -DrelaxedAutoImplicit=false \
  music/maximally-even-energy/MaximallyEvenEnergy.lean
```
Details in `VERIFY.md`. Independent exact check: `python3 check.py`.

## Status

- **Solved (negative answer to both parts, for paths and cycles), verified in Lean 4**
  (2026-10-04).
- Literature check (2026-10-04): no answer found. The arXiv record is still at v3
  (2025-02). Semantic Scholar lists two citing papers: the same group's "The Wiener index of
  vertex colorings" (arXiv:2503.18920; its open questions 5.1–5.7 concern colourings and
  do not mention Question 5.3) and "Metric general position extensions of classical graph
  invariants and perfection" (arXiv:2601.04351, unrelated). OpenAlex lists no citing work
  of the journal version. The companion paper "The Music and Mathematics of Maximally Even
  Sets" (arXiv:2407.18768) does not discuss local minimizers. Barrett's 2018 Dalhousie
  master's thesis (cited in the paper) gives a failing local search only on other graphs.
- Notes: (1) We use the intended reading "no perturbation is smaller" for local
  minimizer, and also refute the literal reading (item 5). (2) The question lets g live on
  {1, …, ⌊n/2⌋}; on a path the distances go up to n−1, so for paths we use g(r) = 1/r on all
  positive integers, as the question allows ("for concreteness take g(r) = 1/r").
  (3) This settles Question 5.3 as asked; it does not characterize when local search does
  succeed. (4) The survey that found these examples also reported that on cycles with
  g = 1/r there is no counterexample for n ≤ 26, and for k ≤ 6, n ≤ 40 only k = 4,
  n = 32, 36, 40; this was not re-checked here.
