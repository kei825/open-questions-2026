# 整数の重みでは Colless 型バランス指数は「健全」にならない

*日本語が先、英語は後半にあります。/ Japanese first; the English version follows below.*

## Problem（問題）

Mir・Rosselló・Rotger（2018）は、多分岐の系統樹がどれだけ偏っているかを測る指数の族
`C_{D,f}` を作りました。指数は重み関数 `f` とばらつきの尺度（dissimilarity）`D` で決まります。
指数が 0 になる木が「完全に釣り合った木（完全対称な木）」とちょうど一致するとき、
その指数は**健全**（sound）であるといいます。著者らは `f(n) = eⁿ` と `f(n) = ln(n+e)` が健全で
あることを示したうえで、次の予想を立てました。

> **予想.** どんな関数 `f : ℕ → ℕ` を選んでも `C_{D,f}` は健全にならない。

## Source（出典）

- A. Mir, F. Rosselló, L. Rotger, *Sound Colless-like balance indices for multifurcating trees*,
  PLoS ONE 13(9): e0203401 (2018), <https://doi.org/10.1371/journal.pone.0203401>,
  arXiv:[1805.01329](https://arxiv.org/abs/1805.01329)。
  問題は "Sound Colless-like indices" の節（定義 9、補題 10、例 11）にあります。予想は結論の節の
  最後の一文 *"Our conjecture is that no function f : N → N satisfies this property."* です。
- M. Fischer ほか『Tree Balance Indices: A Comprehensive Survey』（Springer 2023、
  arXiv:[2109.12281v2](https://arxiv.org/abs/2109.12281)）§9.7。「興味深い予想」として、
  未解決のまま紹介されています。

## Answer（答え）

**予想は正しい。** どんな `f : ℕ → ℕ` と、どんな dissimilarity `D` についても、`C_{D,f}` は
健全ではありません。より一般に、**有理数値**の `f` なら符号に関係なく同じことが成り立ちます。
実際に有理数である必要があるのは `f(0), f(2), f(3), f(4), f(6)` の 5 つの値だけです。
この結果は Lean 4 と Mathlib で検証しました（定理 `mir_rossello_rotger_conjecture`）。

この条件は外せません。`eⁿ` と `ln(n+e)` は健全で、論文はその証明に `e` が超越数であることを
使っています。値が有理数であることこそが、健全さを壊します。

## Why（なぜ／初学者向け）

**系統樹.** 系統樹は根のある木です。葉が種を、内部の頂点が共通祖先を表します。分岐の順番が
分からないところでは、1 つの頂点が 3 つ以上の子を持つことがあります（*多分岐*）。
子がちょうど 1 つの頂点は使いません。

**バランス指数.** 実際の系統樹を進化のモデルと比べるために、木がどれだけ偏っているかを 1 つの
数で表したい、という需要があります。二分岐の木では **Colless 指数** が定番です。内部の頂点ごとに
|左の葉の数 − 右の葉の数| を求めて、全部足します。

```
   釣り合った木（Colless 0）       毛虫型（Colless 0+1+2 = 3）
          o                              o
        /   \                           / \
       o     o                         o   c
      / \   / \                       / \
     a   b c   d                     o   b
                                    / \
                                   a   d
```

**Colless 型指数.** 子が何個あってもよいように、「子が k 個の頂点」に重み `f(k)` を割り当てます。
木 `T` の **f-size** は `δ_f(T) = Σ_頂点 f(子の数)` です。`f ≡ 1` なら頂点の数、
`f(0)=1` かつ `k>0` で `f(k)=0` なら葉の数になります。内部の頂点 `v` ごとに、子の下にある
部分木たちの f-size がどれだけばらついているかを `D` で測ります（例えば中央値からの平均偏差）。
`D` が 0 になるのは、全部が等しいときだけです。そして

`C_{D,f}(T) = Σ_{内部の頂点 v} D(v の子の下にある部分木たちの f-size)`

と定めます。

**完全対称な木.** どの頂点でも、子の下にある部分木がすべて同じ形をしている木を *完全対称* と
いいます。こうした木は、深さごとの子の数で決まります。これを `FS_{k₁,…,k_h}` と書きます。
根が `k₁` 個の子を持ち、その子がそれぞれ `k₂` 個の子を持ち、と続きます。

```
   FS_{2,3}                       FS_{3,2}
        o                             o
      /   \                        /  |  \
     o     o                      o   o   o
    /|\   /|\                    / \ / \ / \
   . . . . . .                   . . . . . .
```

どちらも葉は 6 枚ですが、別の木です。完全対称な木の指数は必ず 0 です。逆に「指数が 0 なら
完全対称」も成り立つとき、指数は健全だといいます。

**落とし穴（論文の補題 10）.** *異なる* 完全対称な木 `T₁`, `T₂` の f-size が等しかったとします。
新しい根の下に 2 つを並べると、`T₁`, `T₂` の内部では指数は 0 です。新しい根でも 2 つの
f-size が等しいので `D = 0` です。よって新しい木の指数は 0 なのに、2 つの部分木の形が違うので
完全対称では**ありません**。つまり健全であることは、「異なる完全対称な木は f-size も異なる」
ことと同じです。

**論文の例 11: `FS_{2,2,2,7}` と `FS_{14,4}`.**

```
FS_{2,2,2,7}                                  FS_{14,4}

               o                                           o
           /       \                      ________________/|\________________
         o           o                   o  o  o  o  o  o  o  o  o  o  o  o  o  o   （14 個）
       /   \       /   \                 この 14 個がそれぞれ葉を 4 枚持つ
      o     o     o     o                → 葉は 56 枚
     / \   / \   / \   / \
    o   o o   o o   o o   o    （8 個）
    この 8 個がそれぞれ葉を 7 枚持つ
    → 葉は 56 枚
```

| | 頂点の数 | 辺の数 = Σ k | Σ k² |
|---|---|---|---|
| `FS_{2,2,2,7}` | 1+2+4+8+56 = 71 | 2+4+8+56 = 70 | 4+8+16+8·49 = 420 |
| `FS_{14,4}` | 1+14+56 = 71 | 14+56 = 70 | 196+14·16 = 420 |

したがって 2 次式の重み `f(k) = ak² + bk + c` なら、どちらの f-size も `420a + 70b + 71c` です。
2 つを根の下に並べると、完全対称でないのに指数が 0 の木ができます。`f ≡ 1`（頂点の数）なら、
もっと小さな例があります。`FS_{4,2,6,3}` の頂点は 1+4+8+48+144 = 205 個、`FS_{6,3,2,4}` の
頂点も 1+6+18+36+144 = 205 個です。

**整数だと必ず失敗する理由（考え方）.** 重みが整数なら f-size も整数です。しかも完全対称な木の
f-size は、およそ「重みの最大値の 2 倍 × 葉の数」を超えません。各深さの子の数を 2, 3, 4, 6 に
限った完全対称な木を数えると、その個数は、f-size が取りうる整数の個数よりも速く増えます。
鳩の巣原理により、f-size が一致する 2 本が必ずあります。

## Proof（証明）

`w = (k₁, …, k_h)`（すべて `kᵢ ≥ 2`）、`P_i = k₁⋯kᵢ`（`P₀ = 1`）、`prod w = P_h` とします。

1. **f-size の式**（論文の例 3）:
   `δ_f(FS_w) = Σ_{i<h} P_i·f(k_{i+1}) + P_h·f(0)`。漸化式で書くと
   `δ_f(FS_{k,w'}) = f(k) + k·δ_f(FS_{w'})`。
2. **上界.** `M ≥ |f(0)|, |f(2)|, |f(3)|, |f(4)|, |f(6)|` とします。文字がすべて `{2,3,4,6}` に
   入っていれば、帰納法で `|δ_f(FS_w)| ≤ M(2P_h − 1)` が言えます。`k ≥ 2` なので
   `M + k·M(2P − 1) ≤ M(2kP − 1)` となるからです（内部の頂点は葉より少ない）。
3. **積が同じ大きな族.** `n` を固定します。`{0,…,2n−1}` の部分集合 `S, T`（どちらも要素 `n` 個）に
   対し、`i` 文字目を `(1 + [i∈S])·(2 + [i∈T]) ∈ {2, 3, 4, 6}` とします。4 つの値は互いに
   違うので、語から `(S,T)` を読み戻せます。積はどれも `2ⁿ·2ⁿ·3ⁿ = 12ⁿ` で、
   語は `C(2n,n)² ≥ 16ⁿ/(2n+1)²` 個あります。
4. **鳩の巣.** `f` が整数値なら、これらの f-size はすべて `[−2M·12ⁿ, 2M·12ⁿ]` に入る整数です。
   この区間の整数は `4M·12ⁿ + 1` 個です。`(16ⁿ/(2n+1)²) ÷ 12ⁿ = (4/3)ⁿ/(2n+1)² → ∞` なので、
   `n` が大きければ語の数が値の数を上回ります。よって異なる語 `w₁ ≠ w₂` で f-size が同じものが
   あります。
5. **木として異なる.** 「どの深さにどの出次数の頂点があるか」は同型で変わりません。`FS_w` では
   それがちょうど `w` です。よって `FS_{w₁}` と `FS_{w₂}` は同型ではありません。
6. **結論.** 補題 10 により、どんな `D` でも `C_{D,f}` は健全ではありません。`f` が有理数値なら、
   `f(0), f(2), f(3), f(4), f(6)` の公分母 `d` を掛けます。上で使う f-size がすべて `d` 倍になる
   だけで、議論はそのまま通ります。

*補足.* 調査メモの証明は、2, 3, 4 をちょうど `N` 個ずつ並べた語と、積 `24ᴺ` に対する
`(3N)!/(N!)³ ≥ 27ᴺ/(3N+1)²` を使っていました。この議論も正しいです。Lean では `{2,3,4,6}` の族を
使いました。個数が中心二項係数の積になり、Mathlib に下界 `4ⁿ ≤ (2n+1)·C(2n,n)` が既にあるからです。

## Verification（検証）

- `CollessLikeIndex.lean`（名前空間 `OpenQuestions.CollessLikeIndex`）は Lean 4.33.1 と
  Mathlib v4.33.1 を使います。エラーも警告もなくコンパイルでき、`sorry`・`admit`・
  `native_decide`・`axiom` は含みません。
- 主定理は `mir_rossello_rotger_conjecture`
  （`∀ f : ℕ → ℕ, ∀ D, IsDissimilarity D → ¬ Sound D (fun n => (f n : ℝ))`）です。
  有理数値の `f` については `not_sound_rat` があります。
- `#print axioms` は `propext`, `Classical.choice`, `Quot.sound` だけです。
- 木は `RTree.node (子のリスト)` で表します。同型は「子どうしの全単射で、対応する子が同型」と
  いう定義です。`Valid` で出次数 1 を除きます。`FullySym`, `fsize`, `colless`,
  `IsDissimilarity`（非負・対称・定数列でちょうど 0）, `Sound`（定義 9）は論文に従いました。
  念のため、`sound_iff` で完全対称な木の指数が 0 であることを示し、`example` で例 11 を
  検算しています。
- 詳細、実行したコマンド、数値での照合は [`VERIFY.md`](VERIFY.md) にあります。

## Status（状況）

- **ここで解決（2026-10-04）、Lean で証明済み。**
- 既出の確認（2026-10-04）:
  - Semantic Scholar と OpenAlex の被引用はそれぞれ 25 件で、予想を解いたと主張するものは
    ありません。
  - Rosselló のその後の arXiv 論文（2019〜2021）もこの予想を扱っていません。
  - 総説の最新版（arXiv v2、2023-11-09、Springer 版と同じ内容）でも未解決とされています。
  - 2024〜2026 年の被引用（Kersting–Wicke–Fischer 2024/25、Kersting–Fischer 2026、
    Doboli–Maranca–Rosenberg 2026）は指数を使っているだけです。
- 注意: 議論は短く初等的です。専門家からは深い結果というより小さな観察と受け取られるかも
  しれません。ただし、論文が述べたとおりの形で問いに決着をつけています。

---

# No integer weight gives a sound Colless-like balance index


## Problem

Mir, Rosselló and Rotger (2018) built a family of indices `C_{D,f}` that measure how unbalanced
a multifurcating phylogenetic tree is. Each index depends on a weight function `f` and a
dissimilarity `D`. An index is called **sound** if it is 0 exactly on the "perfectly balanced"
(fully symmetric) trees. The authors showed that `f(n) = eⁿ` and `f(n) = ln(n+e)` are sound. They
conjectured:

> **Conjecture.** No function `f : ℕ → ℕ` makes `C_{D,f}` sound.

## Source

- A. Mir, F. Rosselló, L. Rotger, *Sound Colless-like balance indices for multifurcating trees*,
  PLoS ONE 13(9): e0203401 (2018), <https://doi.org/10.1371/journal.pone.0203401>,
  arXiv:[1805.01329](https://arxiv.org/abs/1805.01329).
  The problem is in the subsection "Sound Colless-like indices" (Definition 9, Lemma 10,
  Example 11). The conjecture is the last sentence of the Conclusions: *"Our conjecture is that no
  function f : N → N satisfies this property."*
- M. Fischer, L. Herbst, S. Kersting, L. Kühn, K. Wicke, *Tree Balance Indices: A Comprehensive
  Survey* (Springer 2023; arXiv:[2109.12281v2](https://arxiv.org/abs/2109.12281)), §9.7. It calls
  this "an interesting conjecture" and says it is still open.

## Answer

**The conjecture is true.** For every `f : ℕ → ℕ` and every dissimilarity `D`, the index `C_{D,f}`
is not sound. More generally, this holds for every **rational-valued** `f`, with no sign
condition. In fact only the five values `f(0), f(2), f(3), f(4), f(6)` need to be rational. This
is checked in Lean 4 with Mathlib (theorem `mir_rossello_rotger_conjecture`).

The condition cannot be dropped: `eⁿ` and `ln(n+e)` are sound, and the paper's proofs use that
`e` is transcendental. Rational values are exactly what breaks soundness.

## Why

**Phylogenetic trees.** A phylogenetic tree is a rooted tree. The leaves are species and each
internal node is a common ancestor. When the branching order is unresolved, a node may have 3 or
more children (a *multifurcating* tree). A node never has exactly one child.

**Balance indices.** Biologists want one number that says how lopsided a tree is, so that real
trees can be compared with models of evolution. For binary trees the classic choice is the
**Colless index**: at every internal node, take |(leaves on the left) − (leaves on the right)|,
and add these up.

```
   balanced (Colless 0)          caterpillar (Colless 0+1+2 = 3)
          o                              o
        /   \                           / \
       o     o                         o   c
      / \   / \                       / \
     a   b c   d                     o   b
                                    / \
                                   a   d
```

**Colless-like indices.** To handle nodes with many children, Mir–Rosselló–Rotger choose a
weight `f(k)` for "a node with k children". The **f-size** of a tree `T` is
`δ_f(T) = Σ_nodes f(number of children)`. With `f ≡ 1` it is the number of nodes. With `f(0)=1`
and `f(k)=0` for `k>0` it is the number of leaves. At each internal node `v`, `D` measures how
different the f-sizes of the child subtrees are (for example their mean deviation from the
median). `D` is 0 exactly when they are all equal. Then

`C_{D,f}(T) = Σ_{internal v} D(f-sizes of the subtrees below the children of v)`.

**Fully symmetric trees.** A tree is *fully symmetric* if, at every node, all child subtrees have
the same shape. Such a tree is fixed by how many children each level has. We write
`FS_{k₁,…,k_h}`: the root has `k₁` children, each of them has `k₂` children, and so on.

```
   FS_{2,3}                       FS_{3,2}
        o                             o
      /   \                        /  |  \
     o     o                      o   o   o
    /|\   /|\                    / \ / \ / \
   . . . . . .                   . . . . . .
```

Both have 6 leaves, but they are different trees. A fully symmetric tree always has index 0. The
index is *sound* when the converse also holds: index 0 only for fully symmetric trees.

**The trap (Lemma 10 of the paper).** Suppose two *different* fully symmetric trees `T₁`, `T₂`
have the same f-size. Hang both below a new root. Each of them has index 0, and at the new root
the two f-sizes are equal, so `D = 0` there too. The new tree has index 0, yet it is **not**
fully symmetric, because its two subtrees have different shapes. So soundness means exactly this:
different fully symmetric trees must have different f-sizes.

**Example 11 of the paper: `FS_{2,2,2,7}` and `FS_{14,4}`.**

```
FS_{2,2,2,7}                                  FS_{14,4}

               o                                           o
           /       \                      ________________/|\________________
         o           o                   o  o  o  o  o  o  o  o  o  o  o  o  o  o   (14 nodes)
       /   \       /   \                 each of these 14 nodes has 4 leaves
      o     o     o     o                → 56 leaves
     / \   / \   / \   / \
    o   o o   o o   o o   o    (8 nodes)
    each of these 8 nodes has 7 leaves
    → 56 leaves
```

| | nodes | edges = Σ k | Σ k² |
|---|---|---|---|
| `FS_{2,2,2,7}` | 1+2+4+8+56 = 71 | 2+4+8+56 = 70 | 4+8+16+8·49 = 420 |
| `FS_{14,4}` | 1+14+56 = 71 | 14+56 = 70 | 196+14·16 = 420 |

So for every quadratic weight `f(k) = ak² + bk + c` both trees have f-size `420a + 70b + 71c`.
Put them side by side below a root and you get a non-symmetric tree with index 0. An even smaller
example for `f ≡ 1` (node count): `FS_{4,2,6,3}` has 1+4+8+48+144 = 205 nodes, and `FS_{6,3,2,4}`
has 1+6+18+36+144 = 205 nodes.

**Why integers always fail (the idea).** With integer weights every f-size is an integer, and
the f-size of a fully symmetric tree is at most about twice the largest weight times the number
of leaves. Count the fully symmetric trees whose levels use only 2, 3, 4 and 6 children: their
number grows faster than the number of integers available for their f-sizes. By the pigeonhole
principle, two of them must share an f-size.

## Proof

Write `w = (k₁, …, k_h)` with all `kᵢ ≥ 2`, `P_i = k₁⋯kᵢ` (with `P₀ = 1`) and `prod w = P_h`.

1. **f-size formula** (paper, Example 3):
   `δ_f(FS_w) = Σ_{i<h} P_i·f(k_{i+1}) + P_h·f(0)`, or recursively
   `δ_f(FS_{k,w'}) = f(k) + k·δ_f(FS_{w'})`.
2. **Bound.** Let `M ≥ |f(0)|, |f(2)|, |f(3)|, |f(4)|, |f(6)|`. If all letters are in
   `{2,3,4,6}`, then `|δ_f(FS_w)| ≤ M(2P_h − 1)`, by induction:
   `M + k·M(2P − 1) ≤ M(2kP − 1)` because `k ≥ 2`. (The internal nodes are fewer than the leaves.)
3. **A big family with the same product.** Fix `n`. For subsets `S, T ⊆ {0,…,2n−1}` of size `n`,
   let the `i`-th letter be `(1 + [i∈S])·(2 + [i∈T]) ∈ {2, 3, 4, 6}`. These four values are
   different, so `(S,T)` can be read back from the word. Every such word has product
   `2ⁿ·2ⁿ·3ⁿ = 12ⁿ`. There are `C(2n,n)² ≥ 16ⁿ/(2n+1)²` of them.
4. **Pigeonhole.** For integer `f`, all these f-sizes are integers in `[−2M·12ⁿ, 2M·12ⁿ]`, which
   holds `4M·12ⁿ + 1` integers. Since `16ⁿ/(2n+1)² ÷ 12ⁿ = (4/3)ⁿ/(2n+1)² → ∞`, for large `n` there
   are more words than values. So two different words `w₁ ≠ w₂` give the same f-size.
5. **They are different trees.** "Which out-degree occurs at which depth" does not change under
   isomorphism, and in `FS_w` it is exactly `w`. So `FS_{w₁}` and `FS_{w₂}` are not isomorphic.
6. **Conclusion.** By Lemma 10, `C_{D,f}` is not sound, for every `D`. For rational `f`, multiply by
   a common denominator `d` of `f(0), f(2), f(3), f(4), f(6)`. This multiplies every f-size used
   above by `d` and changes nothing else.

*Remark.* The survey sketch used the words with exactly `N` letters each of 2, 3 and 4, together
with `(3N)!/(N!)³ ≥ 27ᴺ/(3N+1)²` against the product `24ᴺ`. That argument is also correct. The Lean
proof uses the `{2,3,4,6}` family because its size is a product of central binomial coefficients,
for which Mathlib already has the bound `4ⁿ ≤ (2n+1)·C(2n,n)`.

## Verification

- `CollessLikeIndex.lean` (namespace `OpenQuestions.CollessLikeIndex`) uses Lean 4.33.1 and
  Mathlib v4.33.1. It compiles with no errors or warnings, and has no `sorry`, `admit`,
  `native_decide` or `axiom`.
- Main theorem:
  ```lean
  theorem mir_rossello_rotger_conjecture :
      ∀ f : ℕ → ℕ, ∀ D : List ℝ → ℝ, IsDissimilarity D → ¬ Sound D (fun n => (f n : ℝ))
  ```
  plus `not_sound_rat` for every `f : ℕ → ℚ`.
- `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`.
- Trees are `RTree.node (children)`. Isomorphism is a bijection between children with isomorphic
  partners. `Valid` rules out out-degree 1. `FullySym`, `fsize`, `colless`, `IsDissimilarity`
  (non-negative, symmetric, zero exactly on constant sequences) and `Sound` (Definition 9) follow
  the paper. As a sanity check, `sound_iff` proves that fully symmetric trees have index 0, and an
  `example` re-checks Example 11.
- Details, the command line and numerical cross-checks are in [`VERIFY.md`](VERIFY.md).

## Status

- **Solved here (2026-10-04), with a Lean proof.**
- Prior-work check (2026-10-04):
  - Semantic Scholar and OpenAlex each list 25 citing works. None of them claims to solve the
    conjecture.
  - F. Rosselló's later arXiv papers (2019–2021) do not return to it.
  - The latest version of the survey (arXiv v2, 9 Nov 2023, the same text as the Springer book)
    still calls it open.
  - The citing works from 2024–2026 only use the index: Kersting–Wicke–Fischer 2024/25,
    Kersting–Fischer 2026, Doboli–Maranca–Rosenberg 2026.
- Caveat: the argument is short and elementary. Specialists may see it as a small observation
  rather than a deep result. It does settle the question exactly as the paper states it.
