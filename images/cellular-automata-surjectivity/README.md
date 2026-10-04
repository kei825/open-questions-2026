# 「切り出せない」のに全射な 5 画素の画像変換

*日本語が先、英語は後半にあります。/ Japanese first; the English version follows below.*

## Problem（問題）

無限に広い白黒画像を考えます。**2 次元セル・オートマトン**は、すべての画素を一斉に塗り替える変換です。
各画素の新しい色は、その近くの決まった数画素（**近傍**）の色だけから、1 つの共通の規則で決まります。
どんな画像 `y` に対しても、変換すると `y` になる画像 `x` があるとき、この変換は**全射**といいます。

Fukś と Skelton は、全射を保証する簡単な判定法（下で説明する「スライス置換的」）を見つけました。
そのうえで、5 画素の規則が全射になる理由はこれしかないのか、と問いました。

> 真に 2 次元の 5 点 2 値規則で、全射だがスライス置換的でないものは存在するか。

## Source（出典）

- H. Fukś, A. Skelton, *Classification of two-dimensional binary cellular automata with respect to
  surjectivity*, Proc. CSC-2012, CSREA Press, pp. 51–57。
  [arXiv:1208.0771](https://arxiv.org/abs/1208.0771)。
- 場所: §6 Conclusions（arXiv の PDF の 6 ページ目）。
- 原文: "A related question is whether there exist any truly two-dimensional five-site binary rule
  which is surjective yet not slice permutive? Since in one dimension such rules are possible even
  in four-site neighbourhoods, we suspect that the answer is affirmative, although currently we
  cannot offer any evidence of this claim."

## Answer（答え）

**存在します。** L 形のペントミノを近傍とする規則を具体的に示しました。
この規則は 5 画素すべてに依存し、全射です。しかも**どの画素についても**置換的でないので、
特にスライス置換的ではありません。全射の証明は Lean 4（Mathlib）で完全に検証済みです。

## Why（なぜそうなるか・初学者向け）

### 変換のしくみ

画像を画素 `x(i, j)`（黒 = 1、白 = 0）の格子と考えます。`i` は右へ数えた列、`j` は上へ数えた行です。
画素 `(i, j)` の新しい色は、**L 字形**に並んだ 5 つの古い画素から計算します。

```
行 j+1:   e
行 j  :   a  b  c  d        a = x(i,j)    b = x(i+1,j)   c = x(i+2,j)
          ^                 d = x(i+3,j)  e = x(i,j+1)
          新しい色はここに書く
```

すべての画素を、同じ規則 `f(a, b, c, d, e)` で一斉に塗り替えます。

### 規則（例 B）

まず角の 2 画素をまとめて `s = a XOR e` とします（`a` と `e` のちょうど一方が黒なら 1）。
新しい色は次の表の `g(s, b, c, d)` です。

| b c d | s = 0 | s = 1 |
|:-----:|:-----:|:-----:|
| 0 0 0 | 0 | 0 |
| 0 0 1 | 1 | 0 |
| 0 1 0 | 1 | 1 |
| 0 1 1 | 1 | 1 |
| 1 0 0 | 1 | 1 |
| 1 0 1 | 1 | 0 |
| 1 1 0 | 0 | 0 |
| 1 1 1 | 0 | 0 |

言葉で書くと、`s = 0` なら「`b` が黒なら `c` の反対、白なら `c` または `d`」、
`s = 1` なら「`b` が黒なら `c` も `d` も白のときだけ黒、白なら `c`」です。
32 ビットの真理値表（入力のビット番号 `a + 2b + 4c + 8d + 16e`）では `0x3a3c353c` です。

### 「スライス置換的」とは何か、この規則がそうでない理由

- ある画素について**置換的**とは、他の 4 画素がどんな色でも、その画素を反転すると出力が必ず反転することです。
- 近傍の画素が**切り出せる**（sliceable）とは、その画素を通る直線で、残りの 4 画素がすべて直線の片側（直線上は不可）に来るものがあることです。
  L 字形では 3 つの角 `a`, `d`, `e` が切り出せます。真ん中の `b`, `c` は切り出せません
  （`b` を通るどの直線でも、`a` と `c` は反対側に分かれるか、直線上に乗ります）。
- **スライス置換的** = 切り出せる画素のどれかについて置換的、ということです。Fukś と Skelton は、
  これが全射を導くことを示しました。直線を画像の上で少しずつ動かしながら、切り出した画素の色を
  毎回うまく選べば逆像が作れる、という証明です。

この規則は**どの画素についても**置換的ではありません。どの画素にも、反転しても出力が変わらない場面があります。

| 画素 | 他の 4 画素 | その画素が 0 / 1 のときの出力 |
|---|---|---|
| a | b=c=d=e=0 | 0 / 0 |
| b | a=c=e=0, d=1 | 1 / 1 |
| c | a=b=e=0, d=1 | 1 / 1 |
| d | a=b=c=0, e=1 | 0 / 0 |
| e | a=b=c=d=0 | 0 / 0 |

そのうえで、5 画素のどれにも本当に依存しています（真の 5 点規則）。

### それでも全射になる理由: 1 画素ではなく 1 行ずつ

出力の行 `j` が読むのは、入力の行 `j` と行 `j+1` だけです。しかも行 `j+1` からは 1 画素（`e`）しか読みません。
そこで、逆像を**上から順に**作ります。

1. 画像の 1 つ上の行は適当に決めます。
2. 行 `j+1` が決まると、その画素は行 `j` にとって既知の「切替」`e_i` になります。
   目標の行のすべての列 `i` で `f(r_i, r_{i+1}, r_{i+2}, r_{i+3}, e_i) = y_i` となる行 `r` を探します。
3. これを下へ繰り返します。

この規則では、手順 2 がいつでも成功します。
これは、窓 `(r_i, r_{i+1}, r_{i+2})` を状態とする小さなオートマトン（8 状態）の問題です。
目標の画素 `y_i` と切替 `e_i` を読み、次の画素 `r_{i+3}` を選びます。
手順 2 がいつでも成功することは、到達できる窓の**集合**が決して空にならないことと同じです。
これは有限の検査（集合は高々 256 個）で決まります。
この規則では、到達できる集合は必ず次の 4 つの「良い」窓の集合のどれかを含みます
（窓を `(a, b, c)` と書きます）。

- G0: `a = b`、G1: `a ≠ b`
- G2: （`c = 0` かつ `a = b`）または（`c = 1` かつ `a = 1`）、G3: G2 の補集合

`(e_i, y_i)` が何であっても、良い集合からは次の良い集合へ進めます。
だから、行がどれだけ長くても解の行が必ずあります。

これで**有限の**画像には必ず逆像があります。無限の画像は、標準的なコンパクト性の議論
（ケーニヒの補題、チコノフの定理）で扱います。だんだん大きくなる正方形の逆像の集合は、
コンパクトな「全画像の空間」の中で、空でない閉集合の減少列になります。
だから共通の点があり、それが無限の画像全体の逆像になります。

### 小さな画像での例

目標（7×4、`#` = 黒、上の行から表示）と、上の手順で見つけた逆像（10×5、`demo_preimage.py`）です。

```
目標              逆像
.#...#.           ..........
.......           #..###.##.
#.....#           ..........
.#####.           .#.......#
                  #..#.#.##.
```

左下の出力画素を確かめます。逆像の最下行から `a = 1, b = 0, c = 0, d = 1`、`a` の真上から `e = 0` です。
`s = 1` なので `g(1, 0, 0, 1) = c = 0`（白）となり、目標と合います。
その右隣は `a = 0, b = 0, c = 1, d = 0, e = 1` で、`s = 1`、`g = c = 1`（黒）です。✓

## Proof（証明）

Lean のファイル `CASurjectivity.lean` で次を証明しました。

- `answer`: 近傍 `N`（相異なる 5 点、連結、一直線上にない）と規則 `f` があり、`f` は 5 点すべてに依存し、
  `ℤ × ℤ → Bool` 上の大域写像は全射で、スライス置換的でない。
- `F_surjective`: 例 B の大域写像は全射。組み立ては次のとおりです。
  `good_step`（オートマトンの検査、`decide`）→ `row`（行の補題）→ `rect`（有限の長方形にはすべて逆像がある）
  → コンパクト性（コンパクトな直積空間 `ℤ × ℤ → Bool` での
  `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`）。
- `dependsOn_all`、`not_permutive`、`not_slicePermutive`、`sliceable_iff`
  （切り出せる点は `a`, `d`, `e` だけ。論文どおり有理数の直線で定義）、`rule_truthTable`。

定義は論文の §2–3 に合わせています。大域写像は `F(x)_p = f(x_{p+u}, u ∈ N)`、
`v` について置換的とは、どの `b` についても `t ↦ f([t, b])` が単射であることです。

## Verification（検証）

- Lean 4.33.1 + Mathlib v4.33.1。`sorry`・`admit`・`native_decide`・追加の公理は使っていません。
  `#print axioms answer` は `[propext, Classical.choice, Quot.sound]` です。詳細は `VERIFY.md`。
- 独立の C プログラム `verify_l.c` で、例 B について真理値表、5 点すべてへの依存、置換的な点が無いこと、
  行ごとの条件を確認しました。論文の表 1（1 次元 4 点の全射規則 582 個）も再現しています。

## Status（現状）

- **論文の第 2 の問いは肯定的に解決し、Lean で検証済みです。** 査読は受けていません。
  例は初等的です。問いは小規模な会議録に載ったもので、続報はありませんでした。
- **既出の確認（2026-10-04）。** 2012〜2026 年にこの問いに答えた文献は見つかりませんでした。
  - Fukś の業績一覧（<https://lie.ac.brocku.ca/~hfuks/publications-1.html>）に、
    2 次元の全射性やスライス置換性の続報はありません。
  - Semantic Scholar と OpenAlex にある被引用は 3 件です。
    *Response curves of deterministic and probabilistic cellular automata in one and two dimensions*（2012、全射性ではなく応答曲線の研究）、
    可逆 CA による暗号化を扱ったスペイン語の学位論文（2014）、Hadeler–Müller の教科書
    *Cellular Automata: Analysis and Applications*（Springer 2017）の章 "Surjectivity and Injectivity of Global Maps" です。
    教科書の章は本文を読めませんでしたが、問いに答えているという手がかりはありません。
  - "slice permutive" などの語の Web 検索でも、原論文しか見つかりませんでした。
- **論文の第 1 の問い（残りの 5 点規則を分類できるか）は未解決のままです。**
  参考までに、こちらの計算（`verify_l.c`）では、行ごとの条件を満たし、5 点すべてに依存し、
  スライス置換的でない L 形の規則がちょうど 1472 個ありました。
  これは論文の表 2 にある L の未分類数と一致します。調査担当の別プログラム（ここには含めていません）では Y 形も 1472 個でした。
  Y 形は格子の剪断 `(x, y) ↦ (x + y, y)` で L 形と同値なので、一致は予想どおりです。
  論文の数が正しければ、L 形・Y 形の未分類規則はすべて全射ということになります。
  F・P・S・U・W 形はこの方法では決着しません。この部分は副次的な結果で、Lean では形式化していません。

---

# A surjective 5-pixel image rule that cannot be "sliced"


---

## Problem

Take a black-and-white image on an infinite grid. A **two-dimensional cellular automaton** repaints
every pixel at the same time, using one fixed rule that looks only at a few nearby pixels (the
*neighbourhood*). The rule is **surjective** if every image can be produced: for every image `y`
there is some image `x` that the rule turns into `y`.

Fukś and Skelton found an easy test that guarantees surjectivity ("slice permutivity", explained
below) and asked whether it is the *only* reason a five-pixel rule can be surjective:

> Is there a truly two-dimensional five-site binary rule which is surjective yet not slice permutive?

## Source

- H. Fukś, A. Skelton, *Classification of two-dimensional binary cellular automata with respect to
  surjectivity*, Proc. 2012 Int. Conf. on Scientific Computing (CSC-2012), CSREA Press, pp. 51–57.
  [arXiv:1208.0771](https://arxiv.org/abs/1208.0771).
- Location: §6 *Conclusions*, page 6 of the arXiv PDF.
- Original text: "A related question is whether there exist any truly two-dimensional five-site
  binary rule which is surjective yet not slice permutive? Since in one dimension such rules are
  possible even in four-site neighbourhoods, we suspect that the answer is affirmative, although
  currently we cannot offer any evidence of this claim."

## Answer

**Yes.** Below is an explicit rule on the L-pentomino neighbourhood. It depends on all five pixels
and is surjective. It is not permutive with respect to *any* site, so in particular it is not
slice permutive. The surjectivity proof is fully checked in Lean 4 with Mathlib.

## Why (for beginners)

### The transformation

Think of the picture as a grid of pixels `x(i, j)`, each black (1) or white (0); `i` counts columns
to the right and `j` counts rows upwards. The new colour of pixel `(i, j)` is computed from five old
pixels arranged in an **L shape**:

```
row j+1:   e
row j  :   a  b  c  d        a = x(i,j)    b = x(i+1,j)   c = x(i+2,j)
           ^                 d = x(i+3,j)  e = x(i,j+1)
           the new colour is written here
```

Every pixel is repainted at once with the same rule `f(a, b, c, d, e)`.

### The rule (example B)

First combine the two "corner" pixels: `s = a XOR e` (1 if exactly one of `a`, `e` is black).
Then look up the new colour `g(s, b, c, d)`:

| b c d | s = 0 | s = 1 |
|:-----:|:-----:|:-----:|
| 0 0 0 | 0 | 0 |
| 0 0 1 | 1 | 0 |
| 0 1 0 | 1 | 1 |
| 0 1 1 | 1 | 1 |
| 1 0 0 | 1 | 1 |
| 1 0 1 | 1 | 0 |
| 1 1 0 | 0 | 0 |
| 1 1 1 | 0 | 0 |

In words: if `s = 0`, the output is "`b` ? not `c` : (`c` or `d`)"; if `s = 1` it is
"`b` ? (not `c` and not `d`) : `c`". As one 32-bit truth table (input bit index
`a + 2b + 4c + 8d + 16e`) the rule is `0x3a3c353c`.

### What "slice permutive" means, and why this rule is not

- The rule is **permutive** in a pixel if flipping that pixel *always* flips the output, whatever the
  other four pixels are.
- A pixel of the neighbourhood is **sliceable** if a straight line through it has the other four
  pixels strictly on one side. For the L shape these are the three corners `a`, `d`, `e`; the middle
  pixels `b` and `c` are not (any line through `b` has `a` and `c` on opposite sides, or on it).
- **Slice permutive** = permutive in some sliceable pixel. Fukś and Skelton proved that this implies
  surjectivity: you can build a preimage by sweeping the line across the picture and choosing the
  sliced pixel each time so that the output comes out right.

Our rule is permutive in **no** pixel. For each pixel there is a situation in which flipping it
changes nothing:

| pixel | other four fixed as | output with pixel = 0 / 1 |
|---|---|---|
| a | b=c=d=e=0 | 0 / 0 |
| b | a=c=e=0, d=1 | 1 / 1 |
| c | a=b=e=0, d=1 | 1 / 1 |
| d | a=b=c=0, e=1 | 0 / 0 |
| e | a=b=c=d=0 | 0 / 0 |

It also really depends on each of the five pixels, so it is a genuine five-site rule.

### Why it is still surjective: rows instead of a single pixel

Output row `j` only reads input rows `j` and `j+1`, and from row `j+1` it reads just one pixel
(`e`). So we can build a preimage **from the top down**:

1. Choose the row above the picture arbitrarily.
2. Once row `j+1` is fixed, its pixels act as known "switches" `e_i` for row `j`. We need a row
   `r` with `f(r_i, r_{i+1}, r_{i+2}, r_{i+3}, e_i) = y_i` for every column `i` of the target.
3. Repeat downwards.

Step 2 always works for this rule. This is a question about a small automaton whose state is the
window `(r_i, r_{i+1}, r_{i+2})` (8 states): reading the next target pixel `y_i` together with the
switch `e_i`, the automaton chooses the next pixel `r_{i+3}`. Step 2 always works exactly when the
*set* of reachable windows can never become empty. That is a finite check (at most 256 sets). For
this rule the reachable sets always contain one of four "good" window sets:

- G0: `a = b`, G1: `a ≠ b`,
- G2: (`c = 0` and `a = b`) or (`c = 1` and `a = 1`), G3: the complement of G2,

(here `(a, b, c)` is the window), and each good set leads to another good set whatever `(e_i, y_i)`
is. So a solution row always exists, however long the row is.

This gives a preimage for every **finite** picture. An infinite picture is handled by a standard
compactness argument (König's lemma / Tychonoff): the preimages of larger and larger squares form a
decreasing chain of non-empty closed sets in the compact space of all images, so they have a
common point, which is a preimage of the whole infinite picture.

### A small example

Target (7×4, `#` = black, top row first) and a preimage (10×5) found by the construction above
(`demo_preimage.py`):

```
target            preimage
.#...#.           ..........
.......           #..###.##.
#.....#           ..........
.#####.           .#.......#
                  #..#.#.##.
```

Check of the bottom-left output pixel: `a = 1, b = 0, c = 0, d = 1` (bottom row of the preimage)
and `e = 0` (the pixel above `a`). So `s = 1`, and `g(1, 0, 0, 1) = c = 0`, which is white, as in
the target. The next pixel: `a = 0, b = 0, c = 1, d = 0, e = 1`, so `s = 1`, `g = c = 1` (black). ✓

## Proof

The Lean file `CASurjectivity.lean` proves:

- `answer`: there are a neighbourhood `N` (five distinct sites, contiguous, not collinear) and a
  rule `f` that depends on all five sites, whose global map on `ℤ × ℤ → Bool` is surjective, and
  that is not slice permutive.
- `F_surjective`: the global map of example B is surjective. Structure:
  `good_step` (automaton check by `decide`) → `row` (row lemma) → `rect` (every finite rectangle has
  a preimage) → compactness (`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`
  in the compact product space `ℤ × ℤ → Bool`).
- `dependsOn_all`, `not_permutive`, `not_slicePermutive`, `sliceable_iff` (the sliceable sites are
  exactly `a`, `d`, `e`, with the paper's definition: rational lines), `rule_truthTable`.

The definitions follow §2–3 of the paper: `F(x)_p = f(x_{p+u}, u ∈ N)`, and permutive in `v` means
`t ↦ f([t, b])` is injective for every `b`.

## Verification

- Lean 4.33.1 + Mathlib v4.33.1. No `sorry`, `admit`, `native_decide` or extra axioms;
  `#print axioms answer` = `[propext, Classical.choice, Quot.sound]`. Details: `VERIFY.md`.
- Independent C check `verify_l.c`: confirms the truth table, the dependence on all five sites, no
  permutive site, and the row criterion for example B. It also reproduces the paper's Table 1
  (582 one-dimensional 4-site surjective rules).

## Status

- **Second question of the paper: answered (yes), Lean-verified.** Not peer-reviewed. The example is
  elementary; the question appeared in a small conference paper and had no follow-up.
- **Prior work check (2026-10-04).** No answer found from 2012 to 2026:
  - Fukś's publication list (<https://lie.ac.brocku.ca/~hfuks/publications-1.html>) has no follow-up
    paper on 2D surjectivity or slice permutivity.
  - Semantic Scholar and OpenAlex list three citing works: *Response curves of deterministic and
    probabilistic cellular automata in one and two dimensions* (2012, on response curves, not
    surjectivity); a 2014
    Spanish thesis on encryption with reversible CA; and Hadeler–Müller, *Cellular Automata:
    Analysis and Applications* (Springer 2017), chapter "Surjectivity and Injectivity of Global
    Maps" (a textbook chapter; its full text was not accessible, and nothing indicates it
    answers the question).
  - Web searches for "slice permutive" and related phrases found only the original paper.
- **First question of the paper ("can the remaining 5-site rules be classified?") stays open.**
  For reference, our computation (`verify_l.c`) finds that exactly 1472 L-pentomino rules pass the
  row criterion, depend on all five sites and are not slice permutive. That equals the paper's
  count of unclassified L rules in Table 2. The survey's separate program (not included here) gives
  1472 for the Y pentomino as well, as expected since Y is equivalent to L under the lattice shear
  `(x, y) ↦ (x + y, y)`. If the paper's counts are right, every unclassified L and Y rule is
  surjective. The F, P, S, U and W shapes are not settled by this method. This part is a
  side result and is not formalised in Lean.
