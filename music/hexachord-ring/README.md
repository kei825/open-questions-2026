# Morris の 50 音のヘクサコード環

*日本語が先、英語は後半にあります。/ Japanese first; the English version follows below.*

## 問題

十二音技法の音楽理論では、オクターブの違いを忘れた音名を**音高クラス**と呼びます。
C = 0、C♯ = 1、D = 2、…、B = 11 とすると、音高クラスは 12 を法とする数です。相異なる 6 個の
音高クラスの集合を**ヘクサコード**（6 音音階）といいます。一方を**移調**（すべての音に同じ数 t を
足す、mod 12）するか、移調と**反転**（p ↦ −p + t）を組み合わせて他方になるとき、2 つの
ヘクサコードは同じ**セット・クラス**に属するとします。これがふつうの「TnI」による分類で、
ヘクサコードの**セット・クラスはちょうど 50 個**あります（Forte の 6-1〜6-50。Z 関係の対は別々に数える）。

**50 音の環**とは、音高クラスを輪に並べた列 x₀, x₁, …, x₄₉ です（同じ音が何度出てもよい）。
連続する 6 音の窓を 1 つずつずらして読むと（x₀…x₅、x₁…x₆、…、x₄₉x₀…x₄）、窓は 50 個できます。
環は窓に現れるセット・クラスを**インブリケート**（重ね合わせて提示）する、といいます。

**問い（Morris, 2007）。** 50 個の窓に、50 種のヘクサコードのセット・クラスがすべて
（したがって 1 回ずつ）現れる 50 音の環は存在するか。

## 出典

- R. Morris, "Mathematics and the Twelve-Tone System: Past, Present, and Future"、MCM 2007（ベルリン）の
  講演原稿 <https://ecmc.rochester.edu/rdm/pdflib/berlin.talk.reading.pdf> の **15 ページ**（確認済み）。
  *Perspectives of New Music* 45(2) (2007) 76–107 と MCM 2007 論文集（CCIS 37, Springer 2009）にも収録。
- 原文: *"Another open question is if there exist 50-pc rings that imbricate an instance of
  each of the 50 hexachordal set-classes?"*

## 答え

**存在しない。**

## なぜか（初学者向け）

音高クラス 1, 3, 5, 7, 9, 11（C♯, D♯, F, G, A, B）を「奇数の音」と呼びます。ヘクサコードに奇数の音が
いくつ入っているかを数え、その個数が偶数か奇数かだけに注目します。

| ヘクサコード | 音 | 奇数の音 | 個数 |
|---|---|---|---|
| 6-1（半音階） | 0 1 2 3 4 5 | 1 3 5 | 3 → **奇** |
| 同じものを 1 移調 | 1 2 3 4 5 6 | 1 3 5 | 3 → 奇 |
| 6-35（全音音階） | 0 2 4 6 8 10 | なし | 0 → **偶** |
| 同じものを 1 移調 | 1 3 5 7 9 11 | 6 個全部 | 6 → 偶 |

**段階 1 — 偶奇はセット・クラスの性質。** 偶数の移調では各音の偶奇が変わらないので、個数も
変わりません。奇数の移調では奇数の音と偶数の音が入れ替わるので、個数 j は 6 − j になります。
6 が偶数なので偶奇は同じです。反転 p ↦ −p は各音の偶奇を保ちます。したがって 50 個のセット・
クラスはそれぞれ「奇」か「偶」のどちらかに決まります。

**段階 2 — 50 クラスのうち奇はちょうど 25 個**（有限の数え上げ。計算機で数え、Lean でも確認）。
だから 50 クラスを全部含む環では、**奇の窓が 25 個**、つまり奇数個になります。

**段階 3 — ところが、どの環でも奇の窓は偶数個。** 50 個の窓それぞれについて奇数の音の個数を
数え、全部足します。環のどの位置もちょうど 6 個の窓に入るので、合計は 6 ×（環の中の奇数の音の個数）
で、偶数です。50 個の数の和が偶数になるのは、そのうち奇数であるものが偶数個のときだけです。
したがって奇の窓は偶数個です。

段階 2 と段階 3 が矛盾するので、そのような環はありません。∎

```
位置:     x0 x1 x2 x3 x4 x5 x6 x7 ...
窓 0:    [x0 x1 x2 x3 x4 x5]
窓 1:       [x1 x2 x3 x4 x5 x6]
窓 2:          [x2 x3 x4 x5 x6 x7]
...         どの位置もちょうど 6 個の窓に入る
```

この障害は 6 音の窓に特有です。3 音・4 音・5 音の窓では同じ型の環が存在します（クラス数は
12・29・38）。`check.py` が例を見つけて検算します。例えば 3 音の窓なら 12 音の環
`0 1 2 6 0 7 9 5 1 8 6 9` です。4 音の窓でも偶奇はクラスの不変量ですが、奇のクラスが偶数個（10 個）
なので矛盾が起きません。以前の計算機探索で 6 音の環が毎回「輪を閉じる所」で失敗していたのは、
この偶奇の議論で説明がつきます。

## 証明

W_i = {x_i, …, x_{i+5}}（添字は mod 50）、odd(S) = S に含まれる奇数の音高クラスの個数とします。

1. (a) |S| = 6 で T = s·S + t（s = ±1）なら odd(T) ≡ odd(S) (mod 2)（上で説明したとおり）。
2. (b) Z/12 の 6 元部分集合 924 個は TnI で 50 類に分かれ、そのうち 25 類で odd(S) が奇数。
3. (c) ∑_i odd(W_i) = 6·#{i : x_i が奇数} ≡ 0 (mod 2)。よって odd(W_i) が奇数になる i は偶数個。
4. 50 個の窓が 50 クラスをすべて含むなら、i ↦（W_i のクラス）は全単射で、(a)(b) より
   odd(W_i) が奇数になる i はちょうど 25 個。これは (c) に反する。

## 検証

Lean 4 のファイル `HexachordRing.lean`（名前空間 `OpenQuestions.HexachordRing`）、Mathlib v4.33.1。

- `no_hexachordal_ring`:
  ```lean
  ¬ ∃ x : Fin 50 → ZMod 12,
      (∀ i, (window x i).card = 6) ∧
      (∀ i j, i ≠ j → ¬ TnIEquiv (window x i) (window x j))
  ```
  `window x i` は位置 `i, i+1, …, i+5`（mod 50）の音の集合、
  `TnIEquiv S T := ∃ s t, (s = 1 ∨ s = -1) ∧ S.image (fun p => s * p + t) = T`。
- `no_ring_imbricating_all_classes`（Morris の文言どおり。窓が 6 音であることを仮定しない形）:
  `¬ ∃ x : Fin 50 → ZMod 12, ∀ S, S.card = 6 → ∃ i, TnIEquiv S (window x i)`。
- 補助の定理: `oddCount_parity_of_TnIEquiv`（(a)）、`exists_rep`・`classes_distinct`・`card_classes`
  （50 個の代表元はヘクサコードで、互いに同値でなく、どのヘクサコードもどれかと同値）、
  `card_odd_classes`（奇のクラスは 25 個）。
- 有限の事実は 12 ビットのマスク上の Bool 関数を `decide +kernel` で検査し、証明した補題で
  `Finset (ZMod 12)` の主張に移しています。`sorry`・`admit`・`native_decide`・新しい公理は使っていません。
- 上の各定理の `#print axioms` はすべて `[propext, Classical.choice, Quot.sound]`。
- 再現（約 1 分）:
  ```sh
  # from the repository root (after `lake exe cache get`)
  lake env lean --threads=2 -DautoImplicit=false -DrelaxedAutoImplicit=false \
    music/hexachord-ring/HexachordRing.lean
  ```
  詳細は `VERIFY.md`。Python だけの独立な検算は `python3 check.py`。

## 状況

- **解決（否定）。Lean 4 で検証済み**（2026-10-04）。
- 既出の確認（2026-10-04）: 答えは見つからなかった。OpenAlex では PNM 2007 年版を引用する文献が 14 件、
  2009 年の CCIS 版を引用する文献が 11 件あるが、2024〜2026 年のものはなく、環の問いを扱うものもない。
  Morris 本人の業績一覧（最新は 2024 年の Schoenberg 作品 23-3 の章）にも該当はない。原文の一文や
  「ヘクサコードの環」「imbrication」での Web 検索でも、Morris の原稿そのもの以外は出てこなかった
  （以前の調査でも補助 6 回・親 2 回の検索で解決の報告なし）。PNM 版と CCIS 版の本文は読んでおらず、
  文言は講演原稿によっている。
- 読み方についての注意: 「セット・クラス」は標準的な TnI の類と読んだ（これで Morris の数 50 になる。
  移調だけで分類すると 80 類になり、問いと合わない）。「環」なので列は巡回的で、最後の窓は先頭に回り込む。
  同じ原稿にある別の問い（all-partition array、all-interval かつ all-trichordal な音列が無いことの
  概念的な理由）はここでは扱っていない。

---

# Morris's 50-note hexachordal ring


## Problem

In twelve-tone music theory a **pitch class** is a note name with the octave forgotten:
C = 0, C♯ = 1, D = 2, …, B = 11, so pitch classes are the numbers mod 12. A **hexachord**
is a set of six different pitch classes. Two hexachords belong to the same **set-class**
if one can be turned into the other by a **transposition** (add the same number t to every
note, mod 12) or a transposition combined with **inversion** (p ↦ −p + t). This is the
usual "TnI" classification; there are exactly **50 hexachordal set-classes** (Forte's
6-1 … 6-50, the Z-related pairs counted separately).

A **50-pc ring** is a cyclic sequence x₀, x₁, …, x₄₉ of pitch classes (repetitions are
allowed). Reading it through a window of six consecutive notes, sliding by one step
(x₀…x₅, x₁…x₆, …, x₄₉x₀…x₄), gives 50 windows. The ring **imbricates** the set-classes
it shows in its windows.

**Question (Morris, 2007).** Is there a 50-pc ring whose 50 windows show every one of the
50 hexachordal set-classes (necessarily each exactly once)?

## Source

- R. Morris, "Mathematics and the Twelve-Tone System: Past, Present, and Future", talk at
  MCM 2007 (Berlin), reading text:
  <https://ecmc.rochester.edu/rdm/pdflib/berlin.talk.reading.pdf>, **page 15** (checked).
  Also printed in *Perspectives of New Music* 45(2) (2007) 76–107 and in the MCM 2007
  proceedings (CCIS 37, Springer 2009).
- Quote: *"Another open question is if there exist 50-pc rings that imbricate an instance of
  each of the 50 hexachordal set-classes?"*

## Answer

**No. Such a ring does not exist.**

## Why (for beginners)

Call the pitch classes 1, 3, 5, 7, 9, 11 (C♯, D♯, F, G, A, B) the *odd* notes. For a hexachord,
count how many odd notes it contains, and look only at whether that count is even or odd.

| hexachord | notes | odd notes | count |
|---|---|---|---|
| 6-1 (chromatic) | 0 1 2 3 4 5 | 1 3 5 | 3 → **odd** |
| same, transposed by 1 | 1 2 3 4 5 6 | 1 3 5 | 3 → odd |
| 6-35 (whole-tone) | 0 2 4 6 8 10 | — | 0 → **even** |
| same, transposed by 1 | 1 3 5 7 9 11 | all six | 6 → even |

**Step 1 – the parity is a property of the set-class.** Transposing by an even number keeps
every note's parity, so the count does not change. Transposing by an odd number swaps odd
and even notes, so a count j becomes 6 − j, which has the same parity because 6 is even.
Inversion p ↦ −p keeps every note's parity. So each of the 50 set-classes is either
"odd" or "even".

**Step 2 – exactly 25 of the 50 classes are odd** (a finite count, done by computer and
checked in Lean). So a ring containing all 50 classes would have **25 odd windows** — an
odd number.

**Step 3 – but every ring has an even number of odd windows.** Add up, over all 50
windows, the number of odd notes in the window. Every position of the ring lies in exactly
6 windows, so the total is 6 × (number of odd notes in the ring), an even number. A sum of
50 numbers is even only if an even number of them are odd. So the number of odd windows is
even.

Steps 2 and 3 contradict each other, so no such ring exists. ∎

```
position:   x0 x1 x2 x3 x4 x5 x6 x7 ...
window 0:  [x0 x1 x2 x3 x4 x5]
window 1:     [x1 x2 x3 x4 x5 x6]
window 2:        [x2 x3 x4 x5 x6 x7]
...           each position is covered by exactly 6 windows
```

The obstruction is special to six-note windows. For windows of 3, 4 and 5 notes the
analogous rings exist (12, 29 and 38 classes); `check.py` finds and checks examples, e.g.
for 3-note windows the 12-note ring `0 1 2 6 0 7 9 5 1 8 6 9`. With 4-note windows
the parity is again a class invariant, but the number of odd classes is even (10), so there
is no contradiction. An earlier computer search for the 6-note ring always failed when
closing the ring, which the parity argument explains.

## Proof

Write W_i = {x_i, …, x_{i+5}} (indices mod 50) and odd(S) = number of odd pitch classes in S.

1. (a) If T = s·S + t with s = ±1 and |S| = 6, then odd(T) ≡ odd(S) (mod 2), as explained above.
2. (b) The 924 six-element subsets of Z/12 split into 50 TnI classes; on 25 of them odd(S) is odd.
3. (c) ∑_i odd(W_i) = 6·#{i : x_i odd} ≡ 0 (mod 2), so #{i : odd(W_i) odd} is even.
4. If the 50 windows met all 50 classes, the map i ↦ class(W_i) would be a bijection, and by
   (a) and (b), #{i : odd(W_i) odd} = 25, contradicting (c).

## Verification

Lean 4 file `HexachordRing.lean` (namespace `OpenQuestions.HexachordRing`), Mathlib v4.33.1.

- `no_hexachordal_ring`:
  ```lean
  ¬ ∃ x : Fin 50 → ZMod 12,
      (∀ i, (window x i).card = 6) ∧
      (∀ i j, i ≠ j → ¬ TnIEquiv (window x i) (window x j))
  ```
  where `window x i` is the image of the six positions `i, i+1, …, i+5` (mod 50) and
  `TnIEquiv S T := ∃ s t, (s = 1 ∨ s = -1) ∧ S.image (fun p => s * p + t) = T`.
- `no_ring_imbricating_all_classes` (Morris's wording, without assuming the windows are
  hexachords): `¬ ∃ x : Fin 50 → ZMod 12, ∀ S, S.card = 6 → ∃ i, TnIEquiv S (window x i)`.
- Supporting theorems: `oddCount_parity_of_TnIEquiv` (a); `exists_rep`, `classes_distinct`,
  `card_classes` (the 50 representatives are hexachords, pairwise inequivalent, and every
  hexachord is equivalent to one of them); `card_odd_classes` (25 odd classes).
- The finite facts are checked by `decide +kernel` on boolean functions of 12-bit masks,
  and transported to `Finset (ZMod 12)` by proved lemmas. No `sorry`, `admit`,
  `native_decide` or new axioms.
- `#print axioms` for every theorem above: `[propext, Classical.choice, Quot.sound]`.
- Reproduce (about 1 minute):
  ```sh
  # from the repository root (after `lake exe cache get`)
  lake env lean --threads=2 -DautoImplicit=false -DrelaxedAutoImplicit=false \
    music/hexachord-ring/HexachordRing.lean
  ```
  Details in `VERIFY.md`. Independent check in plain Python: `python3 check.py`.

## Status

- **Solved (negative answer), verified in Lean 4** (2026-10-04).
- Literature check (2026-10-04): no answer found. OpenAlex lists 14 works citing the PNM
  2007 article and 11 citing the 2009 CCIS version; none is from 2024–2026 and none
  addresses the ring question. Morris's own publication list (latest item 2024, a chapter on
  Schoenberg's Op. 23 No. 3) has nothing on it. Web searches for the quoted sentence and
  for hexachordal rings and imbrication found only Morris's text itself. (Earlier survey
  searches, 6 by a helper and 2 by the parent, also found no solution.) The PNM and CCIS
  printed versions were not read; the wording is taken from the reading text.
- Notes on the reading: "set-class" is taken as the standard TnI class (this gives
  Morris's number 50; under transposition only there would be 80 classes, and the question
  would not match). The ring is cyclic (the last windows wrap around), as "ring" means.
  The same text also asks other questions (all-partition arrays; a conceptual reason why
  no all-interval row is all-trichordal); those are not addressed here.
