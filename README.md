# 7つの未解決の問いへの回答（2026 年）

*日本語が先、英語は後半にあります。/ Japanese first; the English version follows below.*

論文・講演・サーベイの中で出され、2026-10-04 に調べた限りまだ答えが出ていなかった小さな問いに、7つ答えを出しました。
どれも、出された問いそのものに回答しています。

各フォルダの README に、出典（ページと原文）、初学者向けの解説、証明、検証の再現手順を書いています。

## 一覧

| 分野 | 問い | 答え | 検証 |
|---|---|---|---|
| 宇宙 | 2 つの軌道の距離の極値は最大 10 個か | いいえ、12 個 | ✅ Lean |
| 宇宙 | X 線望遠鏡のマスク用の差集合はあるか | 無い | 🔷 SAT |
| 音楽 | 50 音の環で 6 音和音の型を 1 回ずつ通れるか | 通れない | ✅ Lean |
| 音楽 | 均等な音階のエネルギー: 局所最小は最小か | いいえ | ✅ Lean |
| 画像 | 既知の条件に当てはまらない全射な規則はあるか | ある | ✅ Lean |
| 計算機科学 | Ramsey 数 R(C₄, K₁,₃₉) は 46 か 47 か | 46 | 🔷 SAT |
| 生物 | 系統樹の指数を健全にする重みはあるか | 無い | ✅ Lean |

**検証の印**

- ✅ **Lean**: 答えを Lean 4（Mathlib v4.33.1）の定理として証明した。`sorry`・`native_decide`・追加の公理は使っていない。使った公理は `propext`・`Classical.choice`・`Quot.sound` だけ。
- 🔷 **SAT**: 手で書いた証明で有限の SAT 問題に帰着し、解が無いことの証明書を、形式検証済みの検査器 [cake_lpr](https://github.com/tanyongkiam/cake_lpr) が受理した。残る信頼の根は各フォルダに書いた。

---

## 宇宙

### 1. 2 つの軌道の距離の極値は 12 個になりうる

- **問い**:
  - 同じ平面にあって焦点を共有する 2 つの楕円（同じ太陽を回る 2 つの軌道）を考える。
  - それぞれの軌道上に 1 点ずつ取り、その距離の 2 乗が極小・極大・鞍点になる点の組は何個ありうるか。
  - 論文は「多くて 12 個」を証明したうえで、「実際の最大は 10 個」と予想した。
- **答え**:
  - 予想は偽。12 個になる軌道の組を具体的に示した（交点 2、極小 2、極大 2、鞍点 6）。
  - 論文の上限と合わせて、最大はちょうど 12 個。
  - 小惑星の衝突リスクの指標（MOID）の計算に関わる問題。
- **検証**: ✅ Lean（定理 `twelve_critical_points`）。加えて、独立した 2 つの厳密計算でも「ちょうど 12 個」。
- **出典**: Gronchi・Baù・Grassi, Celest. Mech. Dyn. Astron. 135:48 (2023), [arXiv:2305.13900](https://arxiv.org/abs/2305.13900)（§7、20 ページ）
- **フォルダ**: [space/keplerian-distance](space/keplerian-distance)

### 2. X 線望遠鏡のマスクに使う (243,121,60) 差集合は Z₃×Z₉×Z₉ に無い

- **問い**:
  - 差集合は、X 線・ガンマ線望遠鏡の「符号化開口マスク」（穴の模様）の土台になる。
  - 群 Z₃×Z₉×Z₉ に (243,121,60) 差集合はあるか。Gordon の一覧の「最小の未解決ケース」。
- **答え**: 無い。
- **検証**: 🔷 SAT。対称性を何も仮定しない SAT 問題が「解なし」で、その証明書を cake_lpr が受理した。
- **出典**:
  - D. M. Gordon の講演スライド（2019）の [38 枚目](https://cargo.wlu.ca/ArasuFest/ArasuFest_talks/Dan_Gordon.pdf)
  - [La Jolla 差集合リポジトリ](https://dmgordon.org/difference-sets/)
- **フォルダ**: [space/difference-set-243](space/difference-set-243)

---

## 音楽

### 3. 50 音の環で、6 音和音の 50 の型を 1 回ずつ通ることはできない

- **問い**: 50 個の音を輪に並べ、6 音ずつずらしながら読む。50 種類ある 6 音和音の型（セット・クラス）を、ちょうど 1 回ずつ通れるか。
- **答え**:
  - 通れない。偶数・奇数を数えるだけで示せる。
  - 50 の型のうち「奇数の音を奇数個含む型」は 25 個ある。ところが、どんな輪でも、そういう窓は偶数個しか現れない。
- **検証**: ✅ Lean（定理 `no_hexachordal_ring`）
- **出典**: R. Morris, [MCM 2007 の講演原稿](https://ecmc.rochester.edu/rdm/pdflib/berlin.talk.reading.pdf)（15 ページ。Perspectives of New Music 45(2), 2007 にも掲載）
- **フォルダ**: [music/hexachord-ring](music/hexachord-ring)

### 4. 均等な音階のエネルギーで、局所最小が最小とは限らない

- **問い**:
  - 全音階のような「最大偶数集合」は、あるエネルギーを最小にする配置として特徴づけられる。
  - 1 音ずつ動かしてエネルギーが下がらなくなった配置（局所最小）は、必ず本当の最小か。
  - 局所探索は必ず最小に着くか。
- **答え**:
  - どちらも「いいえ」。円環 C₃₂ と路 P₁₃ に反例がある。
  - x ≥ 8 の C₄ₓ には、無限に続く反例の族もある。
- **検証**: ✅ Lean（定理 `cycle32_counterexample`・`path13_counterexample`・`cycle_family_counterexample`・`dls_of_isLocalMin`）
- **出典**: Bushaw・Cody・Leffler, Discrete Math. 348 (2025) 114466, [arXiv:2407.18785](https://arxiv.org/abs/2407.18785)（問 5.3）
- **フォルダ**: [music/maximally-even-energy](music/maximally-even-energy)

---

## 画像

### 5. 「切り出せない」のに、どんな画像も作れる 5 画素の規則がある

- **問い**:
  - 白黒画像の各画素を、近くの 5 画素から同じ規則で一斉に塗り替える。
  - 「どんな画像も作れる」（全射）のに、既知の十分条件「スライス置換的」を満たさない規則はあるか。
- **答え**: ある。L 形の 5 画素で、全射なのに、どの画素についても置換的でない規則を具体的に示した。
- **検証**: ✅ Lean（定理 `answer`・`F_surjective`）
- **出典**: Fukś・Skelton, CSC-2012, [arXiv:1208.0771](https://arxiv.org/abs/1208.0771)（§6）
- **フォルダ**: [images/cellular-automata-surjectivity](images/cellular-automata-surjectivity)

---

## 計算機科学

### 6. Ramsey 数 R(C₄, K₁,₃₉) は 46

- **問い**: R(C₄, K₁,₃₉) は 46 か 47 か。2026 年版の表で、n ≤ 41 の範囲に残る唯一の未決の欄。
- **答え**: 46。46 頂点で、四角形（C₄）を含まず、どの頂点からも 7 本以上の辺が出るグラフは無い。
- **検証**:
  - 🔷 SAT。独立に書いた 2 つの符号化で、どちらも解なし。証明書は cake_lpr が受理した。
  - 数え上げによる帰着の一部は Lean で証明した。
  - 1 つの場合分けは、手で証明した対称性の制約に頼っている。
- **出典**: S. Radziszowski, [Small Ramsey Numbers, DS1 改訂 18 版（2026）](https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1)（表 IVa）
- **フォルダ**: [computer-science/ramsey-c4-star](computer-science/ramsey-c4-star)

---

## 生物

### 7. 自然数の重みでは、系統樹の Colless 型指数は「健全」にならない

- **問い**:
  - 系統樹の偏りを測る Colless 型指数は、重み f の選び方で中身が変わる。
  - f : ℕ → ℕ をうまく選べば「健全」（指数が 0 ⇔ 完全に対称な木）にできるか。
  - 著者らは「できない」と予想した。
- **答え**: 予想は正しい。そういう f は無い。有理数値の f まで広げても無い。
- **検証**: ✅ Lean（定理 `mir_rossello_rotger_conjecture`・`not_sound_rat`）
- **出典**: Mir・Rosselló・Rotger, PLoS ONE 13 (2018) e0203401, [arXiv:1805.01329](https://arxiv.org/abs/1805.01329)
- **フォルダ**: [biology/colless-like-index](biology/colless-like-index)

---

## Lean の検証の再現

```sh
lake exe cache get        # Mathlib のビルド済みキャッシュを取得（Lean v4.33.1、Mathlib v4.33.1）
scripts/check_lean.sh     # すべての .lean をコンパイルし、使った公理を表示
```

SAT などの計算による検証を含め、正確なコマンド・出力・所要時間は各フォルダの `VERIFY.md` にあります。

## 注意

- どの答えも査読は受けていません。多くは、1 本の論文や講演の中で出された小さな問いです。
- 「未解決」は、2026-10-04 に調べた範囲（被引用、著者のその後の論文、Web と arXiv の検索）で答えが見つからなかったという意味です。
- 作成: 馬場 啓太（[kei825](https://github.com/kei825)）。AI（Anthropic の Claude）の支援を受けています。

## ライセンス

Apache License 2.0（`LICENSE` を参照）

---
---

# Answers to seven open questions (2026)

We answer seven small open questions. Each was posed in a paper, a talk or a survey, and as far as we could
find it was still unanswered on 2026-10-04. Each answer responds to the question exactly as it was asked.

Each folder's README gives the source (page and quotation), an explanation for beginners, the proof and the
steps to reproduce the check.

## Summary

| Field | Question | Answer | Check |
|---|---|---|---|
| Space | At most 10 critical distances between two orbits? | No, 12 | ✅ Lean |
| Space | A difference set for an X-ray telescope mask? | None | 🔷 SAT |
| Music | A 50-note ring through all hexachord classes? | No | ✅ Lean |
| Music | Energy of even scales: local min = global min? | No | ✅ Lean |
| Images | A surjective rule outside the known criterion? | Yes | ✅ Lean |
| Computer science | R(C₄, K₁,₃₉) = 46 or 47? | 46 | 🔷 SAT |
| Biology | A weight making the tree index sound? | None | ✅ Lean |

**How each answer was checked**

- ✅ **Lean**: the answer is a theorem proved in Lean 4 with Mathlib v4.33.1. No `sorry`, no `native_decide`, no extra axioms. The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.
- 🔷 **SAT**: a written proof reduces the question to a finite SAT problem. The solver's certificate that no solution exists is accepted by the formally verified checker [cake_lpr](https://github.com/tanyongkiam/cake_lpr). What remains to be trusted is listed in that folder.

---

## Space

### 1. Two coplanar orbits can have 12 critical distances

- **Question**:
  - Take two ellipses in one plane that share a focus, like two orbits around the same Sun.
  - Pick one point on each orbit. How many critical points (minima, maxima, saddles) can the squared distance between them have?
  - The authors proved "at most 12" and conjectured that the true maximum is 10.
- **Answer**:
  - The conjecture is false. An explicit pair of orbits has 12 critical points: 2 intersections, 2 minima, 2 maxima and 6 saddles.
  - With the paper's bound, the maximum is exactly 12.
  - The question comes from computing the MOID, a measure of asteroid collision risk.
- **Check**: ✅ Lean (`twelve_critical_points`). Two independent exact computations also find exactly 12.
- **Source**: Gronchi, Baù, Grassi, Celest. Mech. Dyn. Astron. 135:48 (2023), [arXiv:2305.13900](https://arxiv.org/abs/2305.13900) (§7, p. 20)
- **Folder**: [space/keplerian-distance](space/keplerian-distance)

### 2. No (243,121,60) difference set in Z₃×Z₉×Z₉

- **Question**:
  - Difference sets are the basis of coded-aperture masks (patterns of holes) in X-ray and gamma-ray telescopes.
  - Does Z₃×Z₉×Z₉ contain a (243,121,60) difference set? This is the "smallest open case" in Gordon's list.
- **Answer**: No.
- **Check**: 🔷 SAT. A SAT instance that assumes no symmetry has no solution, and cake_lpr accepts its certificate.
- **Source**:
  - D. M. Gordon, talk slides (2019), [slide 38](https://cargo.wlu.ca/ArasuFest/ArasuFest_talks/Dan_Gordon.pdf)
  - [La Jolla Difference Set Repository](https://dmgordon.org/difference-sets/)
- **Folder**: [space/difference-set-243](space/difference-set-243)

---

## Music

### 3. No 50-note ring passes through all 50 hexachord classes once

- **Question**: Put 50 notes on a ring and read 6 consecutive notes at a time. Can the 50 windows contain each of the 50 hexachord set-classes exactly once?
- **Answer**:
  - No. Counting even and odd notes is enough.
  - Of the 50 classes, 25 contain an odd number of odd pitch classes. On any ring, the number of such windows is even.
- **Check**: ✅ Lean (`no_hexachordal_ring`)
- **Source**: R. Morris, [MCM 2007 talk](https://ecmc.rochester.edu/rdm/pdflib/berlin.talk.reading.pdf) (p. 15; also in Perspectives of New Music 45(2), 2007)
- **Folder**: [music/hexachord-ring](music/hexachord-ring)

### 4. For the energy of even scales, a local minimizer need not be a minimizer

- **Question**:
  - Maximally even sets, such as the diatonic scale, are the minimizers of a certain energy.
  - Suppose no single note can be moved to lower the energy (a local minimizer). Must it be a true minimizer?
  - Does descending local search always reach one?
- **Answer**:
  - No, to both. There are counterexamples on the cycle C₃₂ and the path P₁₃.
  - There is also an infinite family of counterexamples on C₄ₓ for x ≥ 8.
- **Check**: ✅ Lean (`cycle32_counterexample`, `path13_counterexample`, `cycle_family_counterexample`, `dls_of_isLocalMin`)
- **Source**: Bushaw, Cody, Leffler, Discrete Math. 348 (2025) 114466, [arXiv:2407.18785](https://arxiv.org/abs/2407.18785) (Question 5.3)
- **Folder**: [music/maximally-even-energy](music/maximally-even-energy)

---

## Images

### 5. A surjective 5-pixel rule that is not slice permutive

- **Question**:
  - Recolour every pixel of a black-and-white image from 5 nearby pixels by one fixed rule.
  - Is there a rule that can produce every image (surjective) but is not "slice permutive", the known sufficient condition?
- **Answer**: Yes. An explicit rule on the L-pentomino is surjective but is permutive in no pixel at all.
- **Check**: ✅ Lean (`answer`, `F_surjective`)
- **Source**: Fukś, Skelton, CSC-2012, [arXiv:1208.0771](https://arxiv.org/abs/1208.0771) (§6)
- **Folder**: [images/cellular-automata-surjectivity](images/cellular-automata-surjectivity)

---

## Computer science

### 6. The Ramsey number R(C₄, K₁,₃₉) is 46

- **Question**: Is R(C₄, K₁,₃₉) equal to 46 or 47? In the 2026 survey table, this is the only undecided entry with n ≤ 41.
- **Answer**: 46. No graph on 46 vertices has no 4-cycle and minimum degree at least 7.
- **Check**:
  - 🔷 SAT. Two independently written encodings both have no solution, and cake_lpr accepts the certificates.
  - Part of the counting reduction is proved in Lean.
  - One case relies on a symmetry-breaking argument that is proved by hand.
- **Source**: S. Radziszowski, [Small Ramsey Numbers, DS1 rev. 18 (2026)](https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1) (Table IVa)
- **Folder**: [computer-science/ramsey-c4-star](computer-science/ramsey-c4-star)

---

## Biology

### 7. No natural-number weight makes the Colless-like tree index sound

- **Question**:
  - The Colless-like index measures how lopsided a phylogenetic tree is, and it depends on a weight f.
  - Can f : ℕ → ℕ be chosen so that the index is "sound", that is, 0 exactly for fully symmetric trees?
  - The authors conjectured that it cannot.
- **Answer**: The conjecture is true. No such f exists, even if f takes rational values.
- **Check**: ✅ Lean (`mir_rossello_rotger_conjecture`, `not_sound_rat`)
- **Source**: Mir, Rosselló, Rotger, PLoS ONE 13 (2018) e0203401, [arXiv:1805.01329](https://arxiv.org/abs/1805.01329)
- **Folder**: [biology/colless-like-index](biology/colless-like-index)

---

## Reproducing the Lean checks

```sh
lake exe cache get        # download the Mathlib build cache (Lean v4.33.1, Mathlib v4.33.1)
scripts/check_lean.sh     # compiles every .lean file and prints the axioms used
```

Each folder's `VERIFY.md` lists the exact commands, outputs and timings, including the SAT and other computer checks.

## Caveats

- None of these answers has been peer-reviewed. Most of the questions are modest ones from a single paper or talk.
- "Open" means that we found no published answer when we searched on 2026-10-04 (citations, the authors' later papers, web and arXiv searches).
- Written by Keita Baba ([kei825](https://github.com/kei825)) with AI assistance (Anthropic's Claude).

## License

Apache License 2.0 (see `LICENSE`)
