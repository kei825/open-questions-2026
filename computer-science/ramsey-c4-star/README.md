# R(C4, K_{1,39}) = 46

*日本語が先、英語は後半にあります。/ Japanese first; the English version follows below.*

## Problem（問題）

Ramsey 数 `R(C4, K_{1,39})` を決める。これは「完全グラフ `K_N` の辺をどう赤と青に塗っても、
赤い 4 閉路 `C4` か、青い星 `K_{1,39}`（中心 1 点と葉 39 点）が必ず現れる」ような最小の `N`。

言い換えると、**46 頂点のグラフで、4 閉路を含まず、どの頂点も 7 本以上の辺を持つものはあるか。**
答えが「ない」ことと `R(C4, K_{1,39}) = 46` が同値。

## Source（出典）

S. Radziszowski, *Small Ramsey Numbers*, Electronic Journal of Combinatorics, Dynamic Survey DS1,
改訂 #18（2026-04-24）、<https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1>。
PDF の 21 ページ目の Table IVa（`R(C4, K_{1,n})`、`n <= 41`）で、`n = 39` の欄は **46–47**
（文献 WuSR / DyDz2）。`n <= 41` で値が決まっていない唯一の欄。
L. Boza, arXiv:2409.12770 v2（2026-06-12）は `n <= 38` の未決の値を決めたが、`n = 39` は 46/47 のまま。

## Answer（答え）

**`R(C4, K_{1,39}) = 46`。** 46 頂点で C4 を含まず最小次数 7 以上のグラフは存在しない。
（文献（Boza の論文など）によれば `R(C4, K_{1,n})` は `C4` 対車輪の Ramsey 数と一致するので、
対応する車輪の欄（40 頂点の車輪で `R(C4, W_40)` と書かれるもの）も決まる。この関係と車輪の
番号の付け方はここでは確かめ直していない。）

## Why（なぜ／初学者向け）

**Ramsey 数。** パーティーの客の 2 人ずつを「知り合い」か「他人」に分ける。人数が十分多いと、
ある形が必ず現れる。たとえば 6 人いれば、互いに知り合いの 3 人か、互いに他人の 3 人が必ずいる
（`R(K3, K3) = 6`）。`R(F, H)` は、「知り合い」の `F` か「他人」の `H` を必ず生む最小の人数。

**C4 と星。** `C4` は四角形で、`a–b`、`b–c`、`c–d`、`d–a` が知り合いの 4 人。言い換えると
「共通の知り合いが **2 人** いる 2 人」。`K_{1,39}` は星で、39 人と他人である 1 人。

**なぜ「46 頂点・最小次数 7」になるか。** 客が 46 人なら、「他人の星」`K_{1,39}` があるとは、
知り合いが `45 - 39 = 6` 人以下の人がいるということ。だから両方の形を避ける 46 人のパーティーは、
「どの 2 人も共通の知り合いが 2 人以上はいない」「全員が 7 人以上と知り合い」という 46 頂点の
グラフそのもの。45 人なら両方を避けられることは知られている（だから 46 以上）。
ここでは 46 人では不可能なことを示す（だからちょうど 46）。

**もっともらしいが難しい理由。** 自分に 7 人の知り合いがいて、その各人に、仲間内の誰とも共有
しない知り合いがさらに 6 人ずついる（共有すると四角形ができる）と、それだけで
`1 + 7 + 7·6 = 50` 人が必要になり、46 人を超える。余裕は三角形（自分の知り合い同士が知り合い）
からしか生まれず、三角形を十分に詰め込めるかが問題になる。この最後の部分は有限だが巨大な探索
なので、SAT ソルバに任せ、その答えを形式検証済みの証明検査器で確かめる。

## Proof（証明）

**段階 1（数え上げ。手の証明と Lean）。** `G` を 46 頂点、`C4` なし、最小次数 7 以上とし、
次数 `d` の頂点 `v` をとる。

* `N(v)` の中では各頂点の隣接点は高々 1 個（2 個あると `v` を通る四角形ができる）。よって
  `N(v)` 内の辺はマッチングで、本数 `m(v) <= ⌊d/2⌋`。
* `v` の異なる隣接点 `u, u'` の、`{v} ∪ N(v)` の外にある隣接点は共通しない（共通の `w` があると
  四角形 `u–w–u'–v`）。これを `u` の**専用の 2 次近傍** `P(u)` と呼ぶ。
* 数えると `46 >= 1 + d + Σ_u |P(u)| >= 1 + 7d - 2m(v)`。

`d >= 8` なら右辺は 49 以上なので、**`G` は 7 正則**。`d = 7` から `m(v) ∈ {2, 3}`。
ここで番号を付け直す: `v = 0`、近傍を `1..7`（マッチングは `(1,2), (3,4)`、`m = 3` なら
`(5,6)` も）、`1, 2, …, 7` の専用の 2 次近傍を 8 から連番の塊（相手のいる近傍は 5 個、
いない近傍は 6 個）、残りの頂点（`m = 3` なら 2 個、`m = 2` なら 0 個）を最後に。
この付け替えの後では、`0..7` に接する辺はすべて決まっている。

**段階 2（SAT）。** `m = 2` と `m = 3` のそれぞれについて、1035 本のありうる辺を変数とする
命題論理式（CNF）を作る。内容は「`C4` なし」（四角形の候補ごとに 1 節）、「全頂点の次数 7 以上」、
「`0..7` の辺は段階 1 のとおり」。どちらも充足不能。

* `m = 2` は対称性の制約を**まったく入れなくても**約 1 秒で解ける。よって反例があるとしたら
  全頂点で `m(v) = 3`。
* `m = 3` には対称性の制約を入れる: 同じ塊の中の頂点は入れ替え可能なので、隣接行列の行が
  辞書式に並んでいることを要求してよい。どんなグラフも入れ替えでこれを満たせる（辞書式最小の
  並べ替えをとればよい）ので解は失われない。証明は `VERIFY.md` §3。これでソルバは約 1 分。

詳細は `VERIFY.md` §2〜§4。

## Verification（検証）

* CNF の生成器は 2 系統: この検証のために白紙から書いたもの（`independent/`）と、調査担当の
  もの（`original/`）。どちらの組も UNSAT。
* 主な 5 本の実行（`VERIFY.md` §5）の UNSAT にはすべて証明を付けた: CaDiCaL 3.0.1 → DRAT → `drat-trim`（VERIFIED）→ LRAT →
  **`cake_lpr`**（CakeML で形式検証された証明検査器、`s VERIFIED UNSAT`）。
  証明ファイル（最大 0.5 GB）はリポジトリに入れていない。バイト単位で再現でき、sha256 は
  `VERIFY.md` の §5 と §9 にある。
* 補助の確認: 部品（カウンタ・辞書式・三角形）の総当たりテスト、小さいパラメータ（最小次数
  4, 5, 6）で構造を固定した式と素の式の答えが一致することの確認、別のソルバ（CaDiCaL 2.1.2、
  Kissat 4.0.4）。
* `lean/C4StarReduction.lean`: 段階 1（7 正則、マッチングの性質、`m(v) ∈ {2,3}`）の Lean 4 +
  Mathlib による証明。`sorry`・`native_decide`・追加の公理なし。

このフォルダの中身:

| パス | 内容 |
|---|---|
| `VERIFY.md` | 証明の全文、全実行、sha256、再現手順、信頼の根 |
| `check_cnf.sh` | 1 つの CNF について 解く → DRAT → drat-trim → LRAT → cake_lpr |
| `independent/gen_c4_46.py` | この検証のために書いた CNF 生成器（オプションは冒頭の説明） |
| `independent/test_encodings.py` | カウンタ・辞書式・三角形の部品の総当たりテスト |
| `independent/validate_small.py` | 最小次数 4, 5, 6 で構造つきの式と素の式を照合 |
| `original/c4_struct_gen.py`, `original/add_lex.py` | 調査担当の生成器（そのまま） |
| `lean/C4StarReduction.lean` | 数え上げの段階の Lean 4 証明 |
| `logs/` | 証明書つき実行と照合のログ |

再現（1 コアで約 8 分。全部の手順は `VERIFY.md` §8）:

```sh
python3 independent/gen_c4_46.py --m 2 --lex none > m2.cnf
python3 independent/gen_c4_46.py --m 3            > m3.cnf
CADICAL=cadical DRAT_TRIM=drat-trim CAKE_LPR=cake_lpr ./check_cnf.sh m2.cnf /tmp
CADICAL=cadical DRAT_TRIM=drat-trim CAKE_LPR=cake_lpr ./check_cnf.sh m3.cnf /tmp
```

## Status（状況）

**解決済み（機械検査済みの証明書つき）。ただし査読・公表はまだ。** 2026-10-04 に確認:

* 段階 1（帰着）: 手の証明（`VERIFY.md` §2）。数え上げの中核は Lean 4 で証明済み。
* 段階 2（SAT）: 独立に書いた 2 つの生成器のどちらでも両方の場合が UNSAT。主な実行の UNSAT は
  すべて `drat-trim` のあと形式検証済みの `cake_lpr` で検査済み。
* `m = 2` の場合は対称性の制約なしで閉じる。

残る信頼の根:

1. **`m = 3` の対称性の制約。** 健全性は短い標準的な議論（`VERIFY.md` §3）だが、機械検査は
   していない。制約なし（またはかなり弱めた版）の `m = 3` は数 CPU 時間では決着しなかった
   （`VERIFY.md` §5）。
2. **「CNF が意図どおりの内容か」。** 固定した配置への番号の付け替えと節の意味は手の議論で、
   形式化していない。独立な 2 つの生成器、部品の総当たりテスト、小さい場合の照合（決着した
   場合はすべて既知の極値 `ex(n; C4)` と整合）で補っている。
3. `cake_lpr` そのもの（HOL4/CakeML で検証済み。同梱のアセンブリを gcc でビルドした）。
4. 文献（DS1）にある下界 46。

既出確認（2026-10-04）: DS1 改訂 #18（2026-04-24、現在も最新）、Boza arXiv:2409.12770 v2
（2026-06-12、`n = 39` は 46/47 のまま）、Wesley arXiv:2509.03784（この欄には届いていない）、
2026 年の arXiv の `C4`–星・`C4`–車輪の Ramsey 数の論文を検索し、`R(C4, K_{1,39})` や
`R(C4, W_40)` を決めたものは見つからなかった。

---

# R(C4, K_{1,39}) = 46


## Problem

Determine the Ramsey number `R(C4, K_{1,39})`: the smallest `N` such that however the edges
of the complete graph `K_N` are coloured red and blue, there is a red 4-cycle `C4` or a blue
star `K_{1,39}` (one centre joined to 39 leaves).

Equivalently: **is there a graph on 46 vertices with no 4-cycle in which every vertex has at
least 7 neighbours?** `R(C4, K_{1,39}) = 46` exactly when the answer is "no".

## Source

S. Radziszowski, *Small Ramsey Numbers*, Electronic Journal of Combinatorics, Dynamic Survey
DS1, revision #18 (2026-04-24), <https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1>.
Table IVa (`R(C4, K_{1,n})` for `n <= 41`, page 21 of the PDF) lists `n = 39` as **46–47**
(references WuSR / DyDz2). It is the only open entry with `n <= 41`.
L. Boza, arXiv:2409.12770 v2 (2026-06-12) settles the open values for `n <= 38` and also
leaves `n = 39` as 46/47.

## Answer

**`R(C4, K_{1,39}) = 46`.** No graph on 46 vertices is C4-free with minimum degree `>= 7`.
(The literature, e.g. Boza's paper, notes that `R(C4, K_{1,n})` equals a `C4`-versus-wheel
Ramsey number, so the corresponding wheel entry — written `R(C4, W_40)` with the wheel on 40
vertices — is settled too. We did not re-check that relation or the wheel indexing.)

## Why (for beginners)

**Ramsey numbers.** At a party, call two guests "friends" or "strangers". Ramsey's theorem
says that if the party is large enough, some pattern is unavoidable: e.g. among any 6 people
there are 3 mutual friends or 3 mutual strangers, so `R(K3, K3) = 6`. In general `R(F, H)` is
the smallest party size that forces a "friend" copy of `F` or a "stranger" copy of `H`.

**C4 and stars.** `C4` is a square: four people `a, b, c, d` with `a–b`, `b–c`, `c–d`, `d–a`
friends. Equivalently, two people who have **two** common friends. `K_{1,39}` is a star: one
person who is a stranger to 39 others.

**Why 46 vertices and degree 7.** With 46 guests, a "stranger star" `K_{1,39}` means someone
has at most `45 - 39 = 6` friends. So a party of 46 that avoids both patterns is exactly a
friendship graph on 46 people in which no two people share two friends and everybody has at
least 7 friends. A party of 45 avoiding both is known to exist (so the number is at least 46);
we show a party of 46 cannot (so it is exactly 46).

**Why this is plausible but hard.** If you have 7 friends, and each of them has 6 more friends
whom nobody else in your circle shares (sharing would create a square), then you already
"see" about `1 + 7 + 7·6 = 50` people — more than 46. The only slack comes from triangles
(two of your friends being friends with each other), and the question is whether enough
triangles can be fitted in. That last part is a finite but enormous search, which we hand to
a SAT solver and then check with a formally verified proof checker.

## Proof

**Step 1 (counting, by hand and in Lean).** Let `G` have 46 vertices, no `C4`, and minimum
degree `>= 7`. Take a vertex `v` with `d` neighbours.

* Inside `N(v)` every vertex has at most one neighbour (two would make a square through `v`),
  so the edges inside `N(v)` form a matching with `m(v) <= ⌊d/2⌋` edges.
* For different neighbours `u, u'` of `v`, their neighbours outside `{v} ∪ N(v)` are disjoint
  (a common one would make a square `u–w–u'–v`). Call them the *private* neighbours `P(u)`.
* Counting: `46 >= 1 + d + Σ_u |P(u)| >= 1 + 7d - 2m(v)`.

If `d >= 8` the right side is at least 49, so **`G` is 7-regular**. With `d = 7` we get
`m(v) ∈ {2, 3}`. Now relabel: `v = 0`, its neighbours `1..7` with matching `(1,2), (3,4)`
[and `(5,6)` if `m = 3`], the private neighbours of `1, 2, …, 7` as consecutive blocks from 8
on (5 vertices for a matched neighbour, 6 otherwise), and the leftover vertices (2 if
`m = 3`, none if `m = 2`) last. After this renaming, every edge touching `0..7` is known.

**Step 2 (SAT).** For `m = 2` and `m = 3` we write a propositional formula (CNF) whose
variables are the 1035 possible edges, saying "no `C4`" (one clause per potential square),
"every vertex has degree `>= 7`", and "the edges at `0..7` are as in Step 1". Both formulas
are unsatisfiable.

* `m = 2` is easy (about 1 second) even **without** any symmetry breaking. Consequently every
  vertex of a hypothetical counterexample has `m(v) = 3`.
* For `m = 3` we add *symmetry breaking*: vertices inside one block are interchangeable, so we
  may demand that their rows of the adjacency matrix appear in lexicographic order. Every graph
  can be rearranged to satisfy this (take the lexicographically smallest rearrangement), so no
  solution is lost; the proof is in `VERIFY.md` §3. Then the solver needs about one minute.

Full details: `VERIFY.md` §2–§4.

## Verification

* Two CNF generators: one written for this check from scratch (`independent/`) and the
  original one from the survey (`original/`). Both pairs of formulas are UNSAT.
* Every UNSAT answer of the five main runs (`VERIFY.md` §5) has a proof: CaDiCaL 3.0.1 → DRAT → `drat-trim` (VERIFIED) → LRAT →
  **`cake_lpr`**, a proof checker formally verified in CakeML (`s VERIFIED UNSAT`).
  Proof files (up to 0.5 GB) are not stored; they are reproducible byte for byte, and their
  sha256 values are in `VERIFY.md` §5 and §9.
* Cross-checks: gadget tests, a validation on smaller parameters (minimum degree 4, 5, 6) where
  the structured and the plain formulas must agree, other solvers (CaDiCaL 2.1.2, Kissat 4.0.4).
* `lean/C4StarReduction.lean`: Lean 4 + Mathlib proof of Step 1 (7-regularity, the matching
  property, `m(v) ∈ {2,3}`), no `sorry` / `native_decide` / extra axioms.

Files in this folder:

| path | what |
|---|---|
| `VERIFY.md` | full proofs, all runs, hashes, reproduction, trust base |
| `check_cnf.sh` | solve → DRAT → drat-trim → LRAT → cake_lpr for one CNF |
| `independent/gen_c4_46.py` | CNF generator written for this check (options in its docstring) |
| `independent/test_encodings.py` | exhaustive tests of the counter / lex / triangle gadgets |
| `independent/validate_small.py` | structured vs plain formulas for minimum degree 4, 5, 6 |
| `original/c4_struct_gen.py`, `original/add_lex.py` | the survey researcher's generator (verbatim) |
| `lean/C4StarReduction.lean` | Lean 4 proof of the counting step |
| `logs/` | logs of the certified runs and of the validation |

Reproduce (about 8 minutes on one core; see `VERIFY.md` §8 for the full list):

```sh
python3 independent/gen_c4_46.py --m 2 --lex none > m2.cnf
python3 independent/gen_c4_46.py --m 3            > m3.cnf
CADICAL=cadical DRAT_TRIM=drat-trim CAKE_LPR=cake_lpr ./check_cnf.sh m2.cnf /tmp
CADICAL=cadical DRAT_TRIM=drat-trim CAKE_LPR=cake_lpr ./check_cnf.sh m3.cnf /tmp
```

## Status

**Solved, with machine-checked certificates; not yet peer-reviewed or published.**
Checked on 2026-10-04:

* Step 1 (reduction): hand proof (`VERIFY.md` §2), and its counting core is proved in Lean 4.
* Step 2 (SAT): both cases are UNSAT for two independently written encoders; every UNSAT
  claim of the main runs is certified by `cake_lpr` (formally verified) after `drat-trim`.
* The `m = 2` case needs no symmetry breaking at all.

Remaining roots of trust:

1. **Symmetry breaking for `m = 3`.** Its soundness is a short, standard argument
   (`VERIFY.md` §3), but it is not machine-checked, and the `m = 3` case without it (or with
   much weaker versions) did not finish within a few CPU-hours (`VERIFY.md` §5).
2. **"The CNF says what we mean."** The relabelling into the fixed layout and the meaning of
   the clauses are argued by hand, not formalised; mitigated by two independent encoders,
   exhaustive gadget tests, and the small-case validation (which agrees with the known
   extremal numbers `ex(n; C4)` in every case it decides).
3. `cake_lpr` itself (verified in HOL4/CakeML; we built it from the shipped assembly with gcc).
4. The lower bound 46 from the literature (DS1).

Prior-art check (2026-10-04): DS1 rev. #18 (2026-04-24, still the current revision), Boza
arXiv:2409.12770 v2 (2026-06-12: `n = 39` still 46/47), Wesley arXiv:2509.03784 (does not reach
this case), and a search of 2026 arXiv papers on `C4`–star / `C4`–wheel Ramsey numbers found no
determination of `R(C4, K_{1,39})` or `R(C4, W_40)`.
