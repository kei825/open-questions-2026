# Verification record / 検証記録

Date / 日付: 2026-10-04 (JST)

## 1. Lean 4 (main proof / 本証明)

- File / ファイル: `CASurjectivity.lean` (355 lines, namespace `OpenQuestions.CASurjectivity`)
  - sha256: `678b106369b3a19493af5d072a72df24c8bd381918c33c43448cc13329684dd5`
- Toolchain: Lean 4.33.1 (commit 819816b2), Mathlib `v4.33.1` (rev `0df444a360eaa60ab8c11dca51a86af692955474`),
  built inside the `formal-conjectures` Lake project (only `import Mathlib` is used).
- No `sorry`, `admit`, `native_decide`, or `axiom` in the file (checked with `grep`).
  All finite checks use the kernel-checked `decide`.
  / `sorry`・`admit`・`native_decide`・`axiom` は使っていない（grep で確認）。有限の検査はすべてカーネルで検査される `decide`。

Command / コマンド:

```sh
# from the repository root (after `lake exe cache get`)
export PATH=$HOME/.elan/bin:$PATH
lake env lean --threads=2 -DautoImplicit=false -DrelaxedAutoImplicit=false \
  images/cellular-automata-surjectivity/CASurjectivity.lean
```

Result / 結果: exit code 0, no errors, no warnings. Wall time 19.4 s (first run with a cold cache: 43 s), max RSS about 6.5 GB (mostly the memory-mapped Mathlib `.olean` files).

```
'OpenQuestions.CASurjectivity.answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.CASurjectivity.F_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.CASurjectivity.not_permutive' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.CASurjectivity.sliceable_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.CASurjectivity.rule_truthTable' depends on axioms: [propext]
```

Only the three standard axioms appear. / 現れる公理は標準の 3 つだけ。

### Main statements / 主な定理

| Lean name | Statement |
|---|---|
| `answer` | `∃ N f, Function.Injective N ∧ Contiguous N ∧ NotCollinear N ∧ (∀ k, DependsOn f k) ∧ Function.Surjective (globalMap N f) ∧ ¬ SlicePermutive N f` |
| `F_surjective` | `Function.Surjective F` (F = global map of example B on `ℤ × ℤ → Bool`) |
| `dependsOn_all` | the rule depends on all five sites |
| `not_permutive` | the rule is permutive with respect to **no** site |
| `not_slicePermutive` | `¬ SlicePermutive nbhd localRule` |
| `sliceable_iff` | site `k` is sliceable ↔ `k ∈ {a, d, e}` (paper's definition: a rational line through the site with the other four sites strictly on one side) |
| `rule_truthTable` | truth table = `0x3a3c353c` (input bit `a + 2b + 4c + 8d + 16e`) |
| `good_step` | the four window sets are closed under the subset construction (the automaton check) |
| `row` | row lemma: any finite switch sequence and target word have a row solution |
| `rect` | every finite rectangle of any target has a preimage |

Definitions follow Fukś–Skelton §2–3: `globalMap N f x p = f (fun k => x (p + N k))`
(= `F(s)_x = f(s_{N(x)})`), permutive = `t ↦ f([t, b])` injective for every `b`.

## 2. C cross-check (independent computation / 独立の計算)

`verify_l.c` is the parent session's independent implementation (copied unchanged from
the survey's working files).

```sh
gcc -O2 -o verify_l verify_l.c        # gcc 13.3.0
taskset -c 0 ./verify_l
```

Output (0.75 s):

```
1D 4-site surjective rules: 582
row-criterion surjective, all 5 sites, not slice-permutive: 1472
  permutive nowhere 768, only b 352, only c 352, both b,c 0
example A: tt=0x36333333 rowcrit=1 f0surj=1 f1surj=1 depends=11111 permutive=01000
example B: tt=0x3a3c353c rowcrit=1 f0surj=1 f1surj=1 depends=11111 permutive=00000
```

- 582 matches Table 1 of the paper (1D 4-site surjective rules). / 論文の表 1 と一致。
- 1472 equals the paper's "Unknown" count for the L pentomino (Table 2). / 論文の表 2 の L の未分類数と一致。

## 3. Demo / 実演

`demo_preimage.py` builds a preimage of a 7×4 picture with the row-by-row construction and checks it
(`python3 demo_preimage.py`, output: `check: F(preimage) == target on the picture: OK`).
The subset-construction computation (reachable subsets from the full set: 7 subsets
`{86, 102, 118, 153, 169, 185, 255}`, minimal ones `{153, 102, 169, 86}`) was also redone in Python;
these four minimal sets are the `good` sets used in the Lean proof.
