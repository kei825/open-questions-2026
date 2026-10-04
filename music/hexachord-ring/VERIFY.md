# Verification record — HexachordRing.lean

- File: `HexachordRing.lean` (542 lines), SHA-256 `50b334958094a15804a927cec40b41d2eba3771f9e442d0c6c307b3bc452ca26`
- Toolchain: Lean 4.33.1 (`leanprover/lean4:v4.33.1`), Mathlib `v4.33.1` (commit `0df444a360`), taken from the local clone of formal-conjectures
- Date: 2026-10-04 11:40 JST, a desktop PC (WSL2)
- No `sorry`, `admit`, `native_decide` or `axiom` in the file. Finite checks use `decide +kernel` (the kernel evaluates them; no extra axioms).

## Command

```sh
# from the repository root (after `lake exe cache get`)
lake env lean --threads=2 -DautoImplicit=false -DrelaxedAutoImplicit=false \
  music/hexachord-ring/HexachordRing.lean
```

## Result

- Exit code 0, no errors, no warnings.
- Wall time 52.9 s (earlier runs of the same final file: 57.9 s, 60.8 s). Peak memory of the systemd scope (lake + lean) about 1.9 GB.
- Output (`#print axioms`):

```
'OpenQuestions.HexachordRing.no_hexachordal_ring' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.HexachordRing.no_ring_imbricating_all_classes' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.HexachordRing.classes_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.HexachordRing.exists_rep' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.HexachordRing.card_odd_classes' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.HexachordRing.oddCount_parity_of_TnIEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Auxiliary check

`python3 check.py` (plain Python 3, about 1 minute, 1 core): 50 hexachordal TnI classes, parity constant on each class, 25 odd classes; the double-counting identity on random rings; and explicit rings for window sizes 3, 4, 5 (12, 29, 38 classes), which do exist.
