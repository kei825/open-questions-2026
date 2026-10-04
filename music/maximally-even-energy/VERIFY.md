# Verification record — MaximallyEvenEnergy.lean

- File: `MaximallyEvenEnergy.lean` (576 lines), SHA-256 `e035e1105ebf4c3620afa6e73bb95314887fa1435297918493ccbc6f8ce44215`
- Toolchain: Lean 4.33.1 (`leanprover/lean4:v4.33.1`), Mathlib `v4.33.1` (commit `0df444a360`), taken from the local clone of formal-conjectures
- Date: 2026-10-04 11:40 JST, a desktop PC (WSL2)
- No `sorry`, `admit`, `native_decide` or `axiom` in the file. Concrete energies are computed with `decide +kernel` (exact rational arithmetic in the kernel); the infinite family is proved symbolically (`omega`, `field_simp`, `ring`, `positivity`).

## Command

```sh
# from the repository root (after `lake exe cache get`)
lake env lean --threads=2 -DautoImplicit=false -DrelaxedAutoImplicit=false \
  music/maximally-even-energy/MaximallyEvenEnergy.lean
```

## Result

- Exit code 0, no errors, no warnings.
- Wall time 24.5 s (an earlier run of the same file: 29.9 s).
- Output (`#print axioms`):

```
'OpenQuestions.MaximallyEvenEnergy.cycle32_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.MaximallyEvenEnergy.cycle32_dls' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.MaximallyEvenEnergy.path13_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.MaximallyEvenEnergy.path13_dls' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.MaximallyEvenEnergy.path10_literal_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OpenQuestions.MaximallyEvenEnergy.cycle8_general_g_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OpenQuestions.MaximallyEvenEnergy.cycle_family_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OpenQuestions.MaximallyEvenEnergy.cycle_family_dls' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Auxiliary scripts

- `python3 check.py` (plain Python 3, < 1 s): exact energies of all examples, all perturbations, exhaustive global minima for P_13, P_10, C_8, and the family for x = 3..40 (strict local minimum exactly when x ≥ 8).
- `gen_family.py` (needs sympy): generates the Lean section for the infinite family and prints the energy differences. Re-running it reproduces that section of the Lean file verbatim.
