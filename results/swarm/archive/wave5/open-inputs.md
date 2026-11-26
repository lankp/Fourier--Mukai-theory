## Your task: `wave5/open-inputs`

**Maintainer's goal (26 November 2026):** AxiomMath's Stacks Project is the only assumption; every other result GL26 and LP26 need comes from Mathlib or is proved in this repository, as needed. Every named hypothesis in the tree that is not a Stacks result is therefore an open item: to be proved, taken from Mathlib, taken from AxiomMath once it is imported (only if it is a Stacks result there), or deleted because no GL26/LP26 path needs it.

This is a **reading and triage task**; no Lean is written. Output: `results/OPEN_INPUTS.md` (new). Branch `wave5/open-inputs`: start with `git fetch --depth=50 origin formalization && git checkout -B wave5/open-inputs origin/formalization`.

1. **Find every named input.** Structures, classes and `Prop` definitions whose role is to be taken as a hypothesis (names ending in `Input`, `Data` with `Prop` fields, `…Statement`, `Tag…`, fields of `StacksInterface`, `SetupMainMinimal`-style setup data that carries mathematical content, explicit hypotheses of the pinned declarations in `results/statement-baseline.txt` and of the `#print axioms` lines in `FourierMukai/Audit.lean`). Start from `results/ASSUMPTIONS.md` (§1b and every row), `results/NEEMAN_3_2.md`, `results/AXIOMMATH_TAGS.md` (cross-check table), and `grep -rnE "structure [A-Za-z]*(Input|Data)\b|def [A-Za-z]*(Input|Statement)\b" FourierMukai WeakApprox`. `wave5/neeman-prune` is removing the Neeman 3.2 inputs; list them anyway with status "being removed".
2. **Triage each**, one row: name, file, what it says (one line), which headline results take it (follow to the pinned statements and to the GL26/LP26 result numbers in `results/COVERAGE.md`), and a verdict:
   * **Stacks** — it is a Stacks result: name the tag and the AxiomMath declaration (`results/AXIOMMATH_TAGS.md`), and whether the repo's rendering matches it;
   * **Mathlib** — Mathlib has it: name the declaration;
   * **prove** — needed on a GL26/LP26 path and neither of the above: say what the proof needs and estimate the size (S < 200 lines, M < 1000, L more), and whether it should be proved in the affine/abstract model now or only after the algebraic-space layer exists (AxiomMath);
   * **delete** — no GL26/LP26 path needs it (say why), or it is false/vacuous (cite the refutation in the tree);
   * **setup** — not an assumption but the paper's own hypothesis (e.g. LP26 Setup 4.4 data): say so and why.
3. **Summary:** counts per verdict; the shortest list of `prove` items that would make the current headline results (pinned declarations) unconditional; and a proposed grouping of the `prove` items into worker-sized tasks for the next waves, in dependency order. Flag any item that, on inspection, looks false as stated.

Files: `results/OPEN_INPUTS.md` only. Be exact about what each input states (read the Lean, not the docstring) and conservative in verdicts.
