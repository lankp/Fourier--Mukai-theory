
## Your task: `wave2/jupper`
Goal: README "What is open" item 2: the last field of `AffineRecollementInput`, i.e. `jUpper : AffineDZ A f ⥤ AffineD A` together with `jStar A f ⊣ jUpper`, so that the affine recollement `D(A[1/f]) → D(A) → D_Z(A)` (GL26 Lemma A.4 `lem:spacey_recollement`, affine case; LP26 Setup 4.1) is fully constructed.

Read first: `Scheme/AffineRecollement.lean`, `Scheme/AffineRecollementAssembly.lean`, `Scheme/AffineJUpperTensorHom.lean` (the categorical reduction: given a fully faithful `E`, `T ⊣ H` and `e : J ⋙ E ≅ T`, then `J ⊣ E ⋙ H`), `Scheme/AffineJUpperAdjoint.lean` (the remaining fields follow formally from `jStarAdj`), `Scheme/AffineJUpperCandidateRefuted.lean` (`Rj_* Lj^*` is NOT it), `Scheme/AffineLocalCohomology*.lean`, `Scheme/StacksInput.lean` (`DerivedTensorHomData`, `Tag0A6R`), and `results/AFFINE.md`.

New file(s): `FourierMukai/Scheme/AffineJUpperConstruction.lean` (and more new files if needed). You may add an `S` row to `results/ASSUMPTIONS.md`. Do not edit existing Lean files.

What is needed: the tensor–Hom adjunction `C ⊗^L (-) ⊣ RHom(C, -)` on `D(A)` for `C = RΓ_Z(A)` (the extended Čech complex `A → A_f`, a bounded complex of flat modules), and the comparison `e` (Stacks 0A6R). Routes, in order of preference:
(a) construct `T ⊣ H` concretely: `C` is a bounded complex of flat `A`-modules, so `C ⊗ -` preserves quasi-isomorphisms and descends to `D(A)`; build its right adjoint (e.g. via K-injective or K-projective replacements available in the repo: `Scheme/KProjectiveResolution.lean`, `KProj*.lean`, `AffineSpaltenstein.lean`), and prove the adjunction;
(b) obtain `T ⊣ H` from the repo's existing `DerivedTensorHomData` interface (an allowed Stacks input), and `e` from `Tag0A6R` — then the result is conditional on exactly those tagged inputs; state it so;
(c) if neither closes, prove as much as possible (e.g. the adjunction on the homotopy category) and report precisely what remains.
Headline: a construction of `AffineRecollementInput A f` (all fields), and the corresponding unconditional/conditional form of the affine LP26 Theorem 1.1 endpoint that previously took the recollement as an input, if that is now a short corollary. Non-vacuity: the inputs you take (if any) must be shown inhabitable or cited as Stacks results.
