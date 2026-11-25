
## Your task: `wave2/trans-2cat`
Goal: **Lemma B.2** (`lem:trans_is_2-cat`): categories with translation, their 1-morphisms `(F, ξ)` and transnatural transformations form a 2-category `Trans` (uniquely) such that the forgetful `Trans → Cat` is a 2-functor; then remove the deviation in **Lemma B.4(5)**.

Files: new `FourierMukai/Prelim/TransTwoCategory.lean`; you may also edit `FourierMukai/Prelim/AppendixB.lean` (it defines the paper's data: `IsTransnatural`, `compIso`, `idIso`, `IsTransAdjunction`, `Trans.lemma_B4`, `Trans.lemma_B5_*`). No other existing file.

1. Build `Trans` as a Mathlib bicategory (`CategoryTheory.Bicategory`; if the associator/unitors can be chosen as identities, also `Bicategory.Strict`) whose objects are `(C, T)` with `T : C ⥤ C` an endofunctor (the paper asks an autoequivalence; say which you use and why), 1-morphisms `(F, ξ : T ⋙ F ≅ F ⋙ T')` composed by the paper's `ζ_F · Gξ` (`compIso`) with identity `idIso`, and 2-morphisms the transnatural transformations, composed as in `Cat`. Mind universes (use a bundled object type at fixed universes). Prove the forgetful pseudofunctor (or strict functor) to `Cat` (Mathlib: `CategoryTheory.Cat`, `Pseudofunctor`/`StrictPseudofunctor`/`Prefunctor` as appropriate) and the paper's uniqueness claim in the form you can state honestly (the 2-category structure is determined by faithfulness on 2-morphisms: e.g. vertical/horizontal composition and identities agree with those of `Cat`).
2. **B.4(5) honestly**: restate condition (5) of `Trans.lemma_B4` as "`(F, ξ) ⊣ (G, ζ)` is an adjunction in the bicategory `Trans` with unit `η` and counit `ε`" using Mathlib's `Bicategory.Adjunction` (or the bicategory's adjunction data), and prove the TFAE again; keep the old `IsTransAdjunction` as a lemma equivalent to it. Update `AppendixB.lean`'s docstring to remove the deviation note for B.4(5).
3. Optional, if cheap: `Triang` as a sub-bicategory (Lemma B.7 gives the 2-cells) — only if it falls out.

## TeX (unpublished; do not commit): GL26 Definition B.1 and Lemma B.2 with proof (tikz pasting diagrams abbreviated)
