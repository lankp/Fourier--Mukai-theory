
## Your task: `wave2/base-change-mates`
Goal: **Lemma 7.12** (`lem:pseudofunctoriality_isos_are_conjugate`) and **Lemma 7.17** (`lem:base_change_mates_pasting`) in abstract form, plus the base-change maps of **Lemma-Definitions 7.13, 7.15** and **Definition 7.14** as abstract constructions, so that they can later discharge fields of `FourierMukai/Scheme/Duality.lean` (which currently records 7.12 as a coherence field and builds `theta` as a mate).

New file: `FourierMukai/Prelim/BaseChangeMates.lean`. Do not edit `Scheme/Duality.lean` or any other existing file (read it to align names and conventions).

Abstract setting (state it as a structure in your file): a category of "spaces" `S`, pseudofunctors `pull : Sᵒᵖ ⥤ Cat`-like (`L(-)^*`) and `push : S ⥤ Cat`-like (`R(-)_*`) given by their values, composition isomorphisms and unit isomorphisms (or Mathlib's `Pseudofunctor` on `LocallyDiscrete S`, if workable), adjunctions `pull f ⊣ push f` for every `f`, and the compatibility that the composition isos of `pull` and `push` are conjugate (Lipman (3.6.2); in the paper this comes from Lemma 2.13 `lem:spacey_Lipman_Hashimoto`). Then:
1. **7.12**: for a commutative square `p ∘ q' = q ∘ p'`, the isos `λ_□ : L(p')^* L q^* ≅ L(q')^* L p^*` and `ρ_□ : R p_* R q'_* ≅ R q_* R p'_*` are conjugate. Proof as in the paper: two pairs of conjugates composed via Lemma 7.9 (`lemma_7_9_comp` in `Prelim/MatesCalculus.lean`, or Mathlib `conjugateEquiv_comp`) and Lemma 7.11 (`Prelim/Mates.lean`).
2. **7.13 / 7.14 / 7.15**: define `θ` (∗-∗ base change, the mate of `λ_□`), its conjugate-side variant 7.14, and — given right adjoints `push f ⊣ cross f` (the paper's `f^×`) — the ∗-× base change `β` of 7.15, as in the TeX.
3. **7.17**: horizontal pasting: the base change map of the outer rectangle equals the composite of those of the two squares, under the pseudofunctorial identifications, for (1) the ∗-∗ maps and (2) the ∗-× maps (and the vertical variant if the TeX states it). Mathlib: `mateEquiv_hcomp`, `mateEquiv_vcomp`, `conjugateEquiv_comp`, `Adjunction.comp`.
4. Non-vacuity: instantiate your structure with a trivial example (e.g. `S` a one-object category and `pull = push = 𝟭` with the identity adjunction), and check `Scheme/Duality.lean`'s data shape: state in the docstring which of its fields your results would discharge.

## TeX (unpublished; do not commit): GL26 Lemma 7.11 through Remark 7.18 (tikz abbreviated)
