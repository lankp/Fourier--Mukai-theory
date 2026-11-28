/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Duality.ProperShriek
import Spaces.Statements.NonVacuity

/-!
# Non-vacuity of the hypotheses of `Spaces/Duality/`

CLAUDE.md, verification step 5: the hypothesis-carrying notions of `Spaces/Duality/` are
satisfiable.  Over an affine, locally Noetherian base scheme `S` (e.g. `Spec k`, `k` a field),
the identity of the base space `S` is

* a 1-morphism of `(Sp/S)_{Noeth,sep,fp}` (`isNoethSepFpHom_id`, `IsNoethSepFpHom`), hence
  satisfies the hypotheses of Stacks 0E55 (`IsQcqsHom`);
* proper (`Statements.isProperHom_id`), with the trivial Nagata compactification
  `𝟙 = 𝟙 ∘ 𝟙` (`Compactification.ofIsProper`; an identity is an open immersion,
  `isOpenImmersion_of_isIso'`, AxiomMath's proof reproduced),

so the hypotheses of **Lemma 2.22** (`lem:neeman187`, `lemma_2_22`) are jointly satisfiable
(`lemma_2_22_hypotheses_satisfiable`).

The tagged inputs used (`Statements.Tag06LTInput`, `IsQuasiCompactOfIsIsoInput`,
`UniversallyClosedOfIsIsoInput`, `AffineQuasiSeparatedInput`) are AxiomMath theorems
(`Spaces/Statements/Inputs.lean`).  That an identity is separated, étale, and that étale
morphisms are locally of finite presentation (Stacks 0468) and separated morphisms
quasi-separated (Stacks 03KK) are AxiomMath theorems in the import closure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Duality

open RelativeFM.Spaces RelativeFM.Spaces.Statements

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An isomorphism of presheaves on the big fppf site is an open immersion.  This is AxiomMath's
`AlgebraicGeometry.Space.isOpenImmersion_of_isIso` (`Spaces/QuasiSeparatedCriteria.lean`, in the
import closure of the import list but not reachable from the imports here), reproduced with its
proof (Apache 2.0). -/
theorem isOpenImmersion_of_isIso' {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    [IsIso f] : IsOpenImmersion B S hS f := by
  refine MorphismProperty.relative.of_exists (fun a g ↦ ⟨a, g ≫ inv f, 𝟙 a, ?_, ?_⟩)
  · exact IsPullback.of_vert_isIso ⟨by simp⟩
  · change AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (𝟙 a))
    rw [CategoryTheory.Functor.map_id]
    infer_instance

/-- The trivial compactification `f = f ∘ 𝟙` of a proper morphism. -/
def Compactification.ofIsProper {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsProper B S hS f.hom) : Compactification f where
  space := Y
  j := 𝟙 Y
  p := f
  isOpenImmersion_j := isOpenImmersion_of_isIso' (𝟙 Y.1)
  isProper_p := hf
  fac := Category.id_comp f


/-- The identity of a Noetherian algebraic space is a 1-morphism of `(Sp/S)_{Noeth,sep,fp}`. -/
theorem isNoethSepFpHom_id (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactOfIsIsoInput B S hS) {X : AlgebraicSpaces B S hS}
    (hX : IsNoetherianSpace hZ X) : IsNoethSepFpHom hZ (𝟙 X) := by
  refine ⟨hX, hX, ?_, ?_⟩
  · change IsSeparated B S hS (𝟙 X.1)
    exact isSeparated_of_isIso B S hS _
  · change IsFinitePresentation B S hS (𝟙 X.1)
    exact ⟨isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_of_isIso B S hS _), hqc _,
      isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isIso B S hS _)⟩

variable (B S hS) in
/-- **The hypotheses of Lemma 2.22 are jointly satisfiable**: over an affine, locally Noetherian
base scheme `S`, the identity of the base space is a proper 1-morphism of
`(Sp/S)_{Noeth,sep,fp}` with a Nagata compactification. -/
theorem lemma_2_22_hypotheses_satisfiable (h06LT : Tag06LTInput B S hS)
    (hqc : IsQuasiCompactOfIsIsoInput B S hS) (huc : UniversallyClosedOfIsIsoInput B S hS)
    (hqs : AffineQuasiSeparatedInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [IsAffine S] [IsLocallyNoetherian S] :
    IsNoethSepFpHom hZ (𝟙 (baseSpace B S hS)) ∧ IsProperHom (𝟙 (baseSpace B S hS)) ∧
      Nonempty (Compactification (𝟙 (baseSpace B S hS))) :=
  ⟨isNoethSepFpHom_id hZ hqc (isNoetherianSpace_baseSpace B S hS hqs hZ),
    isProperHom_id B S hS h06LT hqc huc _,
    ⟨Compactification.ofIsProper _ (isProperHom_id B S hS h06LT hqc huc _)⟩⟩

/-- Example: over `Spec k`, `k` a field. -/
example (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (h06LT : Tag06LTInput B _ hk) (hqc : IsQuasiCompactOfIsIsoInput B _ hk)
    (huc : UniversallyClosedOfIsIsoInput B _ hk) (hqs : AffineQuasiSeparatedInput B _ hk)
    (hZ : B.Contains (⊤_ Scheme.{u})) :
    IsNoethSepFpHom hZ (𝟙 (baseSpace B _ hk)) ∧ IsProperHom (𝟙 (baseSpace B _ hk)) ∧
      Nonempty (Compactification (𝟙 (baseSpace B _ hk))) :=
  lemma_2_22_hypotheses_satisfiable B _ hk h06LT hqc huc hqs hZ

end RelativeFM.Spaces.Duality
