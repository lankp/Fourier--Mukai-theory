import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Coproducts of K-projective complexes

This file proves the replacement-free part of the construction of coproducts
in a derived category: a degreewise coproduct of K-projective cochain complexes
is K-projective. No exactness of coproducts in the abelian category is used.
-/

@[expose] public section

namespace RelativeFM.DerivedCoproducts

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false

universe w v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} (K : ι → CochainComplex C ℤ)
variable [HasCoproductsOfShape ι C]

/-- The explicit degreewise coproduct complex. Its terms are literally the
chosen coproducts of the terms of the `K i`. -/
noncomputable abbrev coproductComplexCocone : Cocone (Discrete.functor K) :=
  HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K)

/-- It is a coproduct cocone in the category of complexes. -/
noncomputable def coproductComplexCoconeIsColimit : IsColimit (coproductComplexCocone K) :=
  HomologicalComplex.isColimitCoconeOfHasColimitEval (Discrete.functor K)

namespace CoproductHomotopy

/-- Assemble the components of homotopies on summands. -/
noncomputable abbrev hom {L : CochainComplex C ℤ}
    (f : (coproductComplexCocone K).pt ⟶ L)
    (h : ∀ i : ι, Homotopy ((coproductComplexCocone K).ι.app ⟨i⟩ ≫ f) 0)
    (n m : ℤ) : (coproductComplexCocone K).pt.X n ⟶ L.X m :=
  colimit.desc (Discrete.functor K ⋙ HomologicalComplex.eval C (.up ℤ) n)
    (Cocone.mk (L.X m) (Discrete.natTrans fun i ↦
      (h i.as).hom n m))

variable {L : CochainComplex C ℤ} {f : (coproductComplexCocone K).pt ⟶ L}
  {h : ∀ i : ι, Homotopy ((coproductComplexCocone K).ι.app ⟨i⟩ ≫ f) 0}

@[simp]
lemma ι_hom (i : ι) (n m : ℤ) :
    ((coproductComplexCocone K).ι.app ⟨i⟩).f n ≫ hom K f h n m = (h i).hom n m := by
  exact colimit.ι_desc _ (⟨i⟩ : Discrete ι)

lemma ι_hom_family (i : Discrete ι) :
    (fun n m ↦ ((coproductComplexCocone K).ι.app i).f n ≫ hom K f h n m) = (h i.as).hom := by
  funext n m
  exact colimit.ι_desc _ i

lemma zero (n m : ℤ) (hnm : ¬ (ComplexShape.up ℤ).Rel m n) : hom K f h n m = 0 := by
  apply colimit.hom_ext
  intro i
  rw [show colimit.ι (Discrete.functor K ⋙ HomologicalComplex.eval C (.up ℤ) n) i ≫
      hom K f h n m = (h i.as).hom n m from colimit.ι_desc _ i,
    (h i.as).zero n m hnm]
  exact comp_zero.symm

lemma comm (n : ℤ) : f.f n = dNext n (hom K f h) + prevD n (hom K f h) := by
  apply colimit.hom_ext
  intro i
  change ((coproductComplexCocone K).ι.app i).f n ≫ f.f n =
    ((coproductComplexCocone K).ι.app i).f n ≫
      (dNext n (hom K f h) + prevD n (hom K f h))
  rw [Preadditive.comp_add, ← dNext_comp_left, ← prevD_comp_left,
    ι_hom_family]
  simpa using (h i.as).comm n

end CoproductHomotopy

/-- A homotopy out of a degreewise coproduct can be assembled from homotopies
of its restrictions to the summands. -/
noncomputable def Homotopy.ofCoproduct
    {L : CochainComplex C ℤ} (f : (coproductComplexCocone K).pt ⟶ L)
    (h : ∀ i : ι, Homotopy ((coproductComplexCocone K).ι.app ⟨i⟩ ≫ f) 0) :
    Homotopy f 0 where
  hom := CoproductHomotopy.hom K f h
  zero := CoproductHomotopy.zero K
  comm n := by simpa using CoproductHomotopy.comm K (f := f) (h := h) n

/-- K-projective complexes are closed under arbitrary small coproducts, formed
degreewise. This does not assume AB4: null-homotopies, not acyclicity of a
coproduct of acyclic complexes, are assembled on the summands. -/
noncomputable instance isKProjectiveCoproduct [∀ i, (K i).IsKProjective] :
    (coproductComplexCocone K).pt.IsKProjective where
  nonempty_homotopy_zero f hL := ⟨Homotopy.ofCoproduct K f fun i ↦ by
    letI : ((Discrete.functor K).obj ⟨i⟩).IsKProjective :=
      inferInstanceAs (K i).IsKProjective
    exact CochainComplex.IsKProjective.homotopyZero
      ((coproductComplexCocone K).ι.app ⟨i⟩ ≫ f) hL⟩


/-- The same degreewise coproduct, viewed in the homotopy category. -/
noncomputable abbrev homotopyCoproductCofan :
    Cofan (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).obj (K i)) :=
  Cofan.mk ((HomotopyCategory.quotient C (.up ℤ)).obj (coproductComplexCocone K).pt)
    (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).map
      ((coproductComplexCocone K).ι.app ⟨i⟩))

/-- A representative of the canonical map from the degreewise coproduct to an
arbitrary cocone in the homotopy category. -/
noncomputable def complexCoproductDesc
    (t : Cofan (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).obj (K i))) :
    (coproductComplexCocone K).pt ⟶ t.pt.as :=
  (coproductComplexCoconeIsColimit K).desc
    (Cofan.mk t.pt.as (fun i ↦ (t.inj i).out))

@[simp]
lemma complexCoproductDesc_fac
    (t : Cofan (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).obj (K i))) (i : ι) :
    (coproductComplexCocone K).ι.app ⟨i⟩ ≫ complexCoproductDesc K t = (t.inj i).out :=
  (coproductComplexCoconeIsColimit K).fac _ ⟨i⟩

/-- The canonical descent map in the homotopy category. -/
noncomputable def homotopyCoproductDesc
    (t : Cofan (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).obj (K i))) :
    (homotopyCoproductCofan K).pt ⟶ t.pt :=
  (HomotopyCategory.quotient C (.up ℤ)).map (complexCoproductDesc K t)

@[simp]
lemma homotopyCoproductDesc_fac
    (t : Cofan (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).obj (K i))) (i : ι) :
    (homotopyCoproductCofan K).inj i ≫ homotopyCoproductDesc K t = t.inj i := by
  change (HomotopyCategory.quotient C (.up ℤ)).map
      ((coproductComplexCocone K).ι.app ⟨i⟩) ≫
    (HomotopyCategory.quotient C (.up ℤ)).map (complexCoproductDesc K t) = _
  rw [← Functor.map_comp, complexCoproductDesc_fac]
  exact HomotopyCategory.quotient_map_out _

/-- The degreewise coproduct of complexes is a coproduct in the homotopy
category. Existence is immediate; uniqueness uses the coproduct homotopy
assembled above. -/
noncomputable def homotopyCoproductCofanIsColimit :
    IsColimit (homotopyCoproductCofan K) := by
  refine Cofan.IsColimit.mk _ (homotopyCoproductDesc K) (homotopyCoproductDesc_fac K) ?_
  intro t m hm
  let q := HomotopyCategory.quotient C (.up ℤ)
  let d := complexCoproductDesc K t
  let m₀ : (coproductComplexCocone K).pt ⟶ t.pt.as := m.out
  have hm₀ : q.map m₀ = m := HomotopyCategory.quotient_map_out m
  have hlocal (i : ι) : Homotopy ((coproductComplexCocone K).ι.app ⟨i⟩ ≫ (m₀ - d)) 0 := by
    have heq : q.map ((coproductComplexCocone K).ι.app ⟨i⟩ ≫ m₀) =
        q.map ((coproductComplexCocone K).ι.app ⟨i⟩ ≫ d) := by
      dsimp [q, d]
      rw [Functor.map_comp, Functor.map_comp]
      change (homotopyCoproductCofan K).inj i ≫ q.map m₀ =
        (homotopyCoproductCofan K).inj i ≫ homotopyCoproductDesc K t
      rw [hm₀]
      exact (hm i).trans (homotopyCoproductDesc_fac K t i).symm
    simpa only [Preadditive.comp_sub] using
      (Homotopy.equivSubZero (HomotopyCategory.homotopyOfEq _ _ heq))
  have hz : Homotopy (m₀ - d) 0 := Homotopy.ofCoproduct K (m₀ - d) hlocal
  rw [← hm₀]
  change q.map m₀ = q.map d
  exact HomotopyCategory.eq_of_homotopy _ _ (Homotopy.equivSubZero.symm hz)


section Derived

variable [HasDerivedCategory C]

/-- The action on Hom sets induced by `Qh`, conjugated by the canonical
`quotient ⋙ Qh ≅ Q` isomorphisms. Unlike `Qh.map`, this lands directly in Homs
between `DerivedCategory.Q`-images. -/
noncomputable def derivedHomMap (K L : CochainComplex C ℤ)
    (f : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) :
    DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L :=
  (DerivedCategory.quotientCompQhIso C).inv.app K ≫
    DerivedCategory.Qh.map f ≫ (DerivedCategory.quotientCompQhIso C).hom.app L

@[simp]
lemma derivedHomMap_quotient_map {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    derivedHomMap K L ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  rw [derivedHomMap, ← Category.assoc,
    ← DerivedCategory.quotientCompQhIso_inv_naturality, Category.assoc]
  simp

@[simp]
lemma derivedHomMap_comp {K L M : CochainComplex C ℤ}
    (f : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L)
    (g : (HomotopyCategory.quotient C (.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj M) :
    derivedHomMap K M (f ≫ g) = derivedHomMap K L f ≫ derivedHomMap L M g := by
  simp [derivedHomMap, Category.assoc]

/-- For a K-projective source, derived Homs between `Q`-images are exactly
homotopy classes of chain maps. -/
noncomputable def derivedHomKProjectiveEquiv (K L : CochainComplex C ℤ)
    [K.IsKProjective] :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) ≃
    (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :=
  (Equiv.ofBijective DerivedCategory.Qh.map
    (CochainComplex.IsKProjective.Qh_map_bijective K _)).trans
  (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
    ((DerivedCategory.quotientCompQhIso C).app L))

@[simp]
lemma derivedHomKProjectiveEquiv_apply (K L : CochainComplex C ℤ) [K.IsKProjective]
    (f : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) :
    derivedHomKProjectiveEquiv K L f = derivedHomMap K L f := rfl


variable [∀ i, (K i).IsKProjective]

/-- The candidate coproduct cocone of `Q`-images of K-projective complexes. -/
noncomputable abbrev derivedCoproductCofan :
    Cofan (fun i ↦ DerivedCategory.Q.obj (K i)) :=
  Cofan.mk (DerivedCategory.Q.obj (coproductComplexCocone K).pt)
    (fun i ↦ DerivedCategory.Q.map ((coproductComplexCocone K).ι.app ⟨i⟩))

/-- Lift the legs of an arbitrary derived cocone to the homotopy category. -/
noncomputable def derivedHomotopyCofan (t : Cofan (fun i ↦ DerivedCategory.Q.obj (K i))) :
    Cofan (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).obj (K i)) :=
  Cofan.mk ((HomotopyCategory.quotient C (.up ℤ)).obj
    (DerivedCategory.Q.objPreimage t.pt)) (fun i ↦
      (derivedHomKProjectiveEquiv (K i) (DerivedCategory.Q.objPreimage t.pt)).symm
        (t.inj i ≫ (DerivedCategory.Q.objObjPreimageIso t.pt).inv))

/-- Descent for K-projective families in the derived category. -/
noncomputable def derivedCoproductDesc
    (t : Cofan (fun i ↦ DerivedCategory.Q.obj (K i))) :
    (derivedCoproductCofan K).pt ⟶ t.pt :=
  derivedHomKProjectiveEquiv (coproductComplexCocone K).pt
      (DerivedCategory.Q.objPreimage t.pt)
      ((homotopyCoproductCofanIsColimit K).desc (derivedHomotopyCofan K t)) ≫
    (DerivedCategory.Q.objObjPreimageIso t.pt).hom

@[simp]
lemma derivedCoproductDesc_fac
    (t : Cofan (fun i ↦ DerivedCategory.Q.obj (K i))) (i : ι) :
    (derivedCoproductCofan K).inj i ≫ derivedCoproductDesc K t = t.inj i := by
  let L := DerivedCategory.Q.objPreimage t.pt
  let e := DerivedCategory.Q.objObjPreimageIso t.pt
  let f : K i ⟶ (coproductComplexCocone K).pt := (coproductComplexCocone K).ι.app ⟨i⟩
  let d : (HomotopyCategory.quotient C (.up ℤ)).obj (coproductComplexCocone K).pt ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L :=
    (homotopyCoproductCofanIsColimit K).desc (derivedHomotopyCofan K t)
  change DerivedCategory.Q.map f ≫ derivedHomMap (coproductComplexCocone K).pt L d ≫ e.hom =
    t.inj i
  rw [← derivedHomMap_quotient_map, ← Category.assoc, ← derivedHomMap_comp]
  have hfac : (HomotopyCategory.quotient C (.up ℤ)).map f ≫ d =
      (derivedHomotopyCofan K t).inj i :=
    (homotopyCoproductCofanIsColimit K).fac (derivedHomotopyCofan K t) ⟨i⟩
  rw [hfac]
  dsimp [derivedHomotopyCofan]
  rw [← derivedHomKProjectiveEquiv_apply, Equiv.apply_symm_apply]
  simp [L, e, Category.assoc]

/-- A family of `Q`-images of K-projective complexes has the degreewise
coproduct of its representatives as a derived coproduct. The target in the
universal property is completely arbitrary. -/
noncomputable def derivedCoproductCofanIsColimit : IsColimit (derivedCoproductCofan K) := by
  refine Cofan.IsColimit.mk _ (derivedCoproductDesc K) (derivedCoproductDesc_fac K) ?_
  intro t m hm
  let L := DerivedCategory.Q.objPreimage t.pt
  let e := DerivedCategory.Q.objObjPreimageIso t.pt
  let E := derivedHomKProjectiveEquiv (coproductComplexCocone K).pt L
  let M : (HomotopyCategory.quotient C (.up ℤ)).obj (coproductComplexCocone K).pt ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L := E.symm (m ≫ e.inv)
  let d : (HomotopyCategory.quotient C (.up ℤ)).obj (coproductComplexCocone K).pt ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L :=
    (homotopyCoproductCofanIsColimit K).desc (derivedHomotopyCofan K t)
  have hM (i : ι) :
      (HomotopyCategory.quotient C (.up ℤ)).map ((coproductComplexCocone K).ι.app ⟨i⟩) ≫ M =
        (derivedHomotopyCofan K t).inj i := by
    apply (derivedHomKProjectiveEquiv (K i) L).injective
    rw [show (derivedHomotopyCofan K t).inj i =
      (derivedHomKProjectiveEquiv (K i) L).symm (t.inj i ≫ e.inv) from rfl,
      Equiv.apply_symm_apply, derivedHomKProjectiveEquiv_apply]
    change derivedHomMap (K i) L
      ((HomotopyCategory.quotient C (.up ℤ)).map
        ((coproductComplexCocone K).ι.app ⟨i⟩) ≫ M) = t.inj i ≫ e.inv
    rw [derivedHomMap_comp, derivedHomMap_quotient_map]
    have hEM : derivedHomMap (coproductComplexCocone K).pt L M = m ≫ e.inv := by
      change derivedHomKProjectiveEquiv (coproductComplexCocone K).pt L M = m ≫ e.inv
      exact E.apply_symm_apply _
    change DerivedCategory.Q.map ((coproductComplexCocone K).ι.app ⟨i⟩) ≫
      derivedHomMap (coproductComplexCocone K).pt L M = t.inj i ≫ e.inv
    rw [hEM]
    have hmi := hm i
    change DerivedCategory.Q.map ((coproductComplexCocone K).ι.app ⟨i⟩) ≫ m = t.inj i at hmi
    dsimp [L, e]
    rw [← Category.assoc, hmi]
  have hMd : M = d := by
    apply (homotopyCoproductCofanIsColimit K).uniq (derivedHomotopyCofan K t) M
    intro j
    exact hM j.as
  have heq : m ≫ e.inv = E d := by
    calc
      m ≫ e.inv = E (E.symm (m ≫ e.inv)) := (E.apply_symm_apply _).symm
      _ = E M := rfl
      _ = E d := congrArg E hMd
  rw [← cancel_mono e.inv, heq]
  simp [derivedCoproductDesc, E, d, L, e, Category.assoc]

/-- In particular, the full subcategory spanned by `Q`-images of K-projective
complexes has coproducts on every fixed index type, computed degreewise. -/
theorem hasCoproductQObjOfKProjective :
    HasCoproduct (fun i ↦ DerivedCategory.Q.obj (K i)) :=
  ⟨⟨⟨derivedCoproductCofan K, derivedCoproductCofanIsColimit K⟩⟩⟩


/-- A K-projective resolution of a derived object, including the comparison
isomorphism. This is data, not an axiom asserting derived coproducts. -/
structure KProjectiveResolution (X : DerivedCategory C) where
  complex : CochainComplex C ℤ
  isKProjective : complex.IsKProjective
  iso : DerivedCategory.Q.obj complex ≅ X


/-- A bounded-above cochain complex of projectives is its own K-projective
resolution. This exposes Mathlib's `isKProjective_of_projective` in the
resolution interface used for coproducts. -/
noncomputable def boundedAboveProjectiveResolution (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ n, Projective (K.X n)] :
    KProjectiveResolution (DerivedCategory.Q.obj K) where
  complex := K
  isKProjective := CochainComplex.isKProjective_of_projective K d
  iso := Iso.refl _

/-- A bounded-below chain complex of projectives, viewed as a cochain complex
indexed by `ℤ`, is likewise its own K-projective resolution. -/
noncomputable def chainProjectiveResolution (K : ChainComplex C ℕ)
    [∀ n, Projective (K.X n)] :
    KProjectiveResolution
      (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingDownNat)) where
  complex := K.extend ComplexShape.embeddingDownNat
  isKProjective := inferInstance
  iso := Iso.refl _

/-- Transport the explicit coproduct to an arbitrary family whose members have
K-projective resolutions. -/
theorem hasCoproductOfKProjectiveResolutions
    (X : ι → DerivedCategory C) (R : ∀ i, KProjectiveResolution (X i)) :
    HasCoproduct X := by
  let _ : ∀ i, (R i).complex.IsKProjective := fun i ↦ (R i).isKProjective
  let _ : HasCoproduct (fun i ↦ DerivedCategory.Q.obj (R i).complex) :=
    hasCoproductQObjOfKProjective (fun i ↦ (R i).complex)
  exact hasCoproduct_of_equiv_of_iso (fun i ↦ DerivedCategory.Q.obj (R i).complex) X
    (Equiv.refl ι) (fun i ↦ (R i).iso.symm)

/-- The precisely remaining input for unrestricted derived coproducts:
Spaltenstein's theorem that every complex has a K-projective replacement.
For module categories this is N. Spaltenstein, *Resolutions of unbounded
complexes*, Compositio Math. 65 (1988), no. 2, 121--154, Theorem C
(https://www.numdam.org/item/CM_1988__65_2_121_0/). Proving it is independent
of the coproduct argument in this file. -/
structure KProjectiveReplacementData (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory C] where
  resolution (X : DerivedCategory C) : KProjectiveResolution X

/-- Spaltenstein replacements and degreewise coproducts in `C` give all small
coproducts in `D(C)`. The replacements are used only on the source family of
each coproduct universal property. -/
theorem hasCoproductsOfKProjectiveReplacementData [HasCoproducts.{w} C]
    (H : KProjectiveReplacementData C) : HasCoproducts.{w} (DerivedCategory C) := by
  let cf : ∀ {J : Type w} (X : J → DerivedCategory C), Cofan X := fun {J} X ↦ by
    letI : HasCoproduct X := hasCoproductOfKProjectiveResolutions X
      (fun j ↦ H.resolution (X j))
    exact colimit.cocone (Discrete.functor X)
  exact hasCoproducts_of_colimit_cofans cf (fun {J} X ↦ by
    letI : HasCoproduct X := hasCoproductOfKProjectiveResolutions X
      (fun j ↦ H.resolution (X j))
    dsimp [cf]
    exact colimit.isColimit _)

#print axioms RelativeFM.DerivedCoproducts.Homotopy.ofCoproduct
#print axioms RelativeFM.DerivedCoproducts.isKProjectiveCoproduct
#print axioms RelativeFM.DerivedCoproducts.homotopyCoproductCofanIsColimit
#print axioms RelativeFM.DerivedCoproducts.derivedHomKProjectiveEquiv
#print axioms RelativeFM.DerivedCoproducts.derivedCoproductCofanIsColimit
#print axioms RelativeFM.DerivedCoproducts.boundedAboveProjectiveResolution
#print axioms RelativeFM.DerivedCoproducts.chainProjectiveResolution
#print axioms RelativeFM.DerivedCoproducts.hasCoproductOfKProjectiveResolutions
#print axioms RelativeFM.DerivedCoproducts.hasCoproductsOfKProjectiveReplacementData

end Derived

end

end RelativeFM.DerivedCoproducts
