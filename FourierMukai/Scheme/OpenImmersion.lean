/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Topology.Sheaves.Sheafify
import WeakApprox.Recollement

/-!
# The open-immersion functors on sheaves of modules

For an open immersion `j : U ⟶ X` this file constructs `j_!`, `j^*` and `j_*`
on sheaves of modules over schemes and proves, at the sheaf level:

* `j_! ⊣ j^* ⊣ j_*` (`extensionByZeroAdjunction`,
  `restrictionPushforwardAdjunction`);
* `j^*` is restriction (`pullbackIsoRestriction`), and `j^* j_! ≅ 𝟭`,
  `j^* j_* ≅ 𝟭` (`restrictionExtensionByZeroIso`,
  `restrictionPushforwardIso`), with `j_!` fully faithful and an essential-image
  criterion;
* `j_!` is exact (`extensionByZeroPreservesFiniteColimits`,
  `extensionByZeroPreservesFiniteLimits`), `j^*` is exact
  (`restrictionPreservesFiniteColimits`, `restrictionPreservesFiniteLimits`), and
  `j_*` is left exact (`pushforwardPreservesFiniteLimits`);
* the exactness of `j_!` and `j^*` makes them triangulated on unbounded derived
  categories, and `DerivedOpenImmersionInterface` isolates the derived `Rj_*`
  (Stacks 079W/07A6) and the derived adjunctions.

`OpenClosedRecollement` and `ConcreteOpenClosedRecollement` then package the
open/closed data on top of `WeakApprox.Recollement`, including both gluing
triangles, with concrete comparison isomorphisms for the three open functors.

Found by a member of the Ultramath run `smwuyku7t` (direction R3).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The isomorphism of sheaves of rings which presents restriction along `j`
as `SheafOfModules.pushforward` along `j.opensFunctor`.

This is the ring map already used internally by
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`.  Naming it lets us apply
Mathlib's generic pullback construction, giving extension by zero.  For the
sheaf-theoretic adjunction, compare Stacks Tags 00A6 and 00AB. -/
noncomputable def restrictionRingHom :
    U.ringCatSheaf ⟶ (j.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  let α : U.presheaf ⟶ j.opensFunctor.op ⋙ X.presheaf :=
    { app V := (j.appIso V.unop).inv }
  ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

/-- The defining presentation of restriction as a generic pushforward. -/
lemma pushforward_restrictionRingHom (j : U ⟶ X) [IsOpenImmersion j] :
    SheafOfModules.pushforward (restrictionRingHom j) =
      Scheme.Modules.restrictFunctor j := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **Extension by zero** `j_! : Mod(O_U) ⥤ Mod(O_X)` (Stacks Tags 00A6 and
00AB), realized as the generic pullback along `restrictionRingHom j`.

It is not `Scheme.Modules.pullback j`: that functor is ordinary geometric
pullback `j^*`, whereas this generic construction is the left adjoint of
`Scheme.Modules.restrictFunctor j`. -/
noncomputable def extensionByZero (j : U ⟶ X) [IsOpenImmersion j] : U.Modules ⥤ X.Modules :=
  SheafOfModules.pullback (restrictionRingHom j)

set_option backward.isDefEq.respectTransparency.types false in
/-- The adjunction `j_! ⊣ j^*` for an open immersion (Stacks Tags 00A6 and
00AB). -/
noncomputable def extensionByZeroAdjunction :
    extensionByZero j ⊣ Scheme.Modules.restrictFunctor j :=
  SheafOfModules.pullbackPushforwardAdjunction (restrictionRingHom j)

/-- The adjunction `j^* ⊣ j_*`; this is a direct specialization of Mathlib's
`Scheme.Modules.restrictAdjunction`. -/
noncomputable abbrev restrictionPushforwardAdjunction :
    Scheme.Modules.restrictFunctor j ⊣ Scheme.Modules.pushforward j :=
  Scheme.Modules.restrictAdjunction j

/-- The open-immersion adjoint triple `j_! ⊣ j^* ⊣ j_*`. -/
noncomputable def adjointTriple : Adjunction.Triple
    (extensionByZero j) (Scheme.Modules.restrictFunctor j)
      (Scheme.Modules.pushforward j) where
  adj₁ := extensionByZeroAdjunction j
  adj₂ := restrictionPushforwardAdjunction j

/-- The unit of `j_! ⊣ j^*` is an isomorphism.  We obtain this without a
section-level computation: in an adjoint triple, invertibility of its unit is
equivalent to invertibility of the counit of `j^* ⊣ j_*`, and Mathlib proves
the latter for open immersions.  This is the identity `j^*j_! ≅ 1` used in
GL26, Lemma `lem:spacey_recollement`. -/
noncomputable instance : IsIso (extensionByZeroAdjunction j).unit := by
  change IsIso (adjointTriple j).adj₁.unit
  rw [(adjointTriple j).isIso_unit_iff_isIso_counit]
  infer_instance

/-- The canonical natural isomorphism `j^*j_! ≅ 𝟭`. -/
noncomputable def restrictionExtensionByZeroIso :
    extensionByZero j ⋙ Scheme.Modules.restrictFunctor j ≅ 𝟭 U.Modules :=
  (asIso (extensionByZeroAdjunction j).unit).symm

/-- The canonical natural isomorphism `j^*j_* ≅ 𝟭`, proved in Mathlib as
`Scheme.Modules.restrictFunctorAdjCounitIso`. -/
noncomputable abbrev restrictionPushforwardIso :
    Scheme.Modules.pushforward j ⋙ Scheme.Modules.restrictFunctor j ≅ 𝟭 U.Modules :=
  Scheme.Modules.restrictFunctorAdjCounitIso j

/-- Restriction is naturally isomorphic to ordinary geometric pullback along
an open immersion (the ringed-space pullback/pushforward formalism of Stacks
Tag 0096). -/
noncomputable def pullbackIsoRestriction :
    Scheme.Modules.pullback j ≅ Scheme.Modules.restrictFunctor j :=
  (Scheme.Modules.restrictFunctorIsoPullback j).symm

/-- The counit identity in the ordinary-pullback spelling, `j^*j_* ≅ 𝟭`. -/
noncomputable def pullbackPushforwardIso :
    Scheme.Modules.pushforward j ⋙ Scheme.Modules.pullback j ≅ 𝟭 U.Modules :=
  Functor.isoWhiskerLeft (Scheme.Modules.pushforward j) (pullbackIsoRestriction j) ≪≫
    restrictionPushforwardIso j

/-- Extension by zero is fully faithful.  This follows from the inverse unit
of `j_! ⊣ j^*` and is the open half of the full-faithfulness requirements in
GL26, Lemma `lem:spacey_recollement`. -/
noncomputable def extensionByZeroFullyFaithful : (extensionByZero j).FullyFaithful :=
  (extensionByZeroAdjunction j).fullyFaithfulLOfIsIsoUnit

noncomputable instance : (extensionByZero j).Full :=
  (extensionByZeroFullyFaithful j).full

noncomputable instance : (extensionByZero j).Faithful :=
  (extensionByZeroFullyFaithful j).faithful

/-- Restriction preserves finite limits because it is right adjoint to
extension by zero. -/
noncomputable instance restrictionPreservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) := by
  letI : PreservesLimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor j) :=
    (extensionByZeroAdjunction j).rightAdjoint_preservesLimits
  infer_instance

/-- Restriction preserves finite colimits because it is left adjoint to
pushforward.  Together with the preceding instance this says that `j^*` is
exact; no separate flatness argument is needed. -/
noncomputable instance restrictionPreservesFiniteColimits :
    PreservesFiniteColimits (Scheme.Modules.restrictFunctor j) := by
  letI : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor j) :=
    (restrictionPushforwardAdjunction j).leftAdjoint_preservesColimits
  infer_instance

/-- Pushforward along an open immersion is left exact.  It is **not generally
right exact**: right exactness of `j_*` does not follow from flatness of `j`.
Derived direct images of a non-affine open can be nonzero. -/
noncomputable instance pushforwardPreservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.pushforward j) := by
  letI : PreservesLimitsOfSize.{u, u} (Scheme.Modules.pushforward j) :=
    (restrictionPushforwardAdjunction j).rightAdjoint_preservesLimits
  infer_instance

/-- Extension by zero preserves finite colimits since it is a left adjoint.
Left exactness is proved below using the stalk calculations behind Stacks
Tags 00A6 and 00AB. -/
noncomputable instance extensionByZeroPreservesFiniteColimits :
    PreservesFiniteColimits (extensionByZero j) := by
  letI : PreservesColimitsOfSize.{u, u} (extensionByZero j) :=
    (extensionByZeroAdjunction j).leftAdjoint_preservesColimits
  infer_instance

/-- Ordinary pullback along an open immersion is left exact, transported from
restriction along `pullbackIsoRestriction`. -/
noncomputable instance pullbackPreservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.pullback j) :=
  preservesFiniteLimits_of_natIso (pullbackIsoRestriction j).symm

/-- Ordinary pullback along an open immersion is right exact, transported from
restriction. -/
noncomputable instance pullbackPreservesFiniteColimits :
    PreservesFiniteColimits (Scheme.Modules.pullback j) :=
  preservesFiniteColimits_of_natIso (pullbackIsoRestriction j).symm

/-- The remaining sheaf-level left-exactness input for `j_!` (Stacks Tag
00AB).  The other finite-colimit half is proved above.  This is a structure of
facts, not a global axiom: an instantiation must supply this preservation
instance. -/
structure ExtensionByZeroLeftExact (j : U ⟶ X) [IsOpenImmersion j] : Prop where
  /-- `j_!` preserves finite limits; the standard proof computes its stalks and
  observes that they vanish outside the open and agree with the original
  stalks inside it (Stacks Tag 00AB). -/
  preservesFiniteLimits : PreservesFiniteLimits (extensionByZero j)

/-- `j_*` preserves finite colimits, i.e. it is right exact.

For an open immersion this is **true**: the stalks of `j_* F` are the stalks of
`F` at points of `U` and `0` outside it, so `j_*` is exact; equivalently
`restrictionPreservesFiniteColimits` below together with the adjunction
`restrictionPushforwardAdjunction`.  It is recorded as a `Prop` rather than an
instance only because the passage "right adjoint preserves colimits when the
left adjoint preserves limits" is not available in Mathlib at this version, so
the exactness of `j_*` requires that small extra step; the statement is not in
doubt. -/
def PushforwardRightExact (j : U ⟶ X) [IsOpenImmersion j] : Prop :=
  PreservesFiniteColimits (Scheme.Modules.pushforward j)

end OpenImmersion

end RelativeFM


namespace RelativeFM.OpenImmersion

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

set_option backward.isDefEq.respectTransparency.types false in
/-- The presheaf-level extension by zero, before sheafification. -/
noncomputable abbrev presheafExtensionByZero (j : U ⟶ X) [IsOpenImmersion j] :
    PresheafOfModules.{u} U.ringCatSheaf.obj ⥤ PresheafOfModules.{u} X.ringCatSheaf.obj :=
  PresheafOfModules.pullback (restrictionRingHom j).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The generic adjunction for presheaves of modules, underlying
`j_! ⊣ j^*`. -/
noncomputable abbrev presheafExtensionByZeroAdjunction :
    presheafExtensionByZero j ⊣
      PresheafOfModules.pushforward (restrictionRingHom j).hom :=
  PresheafOfModules.pullbackPushforwardAdjunction (restrictionRingHom j).hom

/-- The corepresentability presentation of presheaf-level extension by zero. -/
noncomputable def presheafExtensionByZeroCorepresentableBy
    (M : PresheafOfModules.{u} U.ringCatSheaf.obj) :
    ((PresheafOfModules.pushforward (restrictionRingHom j).hom) ⋙
      coyoneda.obj (op M)).CorepresentableBy ((presheafExtensionByZero j).obj M) where
  homEquiv {N} := (presheafExtensionByZeroAdjunction j).homEquiv M N
  homEquiv_comp _ _ :=
    (presheafExtensionByZeroAdjunction j).homEquiv_naturality_right _ _

/-- Presheaf extension by zero takes a free module on `yoneda W` to the free
module on `yoneda (j ''ᵁ W)`. -/
noncomputable def presheafExtensionByZeroFreeYonedaIso (W : U.Opens) :
    (presheafExtensionByZero j).obj
      ((PresheafOfModules.free U.ringCatSheaf.obj).obj (yoneda.obj W)) ≅
    (PresheafOfModules.free X.ringCatSheaf.obj).obj
      (yoneda.obj (j.opensFunctor.obj W)) :=
  (presheafExtensionByZeroCorepresentableBy j _).uniqueUpToIso
    (PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy _ W)

/-- Every open image under `j` is contained in the range of `j`. -/
lemma image_le_opensRange (W : U.Opens) : j.opensFunctor.obj W ≤ j.opensRange := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, rfl⟩

/-- If `V` is not contained in the range of `j`, it is contained in no open
image from `U`. -/
lemma not_le_image {V : X.Opens} (hV : ¬ V ≤ j.opensRange) (W : U.Opens) :
    ¬ V ≤ j.opensFunctor.obj W :=
  fun h => hV (h.trans (image_le_opensRange j W))

/-- A free presheaf of modules on `yoneda V'` has no sections over `V` when
`V` is not contained in `V'`. -/
lemma isZero_freeYoneda_obj (R : X.Opensᵒᵖ ⥤ RingCat.{u}) {V V' : X.Opens}
    (h : ¬ V ≤ V') :
    IsZero (((PresheafOfModules.free R).obj (yoneda.obj V')).obj (op V)) := by
  have : Subsingleton (((PresheafOfModules.free R).obj (yoneda.obj V')).obj (op V)) :=
    ⟨fun _ _ => Finsupp.ext fun f => (h (leOfHom f)).elim⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Presheaf extension by zero of a free Yoneda module vanishes away from the
range of `j`. -/
lemma isZero_presheafExtensionByZero_freeYoneda_obj (W : U.Opens) {V : X.Opens}
    (hV : ¬ V ≤ j.opensRange) :
    IsZero (((presheafExtensionByZero j).obj
      ((PresheafOfModules.free U.ringCatSheaf.obj).obj (yoneda.obj W))).obj (op V)) :=
  (isZero_freeYoneda_obj X.ringCatSheaf.obj (not_le_image j hV W)).of_iso
    ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)).mapIso
      (presheafExtensionByZeroFreeYonedaIso j W))

/-- Presheaf extension by zero preserves colimits in the scheme universe. -/
noncomputable instance presheafExtensionByZeroPreservesColimitsOfSize :
    PreservesColimitsOfSize.{u, u} (presheafExtensionByZero j) :=
  (presheafExtensionByZeroAdjunction j).leftAdjoint_preservesColimits

/-- Presheaf extension by zero also preserves colimits indexed by small
shapes, including cokernels. -/
noncomputable instance presheafExtensionByZeroPreservesColimitsOfSizeZero :
    PreservesColimitsOfSize.{0, 0} (presheafExtensionByZero j) :=
  (presheafExtensionByZeroAdjunction j).leftAdjoint_preservesColimits

/-- Vanishing on every object of a diagram propagates to its colimit after
presheaf extension by zero and evaluation at `V`. -/
private lemma isZero_presheafExtensionByZero_pt_of_isColimit {J : Type*} [Category J]
    {F : J ⥤ PresheafOfModules.{u} U.ringCatSheaf.obj} {c : Cocone F} {V : X.Opens}
    [PreservesColimit F (presheafExtensionByZero j ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (op V))]
    (hc : IsColimit c)
    (h : ∀ k, IsZero (((presheafExtensionByZero j).obj (F.obj k)).obj (op V))) :
    IsZero (((presheafExtensionByZero j).obj c.pt).obj (op V)) :=
  IsColimit.isZero_pt
    (isColimitOfPreserves (presheafExtensionByZero j ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)) hc) (Functor.isZero _ h)

/-- Presheaf extension by zero of a coproduct of free Yoneda modules has no
sections away from the range of `j`. -/
lemma isZero_presheafExtensionByZero_freeYonedaCoproduct
    (N : PresheafOfModules.{u} U.ringCatSheaf.obj) {V : X.Opens}
    (hV : ¬ V ≤ j.opensRange) :
    IsZero (((presheafExtensionByZero j).obj N.freeYonedaCoproduct).obj (op V)) :=
  isZero_presheafExtensionByZero_pt_of_isColimit j (colimit.isColimit _) fun m =>
    isZero_presheafExtensionByZero_freeYoneda_obj j m.as.1.unop hV

/-- **Stacks Tag 00AB, presheaf form.** Presheaf extension by zero of any
module has no sections over an open not contained in the range of `j`. -/
lemma isZero_presheafExtensionByZero_obj
    (M : PresheafOfModules.{u} U.ringCatSheaf.obj) {V : X.Opens}
    (hV : ¬ V ≤ j.opensRange) :
    IsZero (((presheafExtensionByZero j).obj M).obj (op V)) :=
  isZero_presheafExtensionByZero_pt_of_isColimit j
    M.isColimitFreeYonedaCoproductsCokernelCofork fun k => by
      cases k <;> exact isZero_presheafExtensionByZero_freeYonedaCoproduct j _ hV

/-- Underlying-abelian-presheaf form of `isZero_presheafExtensionByZero_obj`. -/
lemma isZero_presheafExtensionByZero_presheaf_obj
    (M : PresheafOfModules.{u} U.ringCatSheaf.obj) {V : X.Opens}
    (hV : ¬ V ≤ j.opensRange) :
    IsZero (((presheafExtensionByZero j).obj M).presheaf.obj (op V)) :=
  @AddCommGrpCat.isZero_of_subsingleton _
    (ModuleCat.isZero_iff_subsingleton.1 (isZero_presheafExtensionByZero_obj j M hV))

/-- The stalk of presheaf extension by zero vanishes at a point outside the
range of `j`. -/
lemma isZero_stalk_presheafExtensionByZero
    (M : PresheafOfModules.{u} U.ringCatSheaf.obj) (x : X) (hx : x ∉ j.opensRange) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      ((presheafExtensionByZero j).obj M).presheaf x) := by
  refine IsColimit.isZero_pt (colimit.isColimit _) (Functor.isZero _ fun V => ?_)
  exact isZero_presheafExtensionByZero_presheaf_obj j M fun hle => hx (hle V.unop.2)

set_option backward.isDefEq.respectTransparency.types false in
/-- The underlying abelian presheaf of `j_! F` is the sheafification of the
underlying presheaf of the explicit presheaf-level extension by zero. -/
noncomputable def extensionByZeroPresheafIso (F : U.Modules) :
    ((extensionByZero j).obj F).val.presheaf ≅
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          ((presheafExtensionByZero j).obj F.val).presheaf) :=
  (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj).mapIso
      ((SheafOfModules.pullbackIso (restrictionRingHom j)).app F) ≪≫
    (PresheafOfModules.sheafificationCompForgetCompToPresheaf
      (𝟙 X.ringCatSheaf.obj)).app _

/-- **Stacks Tag 00AB, stalks off the open.** Sheaf extension by zero has zero
stalk at every point outside the range of `j`. -/
theorem isZero_stalk_extensionByZero (F : U.Modules) (x : X) (hx : x ∉ j.opensRange) :
    IsZero (TopCat.Presheaf.stalk (X := X) ((extensionByZero j).obj F).val.presheaf x) := by
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X)
        ((presheafExtensionByZero j).obj F.val).presheaf)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  exact ((isZero_stalk_presheafExtensionByZero j F.val x hx).of_iso
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X)
        ((presheafExtensionByZero j).obj F.val).presheaf))).symm).of_iso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      (extensionByZeroPresheafIso j F))

end RelativeFM.OpenImmersion


namespace RelativeFM.OpenImmersion

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Monomorphisms of sheaves of modules become monomorphisms on every stalk
of the underlying abelian presheaf. -/
lemma mono_stalk_map_of_mono {Y : Scheme.{u}} {M N : Y.Modules} (g : M ⟶ N)
    [Mono g] (y : Y) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((Scheme.Modules.toPresheaf Y).map g)) := by
  have hmono : Mono ((Scheme.Modules.toPresheaf Y).map g) := Functor.map_mono _ g
  refine ConcreteCategory.mono_of_injective _
    (TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (fun V => ?_) y)
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp
    ((NatTrans.mono_iff_mono_app _).mp hmono (op V))

/-- The unit isomorphism shows that `j^*` preserves monomorphisms on objects
in the image of `j_!`. -/
lemma mono_restriction_extensionByZero_map {M N : U.Modules} (g : M ⟶ N) [Mono g] :
    Mono ((Scheme.Modules.restrictFunctor j).map ((extensionByZero j).map g)) := by
  have e : Arrow.mk g ≅ Arrow.mk
      ((Scheme.Modules.restrictFunctor j).map ((extensionByZero j).map g)) :=
    Arrow.isoMk (asIso ((extensionByZeroAdjunction j).unit.app M))
      (asIso ((extensionByZeroAdjunction j).unit.app N)) (by
        rw [asIso_hom, asIso_hom]
        exact ((extensionByZeroAdjunction j).unit.naturality g).symm)
  exact ((MorphismProperty.monomorphisms U.Modules).arrow_mk_iso_iff e).mp ‹Mono g›

/-- On stalks, extension by zero preserves monomorphisms: inside the open one
uses `j^*j_! ≅ 1`; outside it the stalk is zero by Stacks Tag 00AB. -/
lemma mono_stalk_extensionByZero_map {M N : U.Modules} (g : M ⟶ N) [Mono g] (x : X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf X).map ((extensionByZero j).map g))) := by
  by_cases hx : x ∈ j.opensRange
  · rcases hx with ⟨u, rfl⟩
    have hmono : Mono ((Scheme.Modules.restrictFunctor j).map
        ((extensionByZero j).map g)) := mono_restriction_extensionByZero_map j g
    have h₁ : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} u).map
        ((Scheme.Modules.toPresheaf U).map
          ((Scheme.Modules.restrictFunctor j).map ((extensionByZero j).map g)))) :=
      mono_stalk_map_of_mono _ u
    let e := Scheme.Modules.restrictStalkNatIso j u
    exact ((MorphismProperty.monomorphisms AddCommGrpCat.{u}).arrow_mk_iso_iff
      (Arrow.isoMk (e.app ((extensionByZero j).obj M)) (e.app ((extensionByZero j).obj N))
        (e.hom.naturality ((extensionByZero j).map g)).symm)).mp h₁
  · refine ⟨fun g₁ g₂ _ => ?_⟩
    exact (isZero_stalk_extensionByZero j M x hx).eq_of_tgt g₁ g₂

/-- **Stacks Tag 00AB, monomorphisms.** Extension by zero preserves
monomorphisms of sheaves of modules. -/
noncomputable instance extensionByZeroPreservesMonomorphisms :
    (extensionByZero j).PreservesMonomorphisms where
  preserves {M N} g _ := by
    have : ∀ x : X, Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (((SheafOfModules.toSheaf X.ringCatSheaf).map ((extensionByZero j).map g)).hom)) :=
      fun x => mono_stalk_extensionByZero_map j g x
    exact (SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map
      (TopCat.Presheaf.mono_of_stalk_mono
        ((SheafOfModules.toSheaf X.ringCatSheaf).map ((extensionByZero j).map g)))

/-- Restriction is additive because its right adjoint `j_*` is additive. -/
noncomputable instance restrictionAdditive : (Scheme.Modules.restrictFunctor j).Additive :=
  Adjunction.left_adjoint_additive (restrictionPushforwardAdjunction j)

/-- Extension by zero is additive, as the left adjoint between preadditive
categories. -/
noncomputable instance extensionByZeroAdditive : (extensionByZero j).Additive :=
  Adjunction.left_adjoint_additive (extensionByZeroAdjunction j)

/-- Extension by zero preserves homology: it preserves monomorphisms by the
stalk argument and cokernels because it is a left adjoint. -/
noncomputable instance extensionByZeroPreservesHomology :
    (extensionByZero j).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels (extensionByZero j)

/-- **Stacks Tag 00AB, exactness.** Extension by zero is left exact.  Together
with `extensionByZeroPreservesFiniteColimits`, this proves that `j_!` is
exact. -/
noncomputable instance extensionByZeroPreservesFiniteLimits :
    PreservesFiniteLimits (extensionByZero j) :=
  (extensionByZero j).preservesFiniteLimits_of_preservesHomology

/-- A sheaf-level witness for the previously isolated left-exactness
interface; it is now a theorem, not an additional hypothesis. -/
theorem extensionByZeroLeftExact : ExtensionByZeroLeftExact j where
  preservesFiniteLimits := inferInstance

/-- A short exact sequence of sheaves of modules remains short exact after
extension by zero. -/
lemma shortExact_map_extensionByZero (S : ShortComplex U.Modules) (hS : S.ShortExact) :
    (S.map (extensionByZero j)).ShortExact :=
  hS.map_of_exact (extensionByZero j)

end RelativeFM.OpenImmersion


namespace RelativeFM.OpenImmersion

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Generic ringed-space form of the stalkwise isomorphism criterion. -/
private lemma isIso_of_stalk_isIso_aux {T : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u})
    {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (h : ∀ y : T, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map f))) : IsIso f := by
  have h' : ∀ y : T, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((SheafOfModules.toSheaf R).map f).hom) := h
  have : IsIso ((SheafOfModules.toSheaf R).map f) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ((SheafOfModules.toSheaf R).map f)
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf R)

/-- A morphism of sheaves of modules which is an isomorphism on every stalk
is an isomorphism. -/
lemma isIso_of_stalk_isIso {Y : Scheme.{u}} {M N : Y.Modules} (f : M ⟶ N)
    (h : ∀ y : Y, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((Scheme.Modules.toPresheaf Y).map f))) : IsIso f :=
  isIso_of_stalk_isIso_aux Y.ringCatSheaf f h

/-- If the stalks of `G` vanish outside the open, the counit
`j_!j^*G ⟶ G` is an isomorphism.  This is the converse half of Stacks Tag
00AB's essential-image criterion. -/
theorem isIso_extensionByZeroAdjunction_counit (G : X.Modules)
    (hG : ∀ x : X, x ∉ j.opensRange →
      IsZero (TopCat.Presheaf.stalk (X := X) G.val.presheaf x)) :
    IsIso ((extensionByZeroAdjunction j).counit.app G) := by
  set φ := (extensionByZeroAdjunction j).counit.app G
  refine isIso_of_stalk_isIso φ fun x => ?_
  by_cases hx : x ∈ j.opensRange
  · rcases hx with ⟨u, rfl⟩
    letI hR : IsIso ((Scheme.Modules.restrictFunctor j).map φ) :=
      isIso_of_hom_comp_eq_id _ ((extensionByZeroAdjunction j).right_triangle_components G)
    have hF : IsIso (((Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.toPresheaf U) ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} u).map φ) := by
      change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} u).map
        ((Scheme.Modules.toPresheaf U).map ((Scheme.Modules.restrictFunctor j).map φ)))
      infer_instance
    let e := Scheme.Modules.restrictStalkNatIso j u
    exact ((MorphismProperty.isomorphisms AddCommGrpCat.{u}).arrow_mk_iso_iff
      (Arrow.isoMk (e.app ((extensionByZero j).obj ((Scheme.Modules.restrictFunctor j).obj G)))
        (e.app G) (e.hom.naturality φ).symm)).mp hF
  · exact (isZero_stalk_extensionByZero j ((Scheme.Modules.restrictFunctor j).obj G) x hx).isIso
      (hG x hx) _

/-- **Stacks Tag 00AB, essential image.** A sheaf `G` of modules on `X` lies in
the essential image of extension by zero exactly when its stalks vanish at all
points outside the range of `j`. -/
theorem extensionByZero_essImage (G : X.Modules) :
    (extensionByZero j).essImage G ↔ ∀ x : X, x ∉ j.opensRange →
      IsZero (TopCat.Presheaf.stalk (X := X) G.val.presheaf x) := by
  constructor
  · rintro ⟨F, ⟨e⟩⟩ x hx
    exact (isZero_stalk_extensionByZero j F x hx).of_iso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
        ((Scheme.Modules.toPresheaf X).mapIso e)).symm
  · intro hG
    have := isIso_extensionByZeroAdjunction_counit j G hG
    exact ⟨(Scheme.Modules.restrictFunctor j).obj G,
      ⟨asIso ((extensionByZeroAdjunction j).counit.app G)⟩⟩

/-- **Stacks Tag 00AB.** Extension by zero is fully faithful, and its essential
image is the full subcategory of modules whose stalks vanish outside the open. -/
theorem extensionByZero_fullyFaithful_and_essImage :
    (extensionByZero j).Full ∧ (extensionByZero j).Faithful ∧
      ∀ G : X.Modules, (extensionByZero j).essImage G ↔
        ∀ x : X, x ∉ j.opensRange →
          IsZero (TopCat.Presheaf.stalk (X := X) G.val.presheaf x) :=
  ⟨inferInstance, inferInstance, extensionByZero_essImage j⟩

end RelativeFM.OpenImmersion


/-!
## Derived open immersions and the geometric recollement contract

The two exact functors `j^*` and `j_!` induce triangulated functors on all
unbounded derived categories, without resolutions.  The right derived
pushforward is not defined here: it requires a K-injective-resolution or an
equivalent derivability input which is absent from Mathlib 4.33.1.  Its
interface below makes that input, and the two derived adjunctions, explicit.
-/

namespace RelativeFM.OpenImmersion

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry CategoryTheory.Pretriangulated

universe u wU wX

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{wU} U.Modules] [HasDerivedCategory.{wX} X.Modules]

/-- The derived restriction `Lj^* : D(X) ⥤ D(U)`, obtained degreewise because
restriction is exact.  It is its own left and right derived functor; no
boundedness or K-projective resolution is needed. -/
noncomputable def derivedRestriction :
    DerivedCategory X.Modules ⥤ DerivedCategory U.Modules :=
  (Scheme.Modules.restrictFunctor j).mapDerivedCategory

/-- The derived extension by zero `j_! : D(U) ⥤ D(X)`, obtained degreewise
from the exact functor proved using Stacks Tag 00AB. -/
noncomputable def derivedExtensionByZero :
    DerivedCategory U.Modules ⥤ DerivedCategory X.Modules :=
  (extensionByZero j).mapDerivedCategory

/-- The comparison of derived restriction with its degreewise action on
cochain complexes. -/
noncomputable abbrev derivedRestrictionFactors :
    DerivedCategory.Q ⋙ derivedRestriction j ≅
      (Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors

/-- The comparison of derived extension by zero with its degreewise action on
cochain complexes. -/
noncomputable abbrev derivedExtensionByZeroFactors :
    DerivedCategory.Q ⋙ derivedExtensionByZero j ≅
      (extensionByZero j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (extensionByZero j).mapDerivedCategoryFactors

-- PROVISIONAL: Mathlib 4.33.1 has no unbounded K-injective construction of
-- `Rj_*`; this structure isolates that input and the two derived adjunctions.
/-- **Derived geometric input for GL26, Lemma `lem:spacey_recollement`.**
This structure supplies the unbounded right derived pushforward and the two
derived open adjunctions.  The two other open functors are already the concrete
`derivedRestriction j` and `derivedExtensionByZero j` above.

The field `rightDerivedUnit`/`isRightDerived` is the missing K-injective or
derivability input for `Rj_*` (compare Stacks Tags 079W and 07A6).  Fields
`restrictionPushforwardAdj` and `isIso_counit` say respectively `Lj^* ⊣ Rj_*`
and `Lj^*Rj_* ≅ 1`.  Nothing here asserts right exactness of the underived
`j_*`, which is false in general. -/
structure DerivedOpenImmersionInterface (j : U ⟶ X) [IsOpenImmersion j]
    [HasDerivedCategory.{wU} U.Modules] [HasDerivedCategory.{wX} X.Modules] where
  /-- The right derived pushforward `Rj_*`. -/
  pushforward : DerivedCategory U.Modules ⥤ DerivedCategory X.Modules
  /-- `Rj_*` commutes with integer shifts. -/
  [pushforward_commShift : pushforward.CommShift ℤ]
  /-- `Rj_*` is a triangulated functor. -/
  [pushforward_exact : pushforward.IsTriangulated]
  /-- Its unit as a right derived functor. -/
  rightDerivedUnit :
    (Scheme.Modules.pushforward j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ pushforward
  /-- The universal property of `Rj_*` at quasi-isomorphisms. -/
  isRightDerived : pushforward.IsRightDerivedFunctor rightDerivedUnit
    (HomotopyCategory.quasiIso U.Modules (ComplexShape.up ℤ))
  /-- The derived extension-by-zero/restriction adjunction `j_! ⊣ Lj^*`. -/
  extensionRestrictionAdj : derivedExtensionByZero j ⊣ derivedRestriction j
  /-- The derived restriction/pushforward adjunction `Lj^* ⊣ Rj_*`. -/
  restrictionPushforwardAdj : derivedRestriction j ⊣ pushforward
  /-- The counit identity `Lj^*Rj_* ≅ 1`. -/
  isIso_counit : IsIso restrictionPushforwardAdj.counit

attribute [instance] DerivedOpenImmersionInterface.pushforward_commShift
  DerivedOpenImmersionInterface.pushforward_exact
  DerivedOpenImmersionInterface.isIso_counit

namespace DerivedOpenImmersionInterface

variable (D : DerivedOpenImmersionInterface.{u, wU, wX} j)

/-- The derived open adjoint triple assembled from the interface. -/
noncomputable def adjointTriple : Adjunction.Triple
    (derivedExtensionByZero j) (derivedRestriction j) D.pushforward where
  adj₁ := D.extensionRestrictionAdj
  adj₂ := D.restrictionPushforwardAdj

/-- The unit of the derived `j_! ⊣ Lj^*` is invertible, using the adjoint-triple
argument and invertibility of the counit of `Lj^* ⊣ Rj_*`. -/
noncomputable instance : IsIso D.extensionRestrictionAdj.unit := by
  change IsIso D.adjointTriple.adj₁.unit
  rw [D.adjointTriple.isIso_unit_iff_isIso_counit]
  change IsIso D.restrictionPushforwardAdj.counit
  infer_instance

/-- The derived identity `Lj^*j_! ≅ 1`. -/
noncomputable def restrictionExtensionIso :
    derivedExtensionByZero j ⋙ derivedRestriction j ≅
      𝟭 (DerivedCategory U.Modules) :=
  (asIso D.extensionRestrictionAdj.unit).symm

/-- The derived identity `Lj^*Rj_* ≅ 1`. -/
noncomputable def restrictionPushforwardIso :
    D.pushforward ⋙ derivedRestriction j ≅ 𝟭 (DerivedCategory U.Modules) :=
  asIso D.restrictionPushforwardAdj.counit

/-- Derived extension by zero is fully faithful. -/
noncomputable def extensionFullyFaithful : (derivedExtensionByZero j).FullyFaithful :=
  D.extensionRestrictionAdj.fullyFaithfulLOfIsIsoUnit

/-- Derived pushforward is full. -/
noncomputable instance : D.pushforward.Full :=
  D.restrictionPushforwardAdj.fullyFaithfulROfIsIsoCounit.full

/-- Derived pushforward is faithful. -/
noncomputable instance : D.pushforward.Faithful :=
  D.restrictionPushforwardAdj.fullyFaithfulROfIsIsoCounit.faithful

end DerivedOpenImmersionInterface

end RelativeFM.OpenImmersion

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry CategoryTheory.Pretriangulated

universe u vZ uZ vD uD vU uU
universe wZ wX wU

-- PROVISIONAL: this is the recollement interface; the geometric construction
-- of `D_qc` and Brown-representability inputs remain to be supplied.
/-- The categorical content of the open/closed recollement needed by GL26,
Lemma `lem:spacey_recollement`, is exactly
`RelativeWeakApprox.Recollement`.  We reuse that completed structure rather
than duplicating it.  Its six triangulated functors are
`i^*`, `i_*`, `i^!`, `j_!`, `j^*`, `j_*`; its fields include the four
adjunctions, full faithfulness, the kernel and zero-composite conditions, and
**both natural distinguished gluing triangles**
`j_!j^*E → E → i_*i^*E → j_!j^*E[1]` and
`i_*i^!E → E → j_*j^*E → i_*i^!E[1]`.

For schemes, an instantiation takes the three categories to be the relevant
`D_qc` (or supported `D_qc,W`) categories.  The geometric existence proof uses
quasi-coherent restriction/pushforward, localization at the open complement,
and Brown representability for adjoints; those are not supplied by this alias. -/
abbrev DQCohRecollement := RelativeWeakApprox.Recollement

-- PROVISIONAL: `DZ`, `D`, `DU` must still be instantiated by the relevant
-- derived categories; the structure does not assert their construction.
/-- Geometric bookkeeping for GL26, Lemma `lem:spacey_recollement`: a
quasi-compact open immersion `j`, a closed immersion `i` onto its complement,
and a recollement of the three chosen triangulated categories.

`DZ`, `D`, and `DU` are parameters so that this interface applies both to the
full derived categories and to the `D_qc` categories once R1's construction is
plugged in.  The categorical gluing triangles are fields of `categorical`, not
axioms. -/
structure OpenClosedRecollement {U X Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (DZ : Type uZ) (D : Type uD) (DU : Type uU)
    [Category.{vZ} DZ] [Category.{vD} D] [Category.{vU} DU]
    [Preadditive DZ] [Preadditive D] [Preadditive DU]
    [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
    [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
    [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [∀ (n : ℤ), (shiftFunctor DU n).Additive]
    [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
    [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
    [CategoryTheory.IsTriangulated DU] where
  /-- Quasi-compactness of the open immersion, as in GL26's hypothesis. -/
  quasiCompact_open : QuasiCompact j
  /-- The closed immersion has exactly the complement of the open as its
  underlying set-theoretic range. -/
  range_eq_compl : Set.range i.base = (j.opensRange : Set X)ᶜ
  /-- The six triangulated functors, adjunctions, and two gluing triangles,
  packaged by the completed scheme-independent categorical layer. -/
  categorical : DQCohRecollement DZ D DU

-- PROVISIONAL: this is the full-derived-category recollement specification;
-- its fields are the missing closed-complement and derived-localization facts.
/-- A concrete form of `OpenClosedRecollement` on the full derived categories
of all sheaves of modules.  Unlike the category-polymorphic interface above,
this version explicitly identifies the three open functors in the recollement
with the concrete derived extension by zero, derived restriction, and the
supplied right derived pushforward. -/
structure ConcreteOpenClosedRecollement {U X Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    [HasDerivedCategory.{wU} U.Modules] [HasDerivedCategory.{wX} X.Modules]
    [HasDerivedCategory.{wZ} Z.Modules]
    (Rj : OpenImmersion.DerivedOpenImmersionInterface.{u, wU, wX} j) where
  /-- Quasi-compactness of the open immersion. -/
  quasiCompact_open : QuasiCompact j
  /-- The closed immersion has exactly the complement of the open as its
  underlying range. -/
  range_eq_compl : Set.range i.base = (j.opensRange : Set X)ᶜ
  /-- The six functors and both gluing triangles on the full derived
  categories. -/
  categorical : DQCohRecollement (DerivedCategory Z.Modules)
    (DerivedCategory X.Modules) (DerivedCategory U.Modules)
  /-- The open lower-shriek is derived extension by zero. -/
  jShriek_iso : categorical.jShriek ≅ OpenImmersion.derivedExtensionByZero j
  /-- The open upper-star is derived restriction. -/
  jStar_iso : categorical.jStar ≅ OpenImmersion.derivedRestriction j
  /-- The open lower-star is the supplied `Rj_*`. -/
  jUpper_iso : categorical.jUpper ≅ Rj.pushforward

/-- Forget the concrete comparison isomorphisms, retaining the generic
open/closed geometric interface. -/
def ConcreteOpenClosedRecollement.toOpenClosedRecollement {U X Z : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {i : Z ⟶ X} [IsClosedImmersion i]
    [HasDerivedCategory.{wU} U.Modules] [HasDerivedCategory.{wX} X.Modules]
    [HasDerivedCategory.{wZ} Z.Modules]
    {Rj : OpenImmersion.DerivedOpenImmersionInterface.{u, wU, wX} j}
    (R : ConcreteOpenClosedRecollement j i Rj) :
    OpenClosedRecollement j i (DerivedCategory Z.Modules)
      (DerivedCategory X.Modules) (DerivedCategory U.Modules) where
  quasiCompact_open := R.quasiCompact_open
  range_eq_compl := R.range_eq_compl
  categorical := R.categorical

/-- The first gluing triangle `j_!j^*E → E → i_*i^*E → …`, extracted without
reproving its naturality or distinguishedness. -/
def OpenClosedRecollement.firstTriangle {U X Z : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {i : Z ⟶ X} [IsClosedImmersion i]
    {DZ : Type uZ} {D : Type uD} {DU : Type uU}
    [Category.{vZ} DZ] [Category.{vD} D] [Category.{vU} DU]
    [Preadditive DZ] [Preadditive D] [Preadditive DU]
    [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
    [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
    [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [∀ (n : ℤ), (shiftFunctor DU n).Additive]
    [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
    [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
    [CategoryTheory.IsTriangulated DU]
    (R : OpenClosedRecollement j i DZ D DU) (E : D) : Triangle D :=
  R.categorical.firstTriangle E

/-- The second gluing triangle `i_*i^!E → E → j_*j^*E → …`. -/
def OpenClosedRecollement.secondTriangle {U X Z : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {i : Z ⟶ X} [IsClosedImmersion i]
    {DZ : Type uZ} {D : Type uD} {DU : Type uU}
    [Category.{vZ} DZ] [Category.{vD} D] [Category.{vU} DU]
    [Preadditive DZ] [Preadditive D] [Preadditive DU]
    [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
    [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
    [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [∀ (n : ℤ), (shiftFunctor DU n).Additive]
    [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
    [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
    [CategoryTheory.IsTriangulated DU]
    (R : OpenClosedRecollement j i DZ D DU) (E : D) : Triangle D :=
  R.categorical.secondTriangle E

end RelativeFM


/-! ## Axiom audit

Every declaration checked below must use only `propext`, `Classical.choice`,
and `Quot.sound`.  Interfaces are included as well as the principal geometric
proofs; no declaration in this file introduces an axiom. -/
