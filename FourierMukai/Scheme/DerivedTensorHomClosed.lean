import FourierMukai.Scheme.Duality
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# The derived tensor--Hom interface from a closed monoidal structure

This module does not construct a derived tensor product. It identifies the
categorical input needed by `DerivedTensorHomData`: a symmetric monoidal closed
structure. The only missing library result is naturality in the target of
`MonoidalClosed.ihomCurryIso`; we prove it here and package the result.
-/

@[expose] public section

namespace RelativeFM.MonoidalClosedAdapter

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v

variable (D : Type u) [Category.{v} D] [MonoidalCategory D]

/-- A `Prop`-valued package of a symmetry and a chosen internal Hom with the
tensor--Hom adjunctions. For a derived category of ringed-space modules, the
adjunction part is Stacks 08J8 (08DI on ringed spaces). This is an input
specification, not an assertion that an arbitrary `D` has such a structure. -/
structure SymmetricMonoidalClosedInput : Prop where
  /-- The symmetric structure and tensor--Hom adjunctions. -/
  closed_structure :
    ∃ (_ : SymmetricCategory D), ∃ (rhom : Dᵒᵖ ⥤ D ⥤ D),
      ∀ E : D, Nonempty (MonoidalCategory.tensorLeft E ⊣ rhom.obj (Opposite.op E))

/-- `MonoidalClosed.ihomCurry` is natural in its target object. After two
applications of `uncurry_injective`, the desired identity is the naturality of
evaluation and of the inverse associator. -/
lemma ihomCurry_naturality_right [MonoidalClosed D] (L M : D) {X Y : D} (f : X ⟶ Y) :
    (CategoryTheory.ihom (L ⊗ M)).map f ≫ MonoidalClosed.ihomCurry L M Y =
      MonoidalClosed.ihomCurry L M X ≫
        (CategoryTheory.ihom M).map ((CategoryTheory.ihom L).map f) := by
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_uncurry_ihomCurry, MonoidalClosed.uncurry_ihom_map]
  simp only [← Category.assoc]
  rw [associator_inv_naturality_right]
  simp only [MonoidalClosed.ihomCurry, ← MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app, Category.assoc,
    CategoryTheory.ihom.ev_naturality]

/-- `MonoidalClosed.ihomCurryIso` as a natural isomorphism in its target.
Mathlib constructs the objectwise isomorphism but leaves this naturality as a
TODO. -/
def curryNatIso [MonoidalClosed D] (L M : D) :
    CategoryTheory.ihom (L ⊗ M) ≅ CategoryTheory.ihom L ⋙ CategoryTheory.ihom M :=
  NatIso.ofComponents (fun Z => by
    simpa only [Functor.comp_obj] using MonoidalClosed.ihomCurryIso L M Z)
    (fun f => ihomCurry_naturality_right D L M f)

/-- An isomorphism in the contravariant variable induces an isomorphism of
internal-Hom functors. -/
def preNatIso [MonoidalClosed D] {X Y : D} (e : X ≅ Y) : CategoryTheory.ihom Y ≅ CategoryTheory.ihom X where
  hom := MonoidalClosed.pre e.hom
  inv := MonoidalClosed.pre e.inv
  hom_inv_id := by rw [← MonoidalClosed.pre_map, e.inv_hom_id, MonoidalClosed.pre_id]
  inv_hom_id := by rw [← MonoidalClosed.pre_map, e.hom_inv_id, MonoidalClosed.pre_id]

/-- The internal-currying isomorphism in the orientation used by
`DerivedTensorHomData`. The braiding reverses the tensor factors and hence the
nesting order of the two internal Homs. -/
def internalCurryingNatIso [MonoidalClosed D] [BraidedCategory D] (L M : D) :
    CategoryTheory.ihom (L ⊗ M) ≅ CategoryTheory.ihom M ⋙ CategoryTheory.ihom L :=
  (preNatIso D (β_ L M)).symm ≪≫ curryNatIso D M L

/-- A symmetric monoidal closed category supplies all of the repository's
`DerivedTensorHomData` interface. In an application, the symmetric monoidal
closed structure on the derived category must still be constructed or supplied
by the explicitly tagged Stacks interface.
-/
noncomputable def derivedTensorHomData [MonoidalClosed D] [SymmetricCategory D] : DerivedTensorHomData D where
  monoidal := inferInstance
  symmetric := inferInstance
  rhom := MonoidalClosed.internalHom
  tensorHomAdj E := CategoryTheory.ihom.adjunction E
  internalCurrying := internalCurryingNatIso D

/-- The adjunction in the packaged data is definitionally the closed-structure
adjunction. -/
lemma derivedTensorHomData_tensorHomAdj [MonoidalClosed D] [SymmetricCategory D] (E : D) :
    (derivedTensorHomData D).tensorHomAdj E = CategoryTheory.ihom.adjunction E := rfl

/-- Build the full interface directly from a contravariantly indexed internal
Hom and its adjunction in every object. This is the form supplied by the
derived tensor--Hom bijection (Stacks 08J8, or 08DI on ringed spaces).
No separate internal-currying theorem is needed. -/
noncomputable def ofTensorHomAdjunction [SymmetricCategory D]
    (rhom : Dᵒᵖ ⥤ D ⥤ D)
    (tensorHomAdj : ∀ E : D, CategoryTheory.MonoidalCategory.tensorLeft E ⊣ rhom.obj (Opposite.op E)) :
    DerivedTensorHomData D := by
  letI : MonoidalClosed D :=
    { closed := fun E =>
        { rightAdj := rhom.obj (Opposite.op E)
          adj := tensorHomAdj E } }
  exact
    { monoidal := inferInstance
      symmetric := inferInstance
      rhom := rhom
      tensorHomAdj := tensorHomAdj
      internalCurrying := internalCurryingNatIso D }

/-- The internal Hom used by `ofTensorHomAdjunction` is the supplied one. -/
lemma ofTensorHomAdjunction_rhom [SymmetricCategory D]
    (rhom : Dᵒᵖ ⥤ D ⥤ D)
    (tensorHomAdj : ∀ E : D, CategoryTheory.MonoidalCategory.tensorLeft E ⊣ rhom.obj (Opposite.op E)) :
    (ofTensorHomAdjunction D rhom tensorHomAdj).rhom = rhom := rfl

/-- `Prop`-interface variant: only existence of each adjunction is assumed.
`Classical.choice` selects the adjunction data; no mathematical axiom is added. -/
noncomputable def ofNonemptyTensorHomAdjunction [SymmetricCategory D]
    (rhom : Dᵒᵖ ⥤ D ⥤ D)
    (tensorHomAdj : ∀ E : D,
      Nonempty (CategoryTheory.MonoidalCategory.tensorLeft E ⊣ rhom.obj (Opposite.op E))) :
    DerivedTensorHomData D :=
  ofTensorHomAdjunction D rhom (fun E => Classical.choice (tensorHomAdj E))

/-- The `Nonempty` variant also preserves the supplied internal Hom. -/
lemma ofNonemptyTensorHomAdjunction_rhom [SymmetricCategory D]
    (rhom : Dᵒᵖ ⥤ D ⥤ D)
    (tensorHomAdj : ∀ E : D,
      Nonempty (CategoryTheory.MonoidalCategory.tensorLeft E ⊣ rhom.obj (Opposite.op E))) :
    (ofNonemptyTensorHomAdjunction D rhom tensorHomAdj).rhom = rhom := rfl

/-- Realize the `Prop`-valued symmetric closed input as the repository's full
derived tensor--Hom data. -/
noncomputable def derivedTensorHomDataOfInput (I : SymmetricMonoidalClosedInput D) :
    DerivedTensorHomData D := by
  choose s rhom h using I.closed_structure
  letI : SymmetricCategory D := s
  exact ofNonemptyTensorHomAdjunction D rhom h

/-- The Hom bijection of the packaged adjunction is exactly currying. -/
lemma derivedTensorHomData_homEquiv [MonoidalClosed D] [SymmetricCategory D] (E F G : D)
    (f : (CategoryTheory.MonoidalCategory.tensorLeft E).obj F ⟶ G) :
    DerivedTensorHomData.homEquiv (derivedTensorHomData D) E F G f =
      MonoidalClosed.curry f := rfl

end RelativeFM.MonoidalClosedAdapter

#print axioms RelativeFM.MonoidalClosedAdapter.ihomCurry_naturality_right
#print axioms RelativeFM.MonoidalClosedAdapter.curryNatIso
#print axioms RelativeFM.MonoidalClosedAdapter.preNatIso
#print axioms RelativeFM.MonoidalClosedAdapter.internalCurryingNatIso
#print axioms RelativeFM.MonoidalClosedAdapter.derivedTensorHomData
#print axioms RelativeFM.MonoidalClosedAdapter.ofTensorHomAdjunction
#print axioms RelativeFM.MonoidalClosedAdapter.ofTensorHomAdjunction_rhom
#print axioms RelativeFM.MonoidalClosedAdapter.ofNonemptyTensorHomAdjunction
#print axioms RelativeFM.MonoidalClosedAdapter.ofNonemptyTensorHomAdjunction_rhom
#print axioms RelativeFM.MonoidalClosedAdapter.derivedTensorHomDataOfInput
#print axioms RelativeFM.MonoidalClosedAdapter.derivedTensorHomData_homEquiv
