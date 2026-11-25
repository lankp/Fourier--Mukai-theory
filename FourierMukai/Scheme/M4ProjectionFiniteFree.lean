import FourierMukai.Scheme.M4StageFiniteFree
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

@[expose] public section

namespace RelativeFM.Stacks07LT.M4

open CategoryTheory CategoryTheory.Limits Module
open RelativeFM RelativeFM.DerivedCoproducts RelativeFM.NeemanM1
open scoped ZeroObject

universe uA

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (A : Type uA) [CommRing A]
variable {ι : Type uA} (s : Finset ι)

lemma stageCoproduct_isZero (c n : ℤ) (hn : n ≠ c) :
    IsZero ((stageCoproduct A s c).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply (complexCoproductEvalCofan_isColimit (stageComplex A s c) n).hom_ext
  intro i
  exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) c (stageModule A s i.as) n hn).eq_of_src _ _

instance stageCoproduct_isStrictlyGE (c : ℤ) : (stageCoproduct A s c).IsStrictlyGE c := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact stageCoproduct_isZero A s c n (by omega)

instance stageCoproduct_isStrictlyLE (c : ℤ) : (stageCoproduct A s c).IsStrictlyLE c := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  exact stageCoproduct_isZero A s c n (by omega)

/-- A coproduct of single complexes is itself a single complex on its degree-`c`
term. -/
def stageCoproductSingleIso (c : ℤ) :
    stageCoproduct A s c ≅
      (HomologicalComplex.single (ModuleCat A) (.up ℤ) c).obj ((stageCoproduct A s c).X c) where
  hom := HomologicalComplex.mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = c) =>
    ((stageCoproduct A s c).isZero_of_isStrictlyGE c i (by omega)).eq_of_src _ _)
  inv := HomologicalComplex.mkHomFromSingle (𝟙 _) (fun i (hi : c + 1 = i) =>
    ((stageCoproduct A s c).isZero_of_isStrictlyLE c i (by omega)).eq_of_tgt _ _)
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro i
    obtain hi | rfl | hi := lt_trichotomy i c
    · exact ((stageCoproduct A s c).isZero_of_isStrictlyGE c i (by omega)).eq_of_src _ _
    · rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
        HomologicalComplex.mkHomFromSingle_f]
      simp
    · exact ((stageCoproduct A s c).isZero_of_isStrictlyLE c i (by omega)).eq_of_tgt _ _
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro i
    obtain hi | rfl | hi := lt_trichotomy i c
    · apply HomologicalComplex.isZero_single_obj_X (.up ℤ) c _ i (by omega) |>.eq_of_src
    · rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f,
        HomologicalComplex.mkHomToSingle_f]
      simp
    · apply HomologicalComplex.isZero_single_obj_X (.up ℤ) c _ i (by omega) |>.eq_of_tgt

@[simp]
lemma stageCoproductSingleIso_hom_f_c (c : ℤ) :
    (stageCoproductSingleIso A s c).hom.f c =
      (HomologicalComplex.singleObjXSelf (.up ℤ) c ((stageCoproduct A s c).X c)).inv := by
  unfold stageCoproductSingleIso
  rw [HomologicalComplex.mkHomToSingle_f]
  simp

@[simp]
lemma stageCoproductSingleIso_inv_f_c (c : ℤ) :
    (stageCoproductSingleIso A s c).inv.f c =
      (HomologicalComplex.singleObjXSelf (.up ℤ) c ((stageCoproduct A s c).X c)).hom := by
  unfold stageCoproductSingleIso
  rw [HomologicalComplex.mkHomFromSingle_f]
  simp

variable (L : CochainComplex (ModuleCat A) ℤ) (c : ℤ)
variable (b : Basis ι A (L.X c))

/-- The degreewise tail projection before making it a map of complexes. -/
def stageProjectionMap : L.X c ⟶ (stageCoproduct A s c).X c :=
  ModuleCat.ofHom (tailMap b s) ≫ (stageEvalIso A s c).inv

instance stageProjectionMap_epi : Epi (stageProjectionMap A s L c b) := by
  letI : Epi (ModuleCat.ofHom (tailMap b s)) :=
    (ModuleCat.epi_iff_surjective _).mpr (tailMap_surjective b s)
  dsimp [stageProjectionMap]
  infer_instance

/-- The tail projection as a map of complexes. -/
def stageProjection (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0) :
    L ⟶ stageCoproduct A s c :=
  HomologicalComplex.mkHomToSingle (stageProjectionMap A s L c b) (fun i (hi : i + 1 = c) => by
    obtain rfl : i = c - 1 := by omega
    exact h) ≫ (stageCoproductSingleIso A s c).inv

@[simp]
lemma stageProjection_f_c (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0) :
    (stageProjection A s L c b h).f c = stageProjectionMap A s L c b := by
  unfold stageProjection
  rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f]
  simp

lemma stageProjection_f_of_ne (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0)
    (n : ℤ) (hn : n ≠ c) : (stageProjection A s L c b h).f n = 0 := by
  simp [stageProjection, HomologicalComplex.mkHomToSingle, hn]
  exact zero_comp

instance stageProjection_epi (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0) :
    Epi (stageProjection A s L c b h) := by
  apply HomologicalComplex.epi_of_epi_f
  intro n
  by_cases hn : n = c
  · subst n
    rw [stageProjection_f_c]
    infer_instance
  · exact (stageCoproduct_isZero A s c n hn).epi _

/-- The kernel sequence of the chain projection. -/
def stageProjectionShortComplex (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0) :
    ShortComplex (CochainComplex (ModuleCat A) ℤ) :=
  ShortComplex.mk (kernel.ι (stageProjection A s L c b h))
    (stageProjection A s L c b h) (kernel.condition _)

lemma stageProjectionShortComplex_shortExact
    (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0) :
    (stageProjectionShortComplex A s L c b h).ShortExact where
  mono_f := by
    dsimp [stageProjectionShortComplex]
    infer_instance
  epi_g := by
    dsimp [stageProjectionShortComplex]
    infer_instance
  exact := ShortComplex.exact_kernel _

/-- Evaluation of the kernel away from degree `c` recovers the old term. -/
def kernelStageProjectionXIsoOfNe
    (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0)
    (n : ℤ) (hn : n ≠ c) : (kernel (stageProjection A s L c b h)).X n ≅ L.X n := by
  letI : PreservesLimit (parallelPair (stageProjection A s L c b h) 0)
    (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n) := inferInstance
  exact PreservesKernel.iso (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n)
    (stageProjection A s L c b h) ≪≫
    kernelIsoOfEq (stageProjection_f_of_ne A s L c b h n hn) ≪≫
    kernelZeroIsoSource

/-- Evaluation of the improved kernel at degree `c` is the coordinate kernel. -/
def kernelStageProjectionXIsoC
    (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0) :
    (kernel (stageProjection A s L c b h)).X c ≅
      ModuleCat.of A (LinearMap.ker (tailMap b s)) := by
  letI : PreservesLimit (parallelPair (stageProjection A s L c b h) 0)
    (HomologicalComplex.eval (ModuleCat A) (.up ℤ) c) := inferInstance
  exact PreservesKernel.iso (HomologicalComplex.eval (ModuleCat A) (.up ℤ) c)
    (stageProjection A s L c b h) ≪≫
    kernelIsoOfEq (stageProjection_f_c A s L c b h) ≪≫
    kernelCompMono (ModuleCat.ofHom (tailMap b s)) (stageEvalIso A s c).inv ≪≫
    ModuleCat.kernelIsoKer (ModuleCat.ofHom (tailMap b s))

/-- The degree-`c` kernel is finite free on the exceptional index set. -/
def kernelStageProjectionCEquiv
    (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0) :
    (kernel (stageProjection A s L c b h)).X c ≃ₗ[A] (s →₀ A) :=
  (kernelStageProjectionXIsoC A s L c b h).toLinearEquiv ≪≫ₗ
    kernelTailMapEquivFinsupp b s

lemma moduleFinite_kernelStageProjection_c
    (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0) :
    Module.Finite A ((kernel (stageProjection A s L c b h)).X c) := by
  letI : Finite s := Finite.of_fintype s
  exact Module.Finite.equiv (kernelStageProjectionCEquiv A s L c b h).symm

lemma moduleFree_kernelStageProjection_c
    (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0) :
    Module.Free A ((kernel (stageProjection A s L c b h)).X c) :=
  Module.Free.of_equiv (kernelStageProjectionCEquiv A s L c b h).symm

lemma moduleFinite_kernelStageProjection_of_ne
    (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0)
    (n : ℤ) (hn : n ≠ c) [Module.Finite A (L.X n)] :
    Module.Finite A ((kernel (stageProjection A s L c b h)).X n) :=
  Module.Finite.equiv (kernelStageProjectionXIsoOfNe A s L c b h n hn).toLinearEquiv.symm

lemma moduleFree_kernelStageProjection_of_ne
    (h : L.d (c - 1) c ≫ stageProjectionMap A s L c b = 0)
    (n : ℤ) (hn : n ≠ c) [Module.Free A (L.X n)] :
    Module.Free A ((kernel (stageProjection A s L c b h)).X n) :=
  Module.Free.of_equiv (kernelStageProjectionXIsoOfNe A s L c b h n hn).toLinearEquiv.symm

end
end RelativeFM.Stacks07LT.M4

#print axioms RelativeFM.Stacks07LT.M4.stageProjection
#print axioms RelativeFM.Stacks07LT.M4.stageProjectionShortComplex_shortExact
#print axioms RelativeFM.Stacks07LT.M4.kernelStageProjectionCEquiv
#print axioms RelativeFM.Stacks07LT.M4.moduleFinite_kernelStageProjection_c
#print axioms RelativeFM.Stacks07LT.M4.moduleFree_kernelStageProjection_c
