module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportQuotient
public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionNaturality
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

variable {X : Type} [TopologicalSpace X]

/-- Supported singular chains intersect literally on the intersection of their supports. -/
theorem supported_inter (U V : Set X) (n : ℕ) :
    subChainSubmodule ℚ (TopCat.of X) (U ∩ V) n =
      subChainSubmodule ℚ (TopCat.of X) U n ⊓ subChainSubmodule ℚ (TopCat.of X) V n := by
  classical
  apply le_antisymm
  · exact le_inf (subChainSubmodule_mono Set.inter_subset_left n)
      (subChainSubmodule_mono Set.inter_subset_right n)
  · intro c hc
    have hk := keepHom_mem_subChainSubmodule (R := ℚ) (X := TopCat.of X) (S := U) hc.2
    rwa [keepHom_eq_self_of_mem hc.1] at hk

/-- The literal inclusion of supported chains into full chains. -/
def supportedInclusion (U : Set X) : subChainComplex ℚ (TopCat.of X) U ⟶ chains X where
  f n := ModuleCat.ofHom (subChainSubmodule ℚ (TopCat.of X) U n).subtype
  comm' i j hij := by
    obtain ⟨k, rfl⟩ := hij
    rw [subChainComplex_d]
    rfl

instance supportedInclusion_mono (U : Set X) : Mono (supportedInclusion U) := by
  apply mono_of_mono_f
  intro n
  exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The signed inclusion of intersection-supported chains. -/
def supportedDiagonal (U V : Set X) :
    subChainComplex ℚ (TopCat.of X) (U ∩ V) ⟶
      subChainComplex ℚ (TopCat.of X) U ⊞ subChainComplex ℚ (TopCat.of X) V :=
  biprod.lift (subChainInclusion _ _ Set.inter_subset_left)
    (-(subChainInclusion _ _ Set.inter_subset_right))

/-- The literal sum of the two supported-chain inclusions. -/
def supportedSum (U V : Set X) :
    subChainComplex ℚ (TopCat.of X) U ⊞ subChainComplex ℚ (TopCat.of X) V ⟶ chains X :=
  biprod.desc (supportedInclusion U) (supportedInclusion V)

/-- The signed intersection inclusion is annihilated by the literal sum. -/
theorem supportedDiagonal_sum (U V : Set X) : supportedDiagonal U V ≫ supportedSum U V = 0 := by
  rw [supportedDiagonal, supportedSum, biprod.lift_desc, Preadditive.neg_comp]
  have h : subChainInclusion (R := ℚ) (X := TopCat.of X) (U ∩ V) U Set.inter_subset_left ≫
      supportedInclusion U = subChainInclusion _ _ Set.inter_subset_right ≫ supportedInclusion V := by
    ext n c
    rfl
  rw [h, add_neg_cancel]

/-- The actual supported-chain short complex, before restricting its sum to its image. -/
def supportedRow (U V : Set X) : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ) :=
  ShortComplex.mk (supportedDiagonal U V) (supportedSum U V) (supportedDiagonal_sum U V)

/-- Evaluation of biproduct lifts preserves their two actual components. -/
theorem module_biprodEval_lift {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (a : K ⟶ L) (b : K ⟶ M) (n : ℕ) :
    (biprod.lift a b).f n ≫ (biprodXIso L M n).hom = biprod.lift (a.f n) (b.f n) := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprodXIso_hom_fst, biprod.lift_fst]
    exact congrArg (fun f => f.f n) (biprod.lift_fst a b)
  · rw [Category.assoc, biprodXIso_hom_snd, biprod.lift_snd]
    exact congrArg (fun f => f.f n) (biprod.lift_snd a b)

/-- Evaluation of biproduct sum maps preserves their actual components. -/
theorem module_biprodEval_desc {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (a : L ⟶ K) (b : M ⟶ K) (n : ℕ) :
    (biprodXIso L M n).inv ≫ (biprod.desc a b).f n = biprod.desc (a.f n) (b.f n) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, inl_biprodXIso_inv, biprod.inl_desc]
    exact congrArg (fun f => f.f n) (biprod.inl_desc a b)
  · rw [← Category.assoc, inr_biprodXIso_inv, biprod.inr_desc]
    exact congrArg (fun f => f.f n) (biprod.inr_desc a b)

end TernaryPoly.RationalRelativeSupport
