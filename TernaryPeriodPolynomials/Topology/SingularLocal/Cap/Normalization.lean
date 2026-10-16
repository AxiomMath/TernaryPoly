module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.NormalizationEuclidean
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.NormalizationDescent
public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Tensor
public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.HomComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCapNormalization
open CategoryTheory Limits
open SingularLocalConstant SingularLocalCap SingularLocalCompactCap SingularLocalSupport
open EuclideanCompactClasses

attribute [local instance] euclideanAction euclideanContinuousAction euclideanFreeAction euclideanCoverFact

/-- The actual top-degree compact cap on Euclidean space, followed by the actual
augmentation isomorphism, is precisely evaluation on the fixed compact-subset fundamental
class. This is an equality of the existing geometric cap and the uniquely descended literal
V-valued evaluation, for every rational module and every actual cohomology class. -/
theorem euclidean_top_cap_normalization (n : ℕ) (V : ModuleCat.{0} ℚ)
    (K : Set (EuclideanSpace ℝ (Fin (n+2)))) (hK : IsCompact K)
    (x : (supportCochains (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin (n+2)))))
      (constantRep V) K).homology (n+2)) :
    (euclideanAugmentationIso n V).hom
      (supportCapHomology (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin (n+2)))))
        (constantRep V) K (n+2) 0 x (compactGenerator n K hK)) =
      supportHomologyEvaluation (TopCat.of (EuclideanSpace ℝ (Fin (n+2)))) V K (n+2)
        x (compactGenerator n K hK) :=
  supportCapHomology_evaluation_classes (TopCat.of (EuclideanSpace ℝ (Fin (n+2))))
    V K (n+2) x (compactGenerator n K hK)

/-- On a contractible space, both actual constant-coefficient comparisons and the
literal homology augmentation are available without restricting the dimension of V. -/
theorem contractible_constant_comparison (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)
    [ContractibleSpace X] :
    Nonempty (chains X V ≅ tensorChains X V) ∧
      Nonempty (cochains X V ≅ homCochains X V) ∧
      IsIso (augmentation X V) ∧ ∀ n : ℕ, n ≠ 0 → IsZero ((chains X V).homology n) :=
  ⟨⟨localTensorChainIso X V⟩, ⟨homCochainIso X V⟩, augmentation_isIso X V,
    homology_isZero X V⟩

end TernaryPoly.SingularLocalCapNormalization
