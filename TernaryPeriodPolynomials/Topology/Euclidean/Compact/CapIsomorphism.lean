module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapCohomology

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanCompactCap
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalSupport SingularLocalCompactCap
open EuclideanLocalHomology
variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))
local notation "X" => TopCat.of E
local instance isoEuclideanAction : MulAction Unit X := identityAction X
local instance isoEuclideanContinuousAction : ContinuousConstSMul Unit X := identityContinuousAction X
local instance isoEuclideanFreeAction : IsCancelSMul Unit X := identityFreeAction X
local instance isoEuclideanCoverFact : Fact (IsQuotientCoveringMap (𝟙 X) Unit) := ⟨identityCover X⟩

/-- The actual Euclidean compact-support cap map in top cohomological degree is an
isomorphism, because its actual augmentation is the proved evaluation isomorphism. -/
theorem topCompactCap_isIso (V : ModuleCat.{0} ℚ) :
    IsIso (compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E) (euclideanOrientation n)
      (n+2) 0 (by omega)) := by
  have : IsIso (compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E) (euclideanOrientation n)
      (n+2) 0 (by omega) ≫ augmentation X V) := by
    change IsIso (compactTopEvaluationEquiv n V).toModuleIso.hom
    infer_instance
  exact IsIso.of_isIso_comp_right _ (augmentation X V)

/-- Actual compact-support cap is an isomorphism in every pair of complementary
nonnegative degrees on Euclidean space, for arbitrary rational coefficients. -/
theorem compactCap_isIso (V : ModuleCat.{0} ℚ) (a b : ℕ) (hab : a+b = n+2) :
    IsIso (compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E) (euclideanOrientation n)
      a b hab) := by
  let : ContractibleSpace X := inferInstanceAs (ContractibleSpace E)
  by_cases hb : b = 0
  · subst b
    have ha : a = n+2 := by omega
    subst a
    exact topCompactCap_isIso n V
  · exact (compactCohomology_isZero n V a (by omega)).isIso
      (homology_isZero X V b hb) _

/-- The Euclidean compact-support duality isomorphism has exactly the existing actual
cap map as its forward map. -/
def compactCapIso (V : ModuleCat.{0} ℚ) (a b : ℕ) (hab : a+b = n+2) :
    compactCohomology (𝟙 X) (constantRep V) a ≅
      (coveringLocalChains (𝟙 X) (constantRep V)).homology b := by
  have := compactCap_isIso n V a b hab
  exact asIso (compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E) (euclideanOrientation n) a b hab)

/-- Exact forward-map identity for the proved Euclidean duality isomorphism. -/
theorem compactCapIso_hom (V : ModuleCat.{0} ℚ) (a b : ℕ) (hab : a+b = n+2) :
    (compactCapIso n V a b hab).hom =
      compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E) (euclideanOrientation n) a b hab := rfl

end TernaryPoly.EuclideanCompactCap
