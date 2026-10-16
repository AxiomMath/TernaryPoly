module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.NormalizationSupport
public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.Classes

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCapNormalization
open CategoryTheory Limits
open SingularLocalConstant SingularLocalCap SingularLocalCompactCap SingularLocalSupport
open EuclideanCompactClasses

variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))
local notation "X" => TopCat.of E

local instance euclideanAction : MulAction Unit X := identityAction X
local instance euclideanContinuousAction : ContinuousConstSMul Unit X := identityContinuousAction X
local instance euclideanFreeAction : IsCancelSMul Unit X := identityFreeAction X
local instance euclideanCoverFact : Fact (IsQuotientCoveringMap (𝟙 X) Unit) := ⟨identityCover X⟩

/-- The actual augmentation on Euclidean constant-coefficient H0 is an isomorphism
for every rational module V. -/
def euclideanAugmentationIso (V : ModuleCat.{0} ℚ) : (chains X V).homology 0 ≅ V :=
  augmentationIso X V

/-- The fixed actual compact-subset fundamental class has a genuine relative singular cycle representative. -/
theorem compactGenerator_representative (K : Set E) (hK : IsCompact K) :
    ∃ c : Homology.Cycles ((RationalManifoldCompact.supportChains K).sc' (n+2+1) (n+2) (n+2-1)),
      Descent.chainClass _ (n+2) c = compactGenerator n K hK :=
  SingularLocalCompactCap.Algebra.chainClass_surjective _ _ _

/-- Top-degree cap with the fixed compact Euclidean fundamental class becomes literal
relative V-valued evaluation under the actual augmentation, for every cycle representative. -/
theorem compactGenerator_cap_evaluation (V : ModuleCat.{0} ℚ) (K : Set E) (hK : IsCompact K)
    (φ : Homology.Cycles ((supportCochains (𝟙 X) (constantRep V) K).sc' (n+2-1) (n+2) (n+2+1)))
    (c : Homology.Cycles ((RationalManifoldCompact.supportChains K).sc' (n+2+1) (n+2) (n+2-1)))
    (hc : Descent.chainClass _ (n+2) c = compactGenerator n K hK) :
    augmentation X V (supportCapHomology (𝟙 X) (constantRep V) K (n+2) 0
      (Descent.cochainClass _ (n+2) φ) (compactGenerator n K hK)) =
      supportEvaluation X V K (n+2) φ.val c.val := by
  rw [← hc]
  exact supportCapHomology_evaluation X V K (n+2) φ c

/-- The same normalization is evaluation on any ambient scalar chain representing the
fixed compact fundamental relative cycle; it uses the existing geometric cap unchanged. -/
theorem compactGenerator_cap_ambient_evaluation (V : ModuleCat.{0} ℚ) (K : Set E) (hK : IsCompact K)
    (φ : Homology.Cycles ((supportCochains (𝟙 X) (constantRep V) K).sc' (n+2-1) (n+2) (n+2+1)))
    (c : Homology.Cycles ((RationalManifoldCompact.supportChains K).sc' (n+2+1) (n+2) (n+2-1)))
    (hc : Descent.chainClass _ (n+2) c = compactGenerator n K hK)
    (z : (scalarChains X).X (n+2))
    (hz : (cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f (n+2) z = c.val) :
    augmentation X V (supportCapHomology (𝟙 X) (constantRep V) K (n+2) 0
      (Descent.cochainClass _ (n+2) φ) (compactGenerator n K hK)) =
      SingularLocalConstant.evaluation X V (n+2)
        ((supportInclusion (𝟙 X) (constantRep V) K).f (n+2) φ.val) z := by
  rw [← hc]
  exact supportCapHomology_ambient_evaluation X V K (n+2) φ c z hz

/-- Different genuine cycle representatives of the fixed compact class give identical
evaluations; normalization is an equality on actual homology, not a dimension count. -/
theorem compactGenerator_evaluation_independent (V : ModuleCat.{0} ℚ) (K : Set E) (hK : IsCompact K)
    (φ : Homology.Cycles ((supportCochains (𝟙 X) (constantRep V) K).sc' (n+2-1) (n+2) (n+2+1)))
    (c d : Homology.Cycles ((RationalManifoldCompact.supportChains K).sc' (n+2+1) (n+2) (n+2-1)))
    (hc : Descent.chainClass _ (n+2) c = compactGenerator n K hK)
    (hd : Descent.chainClass _ (n+2) d = compactGenerator n K hK) :
    supportEvaluation X V K (n+2) φ.val c.val = supportEvaluation X V K (n+2) φ.val d.val :=
  (compactGenerator_cap_evaluation n V K hK φ c hc).symm.trans
    (compactGenerator_cap_evaluation n V K hK φ d hd)

end TernaryPoly.SingularLocalCapNormalization
