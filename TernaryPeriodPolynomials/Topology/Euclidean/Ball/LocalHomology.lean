module

public import TernaryPeriodPolynomials.Topology.Euclidean.Ball.LocalRadial
public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionAlgebra
public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanBallLocal
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology RationalRelativeSingular
open RationalSingularAugmentation EuclideanLocalHomology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The genuine closed-ball relative chains use the literal complement of the closed ball. -/
abbrev ballRelativeChains (x : E) (r : ℝ) := relativeChains (exterior x r)

/-- The exterior avoids every point of the closed ball. -/
theorem exterior_avoids (x y : E) (r : ℝ) (hy : y ∈ Metric.closedBall x r) :
    exterior x r ⊆ ({y}ᶜ : Set E) := by
  intro z hz he
  exact hz (he ▸ hy)

/-- The actual point-projection map from closed-ball relative chains. -/
def ballPointMap (x : E) (r : ℝ) (y : E) (hy : y ∈ Metric.closedBall x r) :
    ballRelativeChains x r ⟶ localChainsAt d y :=
  relativeMap (ContinuousMap.id E) (exterior x r) {y}ᶜ (exterior_avoids x y r hy)

/-- The exact cokernel projection square for the actual point map. -/
theorem ballPointMap_projection (x : E) (r : ℝ) (y : E) (hy : y ∈ Metric.closedBall x r) :
    cokernel.π (inclusion (exterior x r)) ≫ ballPointMap x r y hy =
      cokernel.π (inclusion ({y}ᶜ : Set E)) := by
  simp [ballPointMap, relativeMap, cokernel.map, chainMap]

/-- The literal exterior inclusion is a quasi-isomorphism on actual rational singular chains. -/
theorem exteriorInclusion_quasiIso (x : E) (r : ℝ) (hr : 0 < r) :
    QuasiIso (chainMap (exteriorInclusion x r hr)) := by
  change QuasiIso (chainHomotopyEquiv (exteriorHomotopyEquiv x r hr)).hom
  infer_instance

/-- The actual relative point map at the center is a quasi-isomorphism in all degrees. -/
theorem ballPointMap_center_quasiIso (x : E) (r : ℝ) (hr : 0 < r) :
    QuasiIso (ballPointMap x r x (Metric.mem_closedBall_self hr.le)) := by
  have hsource : QuasiIso (chainMap (subspaceMap (ContinuousMap.id E)
      (exterior x r) ({x}ᶜ : Set E) (exterior_avoids x x r (Metric.mem_closedBall_self hr.le)))) :=
    exteriorInclusion_quasiIso x r hr
  have htarget : QuasiIso (chainMap (ContinuousMap.id E)) := by
    change QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (𝟙 (TopCat.of E)))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  exact @RelativeExcisionAlgebra.cokernel_map_quasiIso _ _ _ _
    (inclusion (exterior x r)) (inclusion ({x}ᶜ : Set E)) inferInstance inferInstance
    (chainMap (subspaceMap (ContinuousMap.id E) (exterior x r) {x}ᶜ
      (exterior_avoids x x r (Metric.mem_closedBall_self hr.le))))
    (chainMap (ContinuousMap.id E))
    (inclusion_naturality (ContinuousMap.id E) (exterior x r) {x}ᶜ
      (exterior_avoids x x r (Metric.mem_closedBall_self hr.le))) hsource htarget

/-- The actual ball-to-center point map gives a homology isomorphism in every degree. -/
def ballHomologyIso (x : E) (r : ℝ) (hr : 0 < r) (k : ℕ) :
    (ballRelativeChains x r).homology k ≅ (localChainsAt d x).homology k := by
  have := ballPointMap_center_quasiIso x r hr
  exact asIso (homologyMap (ballPointMap x r x (Metric.mem_closedBall_self hr.le)) k)

/-- The ball homology comparison is induced by the literal relative pair map. -/
theorem ballHomologyIso_hom (x : E) (r : ℝ) (hr : 0 < r) (k : ℕ) :
    (ballHomologyIso x r hr k).hom =
      homologyMap (ballPointMap x r x (Metric.mem_closedBall_self hr.le)) k := rfl

/-- Actual relative homology supported on a closed Euclidean ball vanishes away from top degree. -/
theorem ballHomology_isZero (n k : ℕ) (x : EuclideanSpace ℝ (Fin (n+2)))
    (r : ℝ) (hr : 0 < r) (hk : k ≠ n+2) : IsZero ((ballRelativeChains x r).homology k) :=
  (localAt_isZero_of_ne n k x hk).of_iso (ballHomologyIso x r hr k)

end TernaryPoly.EuclideanBallLocal
