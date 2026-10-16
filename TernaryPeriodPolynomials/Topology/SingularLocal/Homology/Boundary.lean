module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Transport

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory FreeActionLinearization CoveringSingularOrbits
open scoped Classical Simplicial

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep ℚ G)

/-- Push an actual geometric chain to a reparametrized simplex, transporting its coefficient
from the original first vertex to the reparametrized first vertex along the reversed simplex path. -/
def faceMap {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)), Convexity.StdSimplex ℝ (Fin (n+1)))) :
    VertexChain p hp V n →ₗ[ℚ] VertexChain p hp V m :=
  DFinsupp.lsum ℚ (fun σ => (DFinsupp.lsingle (pullSimplex θ σ)).comp
    (coefficientTransportLinear p hp (simplexPullPath θ σ).symm))

omit [ContinuousConstSMul G E] in
/-- The elementary geometric face formula uses the actual coefficient fiber and reversed path. -/
theorem faceMap_single {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)), Convexity.StdSimplex ℝ (Fin (n+1))))
    (σ : SingularSimplex B n) (c : FiberCoefficient p hp V (atVertex σ)) :
    faceMap p hp V θ (DFinsupp.single σ c) =
      DFinsupp.single (pullSimplex θ σ)
        (coefficientTransportLinear p hp (simplexPullPath θ σ).symm c) := by
  simp only [faceMap, DFinsupp.lsum_single, LinearMap.comp_apply, DFinsupp.lsingle_apply]

/-- The genuine geometric local-coefficient singular boundary is the alternating sum of
actual face simplices with coefficients transported backwards along simplexPullPath. -/
def boundary (n : ℕ) : VertexChain p hp V (n+1) →ₗ[ℚ] VertexChain p hp V n :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • faceMap p hp V (simplexCoface n i)

omit [ContinuousConstSMul G E] in
/-- The boundary of a geometric elementary chain, with its exact coefficient convention. -/
theorem boundary_single (n : ℕ) (σ : SingularSimplex B (n+1))
    (c : FiberCoefficient p hp V (atVertex σ)) :
    boundary p hp V n (DFinsupp.single σ c) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        DFinsupp.single (pullSimplex (simplexCoface n i) σ)
          (coefficientTransportLinear p hp (simplexPullPath (simplexCoface n i) σ).symm c) := by
  simp only [boundary, LinearMap.sum_apply, LinearMap.smul_apply, faceMap_single]

variable [IsCancelSMul G E]

/-- Under the degreewise inverse, the geometric reparametrized chain is the literal lifted
reparametrized singular generator, with unchanged coefficient at the lifted original vertex. -/
theorem degreeEquiv_symm_face_single {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)), Convexity.StdSimplex ℝ (Fin (n+1))))
    {σ : SingularSimplex B n} (τ : Lifts p σ)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    (degreeEquiv p hp V m).symm (faceMap p hp V θ (DFinsupp.single σ c)) =
      generator G E V m (pullSimplex θ τ.val) (c.val (liftVertexEquiv p hp σ τ)) := by
  rw [faceMap_single, degreeEquiv_symm_single_lift p hp V m (pullLift p θ τ),
    backwardTransport_lift]
  rfl

/-- On each geometric elementary chain, the inverse identification intertwines the actual
transported-face boundary with the actual coinvariant singular boundary. -/
theorem degreeEquiv_symm_boundary_single (n : ℕ) (σ : SingularSimplex B (n+1))
    (c : FiberCoefficient p hp V (atVertex σ)) :
    (degreeEquiv p hp V n).symm (boundary p hp V n (DFinsupp.single σ c)) =
      (coinvariantChains G E V).d (n+1) n
        ((degreeEquiv p hp V (n+1)).symm (DFinsupp.single σ c)) := by
  let τ := chosenLift p hp (n+1) σ
  rw [degreeEquiv_symm_single_lift p hp V (n+1) τ, generator_boundary]
  simp only [boundary, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun v => (-1 : ℤ)^i.val • v)
    (degreeEquiv_symm_face_single p hp V (simplexCoface n i) τ c)

/-- The degreewise actual geometric identification intertwines the two differentials linearly. -/
theorem degreeEquiv_symm_boundary (n : ℕ) :
    (degreeEquiv p hp V n).symm.toLinearMap.comp (boundary p hp V n) =
      ((coinvariantChains G E V).d (n+1) n).hom.comp
        (degreeEquiv p hp V (n+1)).symm.toLinearMap := by
  apply DFinsupp.lhom_ext
  exact degreeEquiv_symm_boundary_single p hp V n

end TernaryPoly.SingularLocalHomology
