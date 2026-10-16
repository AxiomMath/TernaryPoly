module

public import TernaryPeriodPolynomials.Topology.SingularLocal.DualityBasic
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Complex
public import TernaryPeriodPolynomials.Topology.Rational.Homology.Dual

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalDuality
open CategoryTheory HomologicalComplex FreeActionLinearization CoveringSingularOrbits
open SingularLocalCoefficient SingularLocalHomology
open scoped Classical

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

omit [ContinuousConstSMul G E] in
/-- The actual transported-face coboundary is adjoint to the actual backwards-transported
chain boundary, with identical alternating signs. -/
theorem degreeDuality_differential (n : ℕ) (φ : VertexCochain p hp (dualRepresentation V) n) :
    degreeDuality p hp V (n+1) (differential p hp (dualRepresentation V) n φ) =
      (degreeDuality p hp V n φ).comp (boundary p hp V n) := by
  apply DFinsupp.lhom_ext
  intro σ c
  rw [degreeDuality_single, LinearMap.comp_apply, boundary_single,
    map_sum, differential_apply]
  let ev : FiberCoefficient p hp (dualRepresentation V) (atVertex σ) →ₗ[ℚ] ℚ :=
    (LinearMap.applyₗ c).comp (dualCoefficientFiberEquiv (V := V) p hp (atVertex σ)).toLinearMap
  change ev (∑ i : Fin (n+2), (-1 : ℤ)^i.val •
    coefficientTransportLinear p hp (simplexPullPath (simplexCoface n i) σ)
      (φ (pullSimplex (simplexCoface n i) σ))) = _
  rw [map_sum]
  simp only [map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [degreeDuality_single]
  exact congrArg (fun q : ℚ => (-1 : ℤ)^i.val • q)
    (fiber_transport_adjoint p hp V (simplexPullPath (simplexCoface n i) σ) _ c)

variable [IsCancelSMul G E]

/-- The genuine geometric cochain complex with contragredient coefficients is canonically
isomorphic to the full linear-dual of the independently defined geometric chain complex. -/
def cochainDuality :
    localCochains p hp (dualRepresentation V) ≅
      RationalHomologyDual.dualCochains (localChains p hp V) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (degreeDuality p hp V n).toModuleIso) (fun i j hij => by
      obtain rfl : j = i+1 := hij.symm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      change ((RationalHomologyDual.dualCochains (localChains p hp V)).d i (i+1)).hom
        (degreeDuality p hp V i φ) =
        degreeDuality p hp V (i+1) (((localCochains p hp (dualRepresentation V)).d i (i+1)).hom φ)
      rw [RationalHomologyDual.dualCochains_d]
      simp only [localChains, ChainComplex.of_d, localCochains, CochainComplex.of_d]
      exact (degreeDuality_differential p hp V i φ).symm)

/-- Actual local-system cohomology with full-dual coefficients is the full dual of actual
local-system homology, without finite-dimensionality of chains or homology. -/
def universalCoefficientIso (n : ℕ) :
    (localCochains p hp (dualRepresentation V)).homology n ≅
      ModuleCat.of ℚ (Module.Dual ℚ ((localChains p hp V).homology n)) :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso (cochainDuality p hp V) ≪≫
    RationalHomologyDual.universalCoefficientIso (localChains p hp V) n

end TernaryPoly.SingularLocalDuality
