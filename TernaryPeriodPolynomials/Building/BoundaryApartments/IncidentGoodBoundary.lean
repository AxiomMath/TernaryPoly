module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.Boundary

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

theorem goodFlag_inverse_iff (side : Side) (matrix : rationalLevel) (flag : Flags side) :
    GoodFlag side (matrix.val⁻¹ • flag) ↔ GoodFlag side flag := by
  constructor
  · intro inverse_good
    have translated := goodFlag_translate side matrix (matrix.val⁻¹ • flag) inverse_good
    simpa only [smul_inv_smul] using translated
  · exact goodFlag_translate side matrix⁻¹ flag

def incidentGoodCochain {degree : ℕ} (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (paths : rationalLevel → EdgeChains) : EdgeCochains degree trivialCharacter 1 := by
  classical
  refine ⟨fun vertices edge => if GoodFlag .plane (endpoint .plane edge) then
    (goodFlagCochain functional paths .plane).val vertices (endpoint .plane edge)
    else (goodFlagCochain functional paths .line).val vertices (endpoint .line edge), ?_⟩
  intro matrix vertices
  funext edge
  change (if GoodFlag .plane (endpoint .plane edge) then
      (goodFlagCochain functional paths .plane).val (fun index => matrix.val * vertices index)
        (endpoint .plane edge)
      else (goodFlagCochain functional paths .line).val (fun index => matrix.val * vertices index)
        (endpoint .line edge)) =
    rationalCoefficientComponent degree trivialCharacter matrix.val
      (if GoodFlag .plane (endpoint .plane (matrix.val⁻¹ • edge)) then
        (goodFlagCochain functional paths .plane).val vertices
          (endpoint .plane (matrix.val⁻¹ • edge))
      else (goodFlagCochain functional paths .line).val vertices
        (endpoint .line (matrix.val⁻¹ • edge)))
  rw [endpoint_translate, goodFlag_inverse_iff]
  by_cases plane_good : GoodFlag .plane (endpoint .plane edge)
  · rw [ite_eq_left plane_good, ite_eq_left plane_good]
    exact congrFun ((goodFlagCochain functional paths .plane).property matrix vertices)
      (endpoint .plane edge)
  · rw [ite_eq_right plane_good, ite_eq_right plane_good, endpoint_translate]
    exact congrFun ((goodFlagCochain functional paths .line).property matrix vertices)
      (endpoint .line edge)

theorem incidentGoodCochain_differential {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_good : IsPathFamily paths)
    (vertices : Fin 3 → RationalGL3) (edge : Edges)
    (incident_good : GoodFlag .plane (endpoint .plane edge) ∨
      GoodFlag .line (endpoint .line edge)) :
    (differentialOne rationalLevel
      (functionRepresentation (rationalCoefficientComponent degree trivialCharacter) Edges)
      (incidentGoodCochain functional paths)).val vertices edge =
        (pathCocycle functional_property paths_good).val.val vertices := by
  classical
  by_cases plane_good : GoodFlag .plane (endpoint .plane edge)
  · change (incidentGoodCochain functional paths).val ![vertices 1, vertices 2] edge -
        (incidentGoodCochain functional paths).val ![vertices 0, vertices 2] edge +
        (incidentGoodCochain functional paths).val ![vertices 0, vertices 1] edge = _
    simp only [incidentGoodCochain, ite_eq_left plane_good]
    exact goodFlagCochain_differential functional_property paths_good .plane vertices
      (endpoint .plane edge) plane_good
  · have line_good : GoodFlag .line (endpoint .line edge) := incident_good.resolve_left plane_good
    change (incidentGoodCochain functional paths).val ![vertices 1, vertices 2] edge -
        (incidentGoodCochain functional paths).val ![vertices 0, vertices 2] edge +
        (incidentGoodCochain functional paths).val ![vertices 0, vertices 1] edge = _
    simp only [incidentGoodCochain, ite_eq_right plane_good]
    exact goodFlagCochain_differential functional_property paths_good .line vertices
      (endpoint .line edge) line_good

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
