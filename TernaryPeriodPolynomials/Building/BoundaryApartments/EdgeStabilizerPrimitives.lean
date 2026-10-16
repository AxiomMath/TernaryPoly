module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.EdgePrimitiveAssembly

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

def standardBadEdge : Edges := QuotientGroup.mk (1 : RationalGL3)

theorem standardBadEdge_stabilizer : edgeArithmeticStabilizer standardBadEdge =
    upperBorelSubgroup := by
  ext matrix
  change (matrix ∈ rationalLevel ∧ matrix • standardBadEdge = standardBadEdge) ↔
    matrix ∈ rationalLevel ∧ matrix ∈ parabolic .plane ⊓ parabolic .line
  constructor
  · rintro ⟨level, fixes⟩
    refine ⟨level, ?_⟩
    change (QuotientGroup.mk (matrix * 1) : Edges) = QuotientGroup.mk 1 at fixes
    have inverse_mem := QuotientGroup.eq.mp fixes
    simp only [mul_one] at inverse_mem
    simpa only [inv_inv] using (parabolic .plane ⊓ parabolic .line).inv_mem inverse_mem
  · rintro ⟨level, upper⟩
    refine ⟨level, ?_⟩
    change (QuotientGroup.mk (matrix * 1) : Edges) = QuotientGroup.mk 1
    apply QuotientGroup.eq.mpr
    simpa only [mul_one] using (parabolic .plane ⊓ parabolic .line).inv_mem upper

theorem edge_stabilizer_primitive_translate {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (edge : Edges) (matrix : rationalLevel)
    (primitive : cochains (edgeArithmeticStabilizer edge)
      (rationalCoefficientComponent degree trivialCharacter) 1)
    (differential : ∀ vertices, (differentialOne (edgeArithmeticStabilizer edge)
      (rationalCoefficientComponent degree trivialCharacter) primitive).val vertices =
        cocycle.val.val vertices) :
    ∃ translated : cochains (edgeArithmeticStabilizer (matrix.val • edge))
      (rationalCoefficientComponent degree trivialCharacter) 1,
      ∀ vertices, (differentialOne (edgeArithmeticStabilizer (matrix.val • edge))
        (rationalCoefficientComponent degree trivialCharacter) translated).val vertices =
          cocycle.val.val vertices := by
  let translated : cochains (edgeArithmeticStabilizer (matrix.val • edge))
      (rationalCoefficientComponent degree trivialCharacter) 1 :=
    ⟨fun vertices => rationalCoefficientComponent degree trivialCharacter matrix.val
      (primitive.val (fun index => matrix.val⁻¹ * vertices index)), by
      intro acting vertices
      have fixes : (matrix.val⁻¹ * acting.val * matrix.val) • edge = edge := by
        rw [mul_smul, mul_smul, acting.property.2, inv_smul_smul]
      let conjugate : edgeArithmeticStabilizer edge :=
        ⟨matrix.val⁻¹ * acting.val * matrix.val,
          rationalLevel.mul_mem
            (rationalLevel.mul_mem (rationalLevel.inv_mem matrix.property) acting.property.1)
            matrix.property, fixes⟩
      have vertices_eq :
          (fun index => matrix.val⁻¹ * (acting.val * vertices index)) =
            (fun index => conjugate.val * (matrix.val⁻¹ * vertices index)) := by
        funext index
        change matrix.val⁻¹ * (acting.val * vertices index) =
          (matrix.val⁻¹ * acting.val * matrix.val) * (matrix.val⁻¹ * vertices index)
        group
      dsimp only
      rw [vertices_eq, primitive.property]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      change matrix.val * (matrix.val⁻¹ * acting.val * matrix.val) = acting.val * matrix.val
      group⟩
  refine ⟨translated, ?_⟩
  intro vertices
  have translated_pair (first second : RationalGL3) :
      (fun index => matrix.val⁻¹ * (![first, second] : Fin 2 → RationalGL3) index) =
        ![matrix.val⁻¹ * first, matrix.val⁻¹ * second] := by
    funext index
    fin_cases index <;> rfl
  change rationalCoefficientComponent degree trivialCharacter matrix.val
      (primitive.val (fun index => matrix.val⁻¹ * (![vertices 1, vertices 2] : Fin 2 → RationalGL3) index)) -
    rationalCoefficientComponent degree trivialCharacter matrix.val
      (primitive.val (fun index => matrix.val⁻¹ * (![vertices 0, vertices 2] : Fin 2 → RationalGL3) index)) +
    rationalCoefficientComponent degree trivialCharacter matrix.val
      (primitive.val (fun index => matrix.val⁻¹ * (![vertices 0, vertices 1] : Fin 2 → RationalGL3) index)) = _
  simp only [translated_pair, ← map_sub, ← map_add]
  have primitive_differential := differential (fun index => matrix.val⁻¹ * vertices index)
  change primitive.val ![matrix.val⁻¹ * vertices 1, matrix.val⁻¹ * vertices 2] -
    primitive.val ![matrix.val⁻¹ * vertices 0, matrix.val⁻¹ * vertices 2] +
    primitive.val ![matrix.val⁻¹ * vertices 0, matrix.val⁻¹ * vertices 1] = _
    at primitive_differential
  rw [primitive_differential]
  have equivariance := cocycle.val.property matrix (fun index => matrix.val⁻¹ * vertices index)
  simpa only [mul_inv_cancel_left] using equivariance.symm

theorem incident_good_stabilizer_primitive {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    (edge : Edges)
    (incident_good : GoodFlag .plane (endpoint .plane edge) ∨
      GoodFlag .line (endpoint .line edge)) :
    ∃ primitive : cochains (edgeArithmeticStabilizer edge)
      (rationalCoefficientComponent degree trivialCharacter) 1,
      ∀ vertices, (differentialOne (edgeArithmeticStabilizer edge)
        (rationalCoefficientComponent degree trivialCharacter) primitive).val vertices =
          (pathCocycle functional_property specialPaths_isPathFamily).val.val vertices := by
  let primitive : cochains (edgeArithmeticStabilizer edge)
      (rationalCoefficientComponent degree trivialCharacter) 1 :=
    ⟨fun vertices => (incidentGoodCochain functional specialPaths).val vertices edge, by
      intro matrix vertices
      have equivariance := congrFun
        ((incidentGoodCochain functional specialPaths).property
          ⟨matrix.val, matrix.property.1⟩ vertices) edge
      have inverse_fixed : matrix.val⁻¹ • edge = edge := (matrix⁻¹).property.2
      change (incidentGoodCochain functional specialPaths).val
        (fun index => matrix.val * vertices index) edge =
        rationalCoefficientComponent degree trivialCharacter matrix.val
          ((incidentGoodCochain functional specialPaths).val vertices (matrix.val⁻¹ • edge))
        at equivariance
      simpa only [inverse_fixed] using equivariance⟩
  refine ⟨primitive, ?_⟩
  intro vertices
  exact incidentGoodCochain_differential functional_property specialPaths_isPathFamily
    vertices edge incident_good

theorem pathCocycle_inner_of_bad_edge_orbit
    (edge_orbits : ∀ edge : Edges,
      GoodFlag .plane (endpoint .plane edge) ∨ GoodFlag .line (endpoint .line edge) ∨
        ∃ matrix : rationalLevel, matrix.val • standardBadEdge = edge)
    {degree : ℕ} (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional) :
    InnerBoundary degree trivialCharacter .line
      (globalCoordinates degree trivialCharacter
        (pathCocycle functional_property specialPaths_isPathFamily)).2 := by
  let cocycle := pathCocycle functional_property specialPaths_isPathFamily
  apply innerBoundary_of_stabilizer_primitives cocycle
  intro edge
  rcases edge_orbits edge with plane_good | line_good | ⟨matrix, matrix_eq⟩
  · exact incident_good_stabilizer_primitive functional_property edge (Or.inl plane_good)
  · exact incident_good_stabilizer_primitive functional_property edge (Or.inr line_good)
  · have primitive_exists := upperBorel_exists_cochain degree_positive solution
      functional_property (pathCocycle_realizes functional_property specialPaths_isPathFamily)
    rw [← standardBadEdge_stabilizer] at primitive_exists
    obtain ⟨primitive, differential⟩ := primitive_exists
    rw [← matrix_eq]
    exact edge_stabilizer_primitive_translate cocycle standardBadEdge matrix primitive differential

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
