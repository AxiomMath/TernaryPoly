module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Upper.BorelPrimitive
public import TernaryPeriodPolynomials.Building.BoundaryApartments.IncidentGoodBoundary

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

def edgeArithmeticStabilizer (edge : Edges) : Subgroup RationalGL3 :=
  rationalLevel ⊓ MulAction.stabilizer RationalGL3 edge

def edgeOrbitBase (edge : Edges) : Edges :=
  (Quotient.mk (MulAction.orbitRel rationalLevel Edges) edge).out

theorem edgeOrbitBase_translate (matrix : rationalLevel) (edge : Edges) :
    edgeOrbitBase (matrix.val • edge) = edgeOrbitBase edge := by
  unfold edgeOrbitBase
  congr 1
  exact MulAction.orbitRel.Quotient.quotient_smul_eq (g := matrix) (a := edge)

theorem edgeOrbitTransport_exists (edge : Edges) :
    ∃ matrix : rationalLevel, matrix.val • edgeOrbitBase edge = edge := by
  have related : (MulAction.orbitRel rationalLevel Edges) edge (edgeOrbitBase edge) :=
    Quotient.exact (Quotient.out_eq
      (Quotient.mk (MulAction.orbitRel rationalLevel Edges) edge)).symm
  exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp related)

def edgeOrbitTransport (edge : Edges) : rationalLevel :=
  (edgeOrbitTransport_exists edge).choose

theorem edgeOrbitTransport_spec (edge : Edges) :
    (edgeOrbitTransport edge).val • edgeOrbitBase edge = edge :=
  (edgeOrbitTransport_exists edge).choose_spec

def assembledEdgePrimitive {degree : ℕ}
    (primitives : (edge : Edges) → cochains (edgeArithmeticStabilizer edge)
      (rationalCoefficientComponent degree trivialCharacter) 1) :
    EdgeCochains degree trivialCharacter 1 := by
  refine ⟨fun vertices edge =>
    rationalCoefficientComponent degree trivialCharacter (edgeOrbitTransport edge).val
      ((primitives (edgeOrbitBase edge)).val
        (fun index => (edgeOrbitTransport edge).val⁻¹ * vertices index)), ?_⟩
  intro matrix vertices
  funext edge
  let first := edgeOrbitTransport edge
  let second := edgeOrbitTransport (matrix.val⁻¹ • edge)
  have base_eq : edgeOrbitBase (matrix.val⁻¹ • edge) = edgeOrbitBase edge :=
    edgeOrbitBase_translate matrix⁻¹ edge
  have second_transport : second.val • edgeOrbitBase edge = matrix.val⁻¹ • edge := by
    rw [← base_eq]
    exact edgeOrbitTransport_spec _
  let correction : rationalLevel := first⁻¹ * matrix * second
  have fixes : correction.val • edgeOrbitBase edge = edgeOrbitBase edge := by
    change (first.val⁻¹ * matrix.val * second.val) • edgeOrbitBase edge = _
    rw [mul_smul, mul_smul, second_transport, smul_inv_smul]
    have first_transport := edgeOrbitTransport_spec edge
    change first.val • edgeOrbitBase edge = edge at first_transport
    simpa only [inv_smul_smul] using
      congrArg (fun point => first.val⁻¹ • point) first_transport.symm
  let stabilizer_element : edgeArithmeticStabilizer (edgeOrbitBase edge) :=
    ⟨correction.val, correction.property, fixes⟩
  have transformed :
      (fun index => first.val⁻¹ * (matrix.val * vertices index)) =
        (fun index => stabilizer_element.val * (second.val⁻¹ * vertices index)) := by
    funext index
    change first.val⁻¹ * (matrix.val * vertices index) =
      (first.val⁻¹ * matrix.val * second.val) * (second.val⁻¹ * vertices index)
    group
  change rationalCoefficientComponent degree trivialCharacter first.val
      ((primitives (edgeOrbitBase edge)).val
        (fun index => first.val⁻¹ * (matrix.val * vertices index))) =
    rationalCoefficientComponent degree trivialCharacter matrix.val
      (rationalCoefficientComponent degree trivialCharacter second.val
        ((primitives (edgeOrbitBase (matrix.val⁻¹ • edge))).val
          (fun index => second.val⁻¹ * vertices index)))
  rw [base_eq, transformed, (primitives (edgeOrbitBase edge)).property]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  change first.val * (first.val⁻¹ * matrix.val * second.val) = matrix.val * second.val
  group

theorem assembledEdgePrimitive_differential {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitives : (edge : Edges) → cochains (edgeArithmeticStabilizer edge)
      (rationalCoefficientComponent degree trivialCharacter) 1)
    (differential : ∀ edge vertices,
      (differentialOne (edgeArithmeticStabilizer edge)
        (rationalCoefficientComponent degree trivialCharacter) (primitives edge)).val vertices =
          cocycle.val.val vertices) (vertices : Fin 3 → RationalGL3) (edge : Edges) :
    (differentialOne rationalLevel
      (functionRepresentation (rationalCoefficientComponent degree trivialCharacter) Edges)
      (assembledEdgePrimitive primitives)).val vertices edge = cocycle.val.val vertices := by
  let matrix := edgeOrbitTransport edge
  have translated_pair (first second : RationalGL3) :
      (fun index => matrix.val⁻¹ * (![first, second] : Fin 2 → RationalGL3) index) =
        ![matrix.val⁻¹ * first, matrix.val⁻¹ * second] := by
    funext index
    fin_cases index <;> rfl
  change rationalCoefficientComponent degree trivialCharacter matrix.val
      ((primitives (edgeOrbitBase edge)).val
        (fun index => matrix.val⁻¹ * (![vertices 1, vertices 2] : Fin 2 → RationalGL3) index)) -
    rationalCoefficientComponent degree trivialCharacter matrix.val
      ((primitives (edgeOrbitBase edge)).val
        (fun index => matrix.val⁻¹ * (![vertices 0, vertices 2] : Fin 2 → RationalGL3) index)) +
    rationalCoefficientComponent degree trivialCharacter matrix.val
      ((primitives (edgeOrbitBase edge)).val
        (fun index => matrix.val⁻¹ * (![vertices 0, vertices 1] : Fin 2 → RationalGL3) index)) = _
  simp only [translated_pair, ← map_sub, ← map_add]
  have primitive_differential := differential (edgeOrbitBase edge)
    (fun index => matrix.val⁻¹ * vertices index)
  change (primitives (edgeOrbitBase edge)).val ![matrix.val⁻¹ * vertices 1, matrix.val⁻¹ * vertices 2] -
    (primitives (edgeOrbitBase edge)).val ![matrix.val⁻¹ * vertices 0, matrix.val⁻¹ * vertices 2] +
    (primitives (edgeOrbitBase edge)).val ![matrix.val⁻¹ * vertices 0, matrix.val⁻¹ * vertices 1] = _
    at primitive_differential
  rw [primitive_differential]
  have equivariance := cocycle.val.property matrix (fun index => matrix.val⁻¹ * vertices index)
  simpa only [mul_inv_cancel_left] using equivariance.symm

theorem innerBoundary_of_stabilizer_primitives {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitives_exist : ∀ edge, ∃ primitive : cochains (edgeArithmeticStabilizer edge)
      (rationalCoefficientComponent degree trivialCharacter) 1,
      ∀ vertices, (differentialOne (edgeArithmeticStabilizer edge)
        (rationalCoefficientComponent degree trivialCharacter) primitive).val vertices =
          cocycle.val.val vertices) :
    InnerBoundary degree trivialCharacter .line
      (globalCoordinates degree trivialCharacter cocycle).2 := by
  let primitives := fun edge => (primitives_exist edge).choose
  have differential := fun edge => (primitives_exist edge).choose_spec
  refine ⟨restrictionCocycle degree trivialCharacter .line cocycle, rfl,
    assembledEdgePrimitive primitives, ?_⟩
  intro vertices edge
  exact (assembledEdgePrimitive_differential cocycle primitives differential vertices edge).symm

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
