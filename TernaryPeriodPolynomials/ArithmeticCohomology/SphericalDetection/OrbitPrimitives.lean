module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Restriction

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

abbrev ArithmeticFlagOrbits (side : Side) :=
  MulAction.orbitRel.Quotient rationalLevel (Flags side)

def arithmeticFlagOrbit (side : Side) (flag : Flags side) : ArithmeticFlagOrbits side :=
  Quotient.mk _ flag

def arithmeticFlagRepresentative (side : Side) (flag : Flags side) : Flags side :=
  (arithmeticFlagOrbit side flag).out

theorem arithmeticFlagRepresentative_transporter (side : Side) (flag : Flags side) :
    ∃ element : rationalLevel,
      element.val • arithmeticFlagRepresentative side flag = flag := by
  have relation : MulAction.orbitRel rationalLevel (Flags side) flag
      (arithmeticFlagRepresentative side flag) :=
    Quotient.exact (Quotient.out_eq (arithmeticFlagOrbit side flag)).symm
  exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp relation)

def arithmeticFlagTransporter (side : Side) (flag : Flags side) : rationalLevel :=
  Classical.choose (arithmeticFlagRepresentative_transporter side flag)

theorem arithmeticFlagTransporter_smul (side : Side) (flag : Flags side) :
    (arithmeticFlagTransporter side flag).val •
      arithmeticFlagRepresentative side flag = flag :=
  Classical.choose_spec (arithmeticFlagRepresentative_transporter side flag)

theorem arithmeticFlagOrbit_smul (side : Side) (element : rationalLevel)
    (flag : Flags side) :
    arithmeticFlagOrbit side (element.val • flag) = arithmeticFlagOrbit side flag := by
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact MulAction.mem_orbit_iff.mpr ⟨element, rfl⟩

theorem arithmeticFlagRepresentative_smul (side : Side) (element : rationalLevel)
    (flag : Flags side) :
    arithmeticFlagRepresentative side (element.val • flag) =
      arithmeticFlagRepresentative side flag :=
  congrArg Quotient.out (arithmeticFlagOrbit_smul side element flag)

theorem cocycle_coboundary_of_flag_primitives {degree : ℕ}
    (character : RankOneCharacter) (side : Side)
    (cycle : MaximalCycles degree character side)
    (primitives : ∀ flag : Flags side,
      ∃ primitive : cochains (flagArithmeticStabilizer side flag)
          (rationalCoefficientComponent degree character) 1,
        differentialOne (flagArithmeticStabilizer side flag)
          (rationalCoefficientComponent degree character) primitive =
            (evaluateFlagCycle character side flag cycle).val) :
    ∃ primitive : MaximalCochains degree character side 1,
      differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        primitive = cycle.val := by
  classical
  let chosen := fun flag => Classical.choose (primitives flag)
  have chosen_differential := fun flag => Classical.choose_spec (primitives flag)
  let primitive_value := fun (vertices : Fin 2 → RationalGL3) (flag : Flags side) =>
    rationalCoefficientComponent degree character
      (arithmeticFlagTransporter side flag).val
      ((chosen (arithmeticFlagRepresentative side flag)).val
        (fun index => (arithmeticFlagTransporter side flag).val⁻¹ * vertices index))
  have primitive_equivariant : ∀ (element : rationalLevel) vertices,
      primitive_value (fun index => element.val * vertices index) =
        flagRepresentation (rationalCoefficientComponent degree character) side
          element.val (primitive_value vertices) := by
    intro element vertices
    funext flag
    let first := arithmeticFlagTransporter side flag
    let second := arithmeticFlagTransporter side (element.val⁻¹ • flag)
    have same_representative :
        arithmeticFlagRepresentative side (element.val⁻¹ • flag) =
          arithmeticFlagRepresentative side flag :=
      arithmeticFlagRepresentative_smul side element⁻¹ flag
    have first_transports : first.val • arithmeticFlagRepresentative side flag = flag :=
      arithmeticFlagTransporter_smul side flag
    have second_transports : second.val • arithmeticFlagRepresentative side flag =
        element.val⁻¹ • flag := by
      rw [← same_representative]
      exact arithmeticFlagTransporter_smul side (element.val⁻¹ • flag)
    let comparison : flagArithmeticStabilizer side
        (arithmeticFlagRepresentative side flag) :=
      ⟨first.val⁻¹ * element.val * second.val,
        ⟨rationalLevel.mul_mem (rationalLevel.mul_mem
          (rationalLevel.inv_mem first.property) element.property) second.property,
          MulAction.mem_stabilizer_iff.mpr (by
            rw [mul_smul, mul_smul, second_transports, smul_inv_smul,
              ← first_transports, inv_smul_smul]
            exact congrArg (arithmeticFlagRepresentative side) first_transports.symm)⟩⟩
    have equivariance := (chosen (arithmeticFlagRepresentative side flag)).property comparison
      (fun index => second.val⁻¹ * vertices index)
    have same_vertices :
        (fun index => comparison.val * (second.val⁻¹ * vertices index)) =
          (fun index => first.val⁻¹ * (element.val * vertices index)) := by
      funext index
      simp [comparison, mul_assoc]
    rw [same_vertices] at equivariance
    change rationalCoefficientComponent degree character first.val
        ((chosen (arithmeticFlagRepresentative side flag)).val
          (fun index => first.val⁻¹ * (element.val * vertices index))) =
      rationalCoefficientComponent degree character element.val
        (rationalCoefficientComponent degree character second.val
          ((chosen (arithmeticFlagRepresentative side (element.val⁻¹ • flag))).val
            (fun index => second.val⁻¹ * vertices index)))
    rw [same_representative, equivariance]
    have same_product : first.val * comparison.val = element.val * second.val := by
      change first.val * (first.val⁻¹ * element.val * second.val) = _
      simp only [mul_assoc, mul_inv_cancel_left]
    simpa only [map_mul, Module.End.mul_apply] using
      congrArg (fun matrix => rationalCoefficientComponent degree character matrix
        ((chosen (arithmeticFlagRepresentative side flag)).val
          (fun index => second.val⁻¹ * vertices index))) same_product
  refine ⟨⟨primitive_value, primitive_equivariant⟩, ?_⟩
  apply Subtype.ext
  funext vertices flag
  let transporter := arithmeticFlagTransporter side flag
  let representative := arithmeticFlagRepresentative side flag
  have boundary_value := congrArg
    (fun cochain : cochains (flagArithmeticStabilizer side representative)
      (rationalCoefficientComponent degree character) 2 =>
        cochain.val (fun index => transporter.val⁻¹ * vertices index))
    (chosen_differential representative)
  have cycle_equivariant := congrFun
    (cycle.val.property transporter
      (fun index => transporter.val⁻¹ * vertices index)) flag
  have transports_back : transporter.val⁻¹ • flag = representative := by
    rw [← arithmeticFlagTransporter_smul side flag, inv_smul_smul]
  have same_vertices :
      (fun index => transporter.val * (transporter.val⁻¹ * vertices index)) = vertices := by
    funext index
    simp
  change cycle.val.val
      (fun index => transporter.val * (transporter.val⁻¹ * vertices index)) flag =
    rationalCoefficientComponent degree character transporter.val
      (cycle.val.val (fun index => transporter.val⁻¹ * vertices index)
        (transporter.val⁻¹ • flag)) at cycle_equivariant
  rw [same_vertices, transports_back] at cycle_equivariant
  rw [cycle_equivariant]
  change rationalCoefficientComponent degree character transporter.val _ -
      rationalCoefficientComponent degree character transporter.val _ +
      rationalCoefficientComponent degree character transporter.val _ = _
  rw [← map_sub, ← map_add]
  have pair_transforms (first_index second_index : Fin 3) :
      (fun index : Fin 2 => transporter.val⁻¹ *
        ![vertices first_index, vertices second_index] index) =
        ![transporter.val⁻¹ * vertices first_index,
          transporter.val⁻¹ * vertices second_index] := by
    funext index
    fin_cases index <;> rfl
  simpa only [chosen, transporter, representative, differentialOne,
    evaluateFlagCycle, evaluateFlagCochain, LinearMap.coe_mk, AddHom.coe_mk,
    pair_transforms] using
    congrArg (rationalCoefficientComponent degree character transporter.val) boundary_value

theorem classOf_eq_zero_iff_all_flagRestrictions {degree : ℕ}
    (character : RankOneCharacter) (side : Side)
    (cycle : MaximalCycles degree character side) :
    classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) side) cycle = 0 ↔
      ∀ flag, flagRestriction character side flag
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree character) side) cycle) = 0 := by
  constructor
  · intro zero flag
    rw [zero, map_zero]
  · intro zero
    apply (classOf_eq_zero_iff _ _ _).mpr
    apply cocycle_coboundary_of_flag_primitives character side cycle
    intro flag
    exact (classOf_eq_zero_iff _ _ _).mp (zero flag)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
