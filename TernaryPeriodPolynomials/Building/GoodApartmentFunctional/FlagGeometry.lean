module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.FrameOrbit

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry

noncomputable section

def standardSubspace (side : Side) : Submodule ℚ (Fin 3 → ℚ) where
  carrier := {coordinates | match side with
    | .plane => coordinates 2 = 0
    | .line => coordinates 1 = 0 ∧ coordinates 2 = 0}
  zero_mem' := by cases side <;> simp
  add_mem' := by cases side <;> intro first second firstAllowed secondAllowed <;>
    simp_all
  smul_mem' := by cases side <;> intro scalar coordinates allowed <;> simp_all

def frameSubspace (side : Side) (frame : RationalGL3) : Submodule ℚ (Fin 3 → ℚ) :=
  (standardSubspace side).map frame.val.mulVecLin

theorem mem_frameSubspace (side : Side) (frame : RationalGL3) (vector : Fin 3 → ℚ) :
    vector ∈ frameSubspace side frame ↔
      ∃ coordinates : Fin 3 → ℚ, coordinates ∈ standardSubspace side ∧
        frame.val *ᵥ coordinates = vector := by
  rfl

theorem parabolic_preserves_standard (side : Side) (frame : RationalGL3)
    (parabolicMembership : frame ∈ parabolic side) (coordinates : Fin 3 → ℚ)
    (allowed : coordinates ∈ standardSubspace side) :
    frame.val *ᵥ coordinates ∈ standardSubspace side := by
  cases side with
  | plane =>
    change InPlaneParabolic frame at parabolicMembership
    change coordinates 2 = 0 at allowed
    change (frame.val *ᵥ coordinates) 2 = 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, parabolicMembership.1,
      parabolicMembership.2, allowed]
  | line =>
    change InLineParabolic frame at parabolicMembership
    change coordinates 1 = 0 ∧ coordinates 2 = 0 at allowed
    change (frame.val *ᵥ coordinates) 1 = 0 ∧ (frame.val *ᵥ coordinates) 2 = 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, parabolicMembership.1,
      parabolicMembership.2, allowed.1, allowed.2]

theorem frameSubspace_mul_parabolic (side : Side) (frame changeFrame : RationalGL3)
    (parabolicMembership : changeFrame ∈ parabolic side) :
    frameSubspace side (frame * changeFrame) = frameSubspace side frame := by
  ext vector
  rw [mem_frameSubspace, mem_frameSubspace]
  constructor
  · rintro ⟨coordinates, allowed, equality⟩
    refine ⟨changeFrame.val *ᵥ coordinates,
      parabolic_preserves_standard side changeFrame parabolicMembership coordinates allowed, ?_⟩
    rw [Matrix.mulVec_mulVec]
    exact equality
  · rintro ⟨coordinates, allowed, equality⟩
    refine ⟨changeFrame⁻¹.val *ᵥ coordinates,
      parabolic_preserves_standard side changeFrame⁻¹
        ((parabolic side).inv_mem parabolicMembership) coordinates allowed, ?_⟩
    rw [Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul, mul_inv_cancel_right]
    exact equality

def flagSubspace (side : Side) : Flags side → Submodule ℚ (Fin 3 → ℚ) :=
  Quotient.lift (s := QuotientGroup.leftRel (parabolic side)) (frameSubspace side) (by
    intro first second equivalent
    have parabolicMembership : first⁻¹ * second ∈ parabolic side :=
      (QuotientGroup.leftRel_apply (s := parabolic side)).mp equivalent
    have equality : first * (first⁻¹ * second) = second := mul_inv_cancel_left first second
    rw [← equality]
    exact (frameSubspace_mul_parabolic side first (first⁻¹ * second) parabolicMembership).symm)

theorem flagSubspace_mk (side : Side) (frame : RationalGL3) :
    flagSubspace side (QuotientGroup.mk frame) = frameSubspace side frame := rfl

theorem integralVectorInFlag_iff (side : Side) (flag : Flags side) (vector : Fin 3 → ℤ) :
    IntegralVectorInFlag side flag vector ↔
      (fun index => (vector index : ℚ)) ∈ flagSubspace side flag := by
  constructor
  · rintro ⟨frame, equality, coordinates, allowed, equation⟩
    rw [← equality, flagSubspace_mk, mem_frameSubspace]
    refine ⟨coordinates, ?_, equation⟩
    cases side <;> exact allowed
  · induction flag using Quotient.inductionOn with
    | h frame =>
      intro membership
      obtain ⟨coordinates, allowed, equation⟩ :=
        (mem_frameSubspace side frame _).mp membership
      refine ⟨frame, rfl, coordinates, ?_, equation⟩
      cases side <;> exact allowed

theorem goodFlag_iff (side : Side) (flag : Flags side) :
    GoodFlag side flag ↔
      ∃ vector : Fin 3 → ℤ, (fun index => (vector index : ℚ)) ∈ flagSubspace side flag ∧
        (vector 2 : ZMod 3) ≠ 0 := by
  simp only [GoodFlag, integralVectorInFlag_iff]

theorem standard_line_le_plane : standardSubspace .line ≤ standardSubspace .plane := by
  intro coordinates allowed
  exact allowed.2

theorem edge_subspace_incidence (edge : Edges) :
    flagSubspace .line (endpoint .line edge) ≤ flagSubspace .plane (endpoint .plane edge) := by
  induction edge using Quotient.inductionOn with
  | h frame =>
    exact Submodule.map_mono standard_line_le_plane

theorem good_plane_of_good_line (edge : Edges)
    (good : GoodFlag .line (endpoint .line edge)) :
    GoodFlag .plane (endpoint .plane edge) := by
  rw [goodFlag_iff] at good ⊢
  obtain ⟨vector, membership, nonzero⟩ := good
  exact ⟨vector, edge_subspace_incidence edge membership, nonzero⟩

theorem parabolic_of_preserves_standard (side : Side) (frame : RationalGL3)
    (preserves : ∀ coordinates ∈ standardSubspace side,
      frame.val *ᵥ coordinates ∈ standardSubspace side) : frame ∈ parabolic side := by
  have firstAllowed : Pi.single (0 : Fin 3) (1 : ℚ) ∈ standardSubspace side := by
    cases side <;> simp [standardSubspace]
  have first := preserves (Pi.single (0 : Fin 3) (1 : ℚ)) firstAllowed
  rw [Matrix.mulVec_single_one] at first
  cases side with
  | plane =>
    have secondAllowed : Pi.single (1 : Fin 3) (1 : ℚ) ∈ standardSubspace .plane := by
      simp [standardSubspace]
    have second := preserves (Pi.single (1 : Fin 3) (1 : ℚ)) secondAllowed
    rw [Matrix.mulVec_single_one] at second
    exact ⟨first, second⟩
  | line => exact first

theorem inverse_mulVec_mulVec (frame : RationalGL3) (vector : Fin 3 → ℚ) :
    frame⁻¹.val *ᵥ (frame.val *ᵥ vector) = vector := by
  rw [Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
    GeneralLinearGroup.coe_one, Matrix.one_mulVec]

theorem frameSubspace_eq_iff (side : Side) (first second : RationalGL3) :
    frameSubspace side first = frameSubspace side second ↔
      first⁻¹ * second ∈ parabolic side := by
  constructor
  · intro equality
    apply parabolic_of_preserves_standard
    intro coordinates allowed
    have membership : second.val *ᵥ coordinates ∈ frameSubspace side first := by
      rw [equality]
      exact ⟨coordinates, allowed, rfl⟩
    obtain ⟨firstCoordinates, firstAllowed, equation⟩ := membership
    change first.val *ᵥ firstCoordinates = second.val *ᵥ coordinates at equation
    have inverseEquation := congrArg (fun vector => first⁻¹.val *ᵥ vector) equation
    rw [inverse_mulVec_mulVec, Matrix.mulVec_mulVec,
      ← GeneralLinearGroup.coe_mul] at inverseEquation
    rw [← inverseEquation]
    exact firstAllowed
  · intro membership
    have cancellation : first * (first⁻¹ * second) = second := mul_inv_cancel_left first second
    rw [← cancellation]
    exact (frameSubspace_mul_parabolic side first (first⁻¹ * second) membership).symm

theorem flagSubspace_injective (side : Side) : Function.Injective (flagSubspace side) := by
  intro first second
  induction first using Quotient.inductionOn with
  | h firstFrame =>
    induction second using Quotient.inductionOn with
    | h secondFrame =>
      intro equality
      apply QuotientGroup.eq.mpr
      exact (frameSubspace_eq_iff side firstFrame secondFrame).mp equality

theorem flag_eq_iff_subspace_eq (side : Side) (first second : Flags side) :
    first = second ↔ flagSubspace side first = flagSubspace side second :=
  (flagSubspace_injective side).eq_iff.symm

theorem goodChain_iff_lines (chain : EdgeChains) :
    GoodChain chain ↔ ∀ edge ∈ chain.support, GoodFlag .line (endpoint .line edge) := by
  constructor
  · intro good edge supported
    exact (good edge supported).2
  · intro good edge supported
    exact ⟨good_plane_of_good_line edge (good edge supported), good edge supported⟩

def integerVectorMap : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℚ) where
  toFun vector index := vector index
  map_add' first second := by ext index; simp
  map_smul' scalar vector := by ext index; simp

def integralFlagLattice (side : Side) (flag : Flags side) : Submodule ℤ (Fin 3 → ℤ) :=
  ((flagSubspace side flag).restrictScalars ℤ).comap integerVectorMap

theorem mem_integralFlagLattice (side : Side) (flag : Flags side) (vector : Fin 3 → ℤ) :
    vector ∈ integralFlagLattice side flag ↔ IntegralVectorInFlag side flag vector :=
  (integralVectorInFlag_iff side flag vector).symm

theorem goodFlag_iff_lattice (side : Side) (flag : Flags side) :
    GoodFlag side flag ↔
      ∃ vector ∈ integralFlagLattice side flag, (vector 2 : ZMod 3) ≠ 0 := by
  simp only [GoodFlag, mem_integralFlagLattice]

theorem integralFlagLattice_saturated (side : Side) (flag : Flags side)
    (scalar : ℤ) (nonzero : scalar ≠ 0) (vector : Fin 3 → ℤ) :
    scalar • vector ∈ integralFlagLattice side flag ↔ vector ∈ integralFlagLattice side flag := by
  change (fun index => ((scalar * vector index : ℤ) : ℚ)) ∈ flagSubspace side flag ↔
    (fun index => (vector index : ℚ)) ∈ flagSubspace side flag
  simp only [Int.cast_mul]
  exact (flagSubspace side flag).smul_mem_iff (Int.cast_ne_zero.mpr nonzero : (scalar : ℚ) ≠ 0)

theorem edge_eq_of_endpoints_eq (first second : Edges)
    (planeEquality : endpoint .plane first = endpoint .plane second)
    (lineEquality : endpoint .line first = endpoint .line second) : first = second := by
  induction first using Quotient.inductionOn with
  | h firstFrame =>
    induction second using Quotient.inductionOn with
    | h secondFrame =>
      apply QuotientGroup.eq.mpr
      exact ⟨QuotientGroup.eq.mp planeEquality, QuotientGroup.eq.mp lineEquality⟩

def matrixVectorEquiv (frame : RationalGL3) : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ) where
  toFun := frame.val.mulVecLin
  invFun := frame⁻¹.val.mulVecLin
  left_inv vector := inverse_mulVec_mulVec frame vector
  right_inv vector := by
    change frame.val *ᵥ (frame⁻¹.val *ᵥ vector) = vector
    rw [Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul, mul_inv_cancel,
      GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  map_add' := frame.val.mulVecLin.map_add
  map_smul' := frame.val.mulVecLin.map_smul

def standardLineEquiv : standardSubspace .line ≃ₗ[ℚ] ℚ where
  toFun coordinates := coordinates.val 0
  invFun scalar := ⟨![scalar, 0, 0], ⟨rfl, rfl⟩⟩
  left_inv coordinates := by
    apply Subtype.ext
    ext index
    fin_cases index
    · rfl
    · exact coordinates.property.1.symm
    · exact coordinates.property.2.symm
  right_inv _scalar := rfl
  map_add' _first _second := rfl
  map_smul' _scalar _coordinates := rfl

def standardPlaneEquiv : standardSubspace .plane ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun coordinates := ![coordinates.val 0, coordinates.val 1]
  invFun coordinates := ⟨![coordinates 0, coordinates 1, 0], rfl⟩
  left_inv coordinates := by
    apply Subtype.ext
    ext index
    fin_cases index
    · rfl
    · rfl
    · exact coordinates.property.symm
  right_inv coordinates := by
    ext index
    fin_cases index <;> rfl
  map_add' _first _second := by ext index; fin_cases index <;> rfl
  map_smul' _scalar _coordinates := by ext index; fin_cases index <;> rfl

theorem standardSubspace_finrank (side : Side) :
    Module.finrank ℚ (standardSubspace side) = match side with
      | .plane => 2
      | .line => 1 := by
  cases side with
  | plane => simpa using standardPlaneEquiv.finrank_eq
  | line => simpa using standardLineEquiv.finrank_eq

theorem frameSubspace_finrank (side : Side) (frame : RationalGL3) :
    Module.finrank ℚ (frameSubspace side frame) = match side with
      | .plane => 2
      | .line => 1 := by
  change Module.finrank ℚ
    ((standardSubspace side).map (matrixVectorEquiv frame).toLinearMap) = _
  rw [LinearEquiv.finrank_map_eq, standardSubspace_finrank]

theorem flagSubspace_finrank (side : Side) (flag : Flags side) :
    Module.finrank ℚ (flagSubspace side flag) = match side with
      | .plane => 2
      | .line => 1 := by
  induction flag using Quotient.inductionOn with
  | h frame => cases side <;> exact frameSubspace_finrank _ frame

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry
