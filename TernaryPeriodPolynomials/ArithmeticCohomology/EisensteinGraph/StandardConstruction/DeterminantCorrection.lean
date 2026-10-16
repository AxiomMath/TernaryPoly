module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalSmith
public import Mathlib.Tactic.Group

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.DeterminantCorrection

def firstDiagonal {R : Type} [CommRing R] (unit : Rˣ) :
    GeneralLinearGroup (Fin 3) R :=
  RationalSmith.diagonalUnit ![unit, 1, 1]

theorem firstDiagonal_det {R : Type} [CommRing R] (unit : Rˣ) :
    GeneralLinearGroup.det (firstDiagonal unit) = unit := by
  rw [firstDiagonal, RationalSmith.diagonalUnit_det]
  simp [Fin.prod_univ_succ]

theorem map_firstDiagonal {R S : Type} [CommRing R] [CommRing S]
    (hom : R →+* S) (unit : Rˣ) :
    GeneralLinearGroup.map hom (firstDiagonal unit) =
      firstDiagonal (Units.map hom.toMonoidHom unit) := by
  rw [firstDiagonal, RationalSmith.map_diagonalUnit]
  congr 1
  funext index
  fin_cases index <;> simp

theorem firstDiagonal_one {R : Type} [CommRing R] :
    firstDiagonal (1 : Rˣ) = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  change Matrix.diagonal (fun index => (![1, 1, 1] : Fin 3 → Rˣ) index |>.val) row column =
    (1 : Matrix (Fin 3) (Fin 3) R) row column
  simp [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp
  fin_cases row <;> rfl

theorem reduced_conjugate (matrix : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (unit : IntegralAdelesˣ) (reduced : Units.map integralReduction.toMonoidHom unit = 1) :
    GeneralLinearGroup.map integralReduction (matrix * firstDiagonal unit * matrix⁻¹) = 1 := by
  rw [map_mul, map_mul, map_inv, map_firstDiagonal, reduced, firstDiagonal_one]
  simp

theorem conjugate_det {R : Type} [CommRing R]
    (matrix : GeneralLinearGroup (Fin 3) R) (unit : Rˣ) :
    GeneralLinearGroup.det (matrix * firstDiagonal unit * matrix⁻¹) = unit := by
  rw [map_mul, map_mul, map_inv, firstDiagonal_det]
  rw [mul_comm (GeneralLinearGroup.det matrix), mul_assoc, mul_inv_cancel, mul_one]

theorem finite_mem_of_reduction_one (matrix : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (reduced : GeneralLinearGroup.map integralReduction matrix = 1) :
    GeneralLinearGroup.map integralEmbedding matrix ∈ finiteLevel := by
  apply Subgroup.mem_map.mpr
  refine ⟨matrix, ?_, rfl⟩
  change GeneralLinearGroup.map integralReduction matrix ∈ rowStabilizer
  rw [reduced]
  exact rowStabilizer.one_mem

theorem corrections (representative : RationalGL3) (unit : IntegralAdelesˣ)
    (reduced : Units.map integralReduction.toMonoidHom unit = 1) :
    ∃ left right : GeneralLinearGroup (Fin 3) IntegralAdeles,
      GeneralLinearGroup.map integralReduction left = 1 ∧
      GeneralLinearGroup.map integralReduction right = 1 ∧
      GeneralLinearGroup.det left = unit ∧
      GeneralLinearGroup.det right = unit ∧
      GeneralLinearGroup.map integralEmbedding left * rationalFinite representative =
        rationalFinite representative * GeneralLinearGroup.map integralEmbedding right := by
  obtain ⟨left, right, entries, smith⟩ := RationalSmith.rational_smith representative
  let integralLeft := GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) left
  let integralRight := GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) right
  refine ⟨integralLeft * firstDiagonal unit * integralLeft⁻¹,
    integralRight * firstDiagonal unit * integralRight⁻¹,
    reduced_conjugate _ _ reduced, reduced_conjugate _ _ reduced,
    conjugate_det _ _, conjugate_det _ _, ?_⟩
  have leftEquality : GeneralLinearGroup.map integralEmbedding integralLeft =
      rationalFinite (GeneralLinearGroup.map (Int.castRingHom ℚ) left) :=
    (Comparison.integralFinite_integralMap left).symm
  have rightEquality : GeneralLinearGroup.map integralEmbedding integralRight =
      rationalFinite (GeneralLinearGroup.map (Int.castRingHom ℚ) right) :=
    (Comparison.integralFinite_integralMap right).symm
  rw [smith, map_mul, map_mul, map_inv]
  simp only [map_mul, map_inv, leftEquality, rightEquality]
  have commute : GeneralLinearGroup.map integralEmbedding (firstDiagonal unit) *
      rationalFinite (RationalSmith.diagonalUnit entries) =
        rationalFinite (RationalSmith.diagonalUnit entries) *
          GeneralLinearGroup.map integralEmbedding (firstDiagonal unit) := by
    change GeneralLinearGroup.map integralEmbedding (RationalSmith.diagonalUnit _) *
      GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (RationalSmith.diagonalUnit _) = _
    rw [RationalSmith.map_diagonalUnit, RationalSmith.map_diagonalUnit]
    simpa only [rationalFinite, firstDiagonal, RationalSmith.map_diagonalUnit] using
      RationalSmith.diagonalUnit_commute
      (fun index => Units.map integralEmbedding.toMonoidHom
        ((![unit, 1, 1] : Fin 3 → IntegralAdelesˣ) index))
      (fun index => Units.map (algebraMap ℚ FiniteAdeles).toMonoidHom (entries index))
  simp only [mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc (GeneralLinearGroup.map integralEmbedding (firstDiagonal unit)), commute]
  group

theorem residue_unit_lift (unit : (ZMod 3)ˣ) :
    ∃ sign : ℤˣ, Units.map (Int.castRingHom (ZMod 3)).toMonoidHom sign = unit := by
  have alternatives : ∀ value : ZMod 3, value ≠ 0 → value = 1 ∨ value = -1 := by decide
  rcases alternatives unit.val (Units.ne_zero unit) with positive | negative
  · refine ⟨1, ?_⟩
    apply Units.ext
    simpa using positive.symm
  · refine ⟨-1, ?_⟩
    apply Units.ext
    simpa using negative.symm

theorem reduce_integer_unit (unit : ℤˣ) :
    Units.map integralReduction.toMonoidHom
      (Units.map (Int.castRingHom IntegralAdeles).toMonoidHom unit) =
        Units.map (Int.castRingHom (ZMod 3)).toMonoidHom unit := by
  apply Units.ext
  change integralReduction (unit.val : IntegralAdeles) = (unit.val : ZMod 3)
  simp

theorem determinant_sign_representative (level : finiteLevel) (representative : RationalGL3) :
    ∃ approximant : GeneralLinearGroup (Fin 3) IntegralAdeles, ∃ sign : ℤˣ,
      GeneralLinearGroup.map integralEmbedding approximant ∈ finiteLevel ∧
      GeneralLinearGroup.det approximant = Units.map (Int.castRingHom IntegralAdeles).toMonoidHom sign ∧
      (rationalFinite representative)⁻¹ *
        ((GeneralLinearGroup.map integralEmbedding approximant)⁻¹ * level.val) *
          rationalFinite representative ∈ finiteLevel := by
  obtain ⟨integral, integralMembership, integralEquality⟩ := Subgroup.mem_map.mp level.property
  obtain ⟨sign, signEquality⟩ := residue_unit_lift
    (Units.map integralReduction.toMonoidHom (GeneralLinearGroup.det integral))
  let signUnit : IntegralAdelesˣ := Units.map (Int.castRingHom IntegralAdeles).toMonoidHom sign
  let unit := GeneralLinearGroup.det integral * signUnit⁻¹
  have reduced : Units.map integralReduction.toMonoidHom unit = 1 := by
    simp only [unit, signUnit, map_mul, map_inv, reduce_integer_unit, signEquality, mul_inv_cancel]
  obtain ⟨left, right, leftReduced, rightReduced, leftDet, _, commutation⟩ :=
    corrections representative unit reduced
  refine ⟨integral * left⁻¹, sign, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv, integralEquality]
    exact finiteLevel.mul_mem level.property
      (finiteLevel.inv_mem (finite_mem_of_reduction_one left leftReduced))
  · rw [map_mul, map_inv, leftDet]
    change GeneralLinearGroup.det integral *
      (GeneralLinearGroup.det integral * signUnit⁻¹)⁻¹ = signUnit
    simp only [_root_.mul_inv_rev, inv_inv]
    rw [← mul_assoc, mul_comm (GeneralLinearGroup.det integral), mul_assoc, mul_inv_cancel, mul_one]
  · rw [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, integralEquality]
    simp only [mul_assoc, inv_mul_cancel_left]
    rw [commutation, inv_mul_cancel_left]
    exact finite_mem_of_reduction_one right rightReduced

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.DeterminantCorrection
