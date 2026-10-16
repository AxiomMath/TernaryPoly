module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.AwayThreeHeckeGoodCusps.Helpers

theorem int_ne_zero_of_mod_three {denominator : ℤ}
    (hn : (denominator : ZMod 3) ≠ 0) : (denominator : ℚ) ≠ 0 := by
  intro hz
  have he : denominator = 0 := Int.cast_injective hz
  exact hn (by simp [he])

theorem common_denominator {Index : Type} [Fintype Index]
    (values : Index → ℚ) (hint : ∀ index, IntegralAtThree (values index)) :
    ∃ denominator : ℤ, (denominator : ZMod 3) ≠ 0 ∧
      ∃ numerators : Index → ℤ, ∀ index,
        (denominator : ℚ) * values index = (numerators index : ℚ) := by
  classical
  choose numerator denominator hden hvalue using hint
  refine ⟨∏ index, denominator index, ?_,
    fun index => numerator index * ∏ other ∈ Finset.univ.erase index, denominator other, ?_⟩
  · simpa only [Int.cast_prod] using Finset.prod_ne_zero_iff.mpr (fun index _ => hden index)
  · intro index
    rw [← Finset.mul_prod_erase Finset.univ (fun other => denominator other)
      (Finset.mem_univ index), Int.cast_mul, hvalue index]
    have hn := int_ne_zero_of_mod_three (hden index)
    push_cast
    field_simp

def IntegralMatrixAtThree (element : RationalGL3) : Prop :=
  ∃ denominator : ℤ, (denominator : ZMod 3) ≠ 0 ∧
    ∃ numerator : Matrix (Fin 3) (Fin 3) ℤ,
      ∀ row column, (denominator : ℚ) * element.val row column = numerator row column

def LevelMatrixAtThree (element : RationalGL3) : Prop :=
  ∃ denominator : ℤ, (denominator : ZMod 3) ≠ 0 ∧
    ∃ numerator : Matrix (Fin 3) (Fin 3) ℤ,
      (∀ row column, (denominator : ℚ) * element.val row column = numerator row column) ∧
      ∀ column, (numerator 2 column : ZMod 3) =
        (denominator : ZMod 3) * (if column = 2 then 1 else 0)

theorem integral_matrix_of_entries (element : RationalGL3)
    (hint : ∀ row column, IntegralAtThree (element.val row column)) :
    IntegralMatrixAtThree element := by
  obtain ⟨denominator, hden, numerator, hnum⟩ :=
    common_denominator (fun index : Fin 3 × Fin 3 => element.val index.1 index.2)
      (fun index => hint index.1 index.2)
  exact ⟨denominator, hden, fun row column => numerator (row, column),
    fun row column => hnum (row, column)⟩

theorem level_matrix_of_entries (element : RationalGL3)
    (hint : ∀ row column, IntegralAtThree (element.val row column))
    (hrow : ∀ column, IntegralAtThree
      ((element.val 2 column - if column = 2 then 1 else 0) / 3)) :
    LevelMatrixAtThree element := by
  let values : (Fin 3 × Fin 3) ⊕ Fin 3 → ℚ := Sum.elim
    (fun index => element.val index.1 index.2)
    (fun column => (element.val 2 column - if column = 2 then 1 else 0) / 3)
  have hint' : ∀ index, IntegralAtThree (values index) := by
    intro index
    cases index with
    | inl index => exact hint index.1 index.2
    | inr column => exact hrow column
  obtain ⟨denominator, hden, numerator, hnum⟩ := common_denominator values hint'
  refine ⟨denominator, hden, fun row column => numerator (.inl (row, column)),
    fun row column => hnum (.inl (row, column)), ?_⟩
  intro column
  have hentry := hnum (.inl (2, column))
  have hratio := hnum (.inr column)
  change (denominator : ℚ) * element.val 2 column = _ at hentry
  change (denominator : ℚ) *
    ((element.val 2 column - if column = 2 then 1 else 0) / 3) = _ at hratio
  have he : numerator (.inl (2, column)) =
      denominator * (if column = 2 then 1 else 0) + 3 * numerator (.inr column) := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← hentry, ← hratio]
    split_ifs <;> ring
  change (numerator (.inl (2, column)) : ZMod 3) = _
  rw [he]
  push_cast
  have hthree : (3 : ZMod 3) = 0 := by decide
  simp only [hthree, zero_mul, add_zero]

theorem level_matrix_mul {left right : RationalGL3}
    (hleft : LevelMatrixAtThree left) (hright : LevelMatrixAtThree right) :
    LevelMatrixAtThree (left * right) := by
  obtain ⟨leftDen, hleftDen, leftNum, hleftNum, hleftRow⟩ := hleft
  obtain ⟨rightDen, hrightDen, rightNum, hrightNum, hrightRow⟩ := hright
  refine ⟨leftDen * rightDen, ?_, leftNum * rightNum, ?_, ?_⟩
  · simpa only [Int.cast_mul] using mul_ne_zero hleftDen hrightDen
  · intro row column
    simp only [GeneralLinearGroup.coe_mul, mul_apply, Fin.sum_univ_three]
    push_cast
    rw [← hleftNum row 0, ← hleftNum row 1, ← hleftNum row 2,
      ← hrightNum 0 column, ← hrightNum 1 column, ← hrightNum 2 column]
    ring
  · intro column
    simp only [mul_apply, Fin.sum_univ_three]
    push_cast
    rw [hleftRow 0, hleftRow 1, hleftRow 2, hrightRow column]
    simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
      ite_false, ite_true, mul_zero, zero_mul, zero_add, mul_one, mul_assoc]

theorem level_matrix_inv {element : RationalGL3}
    (hlevel : LevelMatrixAtThree element)
    (hinv : IntegralMatrixAtThree element⁻¹) : LevelMatrixAtThree element⁻¹ := by
  obtain ⟨denominator, hden, numerator, hnum, hrow⟩ := hlevel
  obtain ⟨invDen, hinvDen, invNum, hinvNum⟩ := hinv
  refine ⟨invDen, hinvDen, invNum, hinvNum, ?_⟩
  intro column
  have hproduct : (numerator * invNum) 2 column =
      denominator * invDen * (if (2 : Fin 3) = column then 1 else 0) := by
    apply Int.cast_injective (α := ℚ)
    have hidentity := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℚ => matrix 2 column)
      (show element.val * (element⁻¹).val = 1 by
        rw [← GeneralLinearGroup.coe_mul, mul_inv_cancel, GeneralLinearGroup.coe_one])
    simp only [mul_apply, Fin.sum_univ_three, Matrix.one_apply] at hidentity
    simp only [mul_apply, Fin.sum_univ_three]
    push_cast
    rw [← hnum 2 0, ← hnum 2 1, ← hnum 2 2,
      ← hinvNum 0 column, ← hinvNum 1 column, ← hinvNum 2 column]
    calc
      _ = (denominator : ℚ) * invDen *
          (element.val 2 0 * (element⁻¹).val 0 column +
            element.val 2 1 * (element⁻¹).val 1 column +
            element.val 2 2 * (element⁻¹).val 2 column) := by ring
      _ = _ := by rw [hidentity]
  have hreduced := congrArg (fun value : ℤ => (value : ZMod 3)) hproduct
  simp only [mul_apply, Fin.sum_univ_three] at hreduced
  push_cast at hreduced
  rw [hrow 0, hrow 1, hrow 2] at hreduced
  have hreduced' : (denominator : ZMod 3) * (invNum 2 column : ZMod 3) =
      (denominator : ZMod 3) * ((invDen : ZMod 3) *
        (if column = 2 then 1 else 0)) := by
    simpa only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
      ite_false, ite_true, mul_zero, zero_mul, zero_add, mul_one,
      show ((2 : Fin 3) = column) ↔ column = 2 from eq_comm,
      mul_assoc] using hreduced
  have hcancel := mul_left_cancel₀ hden hreduced'
  exact hcancel

theorem level_matrix_of_rational_level {element : RationalGL3}
    (hlevel : element ∈ rationalLevel) : LevelMatrixAtThree element := by
  obtain ⟨integral, rfl⟩ := hlevel
  refine ⟨1, by norm_num, integral.val.val, ?_, ?_⟩
  · intro row column
    simp [rationalInclusion, GeneralLinearGroup.map_apply]
  · intro column
    have hrow := congrFun integral.property column
    simpa [arithmeticLevel, rowStabilizer, reductionThree, lastRow,
      vecMul, single_dotProduct, GeneralLinearGroup.map_apply, Pi.single_apply,
      eq_comm] using hrow

theorem good_flag_smul {element : RationalGL3}
    (hlevel : LevelMatrixAtThree element) {side : Side} {flag : Flags side}
    (hgood : GoodFlag side flag) : GoodFlag side (element • flag) := by
  obtain ⟨denominator, hden, numerator, hnum, hrow⟩ := hlevel
  obtain ⟨vector, ⟨frame, hframe, coordinates, hcoordinates, hvector⟩, hlast⟩ := hgood
  refine ⟨numerator *ᵥ vector, ⟨element * frame, ?_,
    (denominator : ℚ) • coordinates, ?_, ?_⟩, ?_⟩
  · rw [← hframe]
    rfl
  · cases side with
    | plane =>
      change coordinates 2 = 0 at hcoordinates
      change (denominator : ℚ) * coordinates 2 = 0
      rw [hcoordinates, mul_zero]
    | line =>
      change coordinates 1 = 0 ∧ coordinates 2 = 0 at hcoordinates
      constructor <;> simp only [Pi.smul_apply, smul_eq_mul, hcoordinates.1,
        hcoordinates.2, mul_zero]
  · rw [GeneralLinearGroup.coe_mul, Matrix.mulVec_smul,
      ← Matrix.mulVec_mulVec, hvector]
    funext row
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Fin.sum_univ_three]
    push_cast
    rw [← hnum row 0, ← hnum row 1, ← hnum row 2]
    ring
  · have hlastImage : ((numerator *ᵥ vector) 2 : ZMod 3) =
        (denominator : ZMod 3) * (vector 2 : ZMod 3) := by
      simp only [mulVec, dotProduct, Fin.sum_univ_three]
      push_cast
      rw [hrow 0, hrow 1, hrow 2]
      simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
        ite_false, ite_true, mul_zero, zero_mul, zero_add, mul_one]
    rw [hlastImage]
    exact mul_ne_zero hden hlast

theorem inverse_representative_level (correspondence : HeckeCorrespondence)
    (haway : AwayThree correspondence) {representative : RationalGL3}
    (hrep : representative ∈ correspondence.representatives) :
    LevelMatrixAtThree representative⁻¹ := by
  have hlevel := level_matrix_of_entries correspondence.g
    (fun row column => (haway.1 row column).1) haway.2
  have hinv := level_matrix_inv hlevel (integral_matrix_of_entries correspondence.g⁻¹
    (fun row column => (haway.1 row column).2))
  obtain ⟨left, right, hrepresentative⟩ := correspondence.inDoubleCoset representative hrep
  rw [hrepresentative, _root_.mul_inv_rev, _root_.mul_inv_rev]
  exact level_matrix_mul (level_matrix_of_rational_level
    (rationalLevel.inv_mem right.property))
    (level_matrix_mul hinv (level_matrix_of_rational_level
      (rationalLevel.inv_mem left.property)))

theorem boundary_class_zero {Value : Type} [AddCommGroup Value] [Module ℂ Value]
    (representation : Representation ℂ RationalGL3 Value)
    (cochain : cochains rationalLevel representation 1) :
    classOf rationalLevel representation (boundaryMap rationalLevel representation cochain) =
      0 := by
  change Submodule.Quotient.mk (boundaryMap rationalLevel representation cochain) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨cochain, rfl⟩

theorem zero_on_good_representative (degree : ℕ) (character : RankOneCharacter)
    (side : Side) (cohomologyClass : StratumH2 degree character side)
    (hgood : VanishesOnGood degree character side cohomologyClass) :
    ∃ representative : MaximalCycles degree character side,
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree character)
        side) representative = cohomologyClass ∧
      ∀ vertices flag, GoodFlag side flag → representative.val.val vertices flag = 0 := by
  obtain ⟨representative, hclass, cochain, hcochain⟩ := hgood
  refine ⟨representative - boundaryMap rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree character) side) cochain, ?_, ?_⟩
  · rw [map_sub, boundary_class_zero, sub_zero, hclass]
  · intro vertices flag hflag
    change representative.val.val vertices flag -
      (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        cochain).val vertices flag = 0
    exact sub_eq_zero.mpr (hcochain vertices flag hflag)

theorem hecke_vanishes_on_good (degree : ℕ) (character : RankOneCharacter)
    (hecke : BoundaryHecke degree character)
    (hhecke : ActualBoundaryHecke degree character hecke)
    (correspondence : HeckeCorrespondence) (haway : AwayThree correspondence)
    (side : Side) (cohomologyClass : StratumH2 degree character side)
    (hgood : VanishesOnGood degree character side cohomologyClass) :
    VanishesOnGood degree character side (hecke side correspondence cohomologyClass) := by
  classical
  obtain ⟨representative, hclass, hzero⟩ :=
    zero_on_good_representative degree character side cohomologyClass hgood
  obtain ⟨image, himage, haction⟩ := hhecke side correspondence representative
  refine ⟨image, ?_, 0, ?_⟩
  · rw [hclass] at haction
    exact haction.symm
  · intro vertices flag hflag
    have heval : image.val.val vertices flag =
        ∑ translate ∈ correspondence.representatives,
          rationalCoefficientComponent degree character translate
            (representative.val.val (fun index => translate⁻¹ * vertices index)
              (translate⁻¹ • flag)) := by
      rw [himage]
      simp [heckeCochain, flagRepresentation, functionRepresentation]
    rw [heval, map_zero]
    change (∑ translate ∈ correspondence.representatives,
      rationalCoefficientComponent degree character translate
        (representative.val.val (fun index => translate⁻¹ * vertices index)
          (translate⁻¹ • flag))) = 0
    apply Finset.sum_eq_zero
    intro translate htranslate
    rw [hzero _ _ (good_flag_smul
      (inverse_representative_level correspondence haway htranslate) hflag), map_zero]

end TernaryPeriodPolynomials.AwayThreeHeckeGoodCusps.Helpers
