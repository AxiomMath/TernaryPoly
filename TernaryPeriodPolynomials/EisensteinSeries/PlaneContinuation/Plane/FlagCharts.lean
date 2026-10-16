module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FlagRows

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagCharts

def affine {Ring : Type*} [CommRing Ring] (slope shift : Ring) : GL3 Ring :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, slope, shift],
    !![-slope, -shift, 1; 1, 0, 0; 0, 1, 0], by
      ext row column
      fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
      ext row column
      fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def vertical {Ring : Type*} [CommRing Ring] (shift : Ring) : GL3 Ring :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, shift],
    !![1, 0, 0; 0, -shift, 1; 0, 1, 0], by
      ext row column
      fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
      ext row column
      fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem affine_map {Source Target : Type*} [CommRing Source] [CommRing Target]
    (hom : Source →+* Target) (slope shift : Source) :
    GeneralLinearGroup.map hom (affine slope shift) = affine (hom slope) (hom shift) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [affine, GeneralLinearGroup.map_apply]

theorem vertical_map {Source Target : Type*} [CommRing Source] [CommRing Target]
    (hom : Source →+* Target) (shift : Source) :
    GeneralLinearGroup.map hom (vertical shift) = vertical (hom shift) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [vertical, GeneralLinearGroup.map_apply]

inductive Chart where
  | origin
  | vertical (shift : ℚ)
  | affine (slope shift : ℚ)
  deriving DecidableEq

def representative : Chart → RationalGL3
  | .origin => 1
  | .vertical shift => vertical shift
  | .affine slope shift => affine slope shift

def row : Chart → Fin 3 → ℚ
  | .origin => ![0, 0, 1]
  | .vertical shift => ![0, 1, shift]
  | .affine slope shift => ![1, slope, shift]

theorem representative_row (chart : Chart) (column : Fin 3) :
    (representative chart).val 2 column = row chart column := by
  cases chart <;> fin_cases column <;> rfl

theorem row_injective (first second : Chart) (scalar : ℚˣ)
    (equality : ∀ column, row first column = scalar.val * row second column) : first = second := by
  have zero := equality 0
  have one := equality 1
  have two := equality 2
  have nonzero := Units.ne_zero scalar
  clear equality
  cases first <;> cases second <;>
    simp only [row, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      mul_zero, mul_one, zero_eq_mul] at zero one two <;>
    simp_all
  · rw [← one, one_mul]
  · simp only [← zero, one_mul, and_self]

def flag (chart : Chart) : Flags .plane := QuotientGroup.mk (representative chart)⁻¹

theorem flag_injective : Function.Injective flag := by
  intro first second equality
  obtain ⟨scalar, rows⟩ := (FlagRows.planeFlag_eq_iff_rows (representative first)⁻¹ (representative second)⁻¹).mp equality
  simp only [inv_inv, representative_row] at rows
  exact row_injective first second scalar rows

theorem flag_surjective : Function.Surjective flag := by
  intro target
  let matrix := target.out⁻¹
  have targetEquality : (QuotientGroup.mk matrix⁻¹ : Flags .plane) = target := by
    simp only [matrix, inv_inv, QuotientGroup.out_eq']
  by_cases firstNonzero : matrix.val 2 0 ≠ 0
  · refine ⟨.affine (matrix.val 2 1 / matrix.val 2 0) (matrix.val 2 2 / matrix.val 2 0), ?_⟩
    rw [← targetEquality]
    apply Eq.symm
    apply (FlagRows.planeFlag_eq_iff_rows _ _).mpr
    refine ⟨Units.mk0 (matrix.val 2 0) firstNonzero, ?_⟩
    intro column
    simp only [inv_inv, representative_row, Units.val_mk0]
    fin_cases column <;> simp [row] <;> field_simp
  · by_cases secondNonzero : matrix.val 2 1 ≠ 0
    · refine ⟨.vertical (matrix.val 2 2 / matrix.val 2 1), ?_⟩
      rw [← targetEquality]
      apply Eq.symm
      apply (FlagRows.planeFlag_eq_iff_rows _ _).mpr
      refine ⟨Units.mk0 (matrix.val 2 1) secondNonzero, ?_⟩
      intro column
      simp only [inv_inv, representative_row, Units.val_mk0]
      fin_cases column <;> simp_all [row]
      field_simp
    · have firstZero : matrix.val 2 0 = 0 := not_ne_iff.mp firstNonzero
      have secondZero : matrix.val 2 1 = 0 := not_ne_iff.mp secondNonzero
      have lastNonzero : matrix.val 2 2 ≠ 0 := by
        intro lastZero
        apply FlagRows.lastRow_ne_zero matrix
        funext column
        fin_cases column <;> assumption
      refine ⟨.origin, ?_⟩
      rw [← targetEquality]
      apply Eq.symm
      apply (FlagRows.planeFlag_eq_iff_rows _ _).mpr
      refine ⟨Units.mk0 (matrix.val 2 2) lastNonzero, ?_⟩
      intro column
      simp only [inv_inv, representative_row, Units.val_mk0]
      fin_cases column <;> simp [row, firstZero, secondZero]

noncomputable def equivalence : Chart ≃ Flags .plane := Equiv.ofBijective flag ⟨flag_injective, flag_surjective⟩

instance chartCountable : Countable Chart := by
  let _ : Countable (Matrix (Fin 3) (Fin 3) ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 3 → ℚ))
  let _ : Countable RationalGL3 := Function.Injective.countable Units.val_injective
  exact Function.Injective.countable (f := representative) (by
    intro first second equality
    apply flag_injective
    exact congrArg (fun matrix : RationalGL3 => (QuotientGroup.mk matrix⁻¹ : Flags .plane)) equality)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagCharts
