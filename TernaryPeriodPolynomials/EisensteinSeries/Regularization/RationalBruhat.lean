module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ParabolicFactorization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def planeLowerShear {R : Type*} [CommRing R] (coordinate : R) : Adelic.GL3 R :=
  ⟨!![1,0,0;coordinate,1,0;0,0,1], !![1,0,0;-coordinate,1,0;0,0,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem planeLowerShear_parabolic {R : Type*} [CommRing R] (coordinate : R) :
    InPlaneParabolic (planeLowerShear coordinate) := ⟨rfl, rfl⟩

theorem swapLastTwo_square : swapLastTwo * swapLastTwo = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [swapLastTwo, Matrix.mul_apply, Fin.sum_univ_three]

theorem swapFirstTwo_square : swapFirstTwo * swapFirstTwo = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [swapFirstTwo, Matrix.mul_apply, Fin.sum_univ_three]

theorem plane_bruhat_of_second_entry_ne_zero
    (matrix : RationalGL3) (second_nonzero : matrix.val 2 1 ≠ 0) :
    ∃ left right : RationalGL3,
      InPlaneParabolic left ∧ InPlaneParabolic right ∧
      matrix = left * swapLastTwo * right := by
  let rightCorrection := planeLowerShear (-(matrix.val 2 0 / matrix.val 2 1)) *
    planeUnipotent 0 (-(matrix.val 2 2 / matrix.val 2 1))
  have correction_parabolic : InPlaneParabolic rightCorrection :=
    inPlane_mul (planeLowerShear_parabolic _) ⟨rfl, rfl⟩
  have corrected_parabolic : InPlaneParabolic (matrix * rightCorrection * swapLastTwo) := by
    constructor <;>
      simp [rightCorrection, planeLowerShear, planeUnipotent, swapLastTwo,
        Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp <;> ring
  refine ⟨matrix * rightCorrection * swapLastTwo, rightCorrection⁻¹,
    corrected_parabolic, inPlane_inv correction_parabolic, ?_⟩
  simp only [mul_assoc, swapLastTwo_square, mul_inv_cancel, mul_one]

theorem plane_rational_bruhat (matrix : RationalGL3) :
    InPlaneParabolic matrix ∨
      ∃ left right : RationalGL3,
        InPlaneParabolic left ∧ InPlaneParabolic right ∧
        matrix = left * swapLastTwo * right := by
  by_cases second_zero : matrix.val 2 1 = 0
  · by_cases first_zero : matrix.val 2 0 = 0
    · exact Or.inl ⟨first_zero, second_zero⟩
    · have swapped_second : (matrix * swapFirstTwo).val 2 1 ≠ 0 := by
        simpa [swapFirstTwo, Matrix.mul_apply, Fin.sum_univ_three] using first_zero
      obtain ⟨left, right, left_parabolic, right_parabolic, factorization⟩ :=
        plane_bruhat_of_second_entry_ne_zero (matrix * swapFirstTwo) swapped_second
      refine Or.inr ⟨left, right * swapFirstTwo, left_parabolic,
        inPlane_mul right_parabolic ⟨rfl, rfl⟩, ?_⟩
      calc
        matrix = (matrix * swapFirstTwo) * swapFirstTwo := by
          rw [mul_assoc, swapFirstTwo_square, mul_one]
        _ = left * swapLastTwo * (right * swapFirstTwo) := by
          rw [factorization, mul_assoc]
  · exact Or.inr (plane_bruhat_of_second_entry_ne_zero matrix second_zero)

theorem plane_rational_flag_orbits (flag : Flags .plane) :
    flag = QuotientGroup.mk (1 : RationalGL3) ∨
      ∃ parabolicElement : GeneralEisenstein.parabolic .plane,
        flag = parabolicElement.val • QuotientGroup.mk swapLastTwo := by
  obtain parabolic | ⟨left, right, left_parabolic, right_parabolic, factorization⟩ :=
    plane_rational_bruhat flag.out
  · left
    rw [← QuotientGroup.out_eq' flag]
    apply QuotientGroup.eq.mpr
    rw [mul_one]
    exact inPlane_inv parabolic
  · right
    refine ⟨⟨left, left_parabolic⟩, ?_⟩
    rw [← QuotientGroup.out_eq' flag]
    change QuotientGroup.mk flag.out = QuotientGroup.mk (left * swapLastTwo)
    apply QuotientGroup.eq.mpr
    have quotient_difference : flag.out⁻¹ * (left * swapLastTwo) = right⁻¹ := by
      rw [factorization]
      group
    rw [quotient_difference]
    exact inPlane_inv right_parabolic

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
