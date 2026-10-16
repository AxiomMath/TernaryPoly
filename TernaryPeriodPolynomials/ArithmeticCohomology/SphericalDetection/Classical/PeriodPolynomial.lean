module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodNonvanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointFormAnalytic

@[expose] public section


open GeneralEisenstein Matrix MvPolynomial MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryStandardBasis (degree : ℕ) :
    Module.Basis (Fin (degree + 1)) ℂ (Binary.HomogeneousPoly degree) :=
  (binaryMonomialBasis degree).reindex (binaryWeightIndex degree)

theorem binaryStandardBasis_apply (degree : ℕ) (position : Fin (degree + 1)) :
    binaryStandardBasis degree position = binaryMonomialBasis degree (binaryWeightExponent degree position) := by
  rw [binaryStandardBasis, Module.Basis.reindex_apply]
  rfl

theorem binaryStandardBasis_coe (degree : ℕ) (position : Fin (degree + 1)) :
    (binaryStandardBasis degree position).val = X 0 ^ position.val * X 1 ^ (degree - position.val) := by
  rw [binaryStandardBasis_apply, binaryMonomialBasis_weightExponent]

theorem binaryPointPower_standardCoord (degree : ℕ) (point : ℂ) (position : Fin (degree + 1)) :
    (binaryStandardBasis degree).coord position (binaryPointPower degree point) =
      ((degree.choose position.val : ℕ) : ℂ) * (-point) ^ (degree - position.val) := by
  have expansion : binaryPointPower degree point = ∑ index : Fin (degree + 1),
      (((degree.choose index.val : ℕ) : ℂ) * (-point) ^ (degree - index.val)) •
        binaryStandardBasis degree index := by
    simpa only [binaryStandardBasis_apply] using binaryPointPower_expansion degree point
  rw [expansion, map_sum]
  simp [map_smul, Module.Basis.coord_apply, Finsupp.single_apply]

/-- The coefficientwise integral of `f(z) (X-zY)^degree dz` from zero to imaginary infinity. -/
def cuspPeriodPolynomial {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) : Binary.HomogeneousPoly degree :=
  ∑ position : Fin (degree + 1),
    (((degree.choose position.val : ℕ) : ℂ) * (-Complex.I) ^ (degree - position.val) * Complex.I *
      cuspImaginaryMoment form (degree - position.val)) • binaryStandardBasis degree position

theorem cuspPeriodPolynomial_coord {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (position : Fin (degree + 1)) :
    (binaryStandardBasis degree).coord position (cuspPeriodPolynomial form degree) =
      ((degree.choose position.val : ℕ) : ℂ) * (-Complex.I) ^ (degree - position.val) * Complex.I *
        cuspImaginaryMoment form (degree - position.val) := by
  rw [cuspPeriodPolynomial, map_sum]
  simp [map_smul, Module.Basis.coord_apply, Finsupp.single_apply]

theorem cuspPeriodPolynomial_coord_integral {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (position : Fin (degree + 1)) :
    (binaryStandardBasis degree).coord position (cuspPeriodPolynomial form degree) =
      ∫ height : ℝ in Set.Ioi 0,
        (binaryStandardBasis degree).coord position (binaryPointPower degree (Complex.I * (height : ℂ))) *
          form (UpperHalfPlane.ofComplex (Complex.I * (height : ℂ))) * Complex.I := by
  rw [cuspPeriodPolynomial_coord, cuspImaginaryMoment, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with height
  rw [binaryPointPower_standardCoord, ← neg_mul, mul_pow]
  ring

theorem cuspPeriodPolynomial_coord_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (position : Fin (degree + 1))
    (moment_nonzero : cuspImaginaryMoment form (degree - position.val) ≠ 0) :
    (binaryStandardBasis degree).coord position (cuspPeriodPolynomial form degree) ≠ 0 := by
  rw [cuspPeriodPolynomial_coord]
  apply mul_ne_zero _ moment_nonzero
  apply mul_ne_zero _ Complex.I_ne_zero
  apply mul_ne_zero _ (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
  exact_mod_cast (ne_of_gt (Nat.choose_pos (by omega : position.val ≤ degree)))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
