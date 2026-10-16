module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.TernarySubstitutionDerivative
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem map_planeUnipotent {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (first second : R) :
    GeneralLinearGroup.map hom (planeUnipotent first second) = planeUnipotent (hom first) (hom second) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [GeneralLinearGroup.map_apply, planeUnipotent]

theorem map_lowerPlaneUnipotent {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (first second : R) :
    GeneralLinearGroup.map hom (lowerPlaneUnipotent first second) = lowerPlaneUnipotent (hom first) (hom second) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [GeneralLinearGroup.map_apply, lowerPlaneUnipotent]

theorem realCoefficientComponent_trivial (degree : ℕ) (matrix : RealGL3) (polynomial : HomogeneousPoly degree) :
    realCoefficientComponent degree trivialCharacter matrix polynomial =
      homogeneousAction degree (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix) polynomial := by
  change (1 : ℂ) • realCoefficient degree matrix polynomial = _
  rw [one_smul]
  rfl

theorem planeUnipotent_coefficient_derivative {degree : ℕ} (first second : ℂ)
    (polynomial : HomogeneousPoly degree) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt (fun parameter : ℝ => (homogeneousAction degree (-1) (planeUnipotent (parameter * first) (parameter * second)) polynomial).val.coeff monomial)
      ((-(C first * X 2 * pderiv 0 polynomial.val + C second * X 2 * pderiv 1 polynomial.val)).coeff monomial) 0 := by
  let derivative : Matrix (Fin 3) (Fin 3) ℂ := !![0,0,-first;0,0,-second;0,0,0]
  have at_zero : planeUnipotent ((0 : ℝ) * first) ((0 : ℝ) * second) = 1 := by
    apply Units.ext
    funext row column
    fin_cases row <;> fin_cases column <;> simp [planeUnipotent]
  have determinant (parameter : ℝ) :
      (GeneralLinearGroup.det (planeUnipotent (parameter * first) (parameter * second))).val = 1 := by
    change Matrix.det (!![1,0,parameter * first;0,1,parameter * second;0,0,1] :
      Matrix (Fin 3) (Fin 3) ℂ) = 1
    simp [Matrix.det_fin_three]
  have entries (row column : Fin 3) :
      HasDerivAt (fun parameter : ℝ => (planeUnipotent (parameter * first) (parameter * second))⁻¹.val row column)
        (derivative row column) 0 := by
    change HasDerivAt (fun parameter : ℝ =>
      (!![1,0,-(parameter * first);0,1,-(parameter * second);0,0,1] : Matrix (Fin 3) (Fin 3) ℂ) row column)
      (derivative row column) 0
    fin_cases row <;> fin_cases column <;>
      first
      | exact hasDerivAt_const 0 _
      | (solve | convert (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const first).neg using 1 <;> first | rfl | simp [derivative])
      | (solve | convert (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const second).neg using 1 <;> first | rfl | simp [derivative])
  have derived := ternary_homogeneousAction_coeff_hasDerivAt
    (fun parameter : ℝ => planeUnipotent (parameter * first) (parameter * second))
    derivative at_zero determinant entries polynomial monomial
  have formula : ternaryInfinitesimalSubstitution derivative polynomial.val =
      -(C first * X 2 * pderiv 0 polynomial.val + C second * X 2 * pderiv 1 polynomial.val) := by
    simp [ternaryInfinitesimalSubstitution, linearForm, derivative, Fin.sum_univ_three]
    ring
  rwa [formula] at derived

theorem lowerPlaneUnipotent_coefficient_derivative {degree : ℕ} (first second : ℂ)
    (polynomial : HomogeneousPoly degree) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt (fun parameter : ℝ => (homogeneousAction degree (-1) (lowerPlaneUnipotent (parameter * first) (parameter * second)) polynomial).val.coeff monomial)
      ((-((C first * X 0 + C second * X 1) * pderiv 2 polynomial.val)).coeff monomial) 0 := by
  let derivative : Matrix (Fin 3) (Fin 3) ℂ := !![0,0,0;0,0,0;-first,-second,0]
  have at_zero : lowerPlaneUnipotent ((0 : ℝ) * first) ((0 : ℝ) * second) = 1 := by
    apply Units.ext
    funext row column
    fin_cases row <;> fin_cases column <;> simp [lowerPlaneUnipotent]
  have determinant (parameter : ℝ) :
      (GeneralLinearGroup.det (lowerPlaneUnipotent (parameter * first) (parameter * second))).val = 1 := by
    change Matrix.det (!![1,0,0;0,1,0;parameter * first,parameter * second,1] :
      Matrix (Fin 3) (Fin 3) ℂ) = 1
    simp [Matrix.det_fin_three]
  have entries (row column : Fin 3) :
      HasDerivAt (fun parameter : ℝ => (lowerPlaneUnipotent (parameter * first) (parameter * second))⁻¹.val row column)
        (derivative row column) 0 := by
    change HasDerivAt (fun parameter : ℝ =>
      (!![1,0,0;0,1,0;-(parameter * first),-(parameter * second),1] : Matrix (Fin 3) (Fin 3) ℂ) row column)
      (derivative row column) 0
    fin_cases row <;> fin_cases column <;>
      first
      | exact hasDerivAt_const 0 _
      | (solve | convert (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const first).neg using 1 <;> first | rfl | simp [derivative])
      | (solve | convert (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const second).neg using 1 <;> first | rfl | simp [derivative])
  have derived := ternary_homogeneousAction_coeff_hasDerivAt
    (fun parameter : ℝ => lowerPlaneUnipotent (parameter * first) (parameter * second))
    derivative at_zero determinant entries polynomial monomial
  have formula : ternaryInfinitesimalSubstitution derivative polynomial.val =
      -((C first * X 0 + C second * X 1) * pderiv 2 polynomial.val) := by
    simp [ternaryInfinitesimalSubstitution, linearForm, derivative, Fin.sum_univ_three]
    ring
  rwa [formula] at derived

theorem real_planeUnipotent_coefficient_derivative {degree : ℕ} (first second : ℝ)
    (polynomial : HomogeneousPoly degree) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt (fun parameter : ℝ => (realCoefficientComponent degree trivialCharacter
        (planeUnipotent (parameter * first) (parameter * second)) polynomial).val.coeff monomial)
      ((-(C (first : ℂ) * X 2 * pderiv 0 polynomial.val +
        C (second : ℂ) * X 2 * pderiv 1 polynomial.val)).coeff monomial) 0 := by
  simp only [realCoefficientComponent_trivial, map_planeUnipotent, map_mul]
  exact planeUnipotent_coefficient_derivative first second polynomial monomial

theorem real_lowerPlaneUnipotent_coefficient_derivative {degree : ℕ} (first second : ℝ)
    (polynomial : HomogeneousPoly degree) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt (fun parameter : ℝ => (realCoefficientComponent degree trivialCharacter
        (lowerPlaneUnipotent (parameter * first) (parameter * second)) polynomial).val.coeff monomial)
      ((-((C (first : ℂ) * X 0 + C (second : ℂ) * X 1) * pderiv 2 polynomial.val)).coeff monomial) 0 := by
  simp only [realCoefficientComponent_trivial, map_lowerPlaneUnipotent, map_mul]
  exact lowerPlaneUnipotent_coefficient_derivative first second polynomial monomial

end TernaryPeriodPolynomials.SphericalDetection.Helpers
