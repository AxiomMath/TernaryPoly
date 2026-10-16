module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.ShearExponential
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.LineTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.LowerCoordinateLevi

@[expose] public section


/-!
# The infinitesimal action of the real lower radical on coefficients

Along the axis `s ↦ s eᵢ` of the real lower radical, the coefficient action is the exponential of
`s Dᵢ` with `Dᵢ v = -Xᵢ ∂₂ v`; hence every scalar test of the moved coefficient is differentiable
at `s = 0` with derivative the test of `Dᵢ v`. The lower radical coordinate kills the pair
`(D₀ v, D₁ v)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {n : ℕ}

/-- The derivative `Dᵢ v = -Xᵢ ∂₂ v` of the coefficient action of the lower radical. -/
def lowerShear (n : ℕ) (i : Fin 2) : Module.End ℂ (HomogeneousPoly n) :=
  (-1 : ℂ) • homogeneousShearDerivation n 2 i.castSucc

theorem lowerShear_val (i : Fin 2) (v : HomogeneousPoly n) :
    (lowerShear n i v).val = -(X i.castSucc * pderiv 2 v.val) := by
  change (-1 : ℂ) • (X i.castSucc * pderiv 2 v.val) = _
  rw [neg_one_smul]

/-- **The lower radical coordinate kills infinitesimal coboundaries.** -/
theorem lowerRadicalCoordinate_lowerShear (v : HomogeneousPoly n) :
    lowerRadicalCoordinate n (fun i => lowerShear n i v) = 0 := by
  apply Subtype.ext
  change binaryPolynomialRestrict (lowerRadicalContraction (lowerShear n 0 v).val
    (lowerShear n 1 v).val) = 0
  rw [lowerShear_val, lowerShear_val, lowerRadicalContraction]
  have zero : X (1 : Fin 3) * -(X (Fin.castSucc (0 : Fin 2)) * pderiv 2 v.val) -
      X 0 * -(X (Fin.castSucc (1 : Fin 2)) * pderiv 2 v.val) = 0 := by
    simp only [Fin.castSucc_zero, Fin.castSucc_one]
    ring
  rw [zero, map_zero]

theorem lowerShear_pow_zero (i : Fin 2) (scalar : ℂ) :
    (scalar • lowerShear n i) ^ (n + 2) = 0 := by
  rw [lowerShear, smul_smul, pow_succ,
    homogeneousShearDerivation_smul_power_zero n 2 i.castSucc _ (Fin.castSucc_ne_last i), zero_mul]

/-- The coefficient action along an axis of the real lower radical is an exponential. -/
theorem coefficient_lowerAxis (i : Fin 2) (s : ℝ) (v : HomogeneousPoly n) :
    realCoefficientComponent n trivialCharacter
        (lineRadicalMatrix (Multiplicative.ofAdd (s • Pi.single i 1))) v =
      IsNilpotent.exp ((s : ℂ) • lowerShear n i) v := by
  apply Subtype.ext
  rw [lowerShear, smul_smul, mul_neg_one,
    homogeneousShearDerivation_exponential_coe n 2 i.castSucc (-(s : ℂ)) (Fin.castSucc_ne_last i),
    shearPolynomialCurve_eval_one, realCoefficientComponent_trivial, homogeneousAction_coe,
    action_apply]
  have matrix : GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (lineRadicalMatrix (Multiplicative.ofAdd (s • Pi.single i 1))) =
      lowerPlaneUnipotent (if i = 0 then (s : ℂ) else 0) (if i = 1 then (s : ℂ) else 0) := by
    apply Units.ext
    funext row column
    fin_cases i <;> fin_cases row <;> fin_cases column <;>
      simp [lineRadicalMatrix, lowerPlaneUnipotent]
  rw [matrix]
  have determinant : determinantCharacter (-1)
      (lowerPlaneUnipotent (if i = 0 then (s : ℂ) else 0) (if i = 1 then (s : ℂ) else 0)) = 1 := by
    change ((lowerPlaneUnipotent (if i = 0 then (s : ℂ) else 0)
      (if i = 1 then (s : ℂ) else 0)).val.det) ^ (-1 : ℤ) = 1
    fin_cases i <;> simp [lowerPlaneUnipotent, Matrix.det_fin_three]
  rw [determinant, one_smul]
  have substitutions : MvPolynomial.bind₁
      (fun index => X index + if index = (2 : Fin 3) then C (-(s : ℂ)) * X i.castSucc else 0) =
      substitute (lowerPlaneUnipotent (if i = 0 then (s : ℂ) else 0)
        (if i = 1 then (s : ℂ) else 0))⁻¹.val := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases i <;> fin_cases index <;>
      simp [substitute_X, linearForm, lowerPlaneUnipotent, Fin.sum_univ_three, add_comm]
  rw [substitutions]

/-- **Derivative of the coefficient action along an axis of the lower radical.** -/
theorem hasDerivAt_coefficient_lowerAxis (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (v : HomogeneousPoly n) (i : Fin 2) :
    HasDerivAt (fun s : ℝ => functional (realCoefficientComponent n trivialCharacter
        (lineRadicalMatrix (Multiplicative.ofAdd (s • Pi.single i 1))) v))
      (functional (lowerShear n i v)) 0 := by
  have expansion (s : ℝ) : functional (realCoefficientComponent n trivialCharacter
      (lineRadicalMatrix (Multiplicative.ofAdd (s • Pi.single i 1))) v) =
      ∑ k ∈ Finset.range (n + 2), ((k.factorial : ℂ)⁻¹ * functional ((lowerShear n i ^ k) v)) *
        (s : ℂ) ^ k := by
    rw [coefficient_lowerAxis, IsNilpotent.exp_eq_sum (lowerShear_pow_zero i (s : ℂ)),
      LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [LinearMap.smul_apply, ← Rat.cast_smul_eq_qsmul ℂ, smul_pow, LinearMap.smul_apply, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  simp_rw [expansion]
  have term (k : ℕ) : HasDerivAt (fun s : ℝ => ((k.factorial : ℂ)⁻¹ *
      functional ((lowerShear n i ^ k) v)) * (s : ℂ) ^ k)
      (((k.factorial : ℂ)⁻¹ * functional ((lowerShear n i ^ k) v)) *
        ((k : ℂ) * ((0 : ℝ) : ℂ) ^ (k - 1) * 1)) 0 :=
    (((hasDerivAt_pow k (((0 : ℝ) : ℂ))).comp_ofReal).const_mul _).congr_deriv (by simp)
  have sum := HasDerivAt.fun_sum (u := Finset.range (n + 2)) (fun k _ => term k)
  refine sum.congr_deriv ?_
  rw [Finset.sum_eq_single 1]
  · simp
  · intro k _ hk
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · have : k - 1 ≠ 0 := by omega
      simp [zero_pow this]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

end TernaryPeriodPolynomials.AnalyticClasses
