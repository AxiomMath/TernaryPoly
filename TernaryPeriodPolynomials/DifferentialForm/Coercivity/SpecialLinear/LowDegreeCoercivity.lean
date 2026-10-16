module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse1
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse2
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse3
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.StrictEnergy

@[expose] public section


/-! Positive low-degree coercivity, with the actual monomial coordinate correspondence. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

theorem toTen_zero : toTen 0 = 0 := by
  funext i
  fin_cases i <;> rfl

theorem toTen_homogeneous {n : ℕ} (a : TwoCoordinates)
    (ha : ∀ i j, (a i j).IsHomogeneous n) : ∀ i, (toTen a i).IsHomogeneous n := by
  intro i
  fin_cases i <;> exact ha _ _

theorem tenHodgeAction_kernel_of_coordinates {m n : ℕ} (e : Fin m → Exponent)
    (he : Function.Injective e) (hc : ∀ d : Exponent, d.degree = n → ∃ i, e i = d)
    (F : (Fin 10 → Fin m → ℝ) → (Fin 10 → Fin m → ℝ))
    (hF : ∀ x, tenHodgeAction n (fun i => coordinatePolynomial e (x i)) =
      fun i => coordinatePolynomial e (F x i))
    (hker : ∀ x, F x = 0 → x = 0)
    (u : TenCoordinates) (hu : ∀ i, (u i).IsHomogeneous n) (hH : tenHodgeAction n u = 0) :
    u = 0 := by
  let x : Fin 10 → Fin m → ℝ := fun i j => (u i).coeff (e j)
  have hx : (fun i => coordinatePolynomial e (x i)) = u := by
    funext i
    exact coordinatePolynomial_reconstruct e he hc (u i) (hu i)
  rw [← hx, hF] at hH
  have hf : F x = 0 := by
    funext i j
    have h := congrArg (fun v : TenCoordinates => (v i).coeff (e j)) hH
    simpa only [coordinatePolynomial_coeff e he, Pi.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using h
  have hx0 := hker x hf
  rw [← hx, hx0]
  funext i
  simp [coordinatePolynomial]

theorem homogeneousHodgeTwo_kernel_of_coordinates {m n : ℕ} (e : Fin m → Exponent)
    (he : Function.Injective e) (hc : ∀ d : Exponent, d.degree = n → ∃ i, e i = d)
    (F : (Fin 10 → Fin m → ℝ) → (Fin 10 → Fin m → ℝ))
    (hF : ∀ x, tenHodgeAction n (fun i => coordinatePolynomial e (x i)) =
      fun i => coordinatePolynomial e (F x i))
    (hker : ∀ x, F x = 0 → x = 0)
    (a : homogeneousTwoForms n) (hH : algebraicHodgeTwo a.val = 0) : a = 0 := by
  have hu := toTen_homogeneous a.val a.property.2
  have h := congrArg toTen hH
  rw [← fromTen_toTen a.val a.property.1, toTen_algebraicHodgeTwo _ hu] at h
  have hz : toTen a.val = 0 := tenHodgeAction_kernel_of_coordinates e he hc F hF hker
    (toTen a.val) hu (by simpa only [toTen_zero] using h)
  apply Subtype.ext
  rw [← fromTen_toTen a.val a.property.1, hz]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [fromTen]

theorem homogeneousHodgeTwo_coercive_degree1 : ∃ c : ℝ, 0 < c ∧
    ∀ a : homogeneousTwoForms 1, c * twoPairing a.val a.val ≤
      twoPairing (homogeneousHodgeTwo 1 a).val a.val := by
  apply homogeneousHodgeTwo_coercive_of_kernel
  exact homogeneousHodgeTwo_kernel_of_coordinates lowExponent1 lowExponent1_injective
    lowExponent1_complete lowHodgeAction1 lowHodgeAction1_correct lowHodgeAction1_kernel

theorem homogeneousHodgeTwo_coercive_degree2 : ∃ c : ℝ, 0 < c ∧
    ∀ a : homogeneousTwoForms 2, c * twoPairing a.val a.val ≤
      twoPairing (homogeneousHodgeTwo 2 a).val a.val := by
  apply homogeneousHodgeTwo_coercive_of_kernel
  exact homogeneousHodgeTwo_kernel_of_coordinates lowExponent2 lowExponent2_injective
    lowExponent2_complete lowHodgeAction2 lowHodgeAction2_correct lowHodgeAction2_kernel

theorem homogeneousHodgeTwo_coercive_degree3 : ∃ c : ℝ, 0 < c ∧
    ∀ a : homogeneousTwoForms 3, c * twoPairing a.val a.val ≤
      twoPairing (homogeneousHodgeTwo 3 a).val a.val := by
  apply homogeneousHodgeTwo_coercive_of_kernel
  exact homogeneousHodgeTwo_kernel_of_coordinates lowExponent3 lowExponent3_injective
    lowExponent3_complete lowHodgeAction3 lowHodgeAction3_correct lowHodgeAction3_kernel

end TernaryPoly.SL3PolynomialCoercivity
