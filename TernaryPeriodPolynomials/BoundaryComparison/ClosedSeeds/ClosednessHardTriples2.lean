module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.ClosednessHardTriples

@[expose] public section


/-! Clause (i) of Lemma C.3 (`ar:lem:seed`), the two remaining "hard" `Alt3` triples `(0,2,3)` and
`(1,2,3)`, the ones where coordinates `2` and `3` occur together, so the Cauchy–Riemann chain rule
(`hasDerivAt_comp_seedTau_two/three`) is genuinely needed in both nonzero terms. After the chain
rule is applied, the two terms' bracketed sub-expressions coincide up to commutativity, so the
signed difference is `0`. Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `Alt3 n h m p 0 2 3 = 0`: the two nonzero terms both pick up the Cauchy–Riemann relation for
`h ∘ seedTau`, and the resulting bracketed expressions coincide up to commutativity. -/
theorem Alt3_023 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ)
    (hdiff : DifferentiableAt ℂ h (seedTau p)) :
    Alt3 n h m p 0 2 3 = 0 := by
  unfold Alt3
  have hterm_a : coordPartial (fun q => (seedForm n h q 2 3).coeff m) 0 p = 0 := by
    unfold coordPartial
    have hz : (fun s : ℝ => (seedForm n h (Function.update p 0 s) 2 3).coeff m) = fun _ => (0 : ℂ) := by
      funext s; exact coeff_seedForm_23 n h m (Function.update p 0 s)
    rw [hz, deriv_const]
  have hh : HasDerivAt h (deriv h (seedTau p)) (seedTau p) := hdiff.hasDerivAt
  have hterm_b : coordPartial (fun q => (seedForm n h q 0 3).coeff m) 2 p =
      deriv h (seedTau p) * Complex.I * (seedLinear p ^ n).coeff m +
        h (seedTau p) * Complex.I * ((n : ℂ) * (seedLinear p ^ (n - 1) *
          (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ))).coeff m) := by
    unfold coordPartial
    have hfe : (fun s : ℝ => (seedForm n h (Function.update p 2 s) 0 3).coeff m) =
        fun s : ℝ => h (seedTau (Function.update p 2 s)) * Complex.I *
          (seedLinear (Function.update p 2 s) ^ n).coeff m := by
      funext s; rw [coeff_seedForm_03]
    rw [hfe]
    have hh2 := hasDerivAt_comp_seedTau_two p h (deriv h (seedTau p)) hh
    have hcomb := (hh2.mul_const Complex.I).mul (hasDerivAt_seedLinear_pow_two n m p)
    simp only [Function.update_eq_self] at hcomb
    exact hcomb.deriv
  have hterm_c : coordPartial (fun q => (seedForm n h q 0 2).coeff m) 3 p =
      deriv h (seedTau p) * Complex.I * (seedLinear p ^ n).coeff m +
        h (seedTau p) * ((n : ℂ) * (seedLinear p ^ (n - 1) *
          (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ))).coeff m * Complex.I) := by
    unfold coordPartial
    have hfe : (fun s : ℝ => (seedForm n h (Function.update p 3 s) 0 2).coeff m) =
        fun s : ℝ => h (seedTau (Function.update p 3 s)) *
          (seedLinear (Function.update p 3 s) ^ n).coeff m := by
      funext s; rw [coeff_seedForm_02]
    rw [hfe]
    have hh3 := hasDerivAt_comp_seedTau_three p h (deriv h (seedTau p)) hh
    have hcomb := hh3.mul (hasDerivAt_seedLinear_pow_three n m p)
    simp only [Function.update_eq_self] at hcomb
    exact hcomb.deriv
  rw [hterm_a, hterm_b, hterm_c]
  ring

/-- `Alt3 n h m p 1 2 3 = 0`: as `Alt3_023`, but the scalar prefactor is `h (seedTau q) * seedTau q`
(the function `g (z) := h z * z`), needing an extra product rule (`g' = h' * τ + h`) before the
Cauchy–Riemann lift. -/
theorem Alt3_123 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ)
    (hdiff : DifferentiableAt ℂ h (seedTau p)) :
    Alt3 n h m p 1 2 3 = 0 := by
  unfold Alt3
  have hterm_a : coordPartial (fun q => (seedForm n h q 2 3).coeff m) 1 p = 0 := by
    unfold coordPartial
    have hz : (fun s : ℝ => (seedForm n h (Function.update p 1 s) 2 3).coeff m) = fun _ => (0 : ℂ) := by
      funext s; exact coeff_seedForm_23 n h m (Function.update p 1 s)
    rw [hz, deriv_const]
  have hh : HasDerivAt h (deriv h (seedTau p)) (seedTau p) := hdiff.hasDerivAt
  have hg : HasDerivAt (fun z : ℂ => h z * z) (deriv h (seedTau p) * seedTau p + h (seedTau p))
      (seedTau p) := by
    have := hh.mul (hasDerivAt_id (seedTau p))
    simp only [id_eq, mul_one] at this
    exact this
  have hterm_b : coordPartial (fun q => (seedForm n h q 1 3).coeff m) 2 p =
      (-(deriv h (seedTau p) * seedTau p + h (seedTau p))) * Complex.I * (seedLinear p ^ n).coeff m +
        (-(h (seedTau p) * seedTau p)) * Complex.I * ((n : ℂ) * (seedLinear p ^ (n - 1) *
          (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ))).coeff m) := by
    unfold coordPartial
    have hfe : (fun s : ℝ => (seedForm n h (Function.update p 2 s) 1 3).coeff m) =
        fun s : ℝ => -(h (seedTau (Function.update p 2 s)) * seedTau (Function.update p 2 s)) *
          Complex.I * (seedLinear (Function.update p 2 s) ^ n).coeff m := by
      funext s; rw [coeff_seedForm_13]
    rw [hfe]
    have hgcomp := hasDerivAt_comp_seedTau_two p (fun z => h z * z)
      (deriv h (seedTau p) * seedTau p + h (seedTau p)) hg
    have hcomb := (hgcomp.neg.mul_const Complex.I).mul (hasDerivAt_seedLinear_pow_two n m p)
    simp only [Function.update_eq_self] at hcomb
    exact hcomb.deriv
  have hterm_c : coordPartial (fun q => (seedForm n h q 1 2).coeff m) 3 p =
      (-((deriv h (seedTau p) * seedTau p + h (seedTau p)) * Complex.I)) * (seedLinear p ^ n).coeff m +
        (-(h (seedTau p) * seedTau p)) * ((n : ℂ) * (seedLinear p ^ (n - 1) *
          (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ))).coeff m * Complex.I) := by
    unfold coordPartial
    have hfe : (fun s : ℝ => (seedForm n h (Function.update p 3 s) 1 2).coeff m) =
        fun s : ℝ => -(h (seedTau (Function.update p 3 s)) * seedTau (Function.update p 3 s)) *
          (seedLinear (Function.update p 3 s) ^ n).coeff m := by
      funext s; rw [coeff_seedForm_12]
    rw [hfe]
    have hgcomp := hasDerivAt_comp_seedTau_three p (fun z => h z * z)
      (deriv h (seedTau p) * seedTau p + h (seedTau p)) hg
    have hcomb := hgcomp.neg.mul (hasDerivAt_seedLinear_pow_three n m p)
    simp only [Function.update_eq_self] at hcomb
    exact hcomb.deriv
  rw [hterm_a, hterm_b, hterm_c]
  ring

end TernaryPeriodPolynomials.Argument
