module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.ClosednessTrivial
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.ClosednessLinearHasDerivAt

@[expose] public section


/-! Clause (i) of Lemma C.3 (`ar:lem:seed`), the "hard" nontrivial `Alt3` triples (pairwise
distinct indices from `{0,1,2,3}`). This file: the coefficient-level unfolding of `seedForm` for
each of the six pairs from `{0,1,2,3}` (`coeff_seedForm_eq` plus six specializations), and the two
representative triples `(0,1,2)` and `(0,1,3)` that vanish by direct structural cancellation —
`seedForm`'s scalar prefactor is constant along the differentiated coordinate in both nonzero
terms, so no Cauchy–Riemann relation is needed (that is reserved for `(0,2,3)` and `(1,2,3)`,
where both coordinates `2` and `3` occur in the same triple). Feeds
`TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- Coefficient-level unfolding of `seedForm`: `C` pulls out of `coeff`. -/
theorem coeff_seedForm_eq (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    (seedForm n h p i j).coeff m =
      h (seedTau p) * (seedBeta p i * seedDTau j - seedBeta p j * seedDTau i) *
        (seedLinear p ^ n).coeff m := by
  unfold seedForm
  rw [coeff_C_mul]

theorem coeff_seedForm_01 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    (seedForm n h p 0 1).coeff m = 0 := by
  have hz : seedBeta p 0 * seedDTau 1 - seedBeta p 1 * seedDTau 0 = 0 := by simp [seedBeta, seedDTau]
  rw [coeff_seedForm_eq, hz, mul_zero, zero_mul]

theorem coeff_seedForm_02 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    (seedForm n h p 0 2).coeff m = h (seedTau p) * (seedLinear p ^ n).coeff m := by
  have hz : seedBeta p 0 * seedDTau 2 - seedBeta p 2 * seedDTau 0 = 1 := by simp [seedBeta, seedDTau]
  rw [coeff_seedForm_eq, hz, mul_one]

theorem coeff_seedForm_03 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    (seedForm n h p 0 3).coeff m = h (seedTau p) * Complex.I * (seedLinear p ^ n).coeff m := by
  have hz : seedBeta p 0 * seedDTau 3 - seedBeta p 3 * seedDTau 0 = Complex.I := by
    simp [seedBeta, seedDTau]
  rw [coeff_seedForm_eq, hz]

theorem coeff_seedForm_12 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    (seedForm n h p 1 2).coeff m = -(h (seedTau p) * seedTau p) * (seedLinear p ^ n).coeff m := by
  have hz : seedBeta p 1 * seedDTau 2 - seedBeta p 2 * seedDTau 1 = -seedTau p := by
    simp [seedBeta, seedDTau]
  rw [coeff_seedForm_eq, hz]; ring

theorem coeff_seedForm_13 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    (seedForm n h p 1 3).coeff m =
      -(h (seedTau p) * seedTau p) * Complex.I * (seedLinear p ^ n).coeff m := by
  have hz : seedBeta p 1 * seedDTau 3 - seedBeta p 3 * seedDTau 1 = -(seedTau p * Complex.I) := by
    simp [seedBeta, seedDTau]
  rw [coeff_seedForm_eq, hz]; ring

theorem coeff_seedForm_23 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    (seedForm n h p 2 3).coeff m = 0 := by
  have hz : seedBeta p 2 * seedDTau 3 - seedBeta p 3 * seedDTau 2 = 0 := by simp [seedBeta, seedDTau]
  rw [coeff_seedForm_eq, hz, mul_zero, zero_mul]

theorem seedTau_update0 (p : Fin 5 → ℝ) (s : ℝ) : seedTau (Function.update p 0 s) = seedTau p := by
  simp [seedTau]

theorem seedTau_update1 (p : Fin 5 → ℝ) (s : ℝ) : seedTau (Function.update p 1 s) = seedTau p := by
  simp [seedTau]

/-- Bridge used to relate the coordinate-`1` slope `-(C (seedTau p) * X 2)` back to the
coordinate-`0` slope `X 2`: multiplying the bracket by `-(C τ * X 2)` instead of `X 2` just
multiplies its coefficient by `-τ`. -/
theorem coeff_seedLinear_pow_mul_negCX2 (n : ℕ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    (seedLinear p ^ (n - 1) * (-(C (seedTau p) * X 2))).coeff m =
      -seedTau p * (seedLinear p ^ (n - 1) * X 2).coeff m := by
  have hrw : seedLinear p ^ (n - 1) * (-(C (seedTau p) * X 2)) =
      C (-seedTau p) * (seedLinear p ^ (n - 1) * X 2) := by
    rw [map_neg]; ring
  rw [hrw, coeff_C_mul]

/-- `Alt3 n h m p 0 1 2 = 0`: vanishes by direct structural cancellation (`seedForm`'s scalar
prefactor is constant along both coordinates `0` and `1`, no Cauchy–Riemann needed). -/
theorem Alt3_012 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    Alt3 n h m p 0 1 2 = 0 := by
  unfold Alt3
  have hterm_c : coordPartial (fun q => (seedForm n h q 0 1).coeff m) 2 p = 0 := by
    unfold coordPartial
    have hz : (fun s : ℝ => (seedForm n h (Function.update p 2 s) 0 1).coeff m) = fun _ => (0 : ℂ) := by
      funext s; exact coeff_seedForm_01 n h m (Function.update p 2 s)
    rw [hz, deriv_const]
  have hterm_a : coordPartial (fun q => (seedForm n h q 1 2).coeff m) 0 p =
      -(h (seedTau p) * seedTau p) * ((n : ℂ) * (seedLinear p ^ (n - 1) * X 2).coeff m) := by
    unfold coordPartial
    have hfe : (fun s : ℝ => (seedForm n h (Function.update p 0 s) 1 2).coeff m) =
        fun s : ℝ => -(h (seedTau p) * seedTau p) * (seedLinear (Function.update p 0 s) ^ n).coeff m := by
      funext s; rw [coeff_seedForm_12, seedTau_update0]
    rw [hfe]
    exact ((hasDerivAt_seedLinear_pow_zero n m p).const_mul (-(h (seedTau p) * seedTau p))).deriv
  have hterm_b : coordPartial (fun q => (seedForm n h q 0 2).coeff m) 1 p =
      h (seedTau p) * ((n : ℂ) * (seedLinear p ^ (n - 1) * (-(C (seedTau p) * X 2))).coeff m) := by
    unfold coordPartial
    have hfe : (fun s : ℝ => (seedForm n h (Function.update p 1 s) 0 2).coeff m) =
        fun s : ℝ => h (seedTau p) * (seedLinear (Function.update p 1 s) ^ n).coeff m := by
      funext s; rw [coeff_seedForm_02, seedTau_update1]
    rw [hfe]
    exact ((hasDerivAt_seedLinear_pow_one n m p).const_mul (h (seedTau p))).deriv
  rw [hterm_a, hterm_b, hterm_c, coeff_seedLinear_pow_mul_negCX2]
  ring

/-- `Alt3 n h m p 0 1 3 = 0`: vanishes by direct structural cancellation, the index-`3` analogue
of `Alt3_012`. -/
theorem Alt3_013 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    Alt3 n h m p 0 1 3 = 0 := by
  unfold Alt3
  have hterm_c : coordPartial (fun q => (seedForm n h q 0 1).coeff m) 3 p = 0 := by
    unfold coordPartial
    have hz : (fun s : ℝ => (seedForm n h (Function.update p 3 s) 0 1).coeff m) = fun _ => (0 : ℂ) := by
      funext s; exact coeff_seedForm_01 n h m (Function.update p 3 s)
    rw [hz, deriv_const]
  have hterm_a : coordPartial (fun q => (seedForm n h q 1 3).coeff m) 0 p =
      (-(h (seedTau p) * seedTau p) * Complex.I) *
        ((n : ℂ) * (seedLinear p ^ (n - 1) * X 2).coeff m) := by
    unfold coordPartial
    have hfe : (fun s : ℝ => (seedForm n h (Function.update p 0 s) 1 3).coeff m) =
        fun s : ℝ => (-(h (seedTau p) * seedTau p) * Complex.I) *
          (seedLinear (Function.update p 0 s) ^ n).coeff m := by
      funext s; rw [coeff_seedForm_13, seedTau_update0]
    rw [hfe]
    exact ((hasDerivAt_seedLinear_pow_zero n m p).const_mul
      (-(h (seedTau p) * seedTau p) * Complex.I)).deriv
  have hterm_b : coordPartial (fun q => (seedForm n h q 0 3).coeff m) 1 p =
      (h (seedTau p) * Complex.I) *
        ((n : ℂ) * (seedLinear p ^ (n - 1) * (-(C (seedTau p) * X 2))).coeff m) := by
    unfold coordPartial
    have hfe : (fun s : ℝ => (seedForm n h (Function.update p 1 s) 0 3).coeff m) =
        fun s : ℝ => (h (seedTau p) * Complex.I) *
          (seedLinear (Function.update p 1 s) ^ n).coeff m := by
      funext s; rw [coeff_seedForm_03, seedTau_update1]
    rw [hfe]
    exact ((hasDerivAt_seedLinear_pow_one n m p).const_mul (h (seedTau p) * Complex.I)).deriv
  rw [hterm_a, hterm_b, hterm_c, coeff_seedLinear_pow_mul_negCX2]
  ring

end TernaryPeriodPolynomials.Argument
