module

public import TernaryPeriodPolynomials.ModularForm.Period.Axis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

noncomputable section
open Complex MvPolynomial

namespace TernaryPoly.BinaryCuspPeriod

/-- `X` is variable zero and `Y` is variable one. -/
def exponent (d j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j + Finsupp.single 1 (d - j)

@[simp] theorem exponent_zero (d j : ℕ) : exponent d j 0 = j := by
  simp [exponent]

@[simp] theorem exponent_one (d j : ℕ) : exponent d j 1 = d - j := by
  simp [exponent]

theorem exponent_injective (d : ℕ) : Function.Injective (exponent d) := by
  intro j l h
  simpa using congrArg (fun m => m 0) h

/-- The binomial coefficient of `X^j Y^(d-j)` in
`∫₀^{i∞} f(z) (zY-X)^d dz`, after writing `z = i*t` and `dz = i*dt`. -/
def periodCoefficient {d : ℕ} (f : Forms d) (j : ℕ) : ℂ :=
  (d.choose j : ℂ) * (-1) ^ j * I ^ (d - j + 1) * moment f (d - j + 1 : ℕ)

/-- Each finite coefficient is the binomial multiple of its actual imaginary-axis integral. -/
theorem periodCoefficient_eq_axisMoment {d : ℕ} (f : Forms d) (j : ℕ) :
    periodCoefficient f j = (d.choose j : ℂ) * (-1) ^ j * axisMoment f (d - j) := by
  rw [axisMoment_eq, periodCoefficient]
  ring

/-- The homogeneous period polynomial with convention `(zY-X)^d`. -/
def period {d : ℕ} (f : Forms d) : MvPolynomial (Fin 2) ℂ :=
  ∑ j ∈ Finset.range (d + 1), monomial (exponent d j) (periodCoefficient f j)

/-- Odd projection means retaining the odd powers of `X`. For even `d` both exponents are odd. -/
def oddPeriod {d : ℕ} (f : Forms d) : MvPolynomial (Fin 2) ℂ :=
  ∑ j ∈ (Finset.range (d + 1)).filter Odd,
    monomial (exponent d j) (periodCoefficient f j)

/-- Literal coefficient extraction in the finite Mellin expansion. -/
theorem coeff_period {d j : ℕ} (f : Forms d) (hj : j ≤ d) :
    (period f).coeff (exponent d j) = periodCoefficient f j := by
  classical
  rw [period, coeff_sum, Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp only [coeff_monomial, ite_eq_right (fun h => hbj (exponent_injective d h))]
  · simp only [Finset.mem_range]
    omega

/-- Odd projection leaves every odd-`X` coefficient unchanged. -/
theorem coeff_oddPeriod {d j : ℕ} (f : Forms d) (hj : j ≤ d) (ho : Odd j) :
    (oddPeriod f).coeff (exponent d j) = periodCoefficient f j := by
  classical
  rw [oddPeriod, coeff_sum, Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp only [coeff_monomial, ite_eq_right (fun h => hbj (exponent_injective d h))]
  · simp [Finset.mem_range, ho, Nat.lt_succ_iff.mpr hj]

/-- Coefficients with an even exponent of `X` vanish in the odd projection. -/
theorem coeff_oddPeriod_zero_of_even_x {d : ℕ} (f : Forms d)
    (m : Fin 2 →₀ ℕ) (hm : Even (m 0)) : (oddPeriod f).coeff m = 0 := by
  classical
  rw [oddPeriod, coeff_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [coeff_monomial]
  split_ifs with he
  · have hjodd := (Finset.mem_filter.mp hj).2
    have hzero : j = m 0 := by simpa using congrArg (fun z => z 0) he
    exact ((Nat.not_odd_iff_even.mpr hm) (hzero ▸ hjodd)).elim
  · rfl

/-- In even degree the odd projection also has only odd exponents of `Y`. -/
theorem coeff_oddPeriod_zero_of_even_y {d : ℕ} (hd : Even d) (f : Forms d)
    (m : Fin 2 →₀ ℕ) (hm : Even (m 1)) : (oddPeriod f).coeff m = 0 := by
  classical
  rw [oddPeriod, coeff_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [coeff_monomial]
  split_ifs with he
  · have hjle : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
    have hjodd := Nat.Even.sub_odd hjle hd (Finset.mem_filter.mp hj).2
    have hone : d - j = m 1 := by simpa using congrArg (fun z => z 1) he
    exact ((Nat.not_odd_iff_even.mpr hm) (hone ▸ hjodd)).elim
  · rfl

/-- The requested extreme coefficient before inserting the Gamma normalization. -/
theorem coeff_oddPeriod_extreme {d : ℕ} (hd : 0 < d) (f : Forms d) :
    (oddPeriod f).coeff (exponent d 1) = -(d : ℂ) * I ^ d * moment f (d : ℂ) := by
  rw [coeff_oddPeriod f hd (by decide)]
  have he : d - 1 + 1 = d := by omega
  simp [periodCoefficient, he]

/-- The full finite Mellin expansion is homogeneous of the expected degree. -/
theorem period_isHomogeneous {d : ℕ} (f : Forms d) : (period f).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro j hj
  apply isHomogeneous_monomial
  simp only [exponent, map_add, Finsupp.degree_single]
  have : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  omega

/-- The odd projection preserves the actual homogeneous degree. -/
theorem oddPeriod_isHomogeneous {d : ℕ} (f : Forms d) :
    (oddPeriod f).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro j hj
  apply isHomogeneous_monomial
  simp only [exponent, map_add, Finsupp.degree_single]
  have : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  omega

end TernaryPoly.BinaryCuspPeriod
