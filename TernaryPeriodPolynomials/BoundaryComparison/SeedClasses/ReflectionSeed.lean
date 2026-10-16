module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedClass
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedConj

@[expose] public section


/-!
# The reflection `r = diag(-1, 1, 1)` acts on the seed by the conjugate seed (Lemma C.3)

Paper: Lemma C.3
(`ar:lem:seed`),: "The finite reflection projection supplies the corresponding
full-level statement"; the antiholomorphic seeds are obtained by complex conjugation, including the
coefficient polynomial and the differentials.

An element of `GL₂(ℤ)` of determinant `-1`, e.g. `J = diag(-1, 1)`, acts on the plane face by an
antiholomorphic map: `r(u₁, u₂, x, y) = (-u₁, u₂, -x, y)`, `τ ↦ -\bar τ` (`reflMap5`).
For a function
`h` and `h^*(z) = \overline{h(-\bar z)}` (`hStar`) one has, in the coefficient-matrix model,

`r^* ω_h = (-1)^n · \overline{ω_{h^*}}(-X, Y, Z)`   (`refl_pullback`),

i.e. `r^* ω_h = (-1)^{n+1} ρ(r) \overline{ω_{h^*}}` since `ρ(r) q = -q(-X, Y, Z)`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

open TernaryPeriodPolynomials.Argument

/-- The reflection `(u₁, u₂, x, y, t) ↦ (-u₁, u₂, -x, y, t)` of the plane coordinates (the action
of `diag(-1, 1, 1)`, with `τ ↦ -\bar τ`). -/
def reflMap5 (p : Fin 5 → ℝ) : Fin 5 → ℝ := ![-p 0, p 1, -p 2, p 3, p 4]

/-- The conjugate cusp form `h^*(z) = \overline{h(-\bar z)}`. -/
def hStar (h : ℂ → ℂ) : ℂ → ℂ := fun z => conj (h (-conj z))

/-- The signs `(-1, 1, -1, 1, 1)` of the reflection. -/
def reflSign : Fin 5 → ℝ := ![-1, 1, -1, 1, 1]

def reflCLM : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  ContinuousLinearMap.pi fun a => reflSign a • ContinuousLinearMap.proj a

theorem reflCLM_apply (p : Fin 5 → ℝ) (a : Fin 5) : reflCLM p a = reflSign a * p a := by
  simp [reflCLM]

theorem reflMap5_eq : reflMap5 = ⇑reflCLM := by
  funext p a
  rw [reflCLM_apply]
  fin_cases a <;> simp [reflMap5, reflSign]

theorem fderiv_reflMap5 (p : Fin 5 → ℝ) (v : Fin 5 → ℝ) (a : Fin 5) :
    fderiv ℝ reflMap5 p v a = reflSign a * v a := by
  rw [reflMap5_eq, reflCLM.fderiv, reflCLM_apply]

theorem seedTau_reflMap5 (p : Fin 5 → ℝ) : seedTau (reflMap5 p) = -conj (seedTau p) := by
  simp [seedTau, reflMap5, Complex.ext_iff]

theorem seedLinear_reflMap5 (p : Fin 5 → ℝ) :
    seedLinear (reflMap5 p) =
      -bind₁ (![-X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
        (MvPolynomial.map (starRingEnd ℂ) (seedLinear p)) := by
  simp only [seedLinear, seedTau_reflMap5, map_sub, map_add, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, map_neg, bind₁_C_right, bind₁_X_right]
  have h0 : (reflMap5 p 0 : ℂ) = -(p 0 : ℂ) := by simp [reflMap5]
  have h1 : (reflMap5 p 1 : ℂ) = (p 1 : ℂ) := by simp [reflMap5]
  rw [h0, h1]
  simp
  ring

theorem refl_coeff (h hs : ℂ → ℂ) (p : Fin 5 → ℝ)
    (hhs : hs (seedTau p) = conj (h (-conj (seedTau p)))) (i j : Fin 5) :
    reflSign i * reflSign j * (h (seedTau (reflMap5 p)) *
        (seedBeta (reflMap5 p) i * seedDTau j - seedBeta (reflMap5 p) j * seedDTau i)) =
      conj (hs (seedTau p) *
        (seedBeta p i * seedDTau j - seedBeta p j * seedDTau i)) := by
  have ht : seedTau (reflMap5 p) = -conj (seedTau p) := seedTau_reflMap5 p
  have hh : conj (hs (seedTau p)) = h (-conj (seedTau p)) := by
    rw [hhs]; simp
  rw [map_mul, hh, ht]
  fin_cases i <;> fin_cases j <;>
    simp [seedBeta, seedDTau, reflSign, ht]

/-- **The reflection acts on the seed by the conjugate seed.** For `r = diag(-1, 1, 1)`,
`r^*ω_h = (-1)^n · \overline{ω_{h^*}}(-X, Y, Z)` (coefficientwise conjugation of the whole form,
polynomial and differentials, followed by the substitution `𝐗 ↦ r⁻¹𝐗`). -/
theorem formPullback_reflMap5 (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback reflMap5 (seedForm n h) p i j =
      C ((reflSign i * reflSign j : ℝ) : ℂ) * seedForm n h (reflMap5 p) i j := by
  unfold formPullback
  simp only [fderiv_reflMap5, Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i (fun x _ hx => ?_) (by simp)]
  · rw [Finset.sum_eq_single j (fun x _ hx => ?_) (by simp)]
    · simp
    · simp [hx]
  · apply Finset.sum_eq_zero
    intro y _
    simp [hx]

theorem refl_pullback (n : ℕ) (h hs : ℂ → ℂ) (p : Fin 5 → ℝ)
    (hhs : hs (seedTau p) = conj (h (-conj (seedTau p)))) (i j : Fin 5) :
    formPullback reflMap5 (seedForm n h) p i j =
      C ((-1 : ℂ) ^ n) * bind₁ (![-X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
        (MvPolynomial.map (starRingEnd ℂ) (seedForm n hs p i j)) := by
  have hpull := formPullback_reflMap5 n h p i j
  rw [hpull]
  have hc := refl_coeff h hs p hhs i j
  have key : (C ((reflSign i * reflSign j : ℝ) : ℂ) *
      (C (h (seedTau (reflMap5 p))) *
        C (seedBeta (reflMap5 p) i * seedDTau j - seedBeta (reflMap5 p) j * seedDTau i)) :
        MvPolynomial (Fin 3) ℂ) =
      C ((starRingEnd ℂ) (hs (seedTau p) *
        (seedBeta p i * seedDTau j - seedBeta p j * seedDTau i))) := by
    rw [← map_mul, ← map_mul, ← hc]
    push_cast
    ring_nf
  unfold seedForm
  rw [seedLinear_reflMap5]
  simp only [map_mul, map_pow, map_neg, MvPolynomial.map_C, bind₁_C_right, map_one]
  simp only [map_mul] at key
  rw [neg_pow]
  linear_combination ((bind₁ (![-X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ))
    (MvPolynomial.map (starRingEnd ℂ) (seedLinear p)) ^ n * (-1 : MvPolynomial (Fin 3) ℂ) ^ n) *
      key

end TernaryPeriodPolynomials.Argument.SeedC3
