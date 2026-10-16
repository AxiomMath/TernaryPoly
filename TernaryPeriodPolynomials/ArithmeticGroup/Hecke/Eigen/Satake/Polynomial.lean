module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.LineEigen

@[expose] public section


/-!
# The Satake polynomial of the plane eigencharacter

At the cohomological point the plane eigenvalues of the three generators at `p ≠ 3` are

* `μ₁ = χ + (p² + p) e ω`   (`diag(p,1,1)`),
* `μ₂ = p² e² ω_c + (p + 1) χ e ω`   (`diag(p,p,1)`),
* `μ₃ = χ e² ω_c`   (`p · 1`),

with `χ = χ(sAd p)`, `ω = ω(diag(p,1))`, `ω_c = ω_σ(sAd p)` and `e = p^{-(n+3)/2}`. These satisfy the
Satake factorization

`X³ - μ₁ X² + p μ₂ X - p³ μ₃ = (X - χ) (X² - (p² + p) e ω X + p³ e² ω_c)`.

So the eigencharacter determines the cubic, `χ(sAd p)` is one of its roots, and the cofactor is the
`GL₂` Hecke polynomial of the cusp. This is the algebraic core of the strong-multiplicity-one step of
eigencharacter separation.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.RepresentationTheory

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

/-- **The Satake factorization** as a polynomial identity in the eigenvalues. -/
theorem satake_factorization (p χ ω ωc e X : ℂ) :
    X ^ 3 - (χ + (p ^ 2 + p) * (e * ω)) * X ^ 2 +
        p * (p ^ 2 * (e ^ 2 * ωc) + (p + 1) * (χ * (e * ω))) * X - p ^ 3 * (χ * (e ^ 2 * ωc)) =
      (X - χ) * (X ^ 2 - (p ^ 2 + p) * (e * ω) * X + p ^ 3 * (e ^ 2 * ωc)) := by
  ring

/-- The rank-one character value is a root of the Satake cubic of the eigencharacter. -/
theorem satake_root (p χ ω ωc e : ℂ) :
    χ ^ 3 - (χ + (p ^ 2 + p) * (e * ω)) * χ ^ 2 +
        p * (p ^ 2 * (e ^ 2 * ωc) + (p + 1) * (χ * (e * ω))) * χ - p ^ 3 * (χ * (e ^ 2 * ωc)) = 0 := by
  rw [satake_factorization]; ring

theorem exp_sq_half (n : ℕ) (L : ℂ) :
    Complex.exp (-(((n : ℂ) + 3) * L)) = Complex.exp (-(((n : ℂ) + 3) / 2 * L)) ^ 2 := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- **The Satake factorization of the actual plane eigencharacter.** For `p ≠ 3`, under the
nonzero-smooth and nontrivial-fixed-space premises, the three actual plane eigenvalues at the
cohomological point satisfy the Satake factorization with root `χ(sAd p)`. -/
theorem plane_satake_polynomial {n p : ℕ} (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t₁ t₂ t₃ : HeckeCorrespondence) (ht₁ : AwayThree t₁) (ht₂ : AwayThree t₂) (ht₃ : AwayThree t₃)
    (hg₁ : t₁.g = gP hp) (hg₂ : t₂.g = gP2 hp) (hg₃ : t₃.g = pScalar hp)
    (hsm : ∃ v ∈ D.cusp.smooth, v ≠ 0) [Nontrivial (fixedVectors D.cusp K3)]
    (f : AdelicGL → ℂ) (hf : IsInduced D .plane cohomologicalPoint f) (g : AdelicGL)
    (hfg : f g ≠ 0) (μ₁ μ₂ μ₃ : ℂ)
    (h₁ : ∑ r ∈ t₁.representatives, f (g * atFinite (rationalFinite r)) = μ₁ * f g)
    (h₂ : ∑ r ∈ t₂.representatives, f (g * atFinite (rationalFinite r)) = μ₂ * f g)
    (h₃ : ∑ r ∈ t₃.representatives, f (g * atFinite (rationalFinite r)) = μ₃ * f g) (X : ℂ) :
    X ^ 3 - μ₁ * X ^ 2 + (p : ℂ) * μ₂ * X - (p : ℂ) ^ 3 * μ₃ =
      (X - D.chi.toMonoidHom (sAd (pUnit hp))) *
        (X ^ 2 - ((p : ℂ) ^ 2 + p) * (Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ))) *
            omega D.cusp (Bo (dP hp))) * X +
          (p : ℂ) ^ 3 * (Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ))) ^ 2 *
            D.cusp.centralCharacter (sAd (pUnit hp)))) := by
  have e₁ := (prime_plane_eigenvalue_cohomological D hp h3 t₁ ht₁ hg₁ f hf g).symm.trans h₁
  have e₂ := (prime2_plane_eigenvalue_cohomological D hp h3 t₂ ht₂ hg₂ hsm f hf g).symm.trans h₂
  have e₃ := (central_plane_eigenvalue_cohomological D hp h3 t₃ ht₃ hg₃ hsm f hf g).symm.trans h₃
  have m₁ := mul_right_cancel₀ hfg e₁
  have m₂ := mul_right_cancel₀ hfg e₂
  have m₃ := mul_right_cancel₀ hfg e₃
  rw [← m₁, ← m₂, ← m₃, exp_sq_half]
  exact satake_factorization _ _ _ _ _ X

/-- Equal Satake cubics with a common linear factor have equal quadratic cofactors. -/
theorem cofactor_unique (p χ ω ω' ωc ωc' e : ℂ) (hp : p ≠ 0) (he : e ≠ 0) (hpp : p ^ 2 + p ≠ 0)
    (h : ∀ X : ℂ, (X - χ) * (X ^ 2 - (p ^ 2 + p) * (e * ω) * X + p ^ 3 * (e ^ 2 * ωc)) =
      (X - χ) * (X ^ 2 - (p ^ 2 + p) * (e * ω') * X + p ^ 3 * (e ^ 2 * ωc'))) :
    ω = ω' ∧ ωc = ωc' := by
  have hq : ∀ X : ℂ, X ≠ χ → (p ^ 2 + p) * (e * (ω' - ω)) * X = p ^ 3 * (e ^ 2 * (ωc' - ωc)) := by
    intro X hX
    have := mul_left_cancel₀ (sub_ne_zero.mpr hX) (h X)
    linear_combination this
  have h1 := hq (χ + 1) (by intro h; have := congrArg (· - χ) h; simp at this)
  have h2 := hq (χ + 2) (by intro h; have := congrArg (· - χ) h; norm_num at this)
  have hω : (p ^ 2 + p) * (e * (ω' - ω)) = 0 := by linear_combination h2 - h1
  have hω' : ω' - ω = 0 := by
    rcases mul_eq_zero.mp hω with h | h
    · exact absurd h hpp
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h he
      · exact h
  have hc : p ^ 3 * (e ^ 2 * (ωc' - ωc)) = 0 := by
    rw [← h1, hω', mul_zero, mul_zero, zero_mul]
  have hc' : ωc' - ωc = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h (pow_ne_zero _ hp)
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (pow_ne_zero _ he)
      · exact h
  exact ⟨(sub_eq_zero.mp hω').symm, (sub_eq_zero.mp hc').symm⟩

/-- **The eigencharacter and the rank-one character determine the cusp's Hecke data at `p`.**
Two inducing data with the same plane eigenvalues of the three generators at `p ≠ 3` and the same
value `χ(sAd p)` have the same Hecke scalar `ω(diag(p,1))` and the same central value
`ω_σ(sAd p)`. -/
theorem hecke_data_of_eigencharacter {n p : ℕ} (D D' : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t₁ t₂ t₃ : HeckeCorrespondence) (ht₁ : AwayThree t₁) (ht₂ : AwayThree t₂) (ht₃ : AwayThree t₃)
    (hg₁ : t₁.g = gP hp) (hg₂ : t₂.g = gP2 hp) (hg₃ : t₃.g = pScalar hp)
    (hsm : ∃ v ∈ D.cusp.smooth, v ≠ 0) [Nontrivial (fixedVectors D.cusp K3)]
    (hsm' : ∃ v ∈ D'.cusp.smooth, v ≠ 0) [Nontrivial (fixedVectors D'.cusp K3)]
    (f : AdelicGL → ℂ) (hf : IsInduced D .plane cohomologicalPoint f) (g : AdelicGL) (hfg : f g ≠ 0)
    (f' : AdelicGL → ℂ) (hf' : IsInduced D' .plane cohomologicalPoint f') (g' : AdelicGL)
    (hfg' : f' g' ≠ 0) (μ₁ μ₂ μ₃ : ℂ)
    (h₁ : ∑ r ∈ t₁.representatives, f (g * atFinite (rationalFinite r)) = μ₁ * f g)
    (h₂ : ∑ r ∈ t₂.representatives, f (g * atFinite (rationalFinite r)) = μ₂ * f g)
    (h₃ : ∑ r ∈ t₃.representatives, f (g * atFinite (rationalFinite r)) = μ₃ * f g)
    (h₁' : ∑ r ∈ t₁.representatives, f' (g' * atFinite (rationalFinite r)) = μ₁ * f' g')
    (h₂' : ∑ r ∈ t₂.representatives, f' (g' * atFinite (rationalFinite r)) = μ₂ * f' g')
    (h₃' : ∑ r ∈ t₃.representatives, f' (g' * atFinite (rationalFinite r)) = μ₃ * f' g')
    (hχ : D.chi.toMonoidHom (sAd (pUnit hp)) = D'.chi.toMonoidHom (sAd (pUnit hp))) :
    omega D.cusp (Bo (dP hp)) = omega D'.cusp (Bo (dP hp)) ∧
      D.cusp.centralCharacter (sAd (pUnit hp)) = D'.cusp.centralCharacter (sAd (pUnit hp)) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpp : (p : ℂ) ^ 2 + p ≠ 0 := by
    have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have h2 : (0 : ℝ) < (p : ℝ) ^ 2 + p := by positivity
    exact_mod_cast h2.ne'
  apply cofactor_unique (p : ℂ) (D.chi.toMonoidHom (sAd (pUnit hp))) _ _ _ _ _ hp0
    (Complex.exp_ne_zero _) hpp
  intro X
  rw [← plane_satake_polynomial D hp h3 t₁ t₂ t₃ ht₁ ht₂ ht₃ hg₁ hg₂ hg₃ hsm f hf g hfg μ₁ μ₂ μ₃
    h₁ h₂ h₃ X, plane_satake_polynomial D' hp h3 t₁ t₂ t₃ ht₁ ht₂ ht₃ hg₁ hg₂ hg₃ hsm' f' hf' g' hfg'
    μ₁ μ₂ μ₃ h₁' h₂' h₃' X, hχ]

end TernaryPeriodPolynomials.HeckeEigen.Satake
