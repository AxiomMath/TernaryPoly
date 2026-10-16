module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviAssembly
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Potential
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


/-!
# The radical Lie-algebra cohomology of Lemma C.3 and the radical class of the seed

Paper: Appendix C (lines ~1365
and ~3552). Over `ℂ` (the paper computes "after complexification") the radical Lie algebra
`⟨e₁, e₂⟩` of the plane parabolic acts on `E = ℂ[X, Y, Z]_n` by the root operators
`ν₁ = -Z ∂_X`, `ν₂ = -Z ∂_Y`. A 1-cochain is a pair `(a, b) = (c(e₁), c(e₂))`, it is a cocycle iff
`ν₁ b = ν₂ a`, i.e. `a_Y = b_X`, and the coboundaries are `(ν₁ e, ν₂ e)`.

The identification of the class with a binary form is the potential modulo `Z`:
a closed homogeneous pair is the gradient `(P_X, P_Y)` of a homogeneous potential of degree `n + 1`,
the exact pairs being the gradients of the potentials divisible by `Z`. By Euler's identity the
potential modulo `Z` is `P|_{Z=0} = (X a|_{Z=0} + Y b|_{Z=0})/(n+1)`, which is the map
`radicalContraction`. The seed `ω_h` has radical cochain `(ω_h(e₁, ∂_x), ω_h(e₂, ∂_x))
= h(τ) 𝓑ⁿ (1, -τ)`, and its class is `-(h(τ)/(n+1)) (τY - X)^{n+1}`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

/-- The root operator `ν₁ = -Z ∂_X` of the radical Lie algebra on `E = ℂ[X,Y,Z]_n`
(the infinitesimal form of `ρ(exp(s e₁)) f(𝐗) = f(X - sZ, Y, Z)`). -/
def radicalOpX (q : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℂ := -(X 2 * pderiv 0 q)

/-- The root operator `ν₂ = -Z ∂_Y`. -/
def radicalOpY (q : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℂ := -(X 2 * pderiv 1 q)

/-- A radical Lie-algebra 1-cocycle `(a, b)` of the abelian algebra `⟨e₁, e₂⟩`: `ν₁ b = ν₂ a`. -/
def IsRadicalCocycle (a b : MvPolynomial (Fin 3) ℂ) : Prop := radicalOpX b = radicalOpY a

/-- Setting `Z = 0`: reduction of a coefficient polynomial modulo `Z`. -/
def setZ : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  bind₁ (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) ℂ)

/-- The potential-modulo-`Z` map: the contraction `(a, b) ↦ (X a|_{Z=0} + Y b|_{Z=0})/(n+1)`. For a
closed homogeneous pair of degree `n` this is the potential `P` of degree `n + 1` (with
`(a, b) = (∂_X P, ∂_Y P)`) reduced modulo `Z`. -/
def radicalContraction (n : ℕ) (a b : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℂ :=
  C (((n : ℂ) + 1)⁻¹) * (X 0 * setZ a + X 1 * setZ b)

/-- Partial derivatives of a polynomial commute. -/
theorem pderiv_comm' {σ : Type*} (i j : σ) (q : MvPolynomial σ ℂ) :
    pderiv i (pderiv j q) = pderiv j (pderiv i q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hp]
    classical
    have h1 : ∀ a b : σ, pderiv a (X b : MvPolynomial σ ℂ) = if a = b then 1 else 0 := by
      intro a b
      by_cases h : a = b
      · simp [h]
      · simp [h]
    simp only [h1]
    split_ifs <;> simp <;> ring

theorem isRadicalCocycle_iff (a b : MvPolynomial (Fin 3) ℂ) :
    IsRadicalCocycle a b ↔ pderiv 0 b = pderiv 1 a := by
  unfold IsRadicalCocycle radicalOpX radicalOpY
  rw [neg_inj]
  exact mul_right_inj' (X_ne_zero (2 : Fin 3))

theorem setZ_X_two_mul (q : MvPolynomial (Fin 3) ℂ) : setZ (X 2 * q) = 0 := by
  simp [setZ]

/-- Exact pairs `(ν₁ e, ν₂ e)` are cocycles. -/
theorem isRadicalCocycle_coboundary (e : MvPolynomial (Fin 3) ℂ) :
    IsRadicalCocycle (radicalOpX e) (radicalOpY e) := by
  rw [isRadicalCocycle_iff]
  unfold radicalOpX radicalOpY
  simp only [map_neg, Derivation.leibniz, smul_eq_mul,
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide), mul_zero, add_zero, pderiv_comm' 0 1 e]

/-- Exact pairs have zero contraction: the identification is well defined on cohomology. -/
theorem radicalContraction_coboundary (n : ℕ) (e : MvPolynomial (Fin 3) ℂ) :
    radicalContraction n (radicalOpX e) (radicalOpY e) = 0 := by
  unfold radicalContraction radicalOpX radicalOpY
  simp [setZ_X_two_mul, map_neg]

open TernaryPeriodPolynomials.Argument

theorem seedBeta_zero (p : Fin 5 → ℝ) : seedBeta p 0 = 1 := by simp [seedBeta]

theorem seedBeta_one (p : Fin 5 → ℝ) : seedBeta p 1 = -seedTau p := by simp [seedBeta]

/-- The radical components `ω_h(e_i, ∂_x)` of the seed, for the plane directions `i = u₁, u₂`. -/
theorem seedForm_apply_two (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i : Fin 5) :
    seedForm n h p i 2 = C (h (seedTau p) * seedBeta p i) * seedLinear p ^ n := by
  unfold seedForm
  congr 2
  have h2 : seedBeta p 2 = 0 := by simp [seedBeta]
  simp [seedDTau, h2]

/-- The radical cochain of the seed `ω_h` (the coefficients of `du₁, du₂` against `dτ`) is a
radical Lie-algebra 1-cocycle, at every point. -/
theorem seedRadical_isCocycle (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) :
    IsRadicalCocycle (seedForm n h p 0 2) (seedForm n h p 1 2) := by
  rw [isRadicalCocycle_iff, seedForm_apply_two n h p 0,
    seedForm_apply_two n h p 1, seedBeta_zero, seedBeta_one]
  rw [pderiv_C_mul, pderiv_C_mul, pderiv_pow, pderiv_pow, seedLinear_pderiv_zero,
    seedLinear_pderiv_one]
  simp only [map_neg, map_mul, mul_one]
  ring

theorem seedRadical_isHomogeneous (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i : Fin 5) :
    (seedForm n h p i 2).IsHomogeneous n := by
  rw [seedForm_apply_two n h p i]
  have hB : (seedLinear p).IsHomogeneous 1 := by
    unfold seedLinear
    exact (((isHomogeneous_C_mul_X _ _).sub (isHomogeneous_X ℂ _)).add
      (isHomogeneous_C_mul_X _ _))
  simpa using (isHomogeneous_C (Fin 3) (h (seedTau p) * seedBeta p i)).mul (hB.pow n)

theorem setZ_seedLinear (p : Fin 5 → ℝ) :
    setZ (seedLinear p) = C (seedTau p) * X 1 - X 0 := by
  simp [setZ, seedLinear]

/-- **Radical class of the seed.** The potential-modulo-`Z` class of the radical cochain of `ω_h`
is `-(h(τ)/(n+1)) (τY - X)^{n+1}`, at every point (it does not depend on `u`). -/
theorem seedRadical_contraction (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) :
    radicalContraction n (seedForm n h p 0 2) (seedForm n h p 1 2) =
      -(C (((n : ℂ) + 1)⁻¹ * h (seedTau p)) * (C (seedTau p) * X 1 - X 0) ^ (n + 1)) := by
  unfold radicalContraction
  rw [seedForm_apply_two n h p 0, seedForm_apply_two n h p 1,
    seedBeta_zero, seedBeta_one]
  have hC : ∀ c : ℂ, setZ (C c) = C c := fun c => by simp [setZ]
  simp only [map_mul, map_pow, setZ_seedLinear, hC]
  rw [pow_succ]
  simp only [map_neg, map_one]
  ring

end TernaryPeriodPolynomials.Argument.SeedC3
