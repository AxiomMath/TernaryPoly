module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.ClosednessAssembly
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Translation
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviAssembly
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Potential

@[expose] public section


/-! Target: Lemma C.3 (`ar:lem:seed`) of the paper, in plane coordinates. -/

open MvPolynomial

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Lemma C.3.** The seed `ω_h = h(τ)𝓑ⁿ β ∧ dτ` (equation `ar:eq:seed`) is closed for every
function `h` holomorphic at `τ`; a radical translation `u ↦ u + v` acts on it by the coefficient
action `(X, Y) ↦ (X - v₁Z, Y - v₂Z)` of `u(v)`; for `g = diag(A, t)` with `det A > 0` and
`t > 0` one has `g*ω_h = ρ(g) ω_{δ^{k/2}(h|_k A)}`, `k = n + 3` (equation `ar:eq:seed-transform`);
and at `u = 0` the radical cochain `(τY - X)ⁿ(1, -τ)` is the gradient of the potential
`-(τY - X)^{n+1}/(n+1)`. -/
theorem seed_closed_equivariant (n : ℕ) (h : ℂ → ℂ) :
    (∀ p : Fin 5 → ℝ, 0 < p 3 → DifferentiableAt ℂ h (seedTau p) →
      ∀ (m : Fin 3 →₀ ℕ) (i j k : Fin 5),
        coordPartial (fun q => (seedForm n h q j k).coeff m) i p -
          coordPartial (fun q => (seedForm n h q i k).coeff m) j p +
          coordPartial (fun q => (seedForm n h q i j).coeff m) k p = 0) ∧
    (∀ (p : Fin 5 → ℝ) (v w : ℝ) (i j : Fin 5),
      seedForm n h (p + ![v, w, 0, 0, 0]) i j =
        bind₁ ![X 0 - C (v : ℂ) * X 2, X 1 - C (w : ℂ) * X 2, X 2] (seedForm n h p i j)) ∧
    (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ), 0 < A.det → 0 < t →
      ∀ p : Fin 5 → ℝ, 0 < p 3 → ∀ i j : Fin 5,
        formPullback (leviMap A t) (seedForm n h) p i j =
          leviCoefficientAction A t (seedForm n (slashTwisted (n + 3) A h) p i j)) ∧
    (∀ p : Fin 5 → ℝ, p 0 = 0 → p 1 = 0 →
      pderiv 0 (-(C ((n : ℂ) + 1)⁻¹ * seedLinear p ^ (n + 1))) =
          C (seedBeta p 0) * seedLinear p ^ n ∧
        pderiv 1 (-(C ((n : ℂ) + 1)⁻¹ * seedLinear p ^ (n + 1))) =
          C (seedBeta p 1) * seedLinear p ^ n) :=
  ⟨seed_closed n h, lemma_C3_ii n h, lemma_C3_iii n h, fun p _ _ => lemma_C3_iv n p⟩

end TernaryPeriodPolynomials
