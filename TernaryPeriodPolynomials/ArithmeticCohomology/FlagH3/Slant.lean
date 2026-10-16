module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Independence
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.FunctionalDecomp

@[expose] public section



/-!
# Any cycle functional on `H³` of a flag group is a multiple of `λ`

Formalized by Claude Sonnet 5.5.

Since `dim H³(B, ℚ) = 1`, for every bar `3`-cycle `z'` of the flag group there is a rational `m` with `∑ z'(g) Θ(g) = m · λ[Θ]` for all `3`-cocycles `Θ` (`exists_chainEval_eq_mul_lam`),
and `m` is read off from the Heisenberg cocycle: `∑ z'(g) θ(g) = m · (-2 p² q²)` (`chainEval_theta_eq`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

open TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable {B : Type} [Group B]

/-- **Every cycle functional on `H³` of a flag group is a multiple of `λ`.** -/
theorem exists_cycleFunctional_eq_smul (D : FlagCohomDatum B) (z' : (Fin 3 → B) →₀ ℚ) (hz' : IsCycle z') :
    ∃ m : ℚ, cycleFunctional z' hz' = m • D.lam := by
  have := D.finite
  exact functional_eq_smul D.finrank_eq_one.le D.lam (cycleFunctional z' hz') D.lam_ne_zero

/-- On cocycles: `∑ z'(g) Θ(g) = m · λ[Θ]` for a universal `m`. -/
theorem exists_chainEval_eq_mul_lam (D : FlagCohomDatum B) (z' : (Fin 3 → B) →₀ ℚ) (hz' : IsCycle z') :
    ∃ m : ℚ, ∀ (Θ : (Fin 3 → B) → ℚ) (hΘ : dThree Θ = 0), chainEval z' Θ = m * D.lam (cocycleClass Θ hΘ) := by
  obtain ⟨m, hm⟩ := exists_cycleFunctional_eq_smul D z' hz'
  refine ⟨m, fun Θ hΘ => ?_⟩
  rw [← cycleFunctional_cocycleClass z' hz' Θ hΘ, hm]
  rfl

namespace HeisCoords

variable (H : HeisCoords B)

/-- **The constant `m`**: if the cycle functional of `z'` is `m • λ` for the flag datum `flagData`, then
`m · (-2 p² q²) = ∑ z'(g) θ(g)` for the Heisenberg cocycle `θ`; so `m` is read off by evaluating the Heisenberg cocycle on `z'`. -/
theorem chainEval_theta_eq (E : GroupExtension (Multiplicative (ℤ × ℤ)) B (Multiplicative ℤ)) (X Y : B) (p q : ℤ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hXa : H.a X = p) (hXb : H.b X = 0) (hXc : H.c X = 0) (hYa : H.a Y = 0)
    (hYb : H.b Y = q) (hYc : H.c Y = 0) (z' : (Fin 3 → B) →₀ ℚ) (hz' : IsCycle z') (m : ℚ)
    (hm : cycleFunctional z' hz' = m • (H.flagData E X Y p q hp hq hXa hXb hXc hYa hYb hYc).lam) :
    chainEval z' H.theta = m * (-2 * (p : ℚ) ^ 2 * (q : ℚ) ^ 2) := by
  rw [← cycleFunctional_cocycleClass z' hz' H.theta H.theta_cocycle, hm, LinearMap.smul_apply, smul_eq_mul,
    H.flagData_lam_theta E X Y p q hp hq hXa hXb hXc hYa hYb hYc]

end HeisCoords

end TernaryPeriodPolynomials.Argument.FlagH3
