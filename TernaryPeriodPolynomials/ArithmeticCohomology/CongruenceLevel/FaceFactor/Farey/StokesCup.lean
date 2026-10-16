module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Farey.StokesKey
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CuspHomSum

@[expose] public section


/-!
# Twisted Farey Stokes, part 3: `cupForm` as a sum of cusp terms plus a primitive of the cup cocycle

Formalized by Claude Sonnet 5.5.

`cupForm_eq_cusp_sum`: for twisted cusp functions `Φ`, `Φ'` with crossed homomorphisms `f = fTw Φ`, `g = coc(G')` (`G'` the cochain carrying the cocycle of `Φ'`, `deltaTw`) and ANY `η : Γ(N) → ℂ` with
`η(xy) = η x + η y − ⟨f x, x · g y⟩` (a primitive of the cup cocycle `cup11 f g`): `cupForm Φ Φ' = 2 ∑_c (⟨Φ(c), g(σ_c)⟩ + η(σ_c))`.  For strictly equivariant `Φ` (`f = 0`, `η` a homomorphism) this is `pV_bdry_eq`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

variable {N : ℕ}

/-- The cochain carrying the cocycle of a twisted cusp function `Φ'`. -/
def cuspG (hN : 3 ≤ N) {A' : Rep ℂ (gammaNGL N)} {Φ' : RationalLine2 → A'} (hΦ' : Φ' ∈ Tw A'.ρ) : C1 A'.ρ :=
  deltaTw A' (HhatFn A' (gammaNFareyData hN) (fTw A' Φ')) (fTw A' Φ')
    (HhatFn_twisted A' (gammaNFareyData hN) (fTw A' Φ') (fTw_cocycle A' hΦ'))

/-- **The twisted cusp formula for the Poincaré-Lefschetz cup form.** -/
theorem cupForm_eq_cusp_sum (hN : 3 ≤ N) {A A' : Rep ℂ (gammaNGL N)} (C : Coupling A.ρ A'.ρ) {Φ : RationalLine2 → A}
    (hΦ : Φ ∈ Tw A.ρ) {Φ' : RationalLine2 → A'} (hΦ' : Φ' ∈ Tw A'.ρ) (η : gammaNGL N → ℂ)
    (hη : ∀ x y, η (x * y) = η x + η y - C.e (fTw A Φ x) (A'.ρ x (coc A'.ρ (cuspG hN hΦ') y))) :
    cupForm hN C Φ Φ' = 2 * ∑ c ∈ (cuspReps hN).R, (C.e (Φ c) (coc A'.ρ (cuspG hN hΦ') (cuspSigma c)) + η (cuspSigma c)) := by
  rw [← pV_bdry_deltaTw hN C hΦ hΦ']
  change pV C (gammaNFareyData hN) (bdryTw A.ρ hN ⟨Φ, hΦ⟩) (cuspG hN hΦ') = _
  rw [pV_bdryTw_eq hN C hΦ (cuspG hN hΦ')]
  congr 1
  have hf := fTw_cocycle A hΦ
  have hη' : ∀ x y, (fun x => - etaPre hN C (fTw A Φ) (cuspG hN hΦ') x) (x * y) =
      (fun x => - etaPre hN C (fTw A Φ) (cuspG hN hΦ') x) x + (fun x => - etaPre hN C (fTw A Φ) (cuspG hN hΦ') x) y -
        C.e (fTw A Φ x) (A'.ρ x (coc A'.ρ (cuspG hN hΦ') y)) := by
    intro x y
    simp only
    rw [etaPre_mul hN C (fTw A Φ) hf]
    ring
  have hsum := cusp_sum_eq_of_relation hN (fun x y => C.e (fTw A Φ x) (A'.ρ x (coc A'.ρ (cuspG hN hΦ') y))) η
    (fun x => - etaPre hN C (fTw A Φ) (cuspG hN hΦ') x) hη hη'
  rw [Finset.sum_add_distrib, hsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
