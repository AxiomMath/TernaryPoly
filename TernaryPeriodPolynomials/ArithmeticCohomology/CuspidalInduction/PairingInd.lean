module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Pairing

@[expose] public section


/-!
# Compatibility of the cup-form normalised cuspidal pairing with finite-index induction

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

**`cuspidal_pairing_ind`**: let `3 ≤ N`, `3 ≤ M`, `Γ(M) ≤ Γ(N)`, `V, V'` finite-dimensional `Γ(N)`-modules with a perfect `Γ(N)`-invariant pairing `e`, `Ind V = Fun(Γ(N)/Γ(M), V)` (action
`(s F)(x) = ρ(s) F(s⁻¹x)`), `Ind V'` likewise, with the summed pairing `e_ind(F, G) = ∑_x e(F x, G x)`.  If `B_N` is a form on the cuspidal groups of `Ind V × Ind V'` with the cup-form
property (`IsCupPairing`) and `B_M` one on the cuspidal groups of `V|Γ(M) × V'|Γ(M)`, then `B_N(x, y) = B_M(shapiro x, shapiro y)` for all cuspidal classes.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

variable {N M : ℕ} [Fintype (Gamma N ⧸ subM N M)] (V V' : Rep ℂ (Gamma N))
  (e : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)

instance indRep_fd [FiniteDimensional ℂ V] : FiniteDimensional ℂ (indRep M V) :=
  inferInstanceAs (FiniteDimensional ℂ (Gamma N ⧸ subM N M → V))

/-- The summed pairing on the induced modules. -/
def eInd : indRep M V →ₗ[ℂ] indRep M V' →ₗ[ℂ] ℂ := eindQ e

theorem eInd_apply (F : indRep M V) (G : indRep M V') :
    eInd (M := M) V V' e F G = ∑ x : Gamma N ⧸ subM N M, e (F x) (G x) := eindQ_apply e F G

theorem eInd_inv (hinv : ∀ (γ : Gamma N) v w, e (V.ρ γ v) (V'.ρ γ w) = e v w) (γ : Gamma N) (F : indRep M V)
    (G : indRep M V') :
    eInd (M := M) V V' e ((indRep M V).ρ γ F) ((indRep M V').ρ γ G) = eInd (M := M) V V' e F G :=
  eindQ_inv V.ρ V'.ρ e hinv γ F G

theorem eInd_left (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (F : indRep M V)
    (hF : ∀ G : indRep M V', eInd (M := M) V V' e F G = 0) : F = 0 := by
  funext x
  apply hL
  intro w
  have h0 := (eInd_apply (M := M) V V' e F (Function.update (0 : Gamma N ⧸ subM N M → V') x w)).symm.trans
    (hF (Function.update (0 : Gamma N ⧸ subM N M → V') x w))
  rw [Finset.sum_eq_single x] at h0
  · simpa using h0
  · intro y _ hy
    simp [Function.update_of_ne hy]
  · simp

theorem eInd_right (hR : ∀ w, (∀ v, e v w = 0) → w = 0) (G : indRep M V')
    (hG : ∀ F : indRep M V, eInd (M := M) V V' e F G = 0) : G = 0 := by
  funext x
  apply hR
  intro v
  have h0 := (eInd_apply (M := M) V V' e (Function.update (0 : Gamma N ⧸ subM N M → V) x v) G).symm.trans
    (hG (Function.update (0 : Gamma N ⧸ subM N M → V) x v))
  rw [Finset.sum_eq_single x] at h0
  · simpa using h0
  · intro y _ hy
    simp [Function.update_of_ne hy]
  · simp

end TernaryPeriodPolynomials.Argument.CuspidalInduction
