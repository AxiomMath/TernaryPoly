module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Reindex

@[expose] public section


/-!
# The cup form of an induced module is the cup form at the finite-index subgroup

Formalized by Claude Sonnet 5.5.  Context: Step 2 of the literal Stokes lemma at `Γ(N)` (finite-index induction `Γ(M) ≤ Γ(N)`).

Let `ρ, ρ'` be representations of `Γ = Γ(N)` (as `gammaNGL N ≤ GL₂(ℤ)`) with a `Γ`-invariant pairing `e`, `Q` a transitive `Γ`-set with base point `q₀` whose stabilizer is `Δ = Γ(M)`,
`Ind ρ = Fun(Q, E)` with `(s F)(x) = ρ(s) F(s⁻¹ x)` and the summed pairing `e_ind(F, G) = ∑_x e(F x, G x)`.  For twisted cusp functions `Φ, Φ'` with values in `Ind ρ`, `Ind ρ'`,
the evaluations `Φ_Δ = Φ(·)(q₀)` are twisted cusp functions for `ρ|_Δ`, and `cupForm_N(e_ind; Φ, Φ') = cupForm_M(e; Φ_Δ, Φ'_Δ)` (`cupForm_ind`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

section Ind

variable {G : Type} [Group G] {Q : Type} [MulAction G Q] {E E' : Type} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup E'] [Module ℂ E']

/-- `Fun(Q, E)` with `(s · F)(x) = ρ(s) F(s⁻¹ x)`. -/
def indRepQ (ρ : Representation ℂ G E) : Representation ℂ G (Q → E) where
  toFun s :=
    { toFun := fun F x => ρ s (F (s⁻¹ • x))
      map_add' := fun F H => by funext x; simp
      map_smul' := fun a F => by funext x; simp }
  map_one' := by
    ext F x
    simp
  map_mul' s t := by
    ext F x
    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, mul_inv_rev, map_mul]
    rw [mul_smul]

theorem indRepQ_apply (ρ : Representation ℂ G E) (s : G) (F : Q → E) (x : Q) :
    indRepQ ρ s F x = ρ s (F (s⁻¹ • x)) := rfl

variable [Fintype Q]

/-- The summed pairing on `Fun(Q, E) × Fun(Q, E')`. -/
def eindQ (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ) : (Q → E) →ₗ[ℂ] (Q → E') →ₗ[ℂ] ℂ :=
  ∑ x : Q, (e.comp (LinearMap.proj x)).compl₂ (LinearMap.proj x)

theorem eindQ_apply (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ) (F : Q → E) (H : Q → E') : eindQ e F H = ∑ x, e (F x) (H x) := by
  simp [eindQ, LinearMap.sum_apply]

theorem eindQ_inv (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ)
    (hinv : ∀ (γ : G) v w, e (ρ γ v) (ρ' γ w) = e v w) (γ : G) (F : Q → E) (H : Q → E') :
    eindQ e (indRepQ ρ γ F) (indRepQ ρ' γ H) = eindQ e F H := by
  rw [eindQ_apply, eindQ_apply]
  simp only [indRepQ_apply, hinv]
  exact Fintype.sum_equiv (MulAction.toPerm γ⁻¹) _ _ (fun x => by simp)

end Ind

end TernaryPeriodPolynomials.Argument.CuspidalInduction
