module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.SlantCycle

@[expose] public section


/-!
# The slant of the flag cocycle `cup12 w z' - γ̄` on a flag group

Formalized by Claude Sonnet 5.5.

`flagTheta Lt ρ' e w z' γ` is the cochain `x ↦ e (w x₀) (ρ' ι(x₀) (z' ι(x₁) ι(x₂))) - γ (ι x₀) (ι x₁) (ι x₂)` of the flag group `B`; `flagTheta_nl` says it vanishes on triples of `N`-letters (normal form `z'(nl _, _) = 0`
and `γ` of filtration `≥ 1`), and `chainEval_nuSh_flagTheta` evaluates it on `Sh₁ σ`:
`⟨Θ, Sh₁σ⟩ = - (e (w e₁) (e₁ · c'σ(e₂)) - e (w e₂) (e₂ · c'σ(e₁))) - μ σ`, `c'σ(r) = z'(σ, σ·r)` (T2 and the definition of `μ`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FlagH3

namespace LetterLift

variable {G M L B : Type} [Group G] [AddCommGroup M] [Group L] [Group B] {P : PairModel G M L} {σ : L} (Lt : LetterLift P B σ)
  {V W' : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W'] [Module ℚ W']
  (ρ' : Representation ℚ G W') (e : V →ₗ[ℚ] W' →ₗ[ℚ] ℚ)

/-- The flag cochain `cup12 w z' - γ` of the flag group `B`, `w` a `1`-cochain of `B`. -/
def flagTheta (w : B → V) (z' : G → G → W') (γ : G → G → G → ℚ) : (Fin 3 → B) → ℚ :=
  fun x => e (w (x 0)) (ρ' (Lt.ι (x 0)) (z' (Lt.ι (x 1)) (Lt.ι (x 2)))) - γ (Lt.ι (x 0)) (Lt.ι (x 1)) (Lt.ι (x 2))

theorem flagTheta_nl (w : B → V) (z' : G → G → W') (γ : G → G → G → ℚ) (hz' : ∀ v g, z' (P.nl v) g = 0)
    (hγ : P.Ge1 γ) (a b c : M) : Lt.flagTheta ρ' e w z' γ ![Lt.nlB a, Lt.nlB b, Lt.nlB c] = 0 := by
  simp [flagTheta, Lt.hnl, hz', hγ a b c]

/-- **The slant of the flag cochain**. -/
theorem chainEval_nuSh_flagTheta (w : B → V) (z' : G → G → W') (γ : G → G → G → ℚ) (hz' : ∀ v g, z' (P.nl v) g = 0)
    (e₁ e₂ : M) :
    chainEval (Lt.nuSh e₁ e₂) (Lt.flagTheta ρ' e w z' γ) =
      -(e (w (Lt.nlB e₁)) (ρ' (P.nl e₁) (z' (P.ll σ) (P.nl (P.ψ σ⁻¹ e₂)))) -
          e (w (Lt.nlB e₂)) (ρ' (P.nl e₂) (z' (P.ll σ) (P.nl (P.ψ σ⁻¹ e₁))))) - P.mu γ e₁ e₂ σ := by
  classical
  set wG : G → V := fun g => w (Function.invFun Lt.ι g) with hwG
  have hw : ∀ b, wG (Lt.ι b) = w b := fun b => by simp only [hwG]; rw [Function.leftInverse_invFun Lt.inj b]
  have hfun : Lt.flagTheta ρ' e w z' γ = fun x => (cup12 ρ' e wG z' - γ) (Lt.ι (x 0)) (Lt.ι (x 1)) (Lt.ι (x 2)) := by
    funext x
    simp only [flagTheta, cup12, Pi.sub_apply, hw]
  unfold nuSh
  rw [chainEval_sub, hfun, chainEval_sh1Chain_comp, chainEval_sh1Chain_comp]
  show P.sh1 (cup12 ρ' e wG z' - γ) e₁ e₂ σ - P.sh1 (cup12 ρ' e wG z' - γ) e₂ e₁ σ = _
  have key : ∀ v₁ v₂ : M, P.sh1 (cup12 ρ' e wG z' - γ) v₁ v₂ σ =
      P.sh1 (cup12 ρ' e wG z') v₁ v₂ σ - P.sh1 γ v₁ v₂ σ := fun v₁ v₂ => by
    unfold PairModel.sh1; simp only [Pi.sub_apply]; ring
  have hnl : ∀ a, wG (P.nl a) = w (Lt.nlB a) := fun a => by rw [← Lt.hnl a, hw]
  rw [key, key, P.T2_cup12 ρ' e wG z' hz', P.T2_cup12 ρ' e wG z' hz', hnl, hnl]
  unfold PairModel.mu
  ring

end LetterLift

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
