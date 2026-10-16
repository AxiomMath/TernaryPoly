module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.SlantEval
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Plane.Lift
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.LocalCuspPlane

@[expose] public section


/-!
# The slant of the plane flag cocycle `cup21 z (-w') + γ` on a plane flag group

Formalized by Claude Sonnet 5.5.

`planeFlagTheta Lt ρ' e z w' γ x = e (z ι(x₀) ι(x₁)) (ρ' (ι x₀ ι x₁) (-w'(x₂))) + γ (ι x₀) (ι x₁) (ι x₂)`.  It vanishes on triples of `N`-letters (`z(nl _, _) = 0`, `γ ∈ (≥1)`), and
`⟨Θ, Sh₁σ⟩ = -⟨cup21 z w', Sh₁σ⟩ + μ σ` (`chainEval_nuSh_planeTheta`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FlagH3

namespace LetterLift

variable {G M L B : Type} [Group G] [AddCommGroup M] [Group L] [Group B] {P : PairModel G M L} {σ : L} (Lt : LetterLift P B σ)
  {V W' : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W'] [Module ℚ W']
  (ρ' : Representation ℚ G W') (e : V →ₗ[ℚ] W' →ₗ[ℚ] ℚ)

/-- The plane flag cochain `cup21 z (-w') + γ` of the flag group `B`, `w'` a `1`-cochain of `B`. -/
def planeFlagTheta (z : G → G → V) (w' : B → W') (γ : G → G → G → ℚ) : (Fin 3 → B) → ℚ :=
  fun x => e (z (Lt.ι (x 0)) (Lt.ι (x 1))) (ρ' (Lt.ι (x 0) * Lt.ι (x 1)) (-(w' (x 2)))) + γ (Lt.ι (x 0)) (Lt.ι (x 1)) (Lt.ι (x 2))

theorem planeFlagTheta_nl (z : G → G → V) (w' : B → W') (γ : G → G → G → ℚ) (hz : ∀ v g, z (P.nl v) g = 0)
    (hγ : P.Ge1 γ) (a b c : M) : Lt.planeFlagTheta ρ' e z w' γ ![Lt.nlB a, Lt.nlB b, Lt.nlB c] = 0 := by
  simp [planeFlagTheta, Lt.hnl, hz, hγ a b c]

/-- **The slant of the plane flag cochain**: `⟨Θ, Sh₁σ⟩ = -⟨cup21 z w', Sh₁σ⟩ + μ σ`, where `w'` is extended to `G` by `invFun`. -/
theorem chainEval_nuSh_planeTheta (z : G → G → V) (w' : B → W') (γ : G → G → G → ℚ) (e₁ e₂ : M) :
    chainEval (Lt.nuSh e₁ e₂) (Lt.planeFlagTheta ρ' e z w' γ) =
      -P.mu (cup21 ρ' e z (fun g => w' (Function.invFun Lt.ι g))) e₁ e₂ σ + P.mu γ e₁ e₂ σ := by
  classical
  set wG : G → W' := fun g => w' (Function.invFun Lt.ι g) with hwG
  have hw : ∀ b, wG (Lt.ι b) = w' b := fun b => by simp only [hwG]; rw [Function.leftInverse_invFun Lt.inj b]
  have hfun : Lt.planeFlagTheta ρ' e z w' γ =
      fun x => (cup21 ρ' e z (-wG) + γ) (Lt.ι (x 0)) (Lt.ι (x 1)) (Lt.ι (x 2)) := by
    funext x
    simp only [planeFlagTheta, cup21, Pi.add_apply, Pi.neg_apply, hw]
  unfold nuSh
  rw [chainEval_sub, hfun, chainEval_sh1Chain_comp, chainEval_sh1Chain_comp]
  show P.sh1 (cup21 ρ' e z (-wG) + γ) e₁ e₂ σ - P.sh1 (cup21 ρ' e z (-wG) + γ) e₂ e₁ σ = _
  have key : ∀ v₁ v₂ : M, P.sh1 (cup21 ρ' e z (-wG) + γ) v₁ v₂ σ =
      -P.sh1 (cup21 ρ' e z wG) v₁ v₂ σ + P.sh1 γ v₁ v₂ σ := fun v₁ v₂ => by
    unfold PairModel.sh1; simp only [Pi.add_apply, cup21, Pi.neg_apply, map_neg]; ring
  rw [key, key]
  unfold PairModel.mu
  ring

end LetterLift

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
