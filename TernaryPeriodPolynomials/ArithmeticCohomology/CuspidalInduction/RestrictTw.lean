module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.GLQuot

@[expose] public section


/-!
# Evaluating twisted cusp functions with values in an induced module

Formalized by Claude Sonnet 5.5.

`restrTw`: a twisted cusp function of `Γ(N)` with values in `Ind V = Fun(Γ(N)/Γ(M), V)` evaluates, at the base coset, to a twisted cusp function of `Γ(M)` with values in `V`
(the crossed homomorphism is evaluated at the base coset too).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPoly.RankTwoAugmentedFrames
open scoped Classical

variable {N M : ℕ}

theorem transRep_indRep_apply [hN : Fact (3 ≤ N)] (V : Rep ℂ (Gamma N)) (g : gammaNGL N)
    (F : QGL N M → V) (x : QGL N M) :
    (transRep hN.out (indRep M V)).ρ g F x = indRepQ (Q := QGL N M) (transRep hN.out V).ρ g F x := by
  change V.ρ ((gammaEquiv hN.out).symm g) (F (((gammaEquiv hN.out).symm g)⁻¹ • x)) =
    V.ρ ((gammaEquiv hN.out).symm g) (F (((gammaEquiv hN.out).symm (g⁻¹)) • x))
  rw [map_inv]

theorem ev_incl [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (hle : Gamma M ≤ Gamma N) (V : Rep ℂ (Gamma N)) (g : gammaNGL M)
    (F : QGL N M → V) :
    (transRep hN.out (indRep M V)).ρ (inclGL hM hle g) F (base N M) =
      (transRep hM (Rep.res (Subgroup.inclusion hle) V)).ρ g (F (base N M)) := by
  change V.ρ ((gammaEquiv hN.out).symm (inclGL hM hle g))
      (F (((gammaEquiv hN.out).symm (inclGL hM hle g))⁻¹ • base N M)) = _
  rw [symm_incl hN.out hM hle g, show ((Subgroup.inclusion hle ((gammaEquiv hM).symm g))⁻¹ : Gamma N) • base N M = base N M from
    inv_smul_base hle _]
  rfl

section Restr

variable [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (hle : Gamma M ≤ Gamma N) (V : Rep ℂ (Gamma N))

/-- Evaluating a twisted cusp function with values in `Ind V` at the base coset. -/
theorem restr_mem (Φ : RationalLine2 → (QGL N M → V)) (hΦ : Φ ∈ Tw (transRep hN.out (indRep M V)).ρ) :
    (fun c => Φ c (base N M)) ∈ Tw (transRep hM (Rep.res (Subgroup.inclusion hle) V)).ρ := by
  obtain ⟨f, hf, htw⟩ := hΦ
  refine ⟨fun g => f (inclGL hM hle g) (base N M), fun g h => ?_, fun γ x => ?_⟩
  · calc f (inclGL hM hle (g * h)) (base N M) = f (inclGL hM hle g * inclGL hM hle h) (base N M) := by
          rw [map_mul]
      _ = ((transRep hN.out (indRep M V)).ρ (inclGL hM hle g) (f (inclGL hM hle h)) + f (inclGL hM hle g))
            (base N M) := congrFun (hf _ _) _
      _ = (transRep hN.out (indRep M V)).ρ (inclGL hM hle g) (f (inclGL hM hle h)) (base N M) +
            f (inclGL hM hle g) (base N M) := rfl
      _ = _ := congrArg (fun t => t + f (inclGL hM hle g) (base N M)) (ev_incl hM hle V g (f (inclGL hM hle h)))
  · calc Φ (γ • x) (base N M) = Φ ((inclGL hM hle γ) • x) (base N M) := rfl
      _ = ((transRep hN.out (indRep M V)).ρ (inclGL hM hle γ) (Φ x) + f (inclGL hM hle γ)) (base N M) :=
          congrFun (htw _ _) _
      _ = (transRep hN.out (indRep M V)).ρ (inclGL hM hle γ) (Φ x) (base N M) +
            f (inclGL hM hle γ) (base N M) := rfl
      _ = _ := congrArg (fun t => t + f (inclGL hM hle γ) (base N M)) (ev_incl hM hle V γ (Φ x))

end Restr

end TernaryPeriodPolynomials.Argument.CuspidalInduction
