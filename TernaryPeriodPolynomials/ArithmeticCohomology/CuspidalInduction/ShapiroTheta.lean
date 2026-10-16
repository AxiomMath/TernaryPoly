module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.RestrictTw

@[expose] public section


/-!
# The Shapiro map on the classes of twisted cusp functions

Formalized by Claude Sonnet 5.5.

`shapiro_theta`: if `θ_N(x) = mTw Φ` for a twisted cusp function `Φ` with values in `Ind V`, then `θ_M(shapiro x) = mTw (Φ(·)(q₀))`.  Here `θ_N : H¹(Γ(N), A) ≅ H¹(gammaNGL N, A)`
is `thetaIso`.  Consequently `shapiro` maps the cuspidal subspace of `Ind V` into that of `V`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

theorem H1π_eq_iff_gen {G : Type} [Group G] (A : Rep ℂ G) (c c' : groupCohomology.cocycles₁ A) :
    groupCohomology.H1π A c = groupCohomology.H1π A c' ↔ ∃ w : A, ∀ g, c.1 g - c'.1 g = A.ρ g w - w := by
  rw [groupCohomology.H1π_eq_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun g => ?_⟩
    have := congrFun hu g
    simp only [groupCohomology.d₀₁_hom_apply] at this
    exact this.symm
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    funext g
    simp only [groupCohomology.d₀₁_hom_apply]
    exact (hu g).symm

variable {N M : ℕ}

section Theta

variable [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (hle : Gamma M ≤ Gamma N) (V : Rep ℂ (Gamma N))

theorem fTw_restr (Φ : Tw (transRep hN.out (indRep M V)).ρ) (g : gammaNGL M) :
    fTw (transRep hM (Rep.res (Subgroup.inclusion hle) V)) (fun c => Φ.1 c (base N M)) g =
      fTw (transRep hN.out (indRep M V)) Φ.1 (inclGL hM hle g) (base N M) := by
  unfold fTw
  exact (congrArg (fun t => Φ.1 ((g : IntegralGL) • cusp1) (base N M) - t) (ev_incl hM hle V g (Φ.1 cusp1))).symm

/-- The evaluation of a twisted cusp function with values in `Ind V` at the base coset, as an element of `Tw`. -/
def restrTw (Φ : Tw (transRep hN.out (indRep M V)).ρ) : Tw (transRep hM (Rep.res (Subgroup.inclusion hle) V)).ρ :=
  ⟨fun c => Φ.1 c (base N M), restr_mem hM hle V Φ.1 Φ.2⟩

theorem shapiro_theta (Φ : Tw (transRep hN.out (indRep M V)).ρ) (x : groupCohomology.H1 (indRep M V))
    (hx : (thetaIso hN.out (indRep M V)).hom.hom x = mTw (transRep hN.out (indRep M V)) Φ) :
    (thetaIso hM (Rep.res (Subgroup.inclusion hle) V)).hom.hom (shapiro hle V x) =
      mTw (transRep hM (Rep.res (Subgroup.inclusion hle) V)) (restrTw hM hle V Φ) := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    obtain ⟨c', hc', hθ⟩ := thetaIso_hom_π hN.out (indRep M V) c
    rw [hθ, mTw_apply] at hx
    obtain ⟨w, hw⟩ := (H1π_eq_iff_gen _ _ _).1 hx
    rw [shapiro_π]
    obtain ⟨c'', hc'', hθ'⟩ := thetaIso_hom_π hM (Rep.res (Subgroup.inclusion hle) V)
      (groupCohomology.mapCocycles₁ (Subgroup.inclusion hle) (evHom hle V) c)
    rw [hθ', mTw_apply]
    refine (H1π_eq_iff_gen _ _ _).2 ⟨w (base N M), fun g => ?_⟩
    have h1 := congrFun (hw (inclGL hM hle g)) (base N M)
    have h2 : c'.1 (inclGL hM hle g) = c.1 (Subgroup.inclusion hle ((gammaEquiv hM).symm g)) := by
      rw [hc', symm_incl hN.out hM hle g]
    have e1 : c''.1 g = c'.1 (inclGL hM hle g) (base N M) :=
      (hc'' g).trans ((shapiro_cocycle hle V c _).trans
        (congrArg (fun F : QGL N M → V => F (base N M)) h2.symm))
    have e2 : c'.1 (inclGL hM hle g) (base N M) -
        fTw (transRep hN.out (indRep M V)) Φ.1 (inclGL hM hle g) (base N M) =
        (transRep hM (Rep.res (Subgroup.inclusion hle) V)).ρ g (w (base N M)) - w (base N M) :=
      h1.trans (congrArg (fun t => t - w (base N M)) (ev_incl hM hle V g w))
    change c''.1 g - fTw (transRep hM (Rep.res (Subgroup.inclusion hle) V)) (fun c => Φ.1 c (base N M)) g = _
    rw [fTw_restr hM hle V Φ g, e1]
    exact e2

end Theta

end TernaryPeriodPolynomials.Argument.CuspidalInduction
