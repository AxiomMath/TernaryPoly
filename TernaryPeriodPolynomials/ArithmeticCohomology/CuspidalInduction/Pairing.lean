module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.ShapiroTheta

@[expose] public section


/-!
# Compatibility of the cup-form normalised cuspidal pairing with finite-index induction

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

Let `Γ(M) ≤ Γ(N)`, `N, M ≥ 3`, `V, V'` finite-dimensional `Γ(N)`-modules with a perfect `Γ(N)`-invariant pairing `e`, and `Ind V = Fun(Γ(N)/Γ(M), V)`, `Ind V'` with the summed
pairing `e_ind`.  If `B_N` is a bilinear form on the cuspidal groups of `Ind V`, `Ind V'` with the cup-form values of `cuspidal_pairing_gammaN_cup`, and `B_M` one on the
cuspidal groups of `V|Γ(M)`, `V'|Γ(M)` with the cup-form values at level `M` (e.g. the `facePairingCan`), then
`B_N(x, y) = B_M(shapiro x, shapiro' y)` for all cuspidal classes `x`, `y` (`cuspidal_pairing_ind`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

variable {N M : ℕ}

/-- The characterising cup-form property of a pairing on the cuspidal groups of `Γ(N)` (the conclusion of `cuspidal_pairing_gammaN_cup`
and of `facePairingCan_cup`), on the classes of normalised twisted cusp functions. -/
def IsCupPairing (hN : 3 ≤ N) (A A' : Rep ℂ (Gamma N)) [FiniteDimensional ℂ A] [FiniteDimensional ℂ A']
    (e : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ) (hinv : ∀ (γ : Gamma N) v w, e (A.ρ γ v) (A'.ρ γ w) = e v w)
    (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (hR : ∀ w, (∀ v, e v w = 0) → w = 0)
    (B : cuspidalSubspace (Gamma N) A →ₗ[ℂ] cuspidalSubspace (Gamma N) A' →ₗ[ℂ] ℂ) : Prop :=
  ∀ (Φ : Tw (transRep hN A).ρ) (Φ' : Tw (transRep hN A').ρ), Φ.1 cusp1 = 0 → Φ'.1 cusp1 = 0 →
    B ((cuspEquiv hN A).symm ⟨mTw (transRep hN A) Φ, mTw_mem_cuspidal _ Φ⟩)
      ((cuspEquiv hN A').symm ⟨mTw (transRep hN A') Φ', mTw_mem_cuspidal _ Φ'⟩) =
        cupForm hN (couplingOf hN e hinv hL hR) Φ.1 Φ'.1

theorem exists_norm_rep (hN : 3 ≤ N) (A : Rep ℂ (Gamma N)) (x : cuspidalSubspace (Gamma N) A) :
    ∃ Φ : Tw (transRep hN A).ρ, Φ.1 cusp1 = 0 ∧
      (cuspEquiv hN A).symm ⟨mTw (transRep hN A) Φ, mTw_mem_cuspidal _ Φ⟩ = x := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_Tn_of_cuspidal hN (transRep hN A) (x := (cuspEquiv hN A x).1) (cuspEquiv hN A x).2
  refine ⟨Φ, h0, ?_⟩
  apply (cuspEquiv hN A).injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext hΦ

theorem cuspEquiv_val (hN : 3 ≤ N) (A : Rep ℂ (Gamma N)) (x : cuspidalSubspace (Gamma N) A) :
    ((cuspEquiv hN A x : cuspidalSub (transRep hN A)) : groupCohomology.H1 (transRep hN A)) =
      (thetaIso hN A).hom.hom x.1 := rfl

section Induced

variable [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (hle : Gamma M ≤ Gamma N) (V : Rep ℂ (Gamma N))

include hM

theorem shapiro_eq (Φ : Tw (transRep hN.out (indRep M V)).ρ)
    (x : cuspidalSubspace (Gamma N) (indRep M V))
    (hx : (cuspEquiv hN.out (indRep M V)).symm ⟨mTw (transRep hN.out (indRep M V)) Φ, mTw_mem_cuspidal _ Φ⟩ = x) :
    (thetaIso hM (Rep.res (Subgroup.inclusion hle) V)).hom.hom (shapiro hle V x.1) =
      mTw (transRep hM (Rep.res (Subgroup.inclusion hle) V)) (restrTw hM hle V Φ) := by
  apply shapiro_theta hM hle V Φ x.1
  rw [← hx, ← cuspEquiv_val]
  simp

theorem shapiro_mem (x : cuspidalSubspace (Gamma N) (indRep M V)) :
    shapiro hle V x.1 ∈ cuspidalSubspace (Gamma M) (Rep.res (Subgroup.inclusion hle) V) := by
  obtain ⟨Φ, -, hΦ⟩ := exists_norm_rep hN.out (indRep M V) x
  rw [theta_mem_cuspidal_iff hM, shapiro_eq hM hle V Φ x hΦ]
  exact mTw_mem_cuspidal _ _

/-- The Shapiro map restricted to the cuspidal subspaces. -/
def shapiroCusp : cuspidalSubspace (Gamma N) (indRep M V) →ₗ[ℂ]
    cuspidalSubspace (Gamma M) (Rep.res (Subgroup.inclusion hle) V) :=
  ((shapiro hle V).comp (cuspidalSubspace (Gamma N) (indRep M V)).subtype).codRestrict _ (shapiro_mem hM hle V)

theorem shapiroCusp_eq (Φ : Tw (transRep hN.out (indRep M V)).ρ) :
    shapiroCusp hM hle V ((cuspEquiv hN.out (indRep M V)).symm ⟨mTw (transRep hN.out (indRep M V)) Φ, mTw_mem_cuspidal _ Φ⟩) =
      (cuspEquiv hM (Rep.res (Subgroup.inclusion hle) V)).symm
        ⟨mTw (transRep hM (Rep.res (Subgroup.inclusion hle) V)) (restrTw hM hle V Φ), mTw_mem_cuspidal _ _⟩ := by
  apply (cuspEquiv hM (Rep.res (Subgroup.inclusion hle) V)).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [cuspEquiv_val]
  exact shapiro_eq hM hle V Φ _ rfl

end Induced

end TernaryPeriodPolynomials.Argument.CuspidalInduction
