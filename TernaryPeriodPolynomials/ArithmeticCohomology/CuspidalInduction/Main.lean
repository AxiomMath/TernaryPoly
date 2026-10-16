module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.PairingInd

@[expose] public section


/-!
# Compatibility of the cup-form normalised cuspidal pairing with finite-index induction: the theorem

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

See `PairingInd` for the statement in words.  `cupForm_eq_of_ind`: the cup form of the summed pairing on `Ind V` equals the cup form at level `M` of the evaluations at the base coset;
`cuspidal_pairing_ind`: `B_N(x, y) = B_M(shapiro x, shapiro y)` for any pairings `B_N`, `B_M` with the cup-form property.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

variable {N M : ℕ} [hN : Fact (3 ≤ N)] [Fintype (Gamma N ⧸ subM N M)] (hM : 3 ≤ M) (hle : Gamma M ≤ Gamma N)
  (V V' : Rep ℂ (Gamma N)) [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] (e : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
  (hinv : ∀ (γ : Gamma N) v w, e (V.ρ γ v) (V'.ρ γ w) = e v w)
  (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (hR : ∀ w, (∀ v, e v w = 0) → w = 0)

instance resRep_fd (hle : Gamma M ≤ Gamma N) :
    FiniteDimensional ℂ (Rep.res (Subgroup.inclusion hle) V) :=
  inferInstanceAs (FiniteDimensional ℂ V)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] in
include hM in
/-- **The cup form of the induced module is the cup form at the finite-index subgroup.** -/
theorem cupForm_eq_of_ind (Φ : Tw (transRep hN.out (indRep M V)).ρ) (Φ' : Tw (transRep hN.out (indRep M V')).ρ) :
    cupForm hN.out (couplingOf hN.out (eInd V V' e) (eInd_inv V V' e hinv) (eInd_left V V' e hL) (eInd_right V V' e hR))
        Φ.1 Φ'.1 =
      cupForm hM (couplingOf hM (V := Rep.res (Subgroup.inclusion hle) V) (V' := Rep.res (Subgroup.inclusion hle) V') e
        (fun γ v w => hinv (Subgroup.inclusion hle γ) v w) hL hR)
        (restrTw hM hle V Φ).1 (restrTw hM hle V' Φ').1 := by
  rw [cupForm_eq_sum, cupForm_eq_sum]
  obtain ⟨f, -, htw⟩ := Φ.2
  obtain ⟨f', -, htw'⟩ := Φ'.2
  refine cupForm_ind hN.out hM (gammaNGL_le hM hle) (transRep hN.out V).ρ (transRep hN.out V').ρ e
    (fun γ v w => hinv ((gammaEquiv hN.out).symm γ) v w) (base N M) uLift uLift_base smul_base_iff
    Φ.1 Φ'.1 f f' (fun γ x => ?_) (fun γ x => ?_)
  · exact (htw γ x).trans (congrArg (fun t => t + f γ) (funext (transRep_indRep_apply V γ (Φ.1 x))))
  · exact (htw' γ x).trans (congrArg (fun t => t + f' γ) (funext (transRep_indRep_apply V' γ (Φ'.1 x))))

include hM in
/-- **Compatibility of the cup-form normalised cuspidal pairing with finite-index induction** (Step 2 of the literal Stokes lemma at `Γ(N)`). -/
theorem cuspidal_pairing_ind
    (BN : cuspidalSubspace (Gamma N) (indRep M V) →ₗ[ℂ] cuspidalSubspace (Gamma N) (indRep M V') →ₗ[ℂ] ℂ)
    (BM : cuspidalSubspace (Gamma M) (Rep.res (Subgroup.inclusion hle) V) →ₗ[ℂ]
      cuspidalSubspace (Gamma M) (Rep.res (Subgroup.inclusion hle) V') →ₗ[ℂ] ℂ)
    (hBN : IsCupPairing hN.out (indRep M V) (indRep M V') (eInd V V' e) (eInd_inv V V' e hinv) (eInd_left V V' e hL)
      (eInd_right V V' e hR) BN)
    (hBM : IsCupPairing hM (Rep.res (Subgroup.inclusion hle) V) (Rep.res (Subgroup.inclusion hle) V') e
      (fun γ v w => hinv (Subgroup.inclusion hle γ) v w) hL hR BM)
    (x : cuspidalSubspace (Gamma N) (indRep M V)) (y : cuspidalSubspace (Gamma N) (indRep M V')) :
    BN x y = BM (shapiroCusp hM hle V x) (shapiroCusp hM hle V' y) := by
  obtain ⟨Φ, h0, rfl⟩ := exists_norm_rep hN.out _ x
  obtain ⟨Φ', h0', rfl⟩ := exists_norm_rep hN.out _ y
  rw [hBN Φ Φ' h0 h0', shapiroCusp_eq hM hle V Φ, shapiroCusp_eq hM hle V' Φ',
    hBM (restrTw hM hle V Φ) (restrTw hM hle V' Φ') (congrFun h0 (base N M)) (congrFun h0' (base N M)),
    cupForm_eq_of_ind hM hle V V' e hinv hL hR]

end TernaryPeriodPolynomials.Argument.CuspidalInduction
