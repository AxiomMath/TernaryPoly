module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisFlagEmbed

@[expose] public section


/-!
# Vanishing of the flag restriction class from the vanishing of the Haar average

Formalized by Claude Sonnet 5.5.

A `2`-form on the Heisenberg chart is determined by its gauge-trivialized frame coefficients (`form_eq_zero_of_gauge2_zero`), so the representative `ωc` of `flag_restriction_averaged`
vanishes as soon as the constant Haar average of the frame coefficients of the pullback `i_{B,t}^* W` vanishes: `flag_restriction_zero_of_average_zero`.  This reduces
`r_B [W] = 0` to the vanishing of the three Haar integrals `∫ ρ(p)⁻¹ (i_{B,t}^* W)(X_{m+1}, X_{m+2}) dp` over the fundamental domain.
-/

open scoped ContDiff MatrixGroups
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

section Injective

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem alt2_eq_zero_of_frame (φ : Pt [⋀^Fin 2]→L[ℝ] E) (x : Pt)
    (h : ∀ k l : Fin 3, φ ![Xf k x, Xf l x] = 0) : φ = 0 := by
  ext v
  change φ v = 0
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, frame_decomp x (v 0), frame_decomp x (v 1)]
  simp only [Fin.sum_univ_three, alt2_add_left, alt2_add_right, alt2_smul_left, alt2_smul_right, h,
    smul_zero, add_zero]

end Injective

section Zero

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {ρt : Pt → E →L[ℝ] E} {G : Type} [Group G]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- **A `2`-form is zero when its gauge-trivialized frame coefficients vanish.** -/
theorem form_eq_zero_of_gauge2_zero (R : HeisRep ρt) (om : Pt → Pt [⋀^Fin 2]→L[ℝ] E)
    (h : ∀ x m, gauge2 ρt om m x = 0) (x : Pt) : om x = 0 := by
  have hA : ∀ m, A2 om (m + 1) (m + 2) x = 0 := by
    intro m
    rw [congrFun (A2_eq R om m) x, h x m, map_zero]
  apply alt2_eq_zero_of_frame _ x
  intro k l
  have h20 : A2 om 2 0 x = 0 := hA 1
  have h01 : A2 om 0 1 x = 0 := hA 2
  have h12 : A2 om 1 2 x = 0 := hA 0
  fin_cases k <;> fin_cases l
  · exact A2_same (om := om) 0 x
  · exact h01
  · show A2 om 0 2 x = 0
    rw [A2_swap (om := om) 2 0 x, h20, neg_zero]
  · show A2 om 1 0 x = 0
    rw [A2_swap (om := om) 0 1 x, h01, neg_zero]
  · exact A2_same (om := om) 1 x
  · exact h12
  · exact h20
  · show A2 om 2 1 x = 0
    rw [A2_swap (om := om) 1 2 x, h12, neg_zero]
  · exact A2_same (om := om) 2 x

end Zero

section Vanish

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {ρt : Pt → E →L[ℝ] E} {G : Type} [Group G]

/-- **A closed equivariant `2`-form with vanishing gauge-trivialized frame coefficients has class zero.** -/
theorem deRhamClass_eq_zero_of_gauge2_zero (R : HeisRep ρt) (Λ : LatticeAction G)
    (om : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) (latRho R Λ))
    (h : ∀ x m, gauge2 ρt om.1.1 m x = 0) :
    deRhamClass isOpen_univ convex_univ Set.univ_nonempty (latAct Λ) (latRho R Λ) om = 0 := by
  have hom : om = 0 := by
    apply Subtype.ext
    apply Form.ext
    intro x _
    exact form_eq_zero_of_gauge2_zero R om.1.1 h x
  rw [hom, map_zero]

variable {N : ℕ} {Γ : Subgroup SL(3, ℤ)}

/-- **If the Haar average of the frame coefficients of the pullback to the flag boundary model vanishes, the restriction class
vanishes**: `r_B [W] = 0` is reduced to the vanishing of the three Haar integrals `∫ ρ(p)⁻¹ (i_{B,t}^* W)(X_{m+1}, X_{m+2}) dp`. -/
theorem flag_restriction_zero_of_average_zero (hN : 3 ≤ N) (hΓ : flagGroup N ≤ Γ) (n : ℕ)
    (W : InvComponents Γ n)
    (hav : ∀ m, heisAv (N : ℝ) N N (frameCochain (polyRep n)
      (pullInv (flagEquiv hN hΓ) (flag_rho_compat hN hΓ n) W.toInv).1.1) (i2 m) = 0) :
    (groupCohomology.map (Subgroup.inclusion hΓ)
        (resMor (Subgroup.inclusion hΓ) (latRho (polyRep_heisRep n) (flagLat hN)) (gammaRho Γ n)
          (flag_rho_compat hN hΓ n)) 2).hom
      (deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) (gammaRho Γ n) W.toInv) = 0 := by
  obtain ⟨ωc, h1, -, h3⟩ := flag_restriction_averaged hN hΓ n W
  rw [h3]
  exact deRhamClass_eq_zero_of_gauge2_zero (polyRep_heisRep n) (flagLat hN) ωc (fun x m => by rw [h1, hav])

end Vanish

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
