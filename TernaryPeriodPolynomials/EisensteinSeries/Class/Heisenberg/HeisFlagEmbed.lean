module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisFlag
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisClass
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisPoly
public import TernaryPeriodPolynomials.EisensteinSeries.Class.DeRhamNatural
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Package

@[expose] public section



/-!
# The flag restriction class is represented by the averaged form

Formalized by Claude Sonnet 5.5.

* `flagOrbit`: the boundary map `i_{B,t} : N_B ≅ ℝ³ → Ω`, `p ↦ n(p) · x₀` (`contDiff_flagOrbit`); `flagEquiv`: it is equivariant for the flag group `Γ_B = Γ(N) ∩ B(ℤ) ⊂ Γ`
  acting on the chart by left translation and on `Ω` by `gammaAct`; `flag_rho_compat`: the coefficient representation `Sym^n ⊗ det⁻¹` of `Γ` restricted to `Γ_B` is `ρ(n(γ))`, the restriction to
  the Heisenberg radical of `polyRep n`.
* `flag_restriction_averaged`: for every closed `Γ`-equivariant `E_n`-valued `2`-form `W` on `Ω` (`InvComponents Γ n`, e.g. the form series), the restriction to `Γ_B` of its class
  `[W] ∈ H²(Γ, E_n)` is the zig-zag class of an equivariant closed form `ωc` on the Heisenberg chart whose gauge-trivialized frame coefficients are the *constant Haar average* over the
  nilmanifold fibre `Γ_B \ N_B` of the frame coefficients of the pullback `i_{B,t}^* W` (a cocycle of the Chevalley-Eilenberg complex with unipotent coefficients).
-/

open scoped ContDiff MatrixGroups
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

/-- **The flag boundary map `i_{B,t}`** ("at a flag use two normal coordinates"): the orbit map `p ↦ n(p) · x₀`
of the unipotent radical of the standard Borel in `𝒳 ≅ Ω` through the base point. -/
def flagOrbit (p : Pt) : Fin 5 → ℝ := planeAct (nMat p) basePt

theorem nMat_mulH (p q : Pt) : nMat (mulH p q) = nMat p * nMat q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nMat, mulH, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem nMat_zero : nMat 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nMat]

theorem contDiff_flagOrbit : ContDiff ℝ ∞ flagOrbit := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have h1 := contDiffAt_planeAct_pair (g := nMat p) (det_nMat p) (p := basePt) basePt_mem
  have h2 : ContDiff ℝ ⊤ (fun q : Pt => (matToFun (nMat q), basePt)) := by
    refine ContDiff.prodMk ?_ contDiff_const
    refine contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => ?_
    fin_cases a <;> fin_cases b <;> simp [matToFun, nMat] <;> fun_prop
  have h3 := h1.comp p h2.contDiffAt
  exact (h3.of_le le_top)

section Restriction

variable {N : ℕ} {Γ : Subgroup SL(3, ℤ)}

theorem realMat_flag (hN : 3 ≤ N) (g : flagGroup N) : realMat g.1 = nMat (flagN g.1) := by
  obtain ⟨g00, g11, g22, -⟩ := flag_entries hN g.2
  obtain ⟨-, g10, g20, g21⟩ := g.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realMat_apply, nMat, flagN, g00, g11, g22, g10, g20, g21]

/-- **The flag boundary map is equivariant for `Γ_B ⊂ Γ`**: `i_{B,t}(γ p) = γ · i_{B,t}(p)`. -/
def flagEquiv (hN : 3 ≤ N) (hΓ : flagGroup N ≤ Γ) :
    EquivMap (isOpen_univ : IsOpen (Set.univ : Set Pt)) isOpen_Omega (latAct (flagLat hN)) (gammaAct Γ)
      (Subgroup.inclusion hΓ) where
  φ := flagOrbit
  smooth := contDiff_flagOrbit.contDiffOn
  mapsTo p _ := planeAct_mem (det_nMat p) basePt_mem
  equiv g x _ := by
    change flagOrbit (mulH (flagN g.1) x) = planeAct (realMat g.1) (flagOrbit x)
    unfold flagOrbit
    rw [nMat_mulH, planeAct_mul (det_nMat x) basePt_mem, realMat_flag hN g]

theorem flag_rho_compat (hN : 3 ≤ N) (hΓ : flagGroup N ≤ Γ) (n : ℕ) (g : flagGroup N) :
    latRho (polyRep_heisRep n) (flagLat hN) g = gammaRho Γ n (Subgroup.inclusion hΓ g) := by
  apply LinearMap.ext
  intro q
  apply Coef.toPoly_injective
  rw [toPoly_gammaRho]
  change Coef.toPoly (polyRep n (flagN g.1) q) = _
  rw [toPoly_polyRep]
  change _ = rho (realMat g.1) _
  rw [realMat_flag hN g]

/-- **The averaged pullback along `i_{B,t}` represents the restriction class**, on the actual flag group
`Γ_B = Γ(N) ∩ B(ℤ)` and the actual coefficients `E_n = Sym^n ⊗ det⁻¹`. -/
theorem flag_restriction_averaged (hN : 3 ≤ N) (hΓ : flagGroup N ≤ Γ) (n : ℕ) (W : InvComponents Γ n) :
    ∃ ωc : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct (flagLat hN))
        (latRho (polyRep_heisRep n) (flagLat hN)),
      (∀ x m, gauge2 (polyRep n) ωc.1.1 m x = heisAv (N : ℝ) N N
          (frameCochain (polyRep n)
            (pullInv (flagEquiv hN hΓ) (flag_rho_compat hN hΓ n) W.toInv).1.1) (i2 m)) ∧
      ceD0 (heisGen (polyRep n)) (heisAv (N : ℝ) N N
          (frameCochain (polyRep n) (pullInv (flagEquiv hN hΓ) (flag_rho_compat hN hΓ n) W.toInv).1.1)) = 0 ∧
      (groupCohomology.map (Subgroup.inclusion hΓ)
          (resMor (Subgroup.inclusion hΓ) (latRho (polyRep_heisRep n) (flagLat hN)) (gammaRho Γ n)
            (flag_rho_compat hN hΓ n)) 2).hom
        (deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) (gammaRho Γ n) W.toInv) =
      deRhamClass isOpen_univ convex_univ Set.univ_nonempty (latAct (flagLat hN))
        (latRho (polyRep_heisRep n) (flagLat hN)) ωc := by
  obtain ⟨ωc, h1, h2, h3⟩ := heis_class_av (polyRep_heisRep n) (flagLat hN) N (by omega) (flag_range hN)
    (flag_gens hN) (pullInv (flagEquiv hN hΓ) (flag_rho_compat hN hΓ n) W.toInv)
  refine ⟨ωc, h1, h2, ?_⟩
  rw [← deRhamClass_natural (flagEquiv hN hΓ) convex_univ Set.univ_nonempty convex_Omega Omega_nonempty
    (flag_rho_compat hN hΓ n) W.toInv]
  exact h3

end Restriction

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
