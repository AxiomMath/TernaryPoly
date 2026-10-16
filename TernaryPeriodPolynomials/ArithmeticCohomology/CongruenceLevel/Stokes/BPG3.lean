module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG2
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPlane2

@[expose] public section


/-!
# Plane geometry package, part 3: the flags `pflag h w` represent the orbits of flags over the plane, one for each cusp

Formalized by Claude Sonnet 5.5.

`orbit_flag_iff`: two flags `flagOf (q₁ h)`, `flagOf (q₂ h)` (`q_i ∈ planeBorel`) lie in one `Γ(6)`-orbit iff `qVec (tau q₁) ~ qVec (tau q₂)` in `Cusp6`.  Consequently
`orbit_pflag_iff : [pflag h w] = [pflag h w'] ↔ CuspRel w w'` and every flag over `planeOf h` is in the orbit of some `pflag h w` (`pflag_surj`).
-/

open scoped MatrixGroups
open CongruenceSubgroup

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.BoundaryFaceResolutionComparison

theorem qVec_tau_qBD (w : Prim2) : qVec (tau (qBD w)) = Dref w.1 := by
  rw [qVec_apply, tau_apply, tau_apply, tau_apply, qBD, blockDiag_inv, inv_inv]
  ext i
  fin_cases i <;> simp [Dref, ConvergenceC4.blockDiag, colSL, Fin.rev]

theorem qPrim_tau_qBD (w : Prim2) : qPrim (tau (qBD w)) (tau_mem_lineBorel_of_planeBorel (qBD_mem w)) = DrefP w :=
  Subtype.ext (qVec_tau_qBD w)

/-- **Orbit ⟹ cusp relation.** -/
theorem cusp_of_orbit (h q₁ q₂ : SL(3, ℤ)) (h₁ : q₁ ∈ planeBorel) (h₂ : q₂ ∈ planeBorel)
    (heq : (Quotient.mk'' (flagOf (q₁ * h)) : labelOrbits Γ6 Flag) = Quotient.mk'' (flagOf (q₂ * h))) :
    CuspRel (qPrim (tau q₂) (tau_mem_lineBorel_of_planeBorel h₂)) (qPrim (tau q₁) (tau_mem_lineBorel_of_planeBorel h₁)) := by
  have hrel := Quotient.exact heq.symm
  obtain ⟨δ, hδ⟩ := (MulAction.orbitRel_apply).1 hrel
  have hp : δ = gammaSixEquiv (gammaSixEquiv.symm δ) := by simp
  set p := gammaSixEquiv.symm δ with hpdef
  have hflag : flagOf (q₁ * h * p.1⁻¹) = flagOf (q₂ * h) := by
    rw [← smul_flagOf]
    have : gammaSixEquiv p • flagOf (q₁ * h) = flagOf (q₂ * h) := by rw [← hp]; exact hδ
    exact this
  have hb : q₂ * h * p.1 * (q₁ * h)⁻¹ ∈ borelStab := by
    have := borel_of_flagOf_eq _ _ hflag
    simpa [mul_assoc] using this
  exact cuspP_orbit_change (q₁ * h) (q₂ * h) 1 1 h q₁ q₂ p.1 (Subgroup.one_mem _) (Subgroup.one_mem _) p.2 hb h₁ h₂
    (by group) (by group)

/-- **Cusp relation ⟹ same orbit.** -/
theorem orbit_of_cusp (h q₁ q₂ : SL(3, ℤ)) (h₁ : q₁ ∈ planeBorel) (h₂ : q₂ ∈ planeBorel)
    (hc : CuspRel (qPrim (tau q₁) (tau_mem_lineBorel_of_planeBorel h₁)) (qPrim (tau q₂) (tau_mem_lineBorel_of_planeBorel h₂))) :
    (Quotient.mk'' (flagOf (q₁ * h)) : labelOrbits Γ6 Flag) = Quotient.mk'' (flagOf (q₂ * h)) := by
  obtain ⟨n, hn, hnN, hb⟩ := exists_n_of_cuspRel _ _ _ _ hc
  set n₀ : SL(3, ℤ) := tau n with hn₀
  have hn₀N : n₀ ∈ gammaN 6 := tau_mem_gammaN hnN
  have hb₀ : q₂ * n₀ * q₁⁻¹ ∈ borelStab := by
    have := tau_mem_borelStab hb
    simpa [hn₀, map_mul, map_inv, tau_tau] using this
  set δ : SL(3, ℤ) := h⁻¹ * n₀ * h with hδ
  have hδN : δ ∈ gammaN 6 := by
    have := (gammaN_normal 6).conj_mem n₀ hn₀N h⁻¹
    simpa [hδ, mul_assoc] using this
  have hflag : flagOf (q₁ * h * δ⁻¹) = flagOf (q₂ * h) := by
    apply flagOf_eq_of_borel
    have : q₂ * h * (q₁ * h * δ⁻¹)⁻¹ = q₂ * n₀ * q₁⁻¹ := by rw [hδ]; group
    rw [this]; exact hb₀
  have hsm := flagOf_smul_eq δ hδN (q₁ * h)
  calc (Quotient.mk'' (flagOf (q₁ * h)) : labelOrbits Γ6 Flag)
      = Quotient.mk'' (gammaSixEquiv ⟨δ, hδN⟩ • flagOf (q₁ * h)) := MulAction.orbitRel.Quotient.quotient_smul_eq.symm
    _ = Quotient.mk'' (flagOf (q₂ * h)) := by rw [hsm, hflag]

/-- **Two flags of the form `pflag h w` lie in the same orbit iff the cusps agree.** -/
theorem orbit_pflag_iff (h : SL(3, ℤ)) (w w' : Prim2) :
    (Quotient.mk'' (pflag h w) : labelOrbits Γ6 Flag) = Quotient.mk'' (pflag h w') ↔ CuspRel w w' := by
  constructor
  · intro heq
    have := cusp_of_orbit h (qBD w) (qBD w') (qBD_mem w) (qBD_mem w') heq
    rw [qPrim_tau_qBD, qPrim_tau_qBD] at this
    exact cuspRel_symm (cuspRel_Dref_iff.1 this)
  · intro hc
    apply orbit_of_cusp h (qBD w) (qBD w') (qBD_mem w) (qBD_mem w')
    rw [qPrim_tau_qBD, qPrim_tau_qBD]
    exact cuspRel_Dref hc

/-- **Every flag over `planeOf h` lies in the orbit of some `pflag h w`.** -/
theorem pflag_surj (h : SL(3, ℤ)) (F : Flag) (hF : flagPlaneOf F = planeOf h) :
    ∃ w : Prim2, (Quotient.mk'' (pflag h w) : labelOrbits Γ6 Flag) = Quotient.mk'' F := by
  obtain ⟨g, rfl⟩ := exists_flagOf F
  have hq : g * h⁻¹ ∈ planeBorel := by
    have : planeOf g = planeOf h := by rw [← flagPlaneOf_flagOf]; exact hF
    exact (planeOf_eq_iff h g).1 this.symm
  set q : SL(3, ℤ) := g * h⁻¹ with hqdef
  have hg : g = q * h := by rw [hqdef]; group
  have hqt := tau_mem_lineBorel_of_planeBorel hq
  set u : Prim2 := qPrim (tau q) hqt with hu
  refine ⟨DrefP u, ?_⟩
  rw [hg]
  symm
  apply orbit_of_cusp h q (qBD (DrefP u)) hq (qBD_mem _)
  rw [qPrim_tau_qBD, DrefP_DrefP]
  exact cuspRel_refl _

end TernaryPeriodPolynomials.Argument.GammaNStokes
