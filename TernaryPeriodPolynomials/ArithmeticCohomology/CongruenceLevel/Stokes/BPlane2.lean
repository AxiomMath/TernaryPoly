module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPlane1
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine2

@[expose] public section


/-!
# The flag orbits over a plane orbit are in bijection with the cusps of `Γ(6)`

Formalized by Claude Sonnet 5.5.

The plane version of `BLine2`, obtained by applying the line statements to the images under `tau`: `cuspVecP`, `cuspMapP_injective`, `cuspMapP_surjective`.
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPeriodPolynomials.Argument.SeedC3S4c (planeBorel)

/-- The cusp vector of a flag orbit over a plane orbit, with respect to the frames `F`. -/
def cuspVecP (F : ConjFrames) (o : labelOrbits Γ6 Flag) : Prim2 :=
  qPrim (tau (qOfP o (F.γP o))) (tau_mem_lineBorel_of_planeBorel (qOfP_mem o (F.γP o) (F.hP o)))

theorem qOfP_eq (o : labelOrbits Γ6 Flag) (γ : Γ6) :
    qOfP o γ = gOf o * iotaOf γ * (hOfP (flagPlaneOrbit o))⁻¹ := by
  simp [qOfP, hFrameP, mul_assoc]

/-- **The cusp vector only depends on the `Γ(6)`-orbit of the flag** (plane version). -/
theorem cuspP_orbit_change (g₁ g₂ γ₁ γ₂ h q₁ q₂ δ : SL(3, ℤ)) (hγ₁ : γ₁ ∈ gammaN 6) (hγ₂ : γ₂ ∈ gammaN 6) (hδ : δ ∈ gammaN 6)
    (hb : g₂ * δ * g₁⁻¹ ∈ borelStab) (hq₁ : q₁ ∈ planeBorel) (hq₂ : q₂ ∈ planeBorel)
    (e₁ : q₁ = g₁ * γ₁ * h⁻¹) (e₂ : q₂ = g₂ * γ₂ * h⁻¹) :
    CuspRel (qPrim (tau q₂) (tau_mem_lineBorel_of_planeBorel hq₂)) (qPrim (tau q₁) (tau_mem_lineBorel_of_planeBorel hq₁)) := by
  refine cusp_orbit_change (tau g₁) (tau g₂) (tau γ₁) (tau γ₂) (tau h) (tau q₁) (tau q₂) (tau δ) (tau_mem_gammaN hγ₁)
    (tau_mem_gammaN hγ₂) (tau_mem_gammaN hδ) ?_ (tau_mem_lineBorel_of_planeBorel hq₁) (tau_mem_lineBorel_of_planeBorel hq₂) ?_ ?_
  · have := tau_mem_borelStab hb
    simpa [map_mul, map_inv] using this
  · rw [e₁]; simp [map_mul, map_inv]
  · rw [e₂]; simp [map_mul, map_inv]

/-- **Injectivity** (planes). -/
theorem cuspMapP_injective (F : ConjFrames) (o o' : labelOrbits Γ6 Flag) (ho : flagPlaneOrbit o = flagPlaneOrbit o')
    (hc : CuspRel (cuspVecP F o) (cuspVecP F o')) : o = o' := by
  obtain ⟨n, hn, hnN, hb⟩ := exists_n_of_cuspRel _ _ (tau_mem_lineBorel_of_planeBorel (qOfP_mem o (F.γP o) (F.hP o)))
    (tau_mem_lineBorel_of_planeBorel (qOfP_mem o' (F.γP o') (F.hP o'))) hc
  have hHH : hOfP (flagPlaneOrbit o') = hOfP (flagPlaneOrbit o) := by rw [ho]
  set H := hOfP (flagPlaneOrbit o) with hH
  have e1 : qOfP o (F.γP o) = gOf o * iotaOf (F.γP o) * H⁻¹ := qOfP_eq o _
  have e2 : qOfP o' (F.γP o') = gOf o' * iotaOf (F.γP o') * H⁻¹ := by rw [qOfP_eq, hHH]
  set n₀ : SL(3, ℤ) := tau n with hn₀
  have hn₀N : n₀ ∈ gammaN 6 := tau_mem_gammaN hnN
  have hb₀ : qOfP o' (F.γP o') * n₀ * (qOfP o (F.γP o))⁻¹ ∈ borelStab := by
    have := tau_mem_borelStab hb
    simpa [hn₀, map_mul, map_inv, tau_tau] using this
  set δ : SL(3, ℤ) := iotaOf (F.γP o') * H⁻¹ * n₀ * H * (iotaOf (F.γP o))⁻¹ with hδ
  have hδN : δ ∈ gammaN 6 := by
    have hconj : H⁻¹ * n₀ * H ∈ gammaN 6 := by
      have := (gammaN_normal 6).conj_mem n₀ hn₀N H⁻¹
      simpa using this
    have e : δ = iotaOf (F.γP o') * (H⁻¹ * n₀ * H) * (iotaOf (F.γP o))⁻¹ := by rw [hδ]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (iotaOf_mem _) hconj) (Subgroup.inv_mem _ (iotaOf_mem _))
  have hflag : flagOf (gOf o * δ⁻¹) = flagOf (gOf o') := by
    apply flagOf_eq_of_borel
    have : gOf o' * (gOf o * δ⁻¹)⁻¹ = qOfP o' (F.γP o') * n₀ * (qOfP o (F.γP o))⁻¹ := by
      rw [e1, e2, hδ]; group
    rw [this]
    exact hb₀
  have hsm := flagOf_smul_eq δ hδN (gOf o)
  have hsm2 : gammaSixEquiv ⟨δ, hδN⟩ • o.out = o'.out := by
    calc gammaSixEquiv ⟨δ, hδN⟩ • o.out = gammaSixEquiv ⟨δ, hδN⟩ • flagOf (gOf o) := by rw [flagOf_gOf]
      _ = flagOf (gOf o * δ⁻¹) := hsm
      _ = flagOf (gOf o') := hflag
      _ = o'.out := flagOf_gOf o'
  calc o = Quotient.mk'' o.out := (Quotient.out_eq' o).symm
    _ = Quotient.mk'' (gammaSixEquiv ⟨δ, hδN⟩ • o.out) := MulAction.orbitRel.Quotient.quotient_smul_eq.symm
    _ = Quotient.mk'' o'.out := by rw [hsm2]
    _ = o' := Quotient.out_eq' o'

/-- **Surjectivity** (planes). -/
theorem cuspMapP_surjective (F : ConjFrames) (a : labelOrbits Γ6 Plane) (v : Prim2) :
    ∃ o : labelOrbits Γ6 Flag, flagPlaneOrbit o = a ∧ CuspRel (cuspVecP F o) v := by
  obtain ⟨q0', hq0', hv⟩ := exists_q_of_prim v
  set q0 : SL(3, ℤ) := tau q0' with hq0def
  have hq0 : q0 ∈ planeBorel := tau_mem_planeBorel_of_lineBorel hq0'
  have hq0t : tau q0 = q0' := tau_tau q0'
  set h := hOfP a with hh
  set g0 : SL(3, ℤ) := q0 * h with hg0
  set F0 : Flag := flagOf g0 with hF0
  set o0 : labelOrbits Γ6 Flag := Quotient.mk'' F0 with ho0
  have hmem : F0 ∈ labelOrbit Γ6 Flag o0 := (mem_labelOrbit_iff o0 F0).2 rfl
  have hplane : planeOf g0 = a.out := by
    rw [← planeOf_hOfP a, hg0]
    exact ((planeOf_eq_iff h (q0 * h)).2 (by simpa using hq0)).symm
  have ha : flagPlaneOrbit o0 = a := by
    rw [← flagPlaneOrbit_of_mem hmem]
    show (Quotient.mk'' (planeOf g0) : labelOrbits Γ6 Plane) = a
    rw [hplane]
    exact Quotient.out_eq' a
  refine ⟨o0, ha, ?_⟩
  obtain ⟨δ, hδ⟩ := hmem
  have hp : δ = gammaSixEquiv (gammaSixEquiv.symm δ) := by simp
  set p := gammaSixEquiv.symm δ with hpdef
  have hflag : flagOf (gOf o0 * p.1⁻¹) = flagOf g0 := by
    rw [← smul_flagOf]
    have : gammaSixEquiv p • flagOf (gOf o0) = F0 := by
      rw [flagOf_gOf, ← hp]; exact hδ
    exact this
  have hb : g0 * p.1 * (gOf o0)⁻¹ ∈ borelStab := by
    have := borel_of_flagOf_eq _ _ hflag
    simpa [mul_assoc] using this
  have hHH : hOfP (flagPlaneOrbit o0) = h := by rw [ha]
  have e₁ : qOfP o0 (F.γP o0) = gOf o0 * iotaOf (F.γP o0) * h⁻¹ := by rw [qOfP_eq, hHH]
  have e₂ : q0 = g0 * 1 * h⁻¹ := by rw [hg0]; group
  have key := cuspP_orbit_change (gOf o0) g0 (iotaOf (F.γP o0)) 1 h (qOfP o0 (F.γP o0)) q0 p.1 (iotaOf_mem _) (Subgroup.one_mem _) p.2
    hb (qOfP_mem o0 (F.γP o0) (F.hP o0)) hq0 e₁ e₂
  have hv' : qPrim (tau q0) (tau_mem_lineBorel_of_planeBorel hq0) = v := Subtype.ext (show qVec (tau q0) = v.1 by rw [hq0t]; exact hv)
  rw [hv'] at key
  exact cuspRel_symm key

end TernaryPeriodPolynomials.Argument.GammaNStokes
