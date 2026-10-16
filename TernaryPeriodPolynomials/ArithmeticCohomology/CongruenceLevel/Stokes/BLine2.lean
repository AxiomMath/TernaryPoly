module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine1
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Uniform

@[expose] public section


/-!
# The flag orbits over a line orbit are in bijection with the cusps of `Γ(6)`

Formalized by Claude Sonnet 5.5.

`cusp_orbit_change` (the cusp vector of `q = g γ h⁻¹` only depends on the `Γ(6)`-orbit of the flag `flagOf g`), `cuspMap_injective` and `cuspMap_surjective`: the map
`o ↦ [qVec (qOf o (γ o))]` from the flag orbits over a line orbit to `Cusp6` is a bijection.
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

theorem borel_of_borel_pair {b : SL(3, ℤ)} (h1 : b ∈ lineBorel) (h2 : b ∈ planeBorel) : b ∈ borelStab :=
  ⟨h1.1, h1.2, h2.2⟩

theorem borelStab_le_planeBorel {b : SL(3, ℤ)} (hb : b ∈ borelStab) : b ∈ planeBorel := ⟨hb.2.1, hb.2.2⟩

/-- Equal complete flags have frames differing by an upper triangular matrix. -/
theorem borel_of_flagOf_eq (g g' : SL(3, ℤ)) (h : flagOf g = flagOf g') : g' * g⁻¹ ∈ borelStab := by
  have h1 : lineOf g = lineOf g' := congrArg (fun F : Flag => F.val.1) h
  have h2 : planeOf g = planeOf g' := congrArg (fun F : Flag => F.val.2) h
  exact borel_of_borel_pair ((lineOf_eq_iff g g').1 h1) ((planeOf_eq_iff g g').1 h2)

theorem flagOf_eq_of_borel (g g' : SL(3, ℤ)) (h : g' * g⁻¹ ∈ borelStab) : flagOf g = flagOf g' := by
  apply Subtype.ext
  apply Prod.ext
  · exact (lineOf_eq_iff g g').2 (borel_le_lineBorel h)
  · exact (planeOf_eq_iff g g').2 (borelStab_le_planeBorel h)

theorem flagOf_smul_eq (p : SL(3, ℤ)) (hp : p ∈ gammaN 6) (g : SL(3, ℤ)) :
    gammaSixEquiv ⟨p, hp⟩ • flagOf g = flagOf (g * p⁻¹) := smul_flagOf ⟨p, hp⟩ g

/-- **The cusp vector only depends on the `Γ(6)`-orbit of the flag.** -/
theorem cusp_orbit_change (g₁ g₂ γ₁ γ₂ h q₁ q₂ δ : SL(3, ℤ)) (hγ₁ : γ₁ ∈ gammaN 6) (hγ₂ : γ₂ ∈ gammaN 6) (hδ : δ ∈ gammaN 6)
    (hb : g₂ * δ * g₁⁻¹ ∈ borelStab) (hq₁ : q₁ ∈ lineBorel) (hq₂ : q₂ ∈ lineBorel)
    (e₁ : q₁ = g₁ * γ₁ * h⁻¹) (e₂ : q₂ = g₂ * γ₂ * h⁻¹) : CuspRel (qPrim q₂ hq₂) (qPrim q₁ hq₁) := by
  set m : SL(3, ℤ) := h * (γ₁⁻¹ * δ⁻¹ * γ₂) * h⁻¹ with hm
  have hmN : m ∈ gammaN 6 := by
    have := (gammaN_normal 6).conj_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ₁) (Subgroup.inv_mem _ hδ)) hγ₂) h
    simpa [hm, mul_assoc] using this
  have e : q₂ = (g₂ * δ * g₁⁻¹) * q₁ * m := by
    rw [e₁, e₂, hm]; group
  have hmL : m ∈ lineBorel := by
    have : m = q₁⁻¹ * (g₂ * δ * g₁⁻¹)⁻¹ * q₂ := by
      rw [e₁, e₂, hm]; group
    rw [this]
    exact lineBorel.mul_mem (lineBorel.mul_mem (lineBorel.inv_mem hq₁) (lineBorel.inv_mem (borel_le_lineBorel hb))) hq₂
  have := qVec_change (g₂ * δ * g₁⁻¹) q₁ m hb hq₁ hmL hmN
  subst e
  exact this

/-- The cusp vector of a flag orbit, with respect to the frames `F`. -/
def cuspVec (F : ConjFrames) (o : labelOrbits Γ6 Flag) : Prim2 :=
  qPrim (qOf o (F.γL o)) (qOf_mem o (F.γL o) (F.hL o))

theorem qOf_eq (o : labelOrbits Γ6 Flag) (γ : Γ6) :
    qOf o γ = gOf o * iotaOf γ * (hOf (flagLineOrbit o))⁻¹ := by
  simp [qOf, hFrame, mul_assoc]

/-- **Injectivity**: two flag orbits over the same line orbit with the same cusp coincide. -/
theorem cuspMap_injective (F : ConjFrames) (o o' : labelOrbits Γ6 Flag) (ho : flagLineOrbit o = flagLineOrbit o')
    (hc : CuspRel (cuspVec F o) (cuspVec F o')) : o = o' := by
  obtain ⟨n, hn, hnN, hb⟩ := exists_n_of_cuspRel _ _ (qOf_mem o (F.γL o) (F.hL o)) (qOf_mem o' (F.γL o') (F.hL o')) hc
  have hHH : hOf (flagLineOrbit o') = hOf (flagLineOrbit o) := by rw [ho]
  set H := hOf (flagLineOrbit o) with hH
  have e1 : qOf o (F.γL o) = gOf o * iotaOf (F.γL o) * H⁻¹ := qOf_eq o _
  have e2 : qOf o' (F.γL o') = gOf o' * iotaOf (F.γL o') * H⁻¹ := by rw [qOf_eq, hHH]
  set δ : SL(3, ℤ) := iotaOf (F.γL o') * H⁻¹ * n * H * (iotaOf (F.γL o))⁻¹ with hδ
  have hδN : δ ∈ gammaN 6 := by
    have hconj : H⁻¹ * n * H ∈ gammaN 6 := by
      have := (gammaN_normal 6).conj_mem n hnN H⁻¹
      simpa using this
    have e : δ = iotaOf (F.γL o') * (H⁻¹ * n * H) * (iotaOf (F.γL o))⁻¹ := by rw [hδ]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (iotaOf_mem _) hconj) (Subgroup.inv_mem _ (iotaOf_mem _))
  have hflag : flagOf (gOf o * δ⁻¹) = flagOf (gOf o') := by
    apply flagOf_eq_of_borel
    have : gOf o' * (gOf o * δ⁻¹)⁻¹ = qOf o' (F.γL o') * n * (qOf o (F.γL o))⁻¹ := by
      rw [e1, e2, hδ]; group
    rw [this]
    exact hb
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

/-- **Surjectivity**: every cusp occurs over every line orbit. -/
theorem cuspMap_surjective (F : ConjFrames) (a : labelOrbits Γ6 Line) (v : Prim2) :
    ∃ o : labelOrbits Γ6 Flag, flagLineOrbit o = a ∧ CuspRel (cuspVec F o) v := by
  obtain ⟨q0, hq0, hv⟩ := exists_q_of_prim v
  set h := hOf a with hh
  set g0 : SL(3, ℤ) := q0 * h with hg0
  set F0 : Flag := flagOf g0 with hF0
  set o0 : labelOrbits Γ6 Flag := Quotient.mk'' F0 with ho0
  have hmem : F0 ∈ labelOrbit Γ6 Flag o0 := (mem_labelOrbit_iff o0 F0).2 rfl
  have hline : lineOf g0 = a.out := by
    rw [← lineOf_hOf a, hg0]
    exact ((lineOf_eq_iff h (q0 * h)).2 (by simpa using hq0)).symm
  have ha : flagLineOrbit o0 = a := by
    rw [← flagLineOrbit_of_mem hmem]
    show (Quotient.mk'' (lineOf g0) : labelOrbits Γ6 Line) = a
    rw [hline]
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
  have hHH : hOf (flagLineOrbit o0) = h := by rw [ha]
  have e₁ : qOf o0 (F.γL o0) = gOf o0 * iotaOf (F.γL o0) * h⁻¹ := by rw [qOf_eq, hHH]
  have e₂ : q0 = g0 * 1 * h⁻¹ := by rw [hg0]; group
  have key := cusp_orbit_change (gOf o0) g0 (iotaOf (F.γL o0)) 1 h (qOf o0 (F.γL o0)) q0 p.1 (iotaOf_mem _) (Subgroup.one_mem _) p.2
    hb (qOf_mem o0 (F.γL o0) (F.hL o0)) hq0 e₁ e₂
  have hv' : qPrim q0 hq0 = v := Subtype.ext hv
  rw [hv'] at key
  exact cuspRel_symm key

end TernaryPeriodPolynomials.Argument.GammaNStokes
