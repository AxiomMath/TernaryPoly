module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine4
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.BaseSumZeroBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Vanish
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.CuspGeometry

@[expose] public section

/-!
# The flag orbits over a line orbit are parametrized by the representative cusps

Formalized by Claude Sonnet 5.5.

`orbit_eq_iff`: the flags `flagOf (q h)`, `flagOf (q' h)` (`q, q'` in the Borel of the line) are in one `Γ(6)`-orbit iff the cusp vectors `qVec q`, `qVec q'` are `CuspRel` (the `cusp_orbit_change`, `exists_n_of_cuspRel`).
`flagAt_cusp_injective`, `flagAt_cusp_surjective`, `flagAt_cusp_bijOn` (G-b): `c ↦ [flagAt h (cuspPrim c)]` is a bijection from the representatives of the cusps of `Γ(6)` onto the flag orbits over the line orbit of `lineOf h`.
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (RadicalLattice)

section Orbits

variable (h : SL(3, ℤ))

theorem orbit_eq_iff (q q' : SL(3, ℤ)) (hq : q ∈ lineBorel) (hq' : q' ∈ lineBorel) :
    (Quotient.mk'' (flagOf (q * h)) : labelOrbits Γ6 Flag) = Quotient.mk'' (flagOf (q' * h)) ↔
      CuspRel (qPrim q hq) (qPrim q' hq') := by
  constructor
  · intro hor
    have hor' := Quotient.exact' hor
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hor'
    obtain ⟨δ, hδ⟩ := hor'
    obtain ⟨p, hp⟩ := gammaSixEquiv.surjective δ
    rw [← hp, smul_flagOf] at hδ
    have hb := borel_of_flagOf_eq _ _ hδ
    exact cusp_orbit_change (q' * h) (q * h) 1 1 h q' q p.1 (Subgroup.one_mem _) (Subgroup.one_mem _) p.2
      (by simpa [mul_assoc] using hb) hq' hq (by simp) (by simp)
  · intro hc
    obtain ⟨n, hn, hnN, hb⟩ := exists_n_of_cuspRel q' q hq' hq (cuspRel_symm hc)
    have hp : h⁻¹ * n * h ∈ gammaN 6 := by
      simpa [mul_assoc] using (gammaN_normal 6).conj_mem n hnN h⁻¹
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨gammaSixEquiv ⟨h⁻¹ * n * h, hp⟩, ?_⟩
    rw [smul_flagOf]
    apply flagOf_eq_of_borel
    have e : q * h * (q' * h * (h⁻¹ * n * h)⁻¹)⁻¹ = q * n * q'⁻¹ := by group
    rw [e]
    exact hb

theorem lineP_cuspPrim (c : RationalLine2) : lineP (cuspPrim c) = c :=
  ((isGen_lineP _).line_eq_iff (isGen_cuspElt c)).mpr (Or.inl rfl)

theorem qPrim_qMat (w : Prim2) : qPrim (qMat w) (qMat_mem w) = w := Subtype.ext (qMat_vec w)

theorem flagAt_orbit_eq_iff (w w' : Prim2) :
    (Quotient.mk'' (flagAt h w) : labelOrbits Γ6 Flag) = Quotient.mk'' (flagAt h w') ↔ CuspRel w w' := by
  have := orbit_eq_iff h (qMat w) (qMat w') (qMat_mem w) (qMat_mem w')
  rw [qPrim_qMat, qPrim_qMat] at this
  exact this

/-- **(G-b), injectivity.** -/
theorem flagAt_cusp_injective (c c' : (cuspReps (by norm_num : 3 ≤ 6)).R)
    (heq : (Quotient.mk'' (flagAt h (cuspPrim c)) : labelOrbits Γ6 Flag) = Quotient.mk'' (flagAt h (cuspPrim c'))) :
    c = c' := by
  have hrel := (flagAt_orbit_eq_iff h _ _).1 heq
  obtain ⟨γ, hγ⟩ := orbit_of_rel (by norm_num : 3 ≤ 6) _ _ hrel
  rw [lineP_cuspPrim, lineP_cuspPrim] at hγ
  exact Subtype.ext ((cuspReps (by norm_num : 3 ≤ 6)).inj _ c.2 _ c'.2 γ hγ)

/-- **(G-b), range**: the flag orbit of `flagAt h w` lies over the line orbit of `lineOf h`. -/
theorem flagLineOrbit_flagAt (w : Prim2) :
    flagLineOrbit (Quotient.mk'' (flagAt h w) : labelOrbits Γ6 Flag) = Quotient.mk'' (lineOf h) := by
  have hmem : flagAt h w ∈ labelOrbit Γ6 Flag (Quotient.mk'' (flagAt h w)) := (mem_labelOrbit_iff _ _).2 rfl
  rw [← flagLineOrbit_of_mem hmem]
  show (Quotient.mk'' (flagLineOf (flagAt h w)) : labelOrbits Γ6 Line) = _
  rw [flagLineOf_flagAt]

/-- **(G-b), surjectivity**: every flag orbit over the line orbit of `lineOf h` is the orbit of some `flagAt h (cuspPrim c)`. -/
theorem flagAt_cusp_surjective (o : labelOrbits Γ6 Flag) (ho : flagLineOrbit o = Quotient.mk'' (lineOf h)) :
    ∃ c : (cuspReps (by norm_num : 3 ≤ 6)).R, (Quotient.mk'' (flagAt h (cuspPrim c)) : labelOrbits Γ6 Flag) = o := by
  have hex := Quotient.exact' ho
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hex
  obtain ⟨δ, hδ⟩ := hex
  -- the translate `δ⁻¹ • o.out` has line `lineOf h`
  set F' : Flag := δ⁻¹ • o.out with hF'
  have hline : flagLineOf F' = lineOf h := by
    have e : flagLineOf F' = δ⁻¹ • flagLineOf o.out :=
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant _ _
    rw [e, ← hδ, inv_smul_smul]
  have hmemo : F' ∈ labelOrbit Γ6 Flag o := by
    rw [mem_labelOrbit_iff]
    have : (Quotient.mk'' (δ⁻¹ • o.out) : labelOrbits Γ6 Flag) = Quotient.mk'' o.out :=
      MulAction.orbitRel.Quotient.quotient_smul_eq
    rw [hF', this]
    exact Quotient.out_eq' o
  obtain ⟨g', hg'⟩ := exists_flagOf F'
  have hq : g' * h⁻¹ ∈ lineBorel := by
    have : lineOf h = lineOf g' := by
      rw [← hline, ← hg']
      rfl
    exact (lineOf_eq_iff h g').1 this
  set q := g' * h⁻¹ with hqdef
  have hqh : q * h = g' := by rw [hqdef]; group
  obtain ⟨r, hr, γ, hγ⟩ := (cuspReps (by norm_num : 3 ≤ 6)).cover (lineP (qPrim q hq))
  have hrel : CuspRel (cuspPrim r) (qPrim q hq) := by
    refine rel_of_orbit (by norm_num : 3 ≤ 6) γ _ _ ?_
    rw [lineP_cuspPrim]; exact hγ
  refine ⟨⟨r, hr⟩, ?_⟩
  have h1 := (orbit_eq_iff h (qMat (cuspPrim r)) q (qMat_mem _) hq).2 (by rw [qPrim_qMat]; exact hrel)
  have h2 : (Quotient.mk'' (flagOf (q * h)) : labelOrbits Γ6 Flag) = o := by
    rw [hqh, hg']; exact (mem_labelOrbit_iff _ _).1 hmemo
  exact h1.trans h2

/-- **(G-b)**: the orbit map `c ↦ [flagAt h (cuspPrim c)]` is a bijection from the representative cusps onto the flag orbits over the line orbit of `lineOf h`. -/
theorem flagAt_cusp_bijOn :
    Set.BijOn (fun c : (cuspReps (by norm_num : 3 ≤ 6)).R => (Quotient.mk'' (flagAt h (cuspPrim c)) : labelOrbits Γ6 Flag))
      Set.univ {o | flagLineOrbit o = Quotient.mk'' (lineOf h)} := by
  refine ⟨fun c _ => flagLineOrbit_flagAt h _, fun c _ c' _ e => flagAt_cusp_injective h c c' e, fun o ho => ?_⟩
  obtain ⟨c, hc⟩ := flagAt_cusp_surjective h o ho
  exact ⟨c, Set.mem_univ _, hc⟩

/-- … in the form used by the face sums: `flagLineOf o.out` lies in the line orbit `a` of `lineOf h`. -/
theorem flagAt_cusp_bijOn' (a : labelOrbits Γ6 Line) (ha : lineOf h ∈ labelOrbit Γ6 Line a) :
    Set.BijOn (fun c : (cuspReps (by norm_num : 3 ≤ 6)).R => (Quotient.mk'' (flagAt h (cuspPrim c)) : labelOrbits Γ6 Flag))
      Set.univ {o | flagLineOf o.out ∈ labelOrbit Γ6 Line a} := by
  have e : (Quotient.mk'' (lineOf h) : labelOrbits Γ6 Line) = a := (mem_labelOrbit_iff _ _).1 ha
  rw [← e]
  have := flagAt_cusp_bijOn h
  convert this using 2
  ext o
  exact mem_labelOrbit_iff _ _

end Orbits

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
