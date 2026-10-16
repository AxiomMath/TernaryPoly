module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG3
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.BaseSumZeroBridge

@[expose] public section


/-!
# Plane geometry package, part 4: the flags `Pc c` over the plane of a face, indexed by the representative cusps

Formalized by Claude Sonnet 5.5.

For the representative cusps `c ∈ (cuspReps hN).R` of `Γ(6)` (Farey side) put `wOf c = ` the first column of `cuspElt c` and `Pc h c = pflag h (wOf c)`.  Then:
* `sigmaCusp_val`: the generator `σ_c = (gammaEquiv hN).symm (cuspSigma c)` is `posPar (wOf c)`;
* `Pc_flagPlane`, `Pc_stab_nl`, `Pc_stab_ll`: `Pc h c` is a flag over `planeOf h` whose stabilizer in `Γ(6)` contains the radical letters of the plane group of `h` and the Levi letter `σ_c` (G-a);
* `Pc_orbit_bijective` (G-b): `c ↦ Γ(6)`-orbit of `Pc h c` is a bijection from the representative cusps onto the flag orbits over the orbit of `planeOf h`.
-/

open scoped MatrixGroups
open CongruenceSubgroup

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPoly.OrdinaryIncidence (Plane)

/-- The primitive vector generating the representative cusp `c`. -/
def wOf (c : RationalLine2) : Prim2 := ⟨fun i => (cuspElt c).val i 0, coprime_of_prim (isGen_cuspElt c).1⟩

theorem lineP_wOf (c : RationalLine2) : lineP (wOf c) = c :=
  ((isGen_lineP (wOf c)).line_eq_iff (isGen_cuspElt c)).mpr (Or.inl rfl)

/-- The flag attached to a representative cusp. -/
def Pc (h : SL(3, ℤ)) (c : RationalLine2) : Flag := pflag h (wOf c)

theorem sigmaCusp_val (hN : 3 ≤ 6) (c : RationalLine2) :
    (((gammaEquiv hN).symm (cuspSigma (N := 6) c) : Gamma 6) : SL(2, ℤ)) = posPar (wOf c).1 := by
  apply Subtype.ext
  ext i j
  have h := cuspSigma_eq_posParGL c
  have h2 := congrArg (fun g : IntegralGL => g.val i j) h
  simp only [posParGL_val] at h2
  have : ((((gammaEquiv hN).symm (cuspSigma (N := 6) c) : Gamma 6) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j =
      ((cuspSigma (N := 6) c : gammaNGL 6) : IntegralGL).val i j := rfl
  rw [this, h2]
  fin_cases i <;> fin_cases j <;> simp [posPar, wOf]

theorem Pc_flagPlane (h : SL(3, ℤ)) (c : RationalLine2) : flagPlaneOf (Pc h c) = planeOf h := flagPlaneOf_pflag h _

theorem Pc_stab_nl (h : SL(3, ℤ)) (c : RationalLine2) (r : TernaryPeriodPolynomials.SphericalDetection.Helpers.RadicalLattice) :
    planeEmb h ((faceExt 6 h).inl r) ∈ MulAction.stabilizer Γ6 (Pc h c) := pflag_stab_nl h _ r

theorem Pc_stab_ll (hN : 3 ≤ 6) (h : SL(3, ℤ)) (c : RationalLine2) :
    planeEmb h ((faceSplitting 6 h) ((gammaEquiv hN).symm (cuspSigma (N := 6) c))) ∈ MulAction.stabilizer Γ6 (Pc h c) :=
  pflag_stab_ll h _ _ (sigmaCusp_val hN c)

/-- **(G-b), injectivity**: distinct representative cusps give flags in distinct `Γ(6)`-orbits. -/
theorem Pc_orbit_inj (hN : 3 ≤ 6) (h : SL(3, ℤ)) (c c' : RationalLine2) (hc : c ∈ (cuspReps hN).R) (hc' : c' ∈ (cuspReps hN).R)
    (heq : (Quotient.mk'' (Pc h c) : labelOrbits Γ6 Flag) = Quotient.mk'' (Pc h c')) : c = c' := by
  have hrel := (orbit_pflag_iff h (wOf c) (wOf c')).1 heq
  obtain ⟨γ, hγ⟩ := orbit_of_rel hN _ _ hrel
  rw [lineP_wOf, lineP_wOf] at hγ
  exact (cuspReps hN).inj c hc c' hc' γ hγ

/-- **(G-b), surjectivity**: every flag orbit over the orbit `O` of the plane `planeOf h` contains some `Pc h c`, `c` a representative cusp. -/
theorem Pc_orbit_surj (hN : 3 ≤ 6) (h : SL(3, ℤ)) (O : labelOrbits Γ6 Plane) (hO : planeOf h ∈ labelOrbit Γ6 Plane O)
    (o : labelOrbits Γ6 Flag) (ho : flagPlaneOf o.out ∈ labelOrbit Γ6 Plane O) :
    ∃ c ∈ (cuspReps hN).R, (Quotient.mk'' (Pc h c) : labelOrbits Γ6 Flag) = o := by
  rw [mem_labelOrbit_iff] at hO ho
  obtain ⟨γ, hγ⟩ := (MulAction.orbitRel_apply).1 (Quotient.exact (hO.trans ho.symm))
  have hF : flagPlaneOf (γ • o.out) = planeOf h := by
    exact (TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant γ o.out).trans hγ
  obtain ⟨w, hw⟩ := pflag_surj h (γ • o.out) hF
  obtain ⟨r, hr, γ', hγ'⟩ := (cuspReps hN).cover (lineP w)
  have hrel : CuspRel (wOf r) w := by
    refine rel_of_orbit hN γ' (wOf r) w ?_
    rw [lineP_wOf]; exact hγ'
  refine ⟨r, hr, ?_⟩
  calc (Quotient.mk'' (Pc h r) : labelOrbits Γ6 Flag) = Quotient.mk'' (pflag h w) := (orbit_pflag_iff h _ _).2 hrel
    _ = Quotient.mk'' (γ • o.out) := hw
    _ = o := MulAction.orbitRel.Quotient.quotient_smul_eq.trans (Quotient.out_eq' o)

end TernaryPeriodPolynomials.Argument.GammaNStokes
