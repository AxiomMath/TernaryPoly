module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BFlagTau
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Orbits

@[expose] public section


/-!
# Frames for the flag orbits over a plane orbit

Formalized by Claude Sonnet 5.5.

The plane analogues of `BLine1`: frames `hOfP b` of the representatives of plane orbits, `hFrameP o γ`, `qOfP o γ ∈ planeBorel`, and the plane type of the matrix homomorphisms of the plane stabilizers.
Composing with `tau` turns plane type into line type (`lineType_tau`).
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
open TernaryPeriodPolynomials.Argument.SeedC3 (gammaNP)

/-- The hypothesis that `M s` has bottom row `(0, 0, 1)`. -/
def PlaneType {G : Type} [Group G] (M : G →* SL(3, ℤ)) : Prop :=
  ∀ s, (M s : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧ (M s : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 ∧
    (M s : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1

theorem lineType_tau {G : Type} [Group G] {M : G →* SL(3, ℤ)} (h : PlaneType M) : LineType (tau.comp M) := fun s => by
  have h1 := tau_mem_lineStab_of_planeStab (M := M s) ⟨(h s).1, (h s).2.1, (h s).2.2⟩
  exact ⟨h1.2.1, h1.2.2, h1.1⟩

/-- A frame `h` of the representative of a plane orbit. -/
def hOfP (b : labelOrbits Γ6 Plane) : SL(3, ℤ) := Classical.choose (exists_planeOf b.out)

theorem planeOf_hOfP (b : labelOrbits Γ6 Plane) : planeOf (hOfP b) = b.out := Classical.choose_spec (exists_planeOf b.out)

theorem smul_planeOf' (γ : Γ6) (h : SL(3, ℤ)) : γ • planeOf h = planeOf (h * (iotaOf γ)⁻¹) := by
  have := smul_planeOf (gammaSixEquiv.symm γ) h
  rwa [MulEquiv.apply_symm_apply] at this

/-- **Elements of the stabilizer of `planeOf h` have plane type in the frame `h`, and lie in `Γ(6)` there.** -/
theorem stab_gammaNP (h : SL(3, ℤ)) (R : Plane) (hR : planeOf h = R) (s : ↥(MulAction.stabilizer Γ6 R)) :
    h * iotaOf (s : Γ6) * h⁻¹ ∈ gammaNP 6 := by
  have hs : (s : Γ6) ∈ MulAction.stabilizer Γ6 (planeOf h) := by rw [hR]; exact s.2
  have e : (s : Γ6) = gammaSixEquiv (gammaSixEquiv.symm (s : Γ6)) := by simp
  rw [e] at hs
  exact (mem_stabilizer_planeOf_iff _ h).1 hs

theorem stab_planeType (h : SL(3, ℤ)) (R : Plane) (hR : planeOf h = R) :
    PlaneType (conjIota (MulAction.stabilizer Γ6 R) h) := fun s => by
  have := (stab_gammaNP h R hR s).2
  exact ⟨this.1, this.2.1, this.2.2⟩

theorem stab_gammaN_P (h : SL(3, ℤ)) (R : Plane) (hR : planeOf h = R) (s : ↥(MulAction.stabilizer Γ6 R)) :
    conjIota (MulAction.stabilizer Γ6 R) h s ∈ gammaN 6 := (stab_gammaNP h R hR s).1

/-- The frame of a flag orbit over a plane orbit, given `γ` carrying the representative of the plane orbit to the plane of the flag. -/
def hFrameP (o : labelOrbits Γ6 Flag) (γ : Γ6) : SL(3, ℤ) := hOfP (flagPlaneOrbit o) * (iotaOf γ)⁻¹

/-- The matrix relating the flag frame to the plane frame. -/
def qOfP (o : labelOrbits Γ6 Flag) (γ : Γ6) : SL(3, ℤ) := gOf o * (hFrameP o γ)⁻¹

theorem planeOf_gOf (o : labelOrbits Γ6 Flag) : planeOf (gOf o) = flagPlaneOf o.out :=
  (flagPlaneOf_flagOf (gOf o)).symm.trans (congrArg flagPlaneOf (flagOf_gOf o))

theorem planeOf_hFrameP (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagPlaneOrbit o).out = flagPlaneOf o.out) :
    planeOf (hFrameP o γ) = flagPlaneOf o.out := by
  rw [← hγ, ← planeOf_hOfP (flagPlaneOrbit o), smul_planeOf']
  rfl

theorem qOfP_mem (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagPlaneOrbit o).out = flagPlaneOf o.out) :
    qOfP o γ ∈ planeBorel :=
  (planeOf_eq_iff (hFrameP o γ) (gOf o)).1 ((planeOf_hFrameP o γ hγ).trans (planeOf_gOf o).symm)

theorem conjHom_compP (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagPlaneOrbit o).out = flagPlaneOf o.out) :
    (conjIota (MulAction.stabilizer Γ6 (flagPlaneOrbit o).out) (hOfP (flagPlaneOrbit o))).comp
      (conjStabHom γ (flagPlaneOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_plane_of o γ hγ)) =
    conjIota (MulAction.stabilizer Γ6 o.out) (hFrameP o γ) := by
  refine MonoidHom.ext fun s => ?_
  show hOfP (flagPlaneOrbit o) * iotaOf (↑(conjStabHom γ (flagPlaneOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_plane_of o γ hγ) s) : Γ6) *
      (hOfP (flagPlaneOrbit o))⁻¹ = hFrameP o γ * iotaOf (s : Γ6) * (hFrameP o γ)⁻¹
  rw [conjStabHom_apply, iotaOf_mul, iotaOf_mul, iotaOf_inv, hFrameP]
  group

end TernaryPeriodPolynomials.Argument.GammaNStokes
