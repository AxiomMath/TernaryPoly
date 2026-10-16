module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BFlag
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BCuspP
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Orbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Rel

@[expose] public section


/-!
# Frames for the flag orbits over a line orbit, and the line cocycles of the line stabilizers

Formalized by Claude Sonnet 5.5.

For a line orbit `a` the frame `hOf a` has `lineOf (hOf a) = a.out`; the stabilizer of `a.out` in `Γ(6)` then maps by `s ↦ h ι(s) h⁻¹` to matrices of line type in `Γ(6)` (`stab_lineType`, `stab_gammaN`).
For a flag orbit `o` and `γ ∈ Γ(6)` carrying `a.out` to the line of `o.out` the frame `hFrame o γ = h ι(γ)⁻¹` and `qOf o γ = g_o h⁻¹ ∈ lineBorel` relate the frame of the flag to that of the line
(`qOf_mem`); the conjugation `Stab(o.out) → Stab(a.out)` composed with the matrix homomorphism of `a` is the matrix homomorphism of `hFrame o γ` (`conjHom_comp`).
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

/-- A frame `h` of the representative of a line orbit. -/
def hOf (a : labelOrbits Γ6 Line) : SL(3, ℤ) := Classical.choose (exists_lineOf a.out)

theorem lineOf_hOf (a : labelOrbits Γ6 Line) : lineOf (hOf a) = a.out := Classical.choose_spec (exists_lineOf a.out)

/-- A frame `g` of the representative of a flag orbit. -/
def gOf (o : labelOrbits Γ6 Flag) : SL(3, ℤ) := Classical.choose (exists_flagOf o.out)

theorem flagOf_gOf (o : labelOrbits Γ6 Flag) : flagOf (gOf o) = o.out := Classical.choose_spec (exists_flagOf o.out)

/-- The `SL₃(ℤ)` matrix of an element of `Γ(6)`. -/
def iotaOf (γ : Γ6) : SL(3, ℤ) := (gammaSixEquiv.symm γ).1

theorem iotaOf_mem (γ : Γ6) : iotaOf γ ∈ gammaN 6 := (gammaSixEquiv.symm γ).2

theorem iotaOf_mul (γ δ : Γ6) : iotaOf (γ * δ) = iotaOf γ * iotaOf δ := by simp [iotaOf]

theorem iotaOf_inv (γ : Γ6) : iotaOf γ⁻¹ = (iotaOf γ)⁻¹ := by simp [iotaOf]

theorem iotaS_apply (S : Subgroup Γ6) (s : ↥S) : iotaS S s = iotaOf (s : Γ6) := rfl

/-- **Elements of the stabilizer of `lineOf h` have line type in the frame `h`, and lie in `Γ(6)` there.** -/
theorem stab_gammaNQ (h : SL(3, ℤ)) (R : Line) (hR : lineOf h = R) (s : ↥(MulAction.stabilizer Γ6 R)) :
    h * iotaOf (s : Γ6) * h⁻¹ ∈ gammaNQ 6 := by
  have hs : (s : Γ6) ∈ MulAction.stabilizer Γ6 (lineOf h) := by rw [hR]; exact s.2
  have e : (s : Γ6) = gammaSixEquiv (gammaSixEquiv.symm (s : Γ6)) := by simp
  rw [e] at hs
  exact (mem_stabilizer_lineOf_iff _ h).1 hs

theorem stab_lineType (h : SL(3, ℤ)) (R : Line) (hR : lineOf h = R) :
    LineType (conjIota (MulAction.stabilizer Γ6 R) h) := fun s => by
  have := (stab_gammaNQ h R hR s).2
  exact ⟨this.2.1, this.2.2, this.1⟩

theorem stab_gammaN (h : SL(3, ℤ)) (R : Line) (hR : lineOf h = R) (s : ↥(MulAction.stabilizer Γ6 R)) :
    conjIota (MulAction.stabilizer Γ6 R) h s ∈ gammaN 6 := (stab_gammaNQ h R hR s).1

/-- The frame of a flag orbit over a line orbit, given `γ` carrying the representative of the line orbit to the line of the flag. -/
def hFrame (o : labelOrbits Γ6 Flag) (γ : Γ6) : SL(3, ℤ) := hOf (flagLineOrbit o) * (iotaOf γ)⁻¹

/-- The matrix relating the flag frame to the line frame. -/
def qOf (o : labelOrbits Γ6 Flag) (γ : Γ6) : SL(3, ℤ) := gOf o * (hFrame o γ)⁻¹

theorem flagOf_fst (g : SL(3, ℤ)) : (flagOf g).val.1 = lineOf g := rfl

theorem flagOf_snd (g : SL(3, ℤ)) : (flagOf g).val.2 = planeOf g := rfl

theorem flagLineOf_flagOf (g : SL(3, ℤ)) : flagLineOf (flagOf g) = lineOf g := rfl

theorem flagPlaneOf_flagOf (g : SL(3, ℤ)) : flagPlaneOf (flagOf g) = planeOf g := rfl

theorem lineOf_gOf (o : labelOrbits Γ6 Flag) : lineOf (gOf o) = flagLineOf o.out :=
  (flagLineOf_flagOf (gOf o)).symm.trans (congrArg flagLineOf (flagOf_gOf o))

theorem smul_lineOf' (γ : Γ6) (h : SL(3, ℤ)) : γ • lineOf h = lineOf (h * (iotaOf γ)⁻¹) := by
  have := smul_lineOf (gammaSixEquiv.symm γ) h
  rwa [MulEquiv.apply_symm_apply] at this

theorem lineOf_hFrame (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagLineOrbit o).out = flagLineOf o.out) :
    lineOf (hFrame o γ) = flagLineOf o.out := by
  rw [← hγ, ← lineOf_hOf (flagLineOrbit o), smul_lineOf']
  rfl

theorem qOf_mem (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagLineOrbit o).out = flagLineOf o.out) :
    qOf o γ ∈ lineBorel := by
  have h := (lineOf_eq_iff (hFrame o γ) (gOf o)).1 ((lineOf_hFrame o γ hγ).trans (lineOf_gOf o).symm)
  exact h

/-- **The conjugation from the flag stabilizer to the line stabilizer composed with the matrix homomorphism of the line frame.** -/
theorem conjHom_comp (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagLineOrbit o).out = flagLineOf o.out) :
    (conjIota (MulAction.stabilizer Γ6 (flagLineOrbit o).out) (hOf (flagLineOrbit o))).comp
      (conjStabHom γ (flagLineOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_line_of o γ hγ)) =
    conjIota (MulAction.stabilizer Γ6 o.out) (hFrame o γ) := by
  refine MonoidHom.ext fun s => ?_
  show hOf (flagLineOrbit o) * iotaOf (↑(conjStabHom γ (flagLineOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_line_of o γ hγ) s) : Γ6) *
      (hOf (flagLineOrbit o))⁻¹ = hFrame o γ * iotaOf (s : Γ6) * (hFrame o γ)⁻¹
  rw [conjStabHom_apply, iotaOf_mul, iotaOf_mul, iotaOf_inv, hFrame]
  group

end TernaryPeriodPolynomials.Argument.GammaNStokes
