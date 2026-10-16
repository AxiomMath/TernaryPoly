module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel

@[expose] public section


/-!
# Step 3: the Hochschild-Serre edge maps of the mixed classes of `Γ(6)`, and the statement (a′)

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4

section Edge

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

/-- The coefficient module restricted to the line group of the face `i` of `Γ(6)`. -/
abbrev repAt (i : LineFaces 6) : Rep ℂ ↥(gammaNQAt 6 i.rep) := Rep.res (lineIncl i) (Rep.of ρ)

/-- The coefficient module restricted to the plane group of the face `i` of `Γ(6)`. -/
abbrev planeRepAt (i : PlaneFaces 6) : Rep ℂ ↥(gammaNPAt 6 (planeFaceRepr i)) := Rep.res (planeIncl i) (Rep.of ρ)

variable (i : LineFaces 6)

/-- Step 3 (lines): the Hochschild-Serre edge of a mixed class of the line face `i` of `Γ(6)`, for a general coefficient module. -/
abbrev lineMixedToCusp : lineMixedSub ρ i →ₗ[ℂ] cuspidalSubspace (CongruenceSubgroup.Gamma 6)
    (splitRadicalH1Representation (lineFaceSplitting 6 i.rep) (repAt ρ i)) := mixedEdgeAt 6 i.rep (repAt ρ i)

/-- Step 3 (lines, dual coefficients): the same for `ρ.dual`; its codomain is `H¹` of the literal contragredient (`dualRepG`) of the coefficient module. -/
abbrev lineMixedToCuspDual : lineMixedSub ρ.dual i →ₗ[ℂ] cuspidalSubspace (CongruenceSubgroup.Gamma 6)
    (splitRadicalH1Representation (lineFaceSplitting 6 i.rep) (dualRepG (repAt ρ i))) := mixedEdgeAt 6 i.rep (dualRepG (repAt ρ i))

variable (i' : PlaneFaces 6)

/-- Step 3 (planes). -/
abbrev planeMixedToCusp : planeMixedSub ρ i' →ₗ[ℂ] cuspidalSubspace (CongruenceSubgroup.Gamma 6)
    (splitRadicalH1Representation (faceSplitting 6 (planeFaceRepr i')) (planeRepAt ρ i')) := planeMixedEdgeAt 6 (planeFaceRepr i') (planeRepAt ρ i')

/-- Step 3 (planes, dual coefficients). -/
abbrev planeMixedToCuspDual : planeMixedSub ρ.dual i' →ₗ[ℂ] cuspidalSubspace (CongruenceSubgroup.Gamma 6)
    (splitRadicalH1Representation (faceSplitting 6 (planeFaceRepr i')) (dualRepG (planeRepAt ρ i'))) :=
  planeMixedEdgeAt 6 (planeFaceRepr i') (dualRepG (planeRepAt ρ i'))

variable [FiniteDimensional ℂ V]

/-- **The level-6 canonical pairing of the line face `i` for the coefficient module `ρ`** (S2's `facePairingCan`) on the edges of mixed classes. -/
def can6 (i : LineFaces 6) (x : lineMixedSub ρ i) (y : lineMixedSub ρ.dual i) : ℂ :=
  facePairingCan (by norm_num : 3 ≤ 6) (lineFaceSplitting 6 i.rep) (lineFaceRadicalInput_det 6 i.rep) (repAt ρ i)
    (lineMixedToCusp ρ i x) (lineMixedToCuspDual ρ i y)

/-- **The level-6 canonical pairing of the plane face `i`.** -/
def can6P (i : PlaneFaces 6) (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i) : ℂ :=
  facePairingCan (by norm_num : 3 ≤ 6) (faceSplitting 6 (planeFaceRepr i)) (planeFaceRadicalInput_det 6 (planeFaceRepr i))
    (planeRepAt ρ i) (planeMixedToCusp ρ i x) (planeMixedToCuspDual ρ i y)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem can6_eq_canAt (i : LineFaces 6) (x : lineMixedSub ρ i) (y : lineMixedSub ρ.dual i) :
    can6 ρ i x y = canAt 6 i.rep (by norm_num) (repAt ρ i) x y := rfl

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem can6P_eq_canAtP (i : PlaneFaces 6) (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i) :
    can6P ρ i x y = canAtP 6 (planeFaceRepr i) (by norm_num) (planeRepAt ρ i) x y := rfl

end Edge

/-- **The factorisation of the `Γ(6)` cone pairings through S2's canonical pairing, for general coefficients.**
There are nonzero constants `c i` (line faces) and `d i` (plane faces) of `Γ(6)`, independent of the coefficient module, such that for every finite-dimensional coefficient module `ρ` of `Γ(6)`
and all mixed classes `x`, `y` (for `ρ` and `ρ.dual`), `lineFacePairM ρ i x y = c i · can6 ρ i x y` and `planeFacePairM ρ i x y = d i · can6P ρ i x y`, where `can6`, `can6P` are S2's `facePairingCan` on the
Hochschild-Serre edges. -/
def FaceFactorisation6 : Prop :=
  ∃ (c : LineFaces 6 → ℂ) (d : PlaneFaces 6 → ℂ), (∀ i, c i ≠ 0) ∧ (∀ i, d i ≠ 0) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (gammaN 6) V),
      (∀ (i : LineFaces 6) (x : lineMixedSub ρ i) (y : lineMixedSub ρ.dual i),
        lineFacePairM ρ i x.1 y.1 = c i * can6 ρ i x y) ∧
      (∀ (i : PlaneFaces 6) (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i),
        planeFacePairM ρ i x.1 y.1 = d i * can6P ρ i x y)

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
