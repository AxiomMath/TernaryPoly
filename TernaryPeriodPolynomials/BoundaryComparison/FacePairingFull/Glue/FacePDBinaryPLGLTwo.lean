module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLElliptic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLContragredient
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelOne

@[expose] public section


/-!
# The Poincare-Lefschetz instance for the binary Levi `GL₂(ℤ)`

Formalized by Claude Sonnet 5.5.

`GL₂(ℤ) = SL₂(ℤ) ⋊ ⟨ε⟩`; the three special elements of `SL₂(ℤ)` are `a = S` (order four, an elliptic point), `g₂ = T⁻¹` (the cusp) and
`g₃ = (S T⁻¹)⁻¹` (order three, an elliptic point).  For a perfect pairing `B` of two finite-dimensional representations of
`GL₂(ℤ)` which is `SL₂(ℤ)`-invariant, `ε`-odd, with `-1` acting trivially on the second (`LevelOne.TwistedPairing`), `setup P` is a
`Setup` (the triviality of `-1` on the first system is used only for the right nondegeneracy, `twistedFlip`): the compactly supported cohomology is the cone of the restriction to the cusp subgroup `⟨T⟩` (the elliptic slots are
divided out), `range_j` is the space of parabolic classes `LevelOne.parabolicH1`, `imagePairing_eq` identifies the Lefschetz pairing of the
images with the library's `LevelOne.parabolicPairing`, and it is nondegenerate on both sides
(`imagePairing_left_nondegenerate`, `imagePairing_right_nondegenerate`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL.GLTwo

open CategoryTheory
open TernaryPeriodPolynomials.BoundaryDuality
open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH1 (Modular)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL

section Model

/-- **The model of `H¹(GL₂(ℤ), M)`** by Mathlib's group cohomology: the one-cocycles and `groupCohomology.H1`. -/
def cohomologyModel (M : Rep.{0, 0, 0} ℂ GL2Z) :
    Model M.ρ (groupCohomology.cocycles₁ M) (groupCohomology.H1 M) where
  c := cocycleInclusion M
  f := projectH1 M
  isCocycle := isCocycle_cocycleInclusion M
  inj := Subtype.val_injective
  surj := fun Z hZ => exists_cocycle_of_isCocycle M Z hZ
  ker := fun y => projectH1_eq_zero_iff M y
  fsurj := fun x => groupCohomology.H1_induction_on x (fun y => ⟨y, rfl⟩)

end Model

section Setup

variable {M M' : Rep.{0, 0, 0} ℂ GL2Z} {B : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ}

/-- The ignored subspace: the fixed vectors of the two elliptic special elements `S` and `(S T⁻¹)⁻¹`. -/
def ellIgnored (M : Rep.{0, 0, 0} ℂ GL2Z) : Submodule ℂ (M × M × M) :=
  (fixedBy (M.ρ.comp toGL) ModularGroup.S).prod ((⊥ : Submodule ℂ M).prod
    (fixedBy (M.ρ.comp toGL) (ModularGroup.S * ModularGroup.T⁻¹)⁻¹))

theorem ignoredFor_ell (hinv : ∀ n v w, B (M.ρ (toGL n) v) (M'.ρ (toGL n) w) = B v w) :
    IgnoredFor toGL M'.ρ B ModularGroup.S ModularGroup.T⁻¹ (ellIgnored M) := by
  refine ignoredFor_prod toGL M'.ρ B ModularGroup.S ModularGroup.T⁻¹ _ ⊥ _ (fun Z' hZ' f hf => ?_)
    (fun Z' _ f hf => slot_bot B _ f hf) (fun Z' hZ' f hf => ?_)
  · exact slot_torsion toGL M.ρ M'.ρ B hinv ModularGroup.S (k := 4) (by norm_num) modularOrderFour hZ' f hf
  · have hcube : (ModularGroup.S * ModularGroup.T⁻¹ : Modular) ^ 3 = 1 := modularCone_cube
    exact slot_torsion toGL M.ρ M'.ρ B hinv (ModularGroup.S * ModularGroup.T⁻¹)⁻¹ (k := 3)
      (by norm_num) (by rw [inv_pow, hcube, inv_one]) hZ' f hf

/-- The twisted pairing for the dual system (needs `-1` to act trivially on the first system). -/
theorem twistedFlip (P : TwistedPairing M M' B) (hcM : ∀ v : M, M.ρ (toGL (ModularGroup.S * ModularGroup.S)) v = v) :
    TwistedPairing M' M B.flip where
  left := fun w h => P.right w (fun v => h v)
  right := fun v h => P.left v (fun w => h w)
  special := fun n w v => P.special n v w
  odd := fun w v => P.odd v w
  central := hcM

/-- **The Poincare-Lefschetz setup for `GL₂(ℤ)`.** -/
def setup (P : TwistedPairing M M' B) :
    Setup toGL M.ρ M'.ρ B ModularGroup.S ModularGroup.T⁻¹ (groupCohomology.cocycles₁ M)
      (groupCohomology.H1 M) (groupCohomology.cocycles₁ M') (groupCohomology.H1 M') where
  hinv := fun n v w => P.special n v w
  M := cohomologyModel M
  M' := cohomologyModel M'
  F := ellIgnored M
  F' := ellIgnored M'
  hF := ignoredFor_ell (fun n v w => P.special n v w)
  hF' := ignoredFor_ell (M := M') (M' := M) (B := B.flip) (fun n w v => P.special n v w)

/-- **The image of `j : H¹_c(GL₂(ℤ), M) → H¹(GL₂(ℤ), M)` is the space of parabolic classes.** -/
theorem range_j (P : TwistedPairing M M' B) :
    LinearMap.range (setup P).j = parabolicH1 M :=
  (setup P).range_j

theorem range_j' (P : TwistedPairing M M' B) :
    LinearMap.range (setup P).j' = parabolicH1 M' :=
  (setup P).range_j'

/-- **The Lefschetz pairing of the images of compactly supported cohomology is the library's parabolic cup pairing.** -/
theorem imagePairing_eq (P : TwistedPairing M M' B) (x : LinearMap.range (setup P).j)
    (y : LinearMap.range (setup P).j') :
    (setup P).imagePairing x y =
      parabolicPairing P ((setup P).toParabolic x) ((setup P).toParabolic' y) :=
  (setup P).imagePairing_eq_parabolicPairing x y

variable [FiniteDimensional ℂ M] [FiniteDimensional ℂ M']

/-- **Parabolic Poincare duality of `GL₂(ℤ)` at the cochain level** (the library's left nondegeneracy). -/
theorem cochainND (P : TwistedPairing M M' B) :
    CochainNondegenerate toGL M.ρ M'.ρ B ModularGroup.S ModularGroup.T⁻¹ :=
  cochainNondegenerate_of_nd indexTwo M.ρ M'.ρ B ModularGroup.S ModularGroup.T⁻¹ P.special (nlevelND P)

/-- **Left nondegeneracy** of the Lefschetz pairing of the images. -/
theorem imagePairing_left_nondegenerate (P : TwistedPairing M M' B) (x : LinearMap.range (setup P).j)
    (h : ∀ y : LinearMap.range (setup P).j', (setup P).imagePairing x y = 0) : x = 0 :=
  (setup P).imagePairing_left_nondegenerate P.left P.right (cochainND P) x h

/-- **Right nondegeneracy** of the Lefschetz pairing of the images. -/
theorem imagePairing_right_nondegenerate (P : TwistedPairing M M' B)
    (hcM : ∀ v : M, M.ρ (toGL (ModularGroup.S * ModularGroup.S)) v = v)
    (y : LinearMap.range (setup P).j')
    (h : ∀ x : LinearMap.range (setup P).j, (setup P).imagePairing x y = 0) : y = 0 :=
  (setup P).imagePairing_right_nondegenerate P.left P.right (cochainND (twistedFlip P hcM)) y h

end Setup

section Orientation

/-- **The orientation character of `GL₂(ℤ) ⊃ SL₂(ℤ)` is the determinant.** -/
theorem orientationSign_eq_det (g : GL2Z) : orientationSign toGL g = ((g.val.det : ℤ) : ℂ) := by
  rcases indexTwo.cover g with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · have h : ((toGL n : GL2Z).val).det = 1 := n.property
    rw [orientationSign_ι, h]
    simp
  · have h : ((toGL n * epsGL : GL2Z).val).det = -1 := by
      rw [Units.val_mul, Matrix.det_mul, det_epsGL]
      have h1 : ((toGL n : GL2Z).val).det = 1 := n.property
      rw [h1]
      norm_num
    rw [orientationSign_ιε indexTwo, h]
    simp

end Orientation

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL.GLTwo
