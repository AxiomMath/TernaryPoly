module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTBar
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTAlgPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.GeneralReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG7

@[expose] public section


/-!
# NFT-2 for planes: the bar cochains of a plane datum on the face group and on the flag groups

Formalized by Claude Sonnet 5.5.

For a plane face `i` (face group `gammaNPAt 6 (planeFaceRepr i)`, embedded by `planeEmb`), `zbarP i d` is the face-group cochain `(a, c) ↦ z̄_d(σ a, σ c)` (bar cochain of `d.z` at the plane `planeOf (planeFaceRepr i)`), `gbarP i γ` the same for `γ`.
For a flag `F` over the plane, `flagToP = stabToE`: `Stab F → gammaNPAt 6 (planeFaceRepr i)`; `zbarP_flag`, `gbarP_flag`: the face cochains pulled back along `flagToP` are the bar cochains at `F`.  `gbarP_dd3T`: `dd3T γ̄ = z̄_d ∪ z̄_e`.
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.EquivariantSingularSmall
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section PlaneBar

/-- The stabilizer of a flag over the plane `planeOf h` lies in the stabilizer of the plane. -/
theorem stab_le_planeStab (h : SL(3, ℤ)) (F : Flag) (hF : flagPlaneOf F = planeOf h) :
    MulAction.stabilizer Γ6 F ≤ MulAction.stabilizer Γ6 (planeOf h) := by
  have := stab_flag_le_stab_pt flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant F
  rw [hF] at this
  exact this

theorem planeEmb_stabToE_gen (h : SL(3, ℤ)) (F : Flag) (hF : flagPlaneOf F = planeOf h) (s : ↥(MulAction.stabilizer Γ6 F)) :
    planeEmb h (stabToE h F hF s) = (s : Γ6) := by
  have := (planeStabEquiv h).apply_symm_apply (Subgroup.inclusion (stab_le_planeStab h F hF) s)
  exact congrArg Subtype.val this

/-- The face-group cochain `(a, c) ↦ z̄_d(σ a, σ c)` from a plane datum. -/
def zbarP {W : Rep.{0} ℚ Γ6} (i : PlaneFaces 6) (d : PlaneDatum W) (a c : ↥(gammaNPAt 6 (planeFaceRepr i))) : W :=
  barCochain (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (1 : RationalGL3) (planeOf (planeFaceRepr i)) d.z
    (fun j : Fin 2 => if j = 0 then
      faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
        (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) i a
     else faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
        (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) i c)

/-- The face-group cochain `(a, c, e) ↦ γ̄(σ a, σ c, σ e)`. -/
def gbarP (i : PlaneFaces 6) (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (a c e : ↥(gammaNPAt 6 (planeFaceRepr i))) : ℚ :=
  barCochain (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (1 : RationalGL3) (planeOf (planeFaceRepr i)) γ
    ![faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
        (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) i a,
      faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
        (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) i c,
      faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
        (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) i e]

/-- The bar cochain at the plane, evaluated on `σ ∘ ι_F`, is the bar cochain at the flag plane of `F`. -/
theorem bar_flagP {W₀ : Rep.{0} ℚ Γ6} {k : ℕ} (i : PlaneFaces 6) (F : Flag) (hF : flagPlaneOf F = planeOf (planeFaceRepr i))
    (θ : (prodComplex Γ6 RationalGL3 Plane).X k ⟶ W₀) (x : Fin k → ↥(MulAction.stabilizer Γ6 F)) :
    barCochain (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (1 : RationalGL3) (planeOf (planeFaceRepr i)) θ
      (fun j => faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
        (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) i (stabToE (planeFaceRepr i) F hF (x j))) =
    barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) (flagPlaneOf F) θ x := by
  rw [barCochain_restrict (MulAction.stabilizer Γ6 F) (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i)))
    (stab_le_planeStab _ F hF) (1 : RationalGL3) (flagPlaneOf F) θ x, hF]
  congr 1
  funext j
  apply Subtype.ext
  exact planeEmb_stabToE_gen _ F hF (x j)

theorem zbarP_flag {W : Rep.{0} ℚ Γ6} (i : PlaneFaces 6) (F : Flag) (hF : flagPlaneOf F = planeOf (planeFaceRepr i))
    (d : PlaneDatum W) (s t : ↥(MulAction.stabilizer Γ6 F)) :
    zbarP i d (stabToE (planeFaceRepr i) F hF s) (stabToE (planeFaceRepr i) F hF t) =
      barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) (flagPlaneOf F) d.z (fun j : Fin 2 => if j = 0 then s else t) := by
  rw [← bar_flagP i F hF d.z (fun j : Fin 2 => if j = 0 then s else t)]
  unfold zbarP
  congr 1
  funext j
  by_cases hj : j = 0 <;> simp [hj]

theorem gbarP_flag (i : PlaneFaces 6) (F : Flag) (hF : flagPlaneOf F = planeOf (planeFaceRepr i))
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (a b c : ↥(MulAction.stabilizer Γ6 F)) :
    gbarP i γ (stabToE (planeFaceRepr i) F hF a) (stabToE (planeFaceRepr i) F hF b) (stabToE (planeFaceRepr i) F hF c) =
      barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) (flagPlaneOf F) γ ![a, b, c] := by
  rw [← bar_flagP i F hF γ ![a, b, c]]
  unfold gbarP
  congr 1
  funext j
  fin_cases j <;> rfl

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))

/-- **`dd3T γ̄ = z̄ ∪ z̄'` on the face group**, from the cocycle relation of the primitive. -/
theorem gbarP_dd3T (i : PlaneFaces 6) (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) :
    dd3T (gbarP i γ) = cup22 ((W'.ρ).comp (planeEmb (planeFaceRepr i))) (pairOf π) (zbarP i d) (zbarP i e) := by
  funext a c e' f
  set σ := faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
    (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) i with hσ
  have h1 := bar_dd3T (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (1 : RationalGL3) (planeOf (planeFaceRepr i))
    (fun g => g.2) γ (σ a) (σ c) (σ e') (σ f)
  have h2 := diag22_bar (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (1 : RationalGL3) (planeOf (planeFaceRepr i))
    (fun g => g.2) π d.z e.z ![σ a, σ c, σ e', σ f]
  rw [hγ] at h1
  have e0 : dd3T (gbarP i γ) a c e' f = dd3T (fun a b c => barCochain (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i)))
      (1 : RationalGL3) (planeOf (planeFaceRepr i)) γ ![a, b, c]) (σ a) (σ c) (σ e') (σ f) := by
    simp only [dd3T, gbarP, hσ, map_mul]
  rw [e0, h1]
  refine h2.trans ?_
  simp only [cup22, zbarP, hσ, MonoidHom.comp_apply, Subgroup.coe_subtype, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, map_mul]
  rfl

end PlaneBar

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
