module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Unfold
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Hilbert
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Calculus.IntegrationByParts

@[expose] public section


/-! # General coercivity, Tier B: multiplication by invariant functions

A smooth `Γ`-invariant function `c` acts on `CForm Γ n m` by pointwise multiplication; for
`0 ≤ c ≤ 1` this is a contraction for the `L²` norm and it is symmetric for the `L²` pairing.
The `Γ`-invariant functions arising as cutoffs have gradient controlled by the invariant metric, so
that the commutators `d (c ·) - c d` are bounded operators.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
  TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormConnection
open MeasureTheory Set Filter Topology
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n m : ℕ}

/-- A function that is smooth on the positive coordinates, invariant under `Γ` there, and takes
values in `[0, 1]`. -/
structure InvMult (Γ : Subgroup RealGL) where
  toFun : Coordinates → ℝ
  smooth : ContDiffOn ℝ ∞ toFun positiveCoordinates
  inv : ∀ γ : Γ, ∀ x ∈ positiveCoordinates, toFun (coordinateAction (γ : RealGL) x) = toFun x
  nonneg : ∀ x, 0 ≤ toFun x
  le_one : ∀ x, toFun x ≤ 1

namespace InvMult

variable (c : InvMult Γ)

theorem equivariantAt_smul {w : Coordinates → FormValue n m} (γ : Γ) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) (hw : EquivariantAt n m (γ : RealGL) w x) :
    EquivariantAt n m (γ : RealGL) (fun y => c.toFun y • w y) x := by
  unfold EquivariantAt at *
  show (c.toFun (coordinateAction (γ : RealGL) x) • w (coordinateAction (γ : RealGL) x)).compContinuousLinearMap
      (fderiv ℝ (coordinateAction (γ : RealGL)) x) = coefficientFormMap (realCoefficientMap n (γ : RealGL)) m
      (c.toFun x • w x)
  apply ContinuousAlternatingMap.ext
  intro v
  have h1 := congrArg (fun F : FormValue n m => F v) hw
  change w (coordinateAction (γ : RealGL) x) (fun i => fderiv ℝ (coordinateAction (γ : RealGL)) x (v i)) =
    realCoefficientMap n (γ : RealGL) (w x v) at h1
  show c.toFun (coordinateAction (γ : RealGL) x) • w (coordinateAction (γ : RealGL) x)
      (fun i => fderiv ℝ (coordinateAction (γ : RealGL)) x (v i)) =
    realCoefficientMap n (γ : RealGL) (c.toFun x • w x v)
  rw [c.inv γ x hx, h1, map_smul]

/-- Multiplication by `c` as a linear map on compactly supported equivariant forms. -/
def mulForm (a : CForm Γ n m) : CForm Γ n m :=
  ⟨restrictForm positiveCoordinates (fun y => c.toFun y • CForm.fn a y)
      (c.smooth.smul (CForm.smooth a)), by
    have hres : ∀ y ∈ positiveCoordinates,
        (restrictForm positiveCoordinates (fun y => c.toFun y • CForm.fn a y)
          (c.smooth.smul (CForm.smooth a)) : Coordinates → FormValue n m) y =
          c.toFun y • CForm.fn a y := fun y hy => restrictForm_apply _ _ hy
    refine ⟨?_, ?_⟩
    · rw [isEquivariant_iff]
      intro γ x hx
      have h1 := c.equivariantAt_smul γ hx (CForm.equivariantAt a γ hx)
      unfold EquivariantAt at h1 ⊢
      rw [hres _ (coordinateAction_mem _ x hx), hres x hx]
      exact h1
    · refine (CForm.compact a).of_isClosed_subset isClosed_closure ?_
      apply closure_mono
      apply image_mono
      intro x hx
      rw [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      by_cases hxp : x ∈ positiveCoordinates
      · rw [hres x hxp, h0]
        exact smul_zero (A := FormValue n m) (c.toFun x)
      · exact Form.outside _ hxp⟩

theorem fn_mulForm (a : CForm Γ n m) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    CForm.fn (c.mulForm a) x = c.toFun x • CForm.fn a x :=
  restrictForm_apply _ (c.smooth.smul (CForm.smooth a)) hx

/-- Multiplication by `c` as a linear map. -/
def mulMap : CForm Γ n m →ₗ[ℝ] CForm Γ n m where
  toFun := c.mulForm
  map_add' a b := by
    apply CForm.ext
    intro x hx
    have e1 : CForm.fn (c.mulForm (a + b)) x = c.toFun x • (CForm.fn a x + CForm.fn b x) :=
      c.fn_mulForm (a + b) hx
    have e2 : CForm.fn (c.mulForm a + c.mulForm b) x =
        c.toFun x • CForm.fn a x + c.toFun x • CForm.fn b x :=
      congrArg₂ (· + ·) (c.fn_mulForm a hx) (c.fn_mulForm b hx)
    exact e1.trans ((smul_add (A := FormValue n m) (c.toFun x) (CForm.fn a x) (CForm.fn b x)).trans
      e2.symm)
  map_smul' r a := by
    apply CForm.ext
    intro x hx
    have e1 : CForm.fn (c.mulForm (r • a)) x = c.toFun x • (r • CForm.fn a x) :=
      c.fn_mulForm (r • a) hx
    have e2 : CForm.fn (r • c.mulForm a) x = r • (c.toFun x • CForm.fn a x) :=
      congrArg (fun z : FormValue n m => r • z) (c.fn_mulForm a hx)
    exact e1.trans ((smul_comm (c.toFun x) r (CForm.fn a x)).trans e2.symm)

theorem fn_mulMap (a : CForm Γ n m) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    CForm.fn (c.mulMap a) x = c.toFun x • CForm.fn a x :=
  c.fn_mulForm a hx

theorem pairingFn_mulMap_left (a b : CForm Γ n m) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    formPairing n m x (CForm.fn (c.mulMap a) x) (CForm.fn b x) =
      c.toFun x * formPairing n m x (CForm.fn a x) (CForm.fn b x) := by
  rw [c.fn_mulMap a hx, formPairing_smul_left]

/-- Multiplication by an invariant function is symmetric for the `L²` pairing. -/
theorem l2Form_mulMap (a b : CForm Γ n m) :
    l2Form Γ n m (c.mulMap a) b = l2Form Γ n m a (c.mulMap b) := by
  apply l2Form_congr
  intro x hx
  rw [c.pairingFn_mulMap_left a b hx, c.fn_mulMap b hx, formPairing_smul_right]

theorem pairingFn_mulMap_self (a : CForm Γ n m) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    pairingFn (c.mulMap a) (c.mulMap a) x = c.toFun x ^ 2 * pairingFn a a x := by
  unfold pairingFn
  rw [c.fn_mulMap a hx, formPairing_smul_left, formPairing_smul_right]
  ring

theorem scalarPairing_mulMap_self_le [hΓ : Fact (Admissible Γ)] (a : CForm Γ n m)
    (q : OrbitSpace Γ) :
    scalarPairing (c.mulMap a) (c.mulMap a) q ≤ scalarPairing a a q := by
  obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
  have hx : coordinateChart S ∈ positiveCoordinates := extract_mem S
  have e1 : scalarPairing (c.mulMap a) (c.mulMap a) (proj Γ S) =
      c.toFun (coordinateChart S) ^ 2 * pairingFn a a (coordinateChart S) :=
    (scalarPairing_proj hΓ.out _ _ S).trans (c.pairingFn_mulMap_self a hx)
  have e2 : scalarPairing a a (proj Γ S) = pairingFn a a (coordinateChart S) :=
    scalarPairing_proj hΓ.out a a S
  have h0 : 0 ≤ pairingFn a a (coordinateChart S) := formPairing_nonneg n m _ hx _
  have hc0 := c.nonneg (coordinateChart S)
  have hc1 := c.le_one (coordinateChart S)
  rw [e1, e2]
  nlinarith [mul_le_mul hc1 hc1 hc0 zero_le_one]

/-- The `L²` norm does not increase under multiplication by `c` with values in `[0, 1]`. -/
theorem normSq_mulMap_le [hΓ : Fact (Admissible Γ)] (a : CForm Γ n m) :
    normSq (c.mulMap a) ≤ normSq a := by
  rw [normSq_eq, normSq_eq]
  exact integral_mono (integrable_scalarPairing _ _) (integrable_scalarPairing _ _)
    (c.scalarPairing_mulMap_self_le a)

end InvMult

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
