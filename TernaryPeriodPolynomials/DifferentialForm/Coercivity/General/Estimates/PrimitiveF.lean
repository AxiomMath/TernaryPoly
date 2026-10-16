module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Weyl
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Boxes
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Current

@[expose] public section


/-! # General coercivity, Tier B (phase F): a weak primitive is a smooth primitive

Assembly: if a functional `T` on compactly supported test one-forms is invariant under `Γ` and has
as weak coderivative a closed smooth `Γ`-equivariant two-form `ζ`, then `ζ` has a smooth
`Γ`-equivariant primitive `η` with `dη = ζ`. `T` itself need not be smoothly represented; the proof
represents a corrected invariant functional with the same weak coderivative.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.PolynomialFormWeakSmooth TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.CompactCoordinateIntegration
  TernaryPoly.SmoothLocalDeRham
open Set MeasureTheory Filter Topology
open scoped ContDiff Distributions

variable {n k : ℕ}

theorem unbridge_sub (Ω : TopologicalSpace.Opens Coordinates) (W W' : FormWeak n k Ω) :
    unbridge Ω (W - W') = unbridge Ω W - unbridge Ω W' := by
  apply LinearMap.ext
  intro g
  simp only [unbridge_apply, LinearMap.sub_apply, map_sub, Pi.sub_apply, Finset.sum_sub_distrib]

/-- **Local primitive.**  On a coordinate box, a functional whose weak coderivative is a smooth
closed form is a smooth primitive plus the coderivative of a functional. -/
theorem local_primitive (b : WeakCubeFive ≃L[ℝ] Coordinates) (c : Coordinates)
    (hΩ : (coordinateTestBox b c : Set Coordinates) ⊆ positiveCoordinates)
    (T : Cc n 1 →ₗ[ℝ] ℝ) (ζ : Coordinates → FormValue n 2)
    (hζ : ContDiffOn ℝ ∞ ζ (coordinateTestBox b c))
    (hζc : ∀ x ∈ (coordinateTestBox b c : Set Coordinates), extDeriv ζ x = 0)
    (hweak : ∀ g : CcIn n 2 (coordinateTestBox b c : Set Coordinates),
      T (deltaIn n 1 (coordinateTestBox b c : Set Coordinates) g).1 =
        ∫ x, coordinateDensity x * formPairing n 2 x (ζ x) (g.1.1 x)) :
    ∃ (v : Coordinates → FormValue n 1) (hv : ContDiffOn ℝ ∞ v (coordinateTestBox b c))
      (S : CcIn n 0 (coordinateTestBox b c : Set Coordinates) →ₗ[ℝ] ℝ),
      (∀ x ∈ (coordinateTestBox b c : Set Coordinates), extDeriv v x = ζ x) ∧
      ∀ g : CcIn n 1 (coordinateTestBox b c : Set Coordinates),
        T g.1 = pairIn (coordinateTestBox b c) v hv.continuousOn g +
          S (deltaIn n 0 (coordinateTestBox b c : Set Coordinates) g) := by
  let Ω := coordinateTestBox b c
  let om : Form (F := Coefficients n) (Ω : Set Coordinates) 2 := restrictForm (Ω : Set Coordinates) ζ hζ
  have homx : ∀ x ∈ (Ω : Set Coordinates), (om : Coordinates → FormValue n 2) x = ζ x := fun x hx =>
    restrictForm_apply ζ hζ hx
  have hom : d Ω.isOpen 2 om = 0 := by
    apply Form.ext
    intro x hx
    rw [d_apply Ω.isOpen om hx]
    have he : (om : Coordinates → FormValue n 2) =ᶠ[𝓝 x] ζ := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact homx y hy
    rw [he.extDeriv_eq]
    exact hζc x hx
  let Tb : CcIn n 1 (Ω : Set Coordinates) →ₗ[ℝ] ℝ := T.comp (CcIn n 1 (Ω : Set Coordinates)).subtype
  have hW : formWeakExterior n 1 Ω (bridge Ω hΩ Tb) =
      valuedRegularCurrent volume Ω om.val (Form.smooth om).continuousOn := by
    rw [bridge_exterior]
    refine bridge_regular Ω hΩ _ om.val (Form.smooth om).continuousOn (fun g => ?_)
    refine (hweak g).trans ?_
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ (Ω : Set Coordinates)
    · change coordinateDensity x * formPairing n 2 x (ζ x) (g.1.1 x) =
        coordinateDensity x * formPairing n 2 x (om.val x) (g.1.1 x)
      rw [homx x hx]
    · have h0 : g.1.1 x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (g.2 h))
      change coordinateDensity x * formPairing n 2 x (ζ x) (g.1.1 x) =
        coordinateDensity x * formPairing n 2 x (om.val x) (g.1.1 x)
      rw [h0]
      simp
  obtain ⟨v, hv, T0, hT0⟩ := coordinateTestBox_weak_primitive_mod_smooth n b c (bridge Ω hΩ Tb) om hom hW
  refine ⟨v.val, Form.smooth v, unbridge Ω T0, ?_, ?_⟩
  · intro x hx
    have h1 := congrArg (fun w : Form (F := Coefficients n) (Ω : Set Coordinates) 2 => (w : Coordinates → FormValue n 2) x) hv
    simp only [d_apply Ω.isOpen v hx, homx x hx] at h1
    exact h1
  · intro g
    have h1 := congrArg (unbridge Ω) hT0
    rw [unbridge_exterior Ω hΩ, unbridge_sub, unbridge_bridge, unbridge_regular_eq] at h1
    have h2 := LinearMap.congr_fun h1 g
    simp only [LinearMap.comp_apply, LinearMap.sub_apply] at h2
    exact ((add_comm _ _).trans ((congrArg (· + _) h2).trans (sub_add_cancel _ _))).symm

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
