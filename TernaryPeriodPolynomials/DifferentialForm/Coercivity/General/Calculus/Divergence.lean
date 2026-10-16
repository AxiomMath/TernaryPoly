module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Calculus.ChartIntegral
public import TernaryPeriodPolynomials.Analysis.Compact.VectorDivergence
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence.Product
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence.Support

@[expose] public section


/-! # General coercivity: the divergence theorem on the orbit space (G2)

If `V` is a smooth `Γ`-covariant vector field on the positive coordinates, with compact support in
the orbit space, and `D` is a continuous function on `OrbitSpace Γ` whose lift is the weighted
divergence of `V`, then `∫ D = 0` against the Riemannian volume of the orbit space.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set Filter Topology TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.PolynomialFormConnection
  TernaryPoly.PolynomialFormCoordinates TernaryPoly.CompactCoordinateIntegration
open scoped ContDiff

variable {Γ : Subgroup RealGL}

/-- The weighted divergence of a smooth covariant vector field of compact support in the orbit
space integrates to zero against the orbit-space volume. -/
theorem Admissible.integral_eq_zero_of_divergence (h : Admissible Γ) {V : Coordinates → Coordinates}
    (hV : ContDiffOn ℝ ∞ V positiveCoordinates)
    (hcov : ∀ γ : Γ, IsActionVectorField (γ : RealGL) V)
    (hQ : IsCompact (projSupport Γ V)) {D : OrbitSpace Γ → ℝ} (hD : Continuous D)
    (hDV : ∀ x ∈ positiveCoordinates, D (coordProj Γ x) = weightedDivergence V x) :
    ∫ q, D q ∂quotientVolume Γ = 0 := by
  obtain ⟨φ, hφ⟩ := h.exists_cutoff hQ
  have hDQ : Function.support D ⊆ projSupport Γ V := by
    intro q hq
    obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
    by_contra hnot
    have hx : coordinateChart S ∈ positiveCoordinates := extract_mem S
    have hn : coordProj Γ (coordinateChart S) ∉ projSupport Γ V := by rwa [coordProj_chart]
    apply hq
    rw [← coordProj_chart S, hDV _ hx]
    exact weightedDivergence_eq_zero_of_eventuallyEq_zero V _
      (eventuallyEq_zero_of_notMem_projSupport hx hn)
  have h1 := h.integral_quotient_eq hφ hD hDQ
  have hφd : ∀ x, DifferentiableAt ℝ φ x := fun x => hφ.smooth.differentiable (by simp) x
  set B : Coordinates → ℝ := fun x => fderiv ℝ φ x (V x) with hB
  have hBc : ContinuousOn B positiveCoordinates :=
    (hφ.smooth.continuous_fderiv (by simp)).continuousOn.clm_apply hV.continuousOn
  have hBz : ∀ x, x ∉ tsupport φ → B x = 0 := by
    intro x hx
    simp [hB, fderiv_of_notMem_tsupport ℝ hx]
  have hf1c : ContinuousOn (fun x => coordinateDensity x * (φ x * D (coordProj Γ x)))
      positiveCoordinates :=
    contDiffOn_coordinateDensity.continuousOn.mul (hφ.smooth.continuous.continuousOn.mul
      (hD.comp_continuousOn continuousOn_coordProj))
  have hf1z : ∀ x, x ∉ tsupport φ → coordinateDensity x * (φ x * D (coordProj Γ x)) = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hf2c : ContinuousOn (fun x => coordinateDensity x * B x) positiveCoordinates :=
    contDiffOn_coordinateDensity.continuousOn.mul hBc
  have hf2z : ∀ x, x ∉ tsupport φ → coordinateDensity x * B x = 0 := by
    intro x hx
    simp [hBz x hx]
  have hi1 := integrableOn_positive hf1c hφ.compactSupport hφ.tsupport_subset hf1z
  have hi2 := integrableOn_positive hf2c hφ.compactSupport hφ.tsupport_subset hf2z
  -- the compactly supported field `φ V`
  have hUon : ContDiffOn ℝ ∞ (fun x => φ x • V x) positiveCoordinates :=
    hφ.smooth.contDiffOn.smul hV
  have hUs : tsupport (fun x => φ x • V x) ⊆ positiveCoordinates :=
    (tsupport_smul_subset_left φ V).trans hφ.tsupport_subset
  have hU : ContDiff ℝ ∞ (fun x => φ x • V x) :=
    contDiff_of_tsupport_subset isOpen_positiveCoordinates hUon hUs
  have hUc : HasCompactSupport (fun x => φ x • V x) :=
    hφ.compactSupport.mono' ((Function.support_smul_subset_left φ V).trans (subset_tsupport φ))
  have h0 := integral_compact_weightedDivergence (fun x => φ x • V x) hU hUc hUs
  have hout : ∀ x ∉ positiveCoordinates,
      coordinateDensity x * weightedDivergence (fun y => φ y • V y) x = 0 := by
    intro x hx
    rw [weightedDivergence_zero_of_notMem_tsupport _ x (fun hh => hx (hUs hh)), mul_zero]
  have h0' : ∫ x in positiveCoordinates, coordinateDensity x *
      weightedDivergence (fun y => φ y • V y) x = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    exact h0
  have hsplit : ∫ x in positiveCoordinates, coordinateDensity x *
      weightedDivergence (fun y => φ y • V y) x =
      (∫ x in positiveCoordinates, coordinateDensity x * (φ x * D (coordProj Γ x))) +
        ∫ x in positiveCoordinates, coordinateDensity x * B x := by
    rw [← integral_add hi1 hi2]
    apply setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet
    intro x hx
    have hVd : DifferentiableAt ℝ V x :=
      ((hV x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
    dsimp only
    rw [weightedDivergence_smul φ V x hx (hφd x) hVd, ← hDV x hx, mul_add]
  -- the error term vanishes by the sum rule for the translates of the cutoff
  have hE : ∫ S, B (coordinateChart S) ∂spaceVolume = 0 := by
    apply h.integral_eq_zero_of_tsum_eq_zero
    · exact (hBc.comp_continuous continuous_chart_coordinates (fun S => extract_mem S)).measurable
    · exact integrable_chart hBc hφ.compactSupport hφ.tsupport_subset hBz
    · intro S
      have hx : coordinateChart S ∈ positiveCoordinates := extract_mem S
      set x := coordinateChart S with hxdef
      have hterm : ∀ γ : Γ, B (coordinateChart (γ • S)) =
          fderiv ℝ (fun y => φ (coordinateAction (γ : RealGL) y)) x (V x) := by
        intro γ
        have hc : coordinateChart (γ • S) = coordinateAction (γ : RealGL) x :=
          coordinateChart_act (γ : RealGL) S
        have hcA : DifferentiableAt ℝ (coordinateAction (γ : RealGL)) x :=
          ((contDiffOn_coordinateAction (γ : RealGL) x hx).contDiffAt
            (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
        have hch : fderiv ℝ (fun y => φ (coordinateAction (γ : RealGL) y)) x =
            (fderiv ℝ φ (coordinateAction (γ : RealGL) x)).comp
              (fderiv ℝ (coordinateAction (γ : RealGL)) x) :=
          fderiv_comp x (hφd _) hcA
        rw [hc, hch]
        simp only [hB, ContinuousLinearMap.comp_apply]
        rw [hcov γ x hx]
      simp only [hterm]
      by_cases hVx : V x = 0
      · simp [hVx]
      · have hxQ : coordProj Γ x ∈ projSupport Γ V := subset_closure ⟨x, hVx, rfl⟩
        obtain ⟨A, hA0, hAs⟩ := hφ.fderiv_partition hx hxQ
        rw [tsum_eq_sum (s := A) (fun γ hγ => by simp [hA0 γ hγ])]
        have := congrArg (fun L : Coordinates →L[ℝ] ℝ => L (V x)) hAs
        simpa [_root_.sum_apply] using this
  have hI2 : ∫ x in positiveCoordinates, coordinateDensity x * B x = 0 := by
    rw [← integral_chart B]
    exact hE
  rw [h1]
  linarith [h0', hsplit, hI2]

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
