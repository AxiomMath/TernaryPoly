module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Calculus.Partition
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Measure.Unfolding
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Forms.Basic

@[expose] public section


/-! # General coercivity: integrals over the orbit space in the coordinates

Three tools for the integration-by-parts identities on the orbit space:

* `integral_chart`: integrals over `Space` against `spaceVolume` are coordinate integrals against
  the density `coordinateDensity` over the positive coordinates;
* `Admissible.integral_quotient_eq`: an integral over the orbit space equals the coordinate integral
  of the function multiplied by a cutoff `φ` whose translates sum to one on the support;
* `Admissible.integral_eq_zero_of_tsum_eq_zero`: a function whose translates sum to zero at every
  point has integral zero.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set Filter Topology TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpaceRiemannian
open scoped ContDiff ENNReal NNReal

variable {Γ : Subgroup RealGL}

theorem range_coordinateChart : range (fun S : Space => coordinateChart S) = positiveCoordinates := by
  apply Subset.antisymm
  · rintro _ ⟨S, rfl⟩
    exact extract_mem S
  · intro x hx
    refine ⟨coordinateChart.symm x, ?_⟩
    exact coordinateChart.right_inv (by simpa using hx)

/-- Integrals over `Space` against `spaceVolume` are coordinate integrals against the density. -/
theorem integral_chart (g : Coordinates → ℝ) :
    ∫ S, g (coordinateChart S) ∂spaceVolume =
      ∫ x in positiveCoordinates, coordinateDensity x * g x := by
  have hemb := measurableEmbedding_coordinateChart
  rw [← hemb.integral_map g]
  unfold spaceVolume
  rw [hemb.map_comap, range_coordinateChart]
  unfold coordinateVolume
  rw [restrict_withDensity isOpen_positiveCoordinates.measurableSet]
  have hmeas : AEMeasurable (fun x => (coordinateDensity x).toNNReal)
      (volume.restrict positiveCoordinates) :=
    (continuous_real_toNNReal.comp_continuousOn contDiffOn_coordinateDensity.continuousOn).aemeasurable
      isOpen_positiveCoordinates.measurableSet
  have hwd : (fun x => ENNReal.ofReal (coordinateDensity x)) =
      fun x => (((coordinateDensity x).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hwd, integral_withDensity_eq_integral_smul₀ hmeas]
  apply integral_congr_ae
  filter_upwards with x
  have hρ : 0 ≤ coordinateDensity x := Real.sqrt_nonneg _
  rw [NNReal.smul_def, Real.coe_toNNReal _ hρ, smul_eq_mul]

theorem integrableOn_positive {g : Coordinates → ℝ} (hg : ContinuousOn g positiveCoordinates)
    {K : Set Coordinates} (hK : IsCompact K) (hKp : K ⊆ positiveCoordinates)
    (hz : ∀ x, x ∉ K → g x = 0) : IntegrableOn g positiveCoordinates :=
  ((hg.mono hKp).integrableOn_compact hK).of_forall_sdiff_eq_zero
    isOpen_positiveCoordinates.measurableSet (fun x hx => hz x hx.2)

/-- The preimage under the chart of a compact subset of the positive coordinates is compact. -/
theorem isCompact_chart_preimage {K : Set Coordinates} (hK : IsCompact K)
    (hKp : K ⊆ positiveCoordinates) : IsCompact ((fun S : Space => coordinateChart S) ⁻¹' K) := by
  have himg : IsCompact (coordinateChart.symm '' K) :=
    hK.image_of_continuousOn (coordinateChart.continuousOn_symm.mono (fun x hx => by
      simpa using hKp hx))
  convert himg using 1
  ext S
  constructor
  · intro hS
    exact ⟨coordinateChart S, hS, coordinateChart.left_inv (by simp)⟩
  · rintro ⟨x, hx, rfl⟩
    show coordinateChart (coordinateChart.symm x) ∈ K
    rwa [coordinateChart.right_inv (by simpa using hKp hx)]

/-- A function of the chart, continuous on the positive coordinates and vanishing off a compact
subset of them, is integrable on `Space`. -/
theorem integrable_chart {g : Coordinates → ℝ} (hg : ContinuousOn g positiveCoordinates)
    {K : Set Coordinates} (hK : IsCompact K) (hKp : K ⊆ positiveCoordinates)
    (hz : ∀ x, x ∉ K → g x = 0) : Integrable (fun S : Space => g (coordinateChart S)) spaceVolume := by
  have hcont : Continuous (fun S : Space => g (coordinateChart S)) :=
    hg.comp_continuous continuous_chart_coordinates (fun S => extract_mem S)
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_chart_preimage hK hKp)
  intro S hS
  exact hz _ hS

/-- Unfolding an integral over the orbit space into a cutoff-weighted coordinate integral. -/
theorem Admissible.integral_quotient_eq (h : Admissible Γ) {Q : Set (OrbitSpace Γ)}
    {φ : Coordinates → ℝ} (hφ : CutoffData Γ Q φ) {F : OrbitSpace Γ → ℝ} (hF : Continuous F)
    (hFQ : Function.support F ⊆ Q) :
    ∫ q, F q ∂quotientVolume Γ =
      ∫ x in positiveCoordinates, coordinateDensity x * (φ x * F (coordProj Γ x)) := by
  have hψ : Measurable (fun S : Space => φ (coordinateChart S)) :=
    (hφ.smooth.continuous.comp continuous_chart_coordinates).measurable
  have hpart : ∀ S : Space, F (proj Γ S) ≠ 0 → ∑' γ : Γ, φ (coordinateChart (γ • S)) = 1 :=
    fun S hS => hφ.tsum_eq_one (hFQ hS)
  have hg : ContinuousOn (fun x => φ x * F (coordProj Γ x)) positiveCoordinates :=
    hφ.smooth.continuous.continuousOn.mul (hF.comp_continuousOn continuousOn_coordProj)
  have hint : Integrable (fun S : Space => φ (coordinateChart S) * F (proj Γ S)) spaceVolume := by
    have := integrable_chart hg hφ.compactSupport hφ.tsupport_subset (fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx])
    refine this.congr (Eventually.of_forall fun S => ?_)
    simp only [coordProj_chart]
  rw [h.integral_unfold hF.measurable hψ hpart hint, ← integral_chart (fun x => φ x * F (coordProj Γ x))]
  simp only [coordProj_chart]

/-- A function on `Space` whose translates sum to zero at every point has integral zero. -/
theorem Admissible.integral_eq_zero_of_tsum_eq_zero (h : Admissible Γ) {E : Space → ℝ}
    (hEm : Measurable E) (hE : Integrable E spaceVolume)
    (hsum : ∀ S : Space, ∑' γ : Γ, E (γ • S) = 0) : ∫ S, E S ∂spaceVolume = 0 := by
  have : Countable Γ := h.countable
  obtain ⟨t, htm, ht⟩ := h.exists_isFundamentalDomain
  have h2 : ∫ S, E S ∂spaceVolume = ∑' g : Γ, ∫ x in t, E (g • x) ∂spaceVolume :=
    ht.integral_eq_tsum'' E hE
  have hsm : ∀ g : Γ, Measurable (fun x : Space => E (g • x)) := fun g =>
    hEm.comp (measurable_const_smul g)
  have h3 : ∑' g : Γ, ∫ x in t, E (g • x) ∂spaceVolume =
      ∫ x in t, ∑' g : Γ, E (g • x) ∂spaceVolume := by
    symm
    apply integral_tsum (fun g => (hsm g).aestronglyMeasurable)
    have := ht.lintegral_eq_tsum'' (fun x => ‖E x‖ₑ)
    rw [← this]
    exact hE.hasFiniteIntegral.ne
  rw [h2, h3]
  simp [hsum]

/-! ### Local partition of unity at a point -/

/-- Near a point whose projection lies in `Q`, finitely many translates of the cutoff are nonzero
and they sum to one. -/
theorem CutoffData.localPartition {Q : Set (OrbitSpace Γ)} {φ : Coordinates → ℝ}
    (hφ : CutoffData Γ Q φ) {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (hxQ : coordProj Γ x ∈ Q) :
    ∃ N ∈ 𝓝 x, ∃ A : Finset Γ, N ⊆ positiveCoordinates ∧
      (∀ γ : Γ, γ ∉ A → ∀ y ∈ N, φ (coordinateAction (γ : RealGL) y) = 0) ∧
      ∀ y ∈ N, ∑ γ ∈ A, φ (coordinateAction (γ : RealGL) y) = 1 := by
  obtain ⟨N₁, hN₁, hN₁p, hfin⟩ := hφ.locallyFinite x hx
  obtain ⟨W, hWo, hWp, hW, hsum⟩ := hφ.partition
  have hxW : x ∈ W := hW x hx hxQ
  refine ⟨N₁ ∩ W, Filter.inter_mem hN₁ (hWo.mem_nhds hxW), hfin.toFinset,
    inter_subset_left.trans hN₁p, ?_, ?_⟩
  · intro γ hγ y hy
    by_contra hne
    exact hγ (hfin.mem_toFinset.mpr ⟨y, hy.1, hne⟩)
  · intro y hy
    rw [← hsum y hy.2]
    symm
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    exact hfin.mem_toFinset.mpr ⟨y, hy.1, hγ⟩

/-- The differentials of the translates of the cutoff sum to zero at a point over the support. -/
theorem CutoffData.fderiv_partition {Q : Set (OrbitSpace Γ)} {φ : Coordinates → ℝ}
    (hφ : CutoffData Γ Q φ) {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (hxQ : coordProj Γ x ∈ Q) :
    ∃ A : Finset Γ, (∀ γ : Γ, γ ∉ A →
        fderiv ℝ (fun y => φ (coordinateAction (γ : RealGL) y)) x = 0) ∧
      ∑ γ ∈ A, fderiv ℝ (fun y => φ (coordinateAction (γ : RealGL) y)) x = 0 := by
  obtain ⟨N, hN, A, hNp, hzero, hsum⟩ := hφ.localPartition hx hxQ
  refine ⟨A, ?_, ?_⟩
  · intro γ hγ
    have he : (fun y => φ (coordinateAction (γ : RealGL) y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hN] with y hy using hzero γ hγ y hy
    rw [he.fderiv_eq]
    exact fderiv_const_apply 0
  · have hd : ∀ γ ∈ A, DifferentiableAt ℝ (fun y => φ (coordinateAction (γ : RealGL) y)) x := by
      intro γ _
      have h1 : DifferentiableAt ℝ (coordinateAction (γ : RealGL)) x :=
        (((contDiffOn_coordinateAction (γ : RealGL)) x hx).contDiffAt
          (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
      exact (hφ.smooth.differentiable (by simp) _).comp x h1
    rw [← fderiv_fun_sum hd]
    have he : (fun y => ∑ γ ∈ A, φ (coordinateAction (γ : RealGL) y)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hN] with y hy using hsum y hy
    rw [he.fderiv_eq]
    exact fderiv_const_apply 1

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
