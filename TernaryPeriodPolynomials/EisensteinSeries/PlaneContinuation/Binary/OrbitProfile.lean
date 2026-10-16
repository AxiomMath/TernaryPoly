module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.OrbitChart

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitChart
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitProfile

def coefficient (degree : ℕ) (parameter : ℂ) (frame : Rectangular ℝ) : ℂ :=
  Complex.exp (((degree : ℂ) / 2 + 3 + parameter) * (height frame : ℂ))

theorem coefficient_analyticAt (degree : ℕ) (parameter : ℂ) (frame : Rectangular ℝ)
    (inside : frame ∈ domain) : AnalyticAt ℝ (coefficient degree parameter) frame :=
  (Complex.contDiff_exp.contDiffAt.comp frame (contDiffAt_const.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp frame (height_contDiffAt frame inside)))).analyticAt

def profile {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (parameter : ℂ) (frame : Rectangular ℝ) : data.cusp.H :=
  coefficient degree parameter frame • realOrbit data.cusp vector.val (block frame)⁻¹

theorem parameter_shift {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (parameter reference : ℂ) (frame : Rectangular ℝ) :
    profile data vector parameter frame =
      Complex.exp ((parameter - reference) * (height frame : ℂ)) • profile data vector reference frame := by
  unfold profile coefficient
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  ring

theorem inner_real {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (binary : BinaryRealGL) (positive : 0 < binary.val.det) :
    GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det (atInfinity binary)) =
      Complex.exp (((degree : ℂ) / 2 + 3 + parameter) * (Real.log binary.val.det : ℂ)) := by
  change (data.chi.toMonoidHom (GeneralLinearGroup.det (atInfinity binary)))⁻¹ * normPower _ _ = _
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.det_atInfinity, data.chi.positiveReal _ positive, inv_one, one_mul,
    normPower, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_real]
  rw [show (GeneralLinearGroup.det binary).val = binary.val.det from rfl, abs_of_pos positive]
  congr 2
  simp only [binaryInductionExponent, inductionExponent]
  ring

theorem coefficient_inner {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (binary : BinaryRealGL) (positive : 0 < binary.val.det) :
    coefficient degree parameter (columns (1 : PlaneMatrix) * binary.val) *
      GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det (atInfinity binary)) = 1 := by
  rw [inner_real data parameter binary positive]
  unfold coefficient height
  rw [block_mul, block_standard, one_mul, Complex.ofReal_neg, mul_neg, Complex.exp_neg]
  exact inv_mul_cancel₀ (Complex.exp_ne_zero _)

theorem exists_local_lift {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence) (parameter : ℂ)
    (frame : Rectangular ℝ) (inside : frame ∈ domain) :
    ∃ neighborhood : Set (Rectangular ℝ), IsOpen neighborhood ∧ frame ∈ neighborhood ∧
      neighborhood ⊆ domain ∧ ∃ radius : ℝ≥0, ∃ positive : 0 < radius,
      ∃ lift : Rectangular ℝ → analyticStage data.cusp finiteCongruence radius positive,
        AnalyticOnNhd ℝ lift neighborhood ∧ ∀ value ∈ neighborhood,
          stageHilbertMap data.cusp finiteCongruence radius positive (lift value) = profile data vector parameter value := by
  obtain ⟨shiftRadius, shiftPositive, radius, positive, matrixLift, analyticLift, liftValue⟩ :=
    BinaryOrbitStage.exists_lift data.cusp vector fixed (inverseMatrix frame) (inverseMatrix_block_nonzero frame inside)
  let offset : Rectangular ℝ → PlaneMatrix := fun value => inverseMatrix value - inverseMatrix frame
  let neighborhood := domain ∩ offset ⁻¹' Metric.eball 0 (shiftRadius : ENNReal)
  have offsetSmooth (value : Rectangular ℝ) (membership : value ∈ domain) : ContDiffAt ℝ ⊤ offset value :=
    (inverseMatrix_contDiffAt value membership).sub contDiffAt_const
  have openNeighborhood : IsOpen neighborhood := by
    apply isOpen_iff_mem_nhds.mpr
    intro value membership
    exact Filter.inter_mem (domain_isOpen.mem_nhds membership.1)
      ((offsetSmooth value membership.1).continuousAt.preimage_mem_nhds (Metric.isOpen_eball.mem_nhds membership.2))
  have centerMembership : frame ∈ neighborhood := by
    refine ⟨inside, ?_⟩
    change offset frame ∈ Metric.eball 0 (shiftRadius : ENNReal)
    rw [show offset frame = 0 from sub_self _, Metric.mem_eball, edist_self]
    exact_mod_cast shiftPositive
  let lift : Rectangular ℝ → analyticStage data.cusp finiteCongruence radius positive :=
    fun value => coefficient degree parameter value • matrixLift (offset value)
  refine ⟨neighborhood, openNeighborhood, centerMembership, (fun _ membership => membership.1), radius, positive, lift, ?_, ?_⟩
  · intro value membership
    exact (coefficient_analyticAt degree parameter value membership.1).smul
      ((analyticLift (offset value) membership.2).comp (offsetSmooth value membership.1).analyticAt)
  · intro value membership
    change stageHilbertMap data.cusp finiteCongruence radius positive
      (coefficient degree parameter value • matrixLift (offset value)) = _
    rw [map_smul, liftValue (offset value) membership.2]
    have cancel : inverseMatrix frame + offset value = inverseMatrix value := by dsimp [offset]; abel
    rw [cancel]
    unfold BinaryOrbitStage.family
    rw [inverseMatrix_block]
    rfl

theorem exists_supported_test {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence) (parameter : ℂ)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff) (supported : tsupport cutoff ⊆ domain) :
    ∃ indices : Finset (tsupport cutoff), ∃ radii : indices → ℝ≥0, ∃ positive : ∀ index, 0 < radii index,
      ∃ realTest : SchwartzMap RealSpace (ProductStages.Source data.cusp radii positive),
        tsupport (fun value => realTest value) ⊆ coordinateEquiv.symm ⁻¹' tsupport cutoff ∧
        ∀ value : RealSpace,
          ProductStages.hilbertMap data.cusp radii positive (realTest value) =
            cutoff (coordinateEquiv.symm value) • profile data vector parameter (coordinateEquiv.symm value) := by
  have localExistence (point : tsupport cutoff) := exists_local_lift data vector fixed parameter point.val (supported point.property)
  choose domains openDomains centerMembership contained radii positive lifts analytic values using localExistence
  have cover : tsupport cutoff ⊆ ⋃ point : tsupport cutoff, domains point := by
    intro point membership
    exact Set.mem_iUnion.mpr ⟨⟨point, membership⟩, centerMembership ⟨point, membership⟩⟩
  obtain ⟨indices, finiteCover⟩ := compact.elim_finite_subcover domains openDomains cover
  have indexedCover : tsupport cutoff ⊆ ⋃ index : indices, domains index.val := by
    intro point membership
    obtain ⟨index, indexMembership, inside⟩ := Set.mem_iUnion₂.mp (finiteCover membership)
    exact Set.mem_iUnion.mpr ⟨⟨index, indexMembership⟩, inside⟩
  obtain ⟨test, testSupported, testValue⟩ := CompactBanachLift.exists_supported_test
    (fun index : indices => stageHilbertMap data.cusp finiteCongruence (radii index.val) (positive index.val))
    (profile data vector parameter) (fun index : indices => domains index.val) (fun index => openDomains index.val)
    (fun index : indices => lifts index.val) (fun index => analytic index.val) (fun index => values index.val)
    cutoff smooth compact indexedCover
  refine ⟨indices, (fun index => radii index.val), (fun index => positive index.val),
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinateEquiv.symm.toContinuousLinearEquiv test, ?_, ?_⟩
  · exact (tsupport_comp_subset_preimage (fun point => test point) coordinateEquiv.symm.toContinuousLinearEquiv.continuous).trans
      (Set.preimage_mono testSupported)
  intro value
  exact testValue (coordinateEquiv.symm value)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitProfile
