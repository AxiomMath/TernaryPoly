module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.ProductHaar

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryProductHaar
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealOrbitalMass

abbrev BinaryMatrix := Matrix (Fin 2) (Fin 2) ℝ

def leftInverse (point : AdelicGL) : Matrix (Fin 2) (Fin 3) ℝ :=
  fun row column => (realGroup point).val row.castSucc column

theorem leftInverse_frame (point : AdelicGL) : leftInverse point * realFrame point = 1 := by
  have inverse : (realGroup point).val * (realGroup point)⁻¹.val = 1 := (realGroup point).val_inv
  ext row column
  simpa only [leftInverse, realFrame, columns, Matrix.mul_apply, Matrix.one_apply, Fin.castSucc_inj] using
    congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix row.castSucc column.castSucc) inverse

def orbitLinear (point : AdelicGL) : BinaryMatrix →ₗ[ℝ] Rectangular ℝ where
  toFun := fun binary => realFrame point * binary
  map_add' := Matrix.mul_add _
  map_smul' := fun scalar binary => Matrix.mul_smul _ scalar binary

theorem orbitLinear_injective (point : AdelicGL) : Function.Injective (orbitLinear point) := by
  intro first second equality
  have recovered := congrArg (fun value : Rectangular ℝ => leftInverse point * value) equality
  change leftInverse point * (realFrame point * first) = leftInverse point * (realFrame point * second) at recovered
  simpa only [← Matrix.mul_assoc, leftInverse_frame, Matrix.one_mul] using recovered

theorem orbitLinear_isClosedEmbedding (point : AdelicGL) : Topology.IsClosedEmbedding (orbitLinear point) :=
  (orbitLinear point).isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr (orbitLinear_injective point))

theorem exterior_mul (value : Rectangular ℝ) (binary : BinaryMatrix) :
    exterior (value * binary) = binary.det • exterior value := by
  ext row
  fin_cases row <;> simp [exterior, crossProduct, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem fullRank_mul_det (value : Rectangular ℝ) (binary : BinaryMatrix)
    (fullRank : FullRank (value * binary)) : binary.det ≠ 0 := by
  intro vanishing
  apply fullRank
  rw [exterior_mul, vanishing, zero_smul]

theorem units_isEmbedding : Topology.IsEmbedding (Units.val : BinaryRealGL → BinaryMatrix) := by
  apply Units.isEmbedding_val_mk' (f := fun matrix : BinaryMatrix => matrix⁻¹)
  · simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    have determinant : Continuous (fun matrix : BinaryMatrix => matrix.det) := by
      simp only [Matrix.det_fin_two]
      fun_prop
    have inverse : ContinuousOn (fun matrix : BinaryMatrix => matrix.det⁻¹) {matrix | IsUnit matrix} :=
      determinant.continuousOn.inv₀ (fun matrix invertible =>
        isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det matrix).mp invertible))
    have adjugate : Continuous (fun matrix : BinaryMatrix => matrix.adjugate) := by
      apply continuous_pi
      intro row
      apply continuous_pi
      intro column
      fin_cases row <;> fin_cases column <;> simp [Matrix.adjugate_fin_two] <;> fun_prop
    exact inverse.smul adjugate.continuousOn
  · intro binary
    exact (GeneralLinearGroup.coe_inv binary).symm

theorem compactSupport (cutoff : Rectangular ℝ → ℝ) (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) (point : AdelicGL) :
    HasCompactSupport (fun binary : BinaryRealGL => cutoff (realFrame point * binary.val)) := by
  let function : BinaryMatrix → ℝ := cutoff ∘ orbitLinear point
  have functionCompact : HasCompactSupport function :=
    compact.comp_isClosedEmbedding (orbitLinear_isClosedEmbedding point)
  have supportContained : tsupport function ⊆ orbitLinear point ⁻¹' tsupport cutoff := by
    apply closure_minimal
    · intro binary nonzero
      exact subset_closure nonzero
    · exact isClosed_closure.preimage (orbitLinear_isClosedEmbedding point).continuous
  have inRange : tsupport function ⊆ Set.range (Units.val : BinaryRealGL → BinaryMatrix) := by
    intro binary membership
    exact ⟨GeneralLinearGroup.mkOfDetNeZero binary
      (fullRank_mul_det _ binary (supported (supportContained membership))), rfl⟩
  have preimageCompact : IsCompact ((Units.val : BinaryRealGL → BinaryMatrix) ⁻¹' tsupport function) := by
    apply units_isEmbedding.isCompact_iff.mpr
    rw [Set.image_preimage_eq_of_subset inRange]
    exact functionCompact
  apply HasCompactSupport.of_support_subset_isCompact preimageCompact
  intro binary nonzero
  exact subset_closure nonzero

theorem continuous (cutoff : Rectangular ℝ → ℝ) (regularity : Continuous cutoff) (point : AdelicGL) :
    Continuous (fun binary : BinaryRealGL => cutoff (realFrame point * binary.val)) :=
  regularity.comp (continuous_const.matrix_mul (Units.continuous_val (M := BinaryMatrix)))

theorem integrable (cutoff : Rectangular ℝ → ℝ) (regularity : Continuous cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) (point : AdelicGL) :
    Integrable (fun binary : BinaryRealGL => cutoff (realFrame point * binary.val)) realMeasure :=
  (continuous cutoff regularity point).integrable_of_hasCompactSupport (compactSupport cutoff compact supported point)

def mass (cutoff : Rectangular ℝ → ℝ) (point : AdelicGL) : ℂ :=
  ∫ binary : BinaryRealGL, (cutoff (realFrame point * binary.val) : ℂ) ∂realMeasure

theorem nonzero (cutoff : Rectangular ℝ → ℝ) (regularity : Continuous cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value})
    (nonnegative : ∀ value, 0 ≤ cutoff value) (point : AdelicGL)
    (positive : cutoff (realFrame point) ≠ 0) : mass cutoff point ≠ 0 := by
  have supportPositive : 0 < realMeasure (Function.support (fun binary : BinaryRealGL =>
      cutoff (realFrame point * binary.val))) := by
    apply (isOpen_ne_fun (continuous cutoff regularity point) continuous_const).measure_pos realMeasure
    refine ⟨1, ?_⟩
    change cutoff (realFrame point * (1 : BinaryRealGL).val) ≠ 0
    simpa only [Units.val_one, Matrix.mul_one] using positive
  have integralPositive := (integral_pos_iff_support_of_nonneg (fun binary : BinaryRealGL =>
    nonnegative (realFrame point * binary.val)) (integrable cutoff regularity compact supported point)).mpr supportPositive
  have equality : mass cutoff point =
      Complex.ofReal (∫ binary : BinaryRealGL, cutoff (realFrame point * binary.val) ∂realMeasure) :=
    integral_ofReal (𝕜 := ℂ) (μ := realMeasure) (f := fun binary : BinaryRealGL =>
      cutoff (realFrame point * binary.val))
  rw [equality]
  exact_mod_cast integralPositive.ne'

theorem exists_cutoff (point : AdelicGL) :
    ∃ cutoff : Rectangular ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff ∧ HasCompactSupport cutoff ∧
      tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value} ∧
      Set.range cutoff ⊆ Set.Icc 0 1 ∧ cutoff (realFrame point) = 1 ∧ mass cutoff point ≠ 0 := by
  obtain ⟨cutoff, smooth, compact, supported, range, value⟩ :=
    RealProfileCutoff.exists_cutoff (realFrame point) (realFrame_fullRank point)
  refine ⟨cutoff, smooth, compact, supported, range, value, ?_⟩
  exact nonzero cutoff smooth.continuous compact supported (fun value => (range ⟨value, rfl⟩).1)
    point (by rw [value]; exact one_ne_zero)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealOrbitalMass
