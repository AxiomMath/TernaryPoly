module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CompactDerivativeIntegral

@[expose] public section


open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

theorem binaryRotationAverage_hasFDerivAt
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (values : P → BinaryRealMatrix → E) (domain : Set P) (domain_open : IsOpen domain)
    (regular : ContDiffOn ℝ 1 (Function.uncurry values) (domain ×ˢ {matrix | matrix.det ≠ 0}))
    (point : P) (member : point ∈ domain) :
    HasFDerivAt (fun parameter => ∫ angle, values parameter (binaryRotationMatrix angle) ∂binaryRotationMeasure)
      (∫ angle, fderiv ℝ (fun parameter => values parameter (binaryRotationMatrix angle)) point ∂binaryRotationMeasure) point := by
  let D : P → Circle → P →L[ℝ] E := fun parameter angle =>
    (fderiv ℝ (Function.uncurry values) (parameter, binaryRotationMatrix angle)).comp
      (ContinuousLinearMap.inl ℝ P BinaryRealMatrix)
  have product_open : IsOpen (domain ×ˢ {matrix : BinaryRealMatrix | matrix.det ≠ 0}) :=
    domain_open.prod (isOpen_ne_fun continuous_id.matrix_det continuous_const)
  have rotation_mem (angle : Circle) : (binaryRotationMatrix angle).det ≠ 0 := by
    rw [binaryRotationMatrix_det]
    exact one_ne_zero
  have derivative (parameter : P) (parameter_mem : parameter ∈ domain) (angle : Circle) :
      HasFDerivAt (fun parameter => values parameter (binaryRotationMatrix angle)) (D parameter angle) parameter := by
    have joint := (regular.differentiableOn (by norm_num)).differentiableAt (x := (parameter, binaryRotationMatrix angle))
      (product_open.mem_nhds ⟨parameter_mem, rotation_mem angle⟩)
    have inclusion : HasFDerivAt (fun argument : P => (argument, binaryRotationMatrix angle))
        (ContinuousLinearMap.inl ℝ P BinaryRealMatrix) parameter := by
      exact (hasFDerivAt_id parameter).prodMk (hasFDerivAt_const (binaryRotationMatrix angle) parameter)
    exact joint.hasFDerivAt.comp parameter inclusion
  have continuous : ContinuousOn (fun pair : P × Circle => values pair.1 (binaryRotationMatrix pair.2)) (domain ×ˢ Set.univ) :=
    regular.continuousOn.comp (continuous_fst.prodMk (binaryRotationMatrix_continuous.comp continuous_snd)).continuousOn
      (fun pair pair_mem => ⟨pair_mem.1, rotation_mem pair.2⟩)
  have derivative_continuous : ContinuousOn (Function.uncurry D) (domain ×ˢ Set.univ) := by
    have full := regular.continuousOn_fderiv_of_isOpen product_open le_rfl
    have restricted := full.comp
      (continuous_fst.prodMk (binaryRotationMatrix_continuous.comp continuous_snd)).continuousOn
      (s := domain ×ˢ (Set.univ : Set Circle)) (fun pair pair_mem => ⟨pair_mem.1, rotation_mem pair.2⟩)
    exact restricted.clm_comp continuousOn_const
  have result := hasFDerivAt_integral_compact_parameter binaryRotationMeasure
    (fun parameter angle => values parameter (binaryRotationMatrix angle)) D domain domain_open
    continuous derivative_continuous derivative point member
  have equality : (fun angle => D point angle) = fun angle => fderiv ℝ (fun parameter => values parameter (binaryRotationMatrix angle)) point := by
    funext angle
    exact (derivative point member angle).fderiv.symm
  rw [equality] at result
  exact result

theorem binaryRotationAverage_fderiv_continuous
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (values : P → BinaryRealMatrix → E) (domain : Set P) (domain_open : IsOpen domain)
    (regular : ContDiffOn ℝ 1 (Function.uncurry values) (domain ×ˢ {matrix | matrix.det ≠ 0}))
    (point : P) (member : point ∈ domain) :
    Continuous (fun angle : Circle => fderiv ℝ (fun parameter => values parameter (binaryRotationMatrix angle)) point) := by
  have product_open : IsOpen (domain ×ˢ {matrix : BinaryRealMatrix | matrix.det ≠ 0}) :=
    domain_open.prod (isOpen_ne_fun continuous_id.matrix_det continuous_const)
  have rotation_mem (angle : Circle) : (binaryRotationMatrix angle).det ≠ 0 := by
    rw [binaryRotationMatrix_det]
    exact one_ne_zero
  have full := regular.continuousOn_fderiv_of_isOpen product_open le_rfl
  have composed : Continuous (fun angle : Circle => fderiv ℝ (Function.uncurry values) (point, binaryRotationMatrix angle)) :=
    full.comp_continuous (continuous_const.prodMk binaryRotationMatrix_continuous) (fun angle => ⟨member, rotation_mem angle⟩)
  have sliced := composed.clm_comp (continuous_const (y := ContinuousLinearMap.inl ℝ P BinaryRealMatrix))
  apply sliced.congr
  intro angle
  have joint := (regular.differentiableOn (by norm_num)).differentiableAt (x := (point, binaryRotationMatrix angle))
    (product_open.mem_nhds ⟨member, rotation_mem angle⟩)
  have inclusion : HasFDerivAt (fun argument : P => (argument, binaryRotationMatrix angle))
      (ContinuousLinearMap.inl ℝ P BinaryRealMatrix) point :=
    (hasFDerivAt_id point).prodMk (hasFDerivAt_const (binaryRotationMatrix angle) point)
  exact (joint.hasFDerivAt.comp point inclusion).fderiv.symm

theorem binaryRotationAverage_hasDerivAt
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (values : ℝ → BinaryRealMatrix → E) (domain : Set ℝ) (domain_open : IsOpen domain)
    (regular : ContDiffOn ℝ 1 (Function.uncurry values) (domain ×ˢ {matrix | matrix.det ≠ 0}))
    (point : ℝ) (member : point ∈ domain) :
    HasDerivAt (fun parameter => ∫ angle, values parameter (binaryRotationMatrix angle) ∂binaryRotationMeasure)
      (∫ angle, deriv (fun parameter => values parameter (binaryRotationMatrix angle)) point ∂binaryRotationMeasure) point := by
  have continuous := binaryRotationAverage_fderiv_continuous values domain domain_open regular point member
  have integrable := continuous.integrable_of_hasCompactSupport (μ := binaryRotationMeasure) (HasCompactSupport.of_compactSpace _)
  have derivative := (binaryRotationAverage_hasFDerivAt values domain domain_open regular point member).hasDerivAt
  rw [ContinuousLinearMap.integral_apply integrable] at derivative
  exact derivative

end TernaryPeriodPolynomials.SphericalDetection.Helpers
