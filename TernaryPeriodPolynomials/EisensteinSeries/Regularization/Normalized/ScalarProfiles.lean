module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.Realization
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.KernelIntegrals
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.RationalNorms
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def normalizedScalarProfile
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (matrix : AdelicGL) :
    BoundedContinuousFunction BinaryAdelicGL ℂ :=
  cuspBoundedRealization inducingData.cusp (normalizedCuspVector flat.1 parameter matrix)

theorem normalizedScalarProfile_apply
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (matrix : AdelicGL)
    (binary : BinaryAdelicGL) :
    normalizedScalarProfile flat parameter matrix binary =
      normPower (GeneralLinearGroup.det binary) (-inductionExponent .plane parameter) *
        unitaryNormalize degree family parameter (planeLevi binary 1 * matrix) :=
  normalizedCuspVector_realize flat.1 parameter matrix binary

theorem normalized_scalar_norm_le_profile
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (matrix : AdelicGL) :
    ‖unitaryNormalize degree family parameter matrix‖ ≤ ‖normalizedScalarProfile flat parameter matrix‖ := by
  rw [← normalizedCuspVector_at_one flat.1 parameter matrix]
  exact cusp_realize_norm_le inducingData.cusp (normalizedCuspVector flat.1 parameter matrix) 1

theorem normalizedScalarProfile_exponential
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) :
    ∃ weight : ℝ, ∀ parameter : ℂ, normalizedScalarProfile flat parameter matrix =
      Complex.exp (parameter * (weight : ℂ)) • normalizedScalarProfile flat 0 matrix := by
  obtain ⟨weight, scaling⟩ := normalizedCuspVector_exponential flat matrix
  refine ⟨weight, ?_⟩
  intro parameter
  simp only [normalizedScalarProfile, scaling parameter, map_smul]

theorem normalizedScalarProfile_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (parameter : ℂ) :
    AnalyticAt ℂ (fun nearby => normalizedScalarProfile flat nearby matrix) parameter := by
  obtain ⟨weight, scaling⟩ := normalizedScalarProfile_exponential flat matrix
  have equality : (fun nearby => normalizedScalarProfile flat nearby matrix) =
      (fun nearby => Complex.exp (nearby * (weight : ℂ)) • normalizedScalarProfile flat 0 matrix) :=
    funext scaling
  rw [equality]
  exact ((analyticAt_id.mul analyticAt_const).cexp).smul analyticAt_const

theorem normalizedScalarProfile_binary_norm
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (matrix : AdelicGL)
    (binary : BinaryAdelicGL) :
    ‖normalizedScalarProfile flat parameter (planeLevi binary 1 * matrix)‖ =
      Real.exp ((inductionExponent .plane parameter).re *
        Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) *
          ‖normalizedScalarProfile flat parameter matrix‖ := by
  simp only [normalizedScalarProfile, normalizedCuspVector_binary, map_smul, norm_smul,
    cuspBoundedRealization_translate_norm, normPower_norm]

theorem normalizedScalarProfile_rankOne_norm
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (matrix : AdelicGL) (scalar : Adelesˣ) :
    ‖normalizedScalarProfile flat parameter (planeLevi 1 scalar * matrix)‖ =
      Real.exp ((-2 * inductionExponent .plane parameter).re * Real.log (adeleNorm scalar : ℝ)) *
        ‖normalizedScalarProfile flat parameter matrix‖ := by
  simp only [normalizedScalarProfile, normalizedCuspVector_rankOne, map_smul, norm_smul,
    norm_mul, inducingData.chi.unitary, one_mul, normPower_norm]

theorem normalizedScalarProfile_unipotent
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (matrix : AdelicGL)
    (first second : Adeles) :
    normalizedScalarProfile flat parameter (planeUnipotent first second * matrix) =
      normalizedScalarProfile flat parameter matrix := by
  simp only [normalizedScalarProfile, normalizedCuspVector_unipotent]

theorem normalizedScalarProfile_flat_compact
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (matrix : AdelicGL)
    (compact : inMaximalCompact matrix) :
    normalizedScalarProfile flat parameter matrix = normalizedScalarProfile flat 0 matrix := by
  simp only [normalizedScalarProfile, normalizedCuspVector_flat_compact flat _ matrix compact]

theorem normalizedScalarProfile_parabolic_rational_norm
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (rationalMatrix : RationalGL3)
    (parabolic : rationalMatrix ∈ GeneralEisenstein.parabolic .plane) (matrix : AdelicGL) :
    ‖normalizedScalarProfile flat parameter (rationalGroup rationalMatrix * matrix)‖ =
      ‖normalizedScalarProfile flat parameter matrix‖ := by
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    planeParabolic_factorization rationalMatrix parabolic
  rw [factorization, map_mul, mul_assoc]
  change ‖normalizedScalarProfile flat parameter
    (GeneralLinearGroup.map rationalAdele (planeUnipotent first second) *
      (GeneralLinearGroup.map rationalAdele (planeLevi binary scalar) * matrix))‖ = _
  rw [map_planeUnipotent, normalizedScalarProfile_unipotent, map_planeLevi,
    planeLevi_rankOne_binary, mul_assoc, normalizedScalarProfile_rankOne_norm,
    normalizedScalarProfile_binary_norm, GeneralLinearGroup.map_det,
    adeleNorm_rational, adeleNorm_rational]
  simp

theorem normalizedScalarProfile_evaluation_joint_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (binary : BinaryAdelicGL) :
    Continuous (fun input : ℂ × AdelicGL => normalizedScalarProfile flat input.1 input.2 binary) := by
  simp_rw [normalizedScalarProfile_apply]
  have exponent_continuous : Continuous
      (fun input : ℂ × AdelicGL => -inductionExponent .plane input.1) :=
    (continuous_const.add (continuous_fst.div_const 3)).neg
  have scalar_continuous := normPower_continuous.comp
    ((continuous_const (y := GeneralLinearGroup.det binary)).prodMk exponent_continuous)
  have matrix_continuous : Continuous (fun input : ℂ × AdelicGL =>
      (input.1, planeLevi binary 1 * input.2)) :=
    continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have section_continuous := (unitaryNormalize_joint_continuous flat).comp matrix_continuous
  dsimp only [Function.comp_def] at scalar_continuous section_continuous
  exact scalar_continuous.mul section_continuous

theorem normalizedScalarProfile_norm_lowerSemicontinuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    LowerSemicontinuous (fun input : ℂ × AdelicGL => ‖normalizedScalarProfile flat input.1 input.2‖) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro bound
  have equality : {input : ℂ × AdelicGL | ‖normalizedScalarProfile flat input.1 input.2‖ ≤ bound} =
      ⋂ binary : BinaryAdelicGL,
        {input | ‖normalizedScalarProfile flat input.1 input.2 binary‖ ≤ bound} := by
    ext input
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, BoundedContinuousFunction.norm_le_of_nonempty]
  change IsClosed {input : ℂ × AdelicGL | ‖normalizedScalarProfile flat input.1 input.2‖ ≤ bound}
  rw [equality]
  exact isClosed_iInter (fun binary =>
    isClosed_le (normalizedScalarProfile_evaluation_joint_continuous flat binary).norm continuous_const)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
