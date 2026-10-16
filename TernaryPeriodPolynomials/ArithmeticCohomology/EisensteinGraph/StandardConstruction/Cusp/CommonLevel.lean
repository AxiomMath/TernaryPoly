module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.HilbertAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.DeterminantCorrection
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedHeight
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealTranslations

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspCommonLevel

/-- The binary principal congruence subgroup modulo three at the finite places. -/
def principal : Subgroup BinaryFiniteGL :=
  (GeneralLinearGroup.map (n := Fin 2) integralReduction).ker.map
    (GeneralLinearGroup.map integralEmbedding)

theorem principal_isOpen : IsOpen (principal : Set BinaryFiniteGL) := by
  have sourceOpen : IsOpen
      ((GeneralLinearGroup.map (n := Fin 2) integralReduction).ker :
        Set (GeneralLinearGroup (Fin 2) IntegralAdeles)) :=
    (isOpen_discrete ({1} : Set (GeneralLinearGroup (Fin 2) (ZMod 3)))).preimage
      (TopologicalMatrices.generalLinearMap_continuous integralReduction
        FiniteLevelTopology.integralReduction_continuous)
  exact (TopologicalMatrices.generalLinearMap_isOpenEmbedding (size := 2) integralEmbedding
    integralEmbedding_isOpenEmbedding).isOpenMap _ sourceOpen

theorem principal_isCompact : IsCompact (principal : Set BinaryFiniteGL) := by
  let : CompactSpace (Matrix (Fin 2) (Fin 2) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → IntegralAdeles))
  have sourceClosed : IsClosed
      ((GeneralLinearGroup.map (n := Fin 2) integralReduction).ker :
        Set (GeneralLinearGroup (Fin 2) IntegralAdeles)) :=
    (isClosed_discrete ({1} : Set (GeneralLinearGroup (Fin 2) (ZMod 3)))).preimage
      (TopologicalMatrices.generalLinearMap_continuous integralReduction
        FiniteLevelTopology.integralReduction_continuous)
  exact sourceClosed.isCompact.image
    (TopologicalMatrices.generalLinearMap_continuous integralEmbedding
      integralEmbedding_isOpenEmbedding.continuous)

theorem atFinite_planeLevi (binary : BinaryFiniteGL) :
    atFinite (planeLevi binary 1) = planeLevi (atFinite binary) 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;> rfl

theorem integral_plane_compact (binary : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    inMaximalCompact (planeLevi (atFinite (GeneralLinearGroup.map integralEmbedding binary)) 1) := by
  rw [← atFinite_planeLevi]
  constructor
  · simp only [InducedContinuity.realGroup_atFinite, GeneralLinearGroup.coe_one,
      Matrix.transpose_one, one_mul]
  · rw [InducedContinuity.finiteGroup_atFinite]
    exact ⟨planeLevi binary 1, by rw [PlaneDecomposition.map_planeLevi, map_one]⟩

theorem integral_binary_norm (binary : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    adeleNorm (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding binary))) = 1 := by
  have norm := InducedHeight.compact_det_norm _ (integral_plane_compact binary)
  simpa only [InducedHeight.planeLevi_det, mul_one] using norm

theorem conjugate_mem_finiteLevel (binary : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (reduced : GeneralLinearGroup.map integralReduction binary = 1)
    (compact : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    GeneralLinearGroup.map integralEmbedding
      (compact⁻¹ * planeLevi binary 1 * compact) ∈ finiteLevel := by
  apply DeterminantCorrection.finite_mem_of_reduction_one
  rw [map_mul, map_mul, map_inv, PlaneDecomposition.map_planeLevi, reduced, map_one,
    ParabolicInvariance.planeLevi_one, mul_one, inv_mul_cancel]

theorem compact_translate (binary : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (reduced : GeneralLinearGroup.map integralReduction binary = 1)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    ∃ level : finiteLevel,
      planeLevi (atFinite (GeneralLinearGroup.map integralEmbedding binary)) 1 * compact =
        compact * atFinite level.val := by
  obtain ⟨integral, finite⟩ := membership.2
  let conjugate := integral⁻¹ * planeLevi binary 1 * integral
  refine ⟨⟨GeneralLinearGroup.map integralEmbedding conjugate,
    conjugate_mem_finiteLevel binary reduced integral⟩, ?_⟩
  rw [← atFinite_planeLevi]
  apply InducedContinuity.adelic_ext
  · simp only [map_mul, InducedContinuity.realGroup_atFinite, one_mul, mul_one]
  · simp only [map_mul, InducedContinuity.finiteGroup_atFinite, conjugate, map_inv,
      PlaneDecomposition.map_planeLevi, map_one, finite]
    group

/-- The same finite subgroup fixes every inducing vector in the compact realization. -/
theorem compact_vector_fixed {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (compact : AdelicGL)
    (membership : inMaximalCompact compact) (unit : principal) :
    data.cusp.π (atFinite unit.val)
      (CuspLift.vector data .plane parameter function induced compact).val =
        (CuspLift.vector data .plane parameter function induced compact).val := by
  obtain ⟨binary, reduced, equality⟩ := unit.property
  change GeneralLinearGroup.map integralReduction binary = 1 at reduced
  obtain ⟨level, translate⟩ := compact_translate binary reduced compact membership
  have covariance := CuspLiftCovariance.vector_binary data .plane parameter function induced
    (atFinite (GeneralLinearGroup.map integralEmbedding binary)) compact
  rw [binaryLevi, translate, CuspLift.finite_invariant] at covariance
  have normPowerOne : normPower
      (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding binary)))
      (binaryInductionExponent degree .plane parameter) = 1 := by
    simp only [normPower, integral_binary_norm, NNReal.coe_one, Real.log_one,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [normPowerOne, one_smul, equality] at covariance
  exact covariance.symm

theorem vector_fixed_of_translation {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data side parameter function)
    (unit : BinaryFiniteGL) (normOne : adeleNorm (GeneralLinearGroup.det (atFinite unit)) = 1)
    (argument : AdelicGL) (level : finiteLevel)
    (translation : binaryLevi side (atFinite unit) * argument = argument * atFinite level.val) :
    data.cusp.π (atFinite unit) (CuspLift.vector data side parameter function induced argument).val =
      (CuspLift.vector data side parameter function induced argument).val := by
  have covariance := CuspLiftCovariance.vector_binary data side parameter function induced
    (atFinite unit) argument
  rw [translation, CuspLift.finite_invariant] at covariance
  simpa only [normPower, normOne, NNReal.coe_one, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_smul] using covariance.symm

theorem compact_real_vector_fixed {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (compact : AdelicGL)
    (membership : inMaximalCompact compact) (real : RealGL3) (unit : principal) :
    data.cusp.π (atFinite unit.val)
      (CuspLift.vector data .plane parameter function induced (compact * atInfinity real)).val =
        (CuspLift.vector data .plane parameter function induced (compact * atInfinity real)).val := by
  obtain ⟨binary, reduced, equality⟩ := unit.property
  change GeneralLinearGroup.map integralReduction binary = 1 at reduced
  obtain ⟨level, translate⟩ := compact_translate binary reduced compact membership
  have normOne : adeleNorm (GeneralLinearGroup.det (atFinite unit.val)) = 1 := by
    rw [← equality]
    exact integral_binary_norm binary
  apply vector_fixed_of_translation data .plane parameter function induced unit.val normOne
    (compact * atInfinity real) level
  change planeLevi (atFinite unit.val) 1 * (compact * atInfinity real) = _
  rw [← equality, ← mul_assoc, translate, mul_assoc,
    RealTranslations.atFinite_atInfinity_commute, ← mul_assoc]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspCommonLevel
