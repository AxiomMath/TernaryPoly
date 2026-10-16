module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ScalarBinaryCenter
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.CommonLevel

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineOrbitLevel

def lineFiniteHom : BinaryFiniteGL →* FiniteGL :=
  (lineLeviHom FiniteAdeles).comp (MonoidHom.inr FiniteAdelesˣ BinaryFiniteGL)

theorem lineFiniteHom_apply (unit : BinaryFiniteGL) :
    lineFiniteHom unit = lineLevi 1 unit := rfl

theorem lineFiniteHom_continuous : Continuous lineFiniteHom := by
  have valueContinuous : Continuous (fun unit : BinaryFiniteGL =>
      (lineFiniteHom unit).val) := by
    change Continuous (fun unit : BinaryFiniteGL => (lineLevi 1 unit).val)
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;> simp [lineLevi_val] <;> fun_prop
  apply Units.continuous_iff.mpr
  refine ⟨valueContinuous, ?_⟩
  convert valueContinuous.comp continuous_inv using 1
  funext unit
  exact congrArg Units.val ((lineFiniteHom.map_inv unit).symm)

def conjugateLineHom (argument : AdelicGL) : BinaryFiniteGL →* FiniteGL where
  toFun unit := (finiteGroup argument)⁻¹ * lineFiniteHom unit * finiteGroup argument
  map_one' := by simp
  map_mul' first second := by
    simp only [map_mul]
    group

theorem conjugateLineHom_continuous (argument : AdelicGL) :
    Continuous (conjugateLineHom argument) :=
  (continuous_const.mul lineFiniteHom_continuous).mul continuous_const

def level (argument : AdelicGL) : Subgroup BinaryFiniteGL :=
  CuspCommonLevel.principal ⊓ finiteLevel.comap (conjugateLineHom argument)

theorem level_isOpen (argument : AdelicGL) :
    IsOpen (level argument : Set BinaryFiniteGL) :=
  CuspCommonLevel.principal_isOpen.inter
    (FiniteLevelTopology.finiteLevel_isOpen.preimage (conjugateLineHom_continuous argument))

theorem level_isCompact (argument : AdelicGL) :
    IsCompact (level argument : Set BinaryFiniteGL) :=
  CuspCommonLevel.principal_isCompact.inter_right
    (FiniteLevelTopology.finiteLevel_isCompact.isClosed.preimage
      (conjugateLineHom_continuous argument))

theorem conjugate_principal_mem_finiteLevel
    (binary : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (reduced : GeneralLinearGroup.map integralReduction binary = 1)
    (compact : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    GeneralLinearGroup.map integralEmbedding
      (compact⁻¹ * lineLevi 1 binary * compact) ∈ finiteLevel := by
  apply DeterminantCorrection.finite_mem_of_reduction_one
  rw [map_mul, map_mul, map_inv, LineDecomposition.map_lineLevi, reduced, map_one,
    ParabolicInvariance.lineLevi_one, mul_one, inv_mul_cancel]

theorem principal_le_level_of_compact (argument : AdelicGL)
    (membership : inMaximalCompact argument) :
    CuspCommonLevel.principal ≤ level argument := by
  intro unit principalMembership
  refine ⟨principalMembership, ?_⟩
  obtain ⟨binary, reduced, equality⟩ := principalMembership
  obtain ⟨compact, compactEquality⟩ := membership.2
  change GeneralLinearGroup.map integralReduction binary = 1 at reduced
  have conjugation : conjugateLineHom argument unit =
      GeneralLinearGroup.map integralEmbedding
        (compact⁻¹ * lineLevi 1 binary * compact) := by
    change (finiteGroup argument)⁻¹ * lineLevi 1 unit * finiteGroup argument = _
    rw [← compactEquality, ← equality, map_mul, map_mul, map_inv,
      LineDecomposition.map_lineLevi, map_one]
  change conjugateLineHom argument unit ∈ finiteLevel
  rw [conjugation]
  exact conjugate_principal_mem_finiteLevel binary reduced compact

theorem level_rightReal (argument : AdelicGL) (real : RealGL3) :
    level (argument * atInfinity real) = level argument := by
  have homEquality : conjugateLineHom (argument * atInfinity real) =
      conjugateLineHom argument := by
    apply MonoidHom.ext
    intro unit
    simp [conjugateLineHom, map_mul, InducedContinuity.finiteGroup_atInfinity]
  simp only [level, homEquality]

theorem atFinite_lineFiniteHom (unit : BinaryFiniteGL) :
    atFinite (lineFiniteHom unit) = lineLevi 1 (atFinite unit) := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [lineFiniteHom_apply, atFinite, combineGL, pairMatrix, lineLevi_val]

theorem level_translate (argument : AdelicGL) (unit : level argument) :
    ∃ levelElement : finiteLevel,
      lineLevi 1 (atFinite unit.val) * argument = argument * atFinite levelElement.val := by
  let levelElement : finiteLevel := ⟨conjugateLineHom argument unit.val, unit.property.2⟩
  refine ⟨levelElement, ?_⟩
  rw [← atFinite_lineFiniteHom]
  apply InducedContinuity.adelic_ext
  · simp only [map_mul, InducedContinuity.realGroup_atFinite, one_mul, mul_one]
  · simp only [map_mul, InducedContinuity.finiteGroup_atFinite,
      levelElement, conjugateLineHom, MonoidHom.coe_mk, OneHom.coe_mk]
    group

theorem level_det_norm_one (argument : AdelicGL) (unit : level argument) :
    adeleNorm (GeneralLinearGroup.det (atFinite unit.val)) = 1 := by
  obtain ⟨integral, _, equality⟩ := unit.property.1
  rw [← equality]
  exact CuspCommonLevel.integral_binary_norm integral

theorem normalized_finite {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint)
    (argument : AdelicGL) (binary : BinaryAdelicGL) (unit : level argument) :
    ScalarBinaryContinuation.normalizedCuspContinuation degree continuation
        (binary * atFinite unit.val) argument cohomologicalPoint =
      ScalarBinaryContinuation.normalizedCuspContinuation degree continuation
        binary argument cohomologicalPoint := by
  obtain ⟨levelElement, translation⟩ := level_translate argument unit
  have determinantNorm := level_det_norm_one argument unit
  have normalizer : normPower (GeneralLinearGroup.det (binary * atFinite unit.val))
      (-binaryInductionExponent degree .line cohomologicalPoint) =
        normPower (GeneralLinearGroup.det binary)
          (-binaryInductionExponent degree .line cohomologicalPoint) := by
    rw [map_mul, NormPower.normPower_mul_units]
    simp [normPower, determinantNorm]
  have lineLeviProduct : lineLevi 1 (binary * atFinite unit.val) * argument =
      lineLevi 1 binary * argument * atFinite levelElement.val := by
    have multiplication := (lineLeviHom Adeles).map_mul
      (1, binary) (1, atFinite unit.val)
    have lineLevi_multiplication : lineLevi 1 (binary * atFinite unit.val) =
        lineLevi 1 binary * lineLevi 1 (atFinite unit.val) := by
      simpa only [Prod.mk_mul_mk, one_mul, lineLeviHom,
        MonoidHom.coe_mk, OneHom.coe_mk] using multiplication
    rw [lineLevi_multiplication, mul_assoc, translation, mul_assoc]
  unfold ScalarBinaryContinuation.normalizedCuspContinuation
  rw [normalizer, lineLeviProduct,
    StandardInvariance.continuation_finite data extension continuation flat continues
      cohomologicalPoint regular levelElement]

theorem normalized_finite_rightReal {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint)
    (argument : AdelicGL) (real : RealGL3)
    (binary : BinaryAdelicGL) (unit : level argument) :
    ScalarBinaryContinuation.normalizedCuspContinuation degree continuation
        (binary * atFinite unit.val) (argument * atInfinity real) cohomologicalPoint =
      ScalarBinaryContinuation.normalizedCuspContinuation degree continuation
        binary (argument * atInfinity real) cohomologicalPoint := by
  have membership : unit.val ∈ level (argument * atInfinity real) := by
    rw [level_rightReal]
    exact unit.property
  exact normalized_finite data extension continuation flat continues regular
    (argument * atInfinity real) binary ⟨unit.val, membership⟩

theorem normalized_principal_rightReal {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint)
    (argument : AdelicGL) (membership : inMaximalCompact argument)
    (real : RealGL3) (binary : BinaryAdelicGL) (unit : CuspCommonLevel.principal) :
    ScalarBinaryContinuation.normalizedCuspContinuation degree continuation
        (binary * atFinite unit.val) (argument * atInfinity real) cohomologicalPoint =
      ScalarBinaryContinuation.normalizedCuspContinuation degree continuation
        binary (argument * atInfinity real) cohomologicalPoint :=
  normalized_finite_rightReal data extension continuation flat continues regular
    argument real binary ⟨unit.val, principal_le_level_of_compact argument membership unit.property⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineOrbitLevel
