module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalNorm
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LinearFamilies

theorem smooth_add {dimension count : ℕ} {Value : Type}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (first second : (Fin count → Matrix.GeneralLinearGroup (Fin dimension) ℝ) → Value)
    (firstSmooth : Smooth first) (secondSmooth : Smooth second) :
    Smooth (fun vertices => first vertices + second vertices) := by
  exact firstSmooth.add secondSmooth

theorem smooth_smul {dimension count : ℕ} {Value : Type}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] [NormedSpace ℂ Value]
    [IsScalarTower ℝ ℂ Value]
    (scalar : ℂ)
    (function : (Fin count → Matrix.GeneralLinearGroup (Fin dimension) ℝ) → Value)
    (functionSmooth : Smooth function) :
    Smooth (fun vertices => scalar • function vertices) := by
  exact functionSmooth.const_smul scalar

theorem smoothCuspLift_add {degree count : ℕ} (data : InducingData degree)
    (side : Side) (parameter : ℂ)
    (first second : (Fin count → RealGL3) → AdelicGL → ℂ)
    (firstLift : HasSmoothCuspLift data side parameter first)
    (secondLift : HasSmoothCuspLift data side parameter second) :
    HasSmoothCuspLift data side parameter
      (fun vertices argument => first vertices argument + second vertices argument) := by
  intro argument
  obtain ⟨firstVectors, firstSmooth, firstRealizes⟩ := firstLift argument
  obtain ⟨secondVectors, secondSmooth, secondRealizes⟩ := secondLift argument
  refine ⟨fun vertices => firstVectors vertices + secondVectors vertices,
    smooth_add _ _ firstSmooth secondSmooth, ?_⟩
  intro vertices binaryElement
  simp only [map_add, Pi.add_apply, firstRealizes, secondRealizes, mul_add]

theorem smoothCuspLift_smul {degree count : ℕ} (data : InducingData degree)
    (side : Side) (parameter scalar : ℂ)
    (function : (Fin count → RealGL3) → AdelicGL → ℂ)
    (functionLift : HasSmoothCuspLift data side parameter function) :
    HasSmoothCuspLift data side parameter
      (fun vertices argument => scalar * function vertices argument) := by
  intro argument
  obtain ⟨vectors, vectorSmooth, realizes⟩ := functionLift argument
  refine ⟨fun vertices => scalar • vectors vertices,
    smooth_smul scalar _ vectorSmooth, ?_⟩
  intro vertices binaryElement
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, realizes]
  ring

theorem induced_add {degree : ℕ} (data : InducingData degree)
    (side : Side) (parameter : ℂ) (first second : AdelicGL → ℂ)
    (firstInduced : IsInduced data side parameter first)
    (secondInduced : IsInduced data side parameter second) :
    IsInduced data side parameter (fun argument => first argument + second argument) := by
  refine ⟨fun argument => smooth_add _ _ (firstInduced.1 argument)
    (secondInduced.1 argument), ?_,
    smoothCuspLift_add data side parameter _ _ firstInduced.2.2.1 secondInduced.2.2.1, ?_⟩
  · intro levelElement argument
    change first _ + second _ = first _ + second _
    rw [firstInduced.2.1, secondInduced.2.1]
  · cases side <;>
      obtain ⟨firstUnipotent, firstRankOne, firstBinary⟩ := firstInduced.2.2.2 <;>
      obtain ⟨secondUnipotent, secondRankOne, secondBinary⟩ := secondInduced.2.2.2 <;>
      refine ⟨?_, ?_, ?_⟩
    · intro firstCoordinate secondCoordinate argument
      change first _ + second _ = first _ + second _
      rw [firstUnipotent, secondUnipotent]
    · intro unit argument
      change first _ + second _ = _ * (first _ + second _)
      rw [firstRankOne, secondRankOne, mul_add]
    · intro argument
      simpa only [Pi.add_def, mul_add] using
        (cuspFunctions data.cusp).add_mem (firstBinary argument) (secondBinary argument)
    · intro firstCoordinate secondCoordinate argument
      change first _ + second _ = first _ + second _
      rw [firstUnipotent, secondUnipotent]
    · intro unit argument
      change first _ + second _ = _ * (first _ + second _)
      rw [firstRankOne, secondRankOne, mul_add]
    · intro argument
      simpa only [Pi.add_def, mul_add] using
        (cuspFunctions data.cusp).add_mem (firstBinary argument) (secondBinary argument)

theorem induced_smul {degree : ℕ} (data : InducingData degree)
    (side : Side) (parameter scalar : ℂ) (function : AdelicGL → ℂ)
    (functionInduced : IsInduced data side parameter function) :
    IsInduced data side parameter (fun argument => scalar * function argument) := by
  refine ⟨fun argument => smooth_smul scalar _ (functionInduced.1 argument), ?_,
    smoothCuspLift_smul data side parameter scalar _ functionInduced.2.2.1, ?_⟩
  · intro levelElement argument
    change scalar * function _ = scalar * function _
    rw [functionInduced.2.1]
  · cases side <;>
      obtain ⟨unipotentInvariant, rankOneCovariance, binaryValues⟩ :=
        functionInduced.2.2.2 <;>
      refine ⟨?_, ?_, ?_⟩
    · intro firstCoordinate secondCoordinate argument
      change scalar * function _ = scalar * function _
      rw [unipotentInvariant]
    · intro unit argument
      change scalar * function _ = _ * (scalar * function _)
      rw [rankOneCovariance]
      ring
    · intro argument
      have membership := (cuspFunctions data.cusp).smul_mem scalar (binaryValues argument)
      convert membership using 1
      funext binaryElement
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · intro firstCoordinate secondCoordinate argument
      change scalar * function _ = scalar * function _
      rw [unipotentInvariant]
    · intro unit argument
      change scalar * function _ = _ * (scalar * function _)
      rw [rankOneCovariance]
      ring
    · intro argument
      have membership := (cuspFunctions data.cusp).smul_mem scalar (binaryValues argument)
      convert membership using 1
      funext binaryElement
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

theorem flat_add {degree : ℕ} (data : InducingData degree)
    (first second : ℂ → AdelicGL → ℂ)
    (firstFlat : IsFlatSection data first) (secondFlat : IsFlatSection data second) :
    IsFlatSection data (fun parameter argument =>
      first parameter argument + second parameter argument) := by
  refine ⟨fun parameter => induced_add data .plane parameter _ _
    (firstFlat.1 parameter) (secondFlat.1 parameter), ?_, ?_⟩
  · intro argument parameter
    exact (firstFlat.2.1 argument parameter).add (secondFlat.2.1 argument parameter)
  · intro parameter binaryElement compactElement compactMembership
    rw [mul_add, firstFlat.2.2 parameter binaryElement compactElement compactMembership,
      secondFlat.2.2 parameter binaryElement compactElement compactMembership, mul_add]

theorem flat_smul {degree : ℕ} (data : InducingData degree) (scalar : ℂ)
    (function : ℂ → AdelicGL → ℂ) (functionFlat : IsFlatSection data function) :
    IsFlatSection data (fun parameter argument => scalar * function parameter argument) := by
  refine ⟨fun parameter => induced_smul data .plane parameter scalar _
    (functionFlat.1 parameter), ?_, ?_⟩
  · intro argument parameter
    exact (functionFlat.2.1 argument parameter).const_smul (c := scalar)
  · intro parameter binaryElement compactElement compactMembership
    calc
      _ = scalar * (normPower (Matrix.GeneralLinearGroup.det binaryElement)
          (-binaryInductionExponent degree .plane parameter) *
          function parameter (planeLevi binaryElement 1 * compactElement)) := by ring
      _ = scalar * (normPower (Matrix.GeneralLinearGroup.det binaryElement)
          (-binaryInductionExponent degree .plane cohomologicalPoint) *
          function cohomologicalPoint (planeLevi binaryElement 1 * compactElement)) := by
        rw [functionFlat.2.2 parameter binaryElement compactElement compactMembership]
      _ = _ := by ring

theorem eisensteinContinuation_add (firstExtension secondExtension first second :
    ℂ → AdelicGL → ℂ)
    (firstContinuation : IsEisensteinContinuation firstExtension first)
    (secondContinuation : IsEisensteinContinuation secondExtension second) :
    IsEisensteinContinuation
      (fun parameter argument => firstExtension parameter argument +
        secondExtension parameter argument)
      (fun parameter argument => first parameter argument + second parameter argument) := by
  refine ⟨fun argument parameter => (firstContinuation.1 argument parameter).add
    (secondContinuation.1 argument parameter), ?_⟩
  obtain ⟨firstThreshold, firstSum⟩ := firstContinuation.2
  obtain ⟨secondThreshold, secondSum⟩ := secondContinuation.2
  refine ⟨max firstThreshold secondThreshold, ?_⟩
  intro parameter membership argument
  exact (firstSum parameter (lt_of_le_of_lt (le_max_left _ _) membership) argument).add
    (secondSum parameter (lt_of_le_of_lt (le_max_right _ _) membership) argument)

theorem eisensteinContinuation_smul (scalar : ℂ) (extension continuation :
    ℂ → AdelicGL → ℂ)
    (continues : IsEisensteinContinuation extension continuation) :
    IsEisensteinContinuation
      (fun parameter argument => scalar * extension parameter argument)
      (fun parameter argument => scalar * continuation parameter argument) := by
  refine ⟨fun argument parameter => (continues.1 argument parameter).const_smul scalar, ?_⟩
  obtain ⟨threshold, sums⟩ := continues.2
  refine ⟨threshold, ?_⟩
  intro parameter membership argument
  exact (sums parameter membership argument).mul_left scalar

theorem standardContinuation_add (firstExtension secondExtension first second :
    ℂ → AdelicGL → ℂ)
    (firstContinuation : IsStandardContinuation firstExtension first)
    (secondContinuation : IsStandardContinuation secondExtension second) :
    IsStandardContinuation
      (fun parameter argument => firstExtension parameter argument +
        secondExtension parameter argument)
      (fun parameter argument => first parameter argument + second parameter argument) := by
  refine ⟨fun argument parameter => (firstContinuation.1 argument parameter).add
    (secondContinuation.1 argument parameter), ?_⟩
  obtain ⟨firstThreshold, firstIntegral⟩ := firstContinuation.2
  obtain ⟨secondThreshold, secondIntegral⟩ := secondContinuation.2
  refine ⟨max firstThreshold secondThreshold, ?_⟩
  intro parameter membership argument
  obtain ⟨firstIntegrable, firstEquality⟩ := firstIntegral parameter
    (lt_of_le_of_lt (le_max_left _ _) membership) argument
  obtain ⟨secondIntegrable, secondEquality⟩ := secondIntegral parameter
    (lt_of_le_of_lt (le_max_right _ _) membership) argument
  refine ⟨firstIntegrable.add secondIntegrable, ?_⟩
  change first parameter argument + second parameter argument =
    ∫ radical, standardIntegrand firstExtension parameter argument radical +
      standardIntegrand secondExtension parameter argument radical ∂radicalMeasure
  rw [integral_add firstIntegrable secondIntegrable, firstEquality, secondEquality]

theorem standardContinuation_smul (scalar : ℂ) (extension continuation :
    ℂ → AdelicGL → ℂ)
    (continues : IsStandardContinuation extension continuation) :
    IsStandardContinuation
      (fun parameter argument => scalar * extension parameter argument)
      (fun parameter argument => scalar * continuation parameter argument) := by
  refine ⟨fun argument parameter => (continues.1 argument parameter).const_smul scalar, ?_⟩
  obtain ⟨threshold, integrals⟩ := continues.2
  refine ⟨threshold, ?_⟩
  intro parameter membership argument
  obtain ⟨integrable, equality⟩ := integrals parameter membership argument
  refine ⟨integrable.const_mul scalar, ?_⟩
  change scalar * continuation parameter argument =
    ∫ radical, scalar * standardIntegrand extension parameter argument radical ∂radicalMeasure
  rw [integral_const_mul, equality]

theorem eisensteinContinuation_sub (firstExtension secondExtension first second :
    ℂ → AdelicGL → ℂ)
    (firstContinuation : IsEisensteinContinuation firstExtension first)
    (secondContinuation : IsEisensteinContinuation secondExtension second) :
    IsEisensteinContinuation
      (fun parameter argument => firstExtension parameter argument -
        secondExtension parameter argument)
      (fun parameter argument => first parameter argument - second parameter argument) := by
  refine ⟨fun argument parameter => (firstContinuation.1 argument parameter).sub
    (secondContinuation.1 argument parameter), ?_⟩
  obtain ⟨firstThreshold, firstSum⟩ := firstContinuation.2
  obtain ⟨secondThreshold, secondSum⟩ := secondContinuation.2
  refine ⟨max firstThreshold secondThreshold, ?_⟩
  intro parameter membership argument
  exact (firstSum parameter (lt_of_le_of_lt (le_max_left _ _) membership) argument).sub
    (secondSum parameter (lt_of_le_of_lt (le_max_right _ _) membership) argument)

theorem standardContinuation_sub (firstExtension secondExtension first second :
    ℂ → AdelicGL → ℂ)
    (firstContinuation : IsStandardContinuation firstExtension first)
    (secondContinuation : IsStandardContinuation secondExtension second) :
    IsStandardContinuation
      (fun parameter argument => firstExtension parameter argument -
        secondExtension parameter argument)
      (fun parameter argument => first parameter argument - second parameter argument) := by
  refine ⟨fun argument parameter => (firstContinuation.1 argument parameter).sub
    (secondContinuation.1 argument parameter), ?_⟩
  obtain ⟨firstThreshold, firstIntegral⟩ := firstContinuation.2
  obtain ⟨secondThreshold, secondIntegral⟩ := secondContinuation.2
  refine ⟨max firstThreshold secondThreshold, ?_⟩
  intro parameter membership argument
  obtain ⟨firstIntegrable, firstEquality⟩ := firstIntegral parameter
    (lt_of_le_of_lt (le_max_left _ _) membership) argument
  obtain ⟨secondIntegrable, secondEquality⟩ := secondIntegral parameter
    (lt_of_le_of_lt (le_max_right _ _) membership) argument
  refine ⟨firstIntegrable.sub secondIntegrable, ?_⟩
  change first parameter argument - second parameter argument =
    ∫ radical, standardIntegrand firstExtension parameter argument radical -
      standardIntegrand secondExtension parameter argument radical ∂radicalMeasure
  rw [integral_sub firstIntegrable secondIntegrable, firstEquality, secondEquality]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LinearFamilies
