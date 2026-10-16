module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rational.Invariance
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Bounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel

theorem atFinite_mul {size : ℕ}
    (first second : Matrix.GeneralLinearGroup (Fin size) FiniteAdeles) :
    atFinite (first * second) = atFinite first * atFinite second := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · simp only [Units.val_mul, atFinite, combineGL, pairMatrix, Matrix.mul_apply,
      Prod.fst_sum, Prod.fst_mul]
    exact (congrArg (fun matrix : Matrix (Fin size) (Fin size) ℝ => matrix row column)
      (one_mul (1 : Matrix (Fin size) (Fin size) ℝ))).symm
  · simp only [Units.val_mul, atFinite, combineGL, pairMatrix, Matrix.mul_apply,
      Prod.snd_sum, Prod.snd_mul]

theorem atFinite_atInfinity_commute {size : ℕ}
    (finiteMatrix : Matrix.GeneralLinearGroup (Fin size) FiniteAdeles)
    (realMatrix : Matrix.GeneralLinearGroup (Fin size) ℝ) :
    atFinite finiteMatrix * atInfinity realMatrix =
      atInfinity realMatrix * atFinite finiteMatrix := by
  rw [← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.combineGL_eq_mul]
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · simp only [Units.val_mul, atFinite, atInfinity, combineGL, pairMatrix, Matrix.mul_apply,
      Prod.fst_sum, Prod.fst_mul]
    exact congrArg (fun matrix : Matrix (Fin size) (Fin size) ℝ => matrix row column)
      (one_mul realMatrix.val)
  · simp only [Units.val_mul, atFinite, atInfinity, combineGL, pairMatrix, Matrix.mul_apply,
      Prod.snd_sum, Prod.snd_mul]
    exact congrArg (fun matrix : Matrix (Fin size) (Fin size) FiniteAdeles => matrix row column)
      (mul_one finiteMatrix.val)

theorem integralFinite_eq_map (matrix : IntegralGL3) :
    integralFinite matrix = Matrix.GeneralLinearGroup.map integralEmbedding
      (Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) matrix) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  change (algebraMap ℚ FiniteAdeles) (matrix.val row column : ℚ) =
    integralEmbedding (matrix.val row column : IntegralAdeles)
  simp

theorem integralGroup_eq_mul (matrix : IntegralGL3) :
    rationalGroup (integralRational matrix) =
      atInfinity (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) *
        atFinite (integralFinite matrix) := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul (rationalGroup (integralRational matrix))]
  congr 1

theorem integralReduction_eq (matrix : IntegralGL3) :
    Matrix.GeneralLinearGroup.map integralReduction
      (Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) matrix) =
      reductionThree matrix := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  exact integralReduction_int (matrix.val row column)

theorem integralFinite_mem_level (matrix : IntegralGL3)
    (levelMembership : matrix ∈ arithmeticLevel) : integralFinite matrix ∈ finiteLevel := by
  refine ⟨Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) matrix, ?_, ?_⟩
  · change Matrix.GeneralLinearGroup.map integralReduction
      (Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) matrix) ∈ rowStabilizer
    rw [integralReduction_eq]
    exact levelMembership
  · exact (integralFinite_eq_map matrix).symm

theorem same_reduction_mem_level (first second : IntegralGL3)
    (sameReduction : reductionThree first = reductionThree second) :
    integralFinite (first⁻¹ * second) ∈ finiteLevel := by
  apply integralFinite_mem_level
  change reductionThree (first⁻¹ * second) ∈ rowStabilizer
  rw [map_mul, map_inv, sameReduction, inv_mul_cancel]
  exact rowStabilizer.one_mem

theorem planeCuspVector_same_reduction {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (basePoint : AdelicGL) (first second : IntegralGL3)
    (sameReduction : reductionThree first = reductionThree second) :
    planeCuspVector inducedSection (basePoint * atFinite (integralFinite first)) =
      planeCuspVector inducedSection (basePoint * atFinite (integralFinite second)) := by
  have invariance := planeCuspVector_finiteLevel inducedSection
    (basePoint * atFinite (integralFinite first))
    ⟨integralFinite (first⁻¹ * second), same_reduction_mem_level first second sameReduction⟩
  change planeCuspVector inducedSection ((basePoint * atFinite (integralFinite first)) *
    atFinite (integralFinite (first⁻¹ * second))) = _ at invariance
  rw [mul_assoc, ← atFinite_mul, ← map_mul, mul_inv_cancel_left] at invariance
  exact invariance.symm

noncomputable def residueRepresentative (residue : Set.range reductionThree) : IntegralGL3 :=
  Classical.choose residue.property

theorem residueRepresentative_reduction (residue : Set.range reductionThree) :
    reductionThree (residueRepresentative residue) = residue.val :=
  Classical.choose_spec residue.property

theorem exists_finite_representatives :
    ∃ representatives : Set IntegralGL3, representatives.Finite ∧
      ∀ matrix : IntegralGL3, ∃ representative ∈ representatives,
        reductionThree representative = reductionThree matrix := by
  refine ⟨Set.range residueRepresentative, Set.finite_range _, fun matrix => ?_⟩
  let residue : Set.range reductionThree := ⟨reductionThree matrix, matrix, rfl⟩
  exact ⟨residueRepresentative residue, ⟨residue, rfl⟩, residueRepresentative_reduction residue⟩

theorem orthogonal_integral_compact (realMatrix : RealGL3)
    (orthogonality : realMatrix.val.transpose * realMatrix.val = 1)
    (integralMatrix : IntegralGL3) :
    inMaximalCompact (atInfinity realMatrix * atFinite (integralFinite integralMatrix)) := by
  rw [← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.combineGL_eq_mul]
  refine ⟨orthogonality,
    Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integralMatrix, ?_⟩
  exact (integralFinite_eq_map integralMatrix).symm

theorem flatSection_compact_cuspVector_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 → ∀ integralMatrix : IntegralGL3,
      ‖(planeCuspVector (flatSection.1 parameter)
        (atInfinity realMatrix * atFinite (integralFinite integralMatrix))).val‖ ≤ bound := by
  classical
  obtain ⟨representatives, finiteRepresentatives, representativeProperty⟩ :=
    exists_finite_representatives
  let : Fintype representatives := finiteRepresentatives.fintype
  have pointwiseBounds (representative : representatives) :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Compact.planeCuspVector_bound_on_orthogonal (flatSection.1 cohomologicalPoint)
      (atFinite (integralFinite representative.val))
  choose bounds nonnegativeBounds boundProperty using pointwiseBounds
  refine ⟨∑ representative, bounds representative,
    Finset.sum_nonneg (fun representative _ => nonnegativeBounds representative),
    fun parameter realMatrix orthogonality integralMatrix => ?_⟩
  obtain ⟨representative, membership, sameReduction⟩ := representativeProperty integralMatrix
  let chosen : representatives := ⟨representative, membership⟩
  rw [← planeCuspVector_same_reduction (flatSection.1 parameter) (atInfinity realMatrix)
    representative integralMatrix sameReduction,
    flatSection_planeCuspVector_eq flatSection parameter _
      (orthogonal_integral_compact realMatrix orthogonality representative),
    ← atFinite_atInfinity_commute]
  exact (boundProperty chosen realMatrix orthogonality).trans
    (Finset.single_le_sum (fun representative _ => nonnegativeBounds representative)
      (Finset.mem_univ chosen))

abbrev IntegralFiniteGL := Matrix.GeneralLinearGroup (Fin 3) IntegralAdeles

theorem same_integralReduction_mem_level (first second : IntegralFiniteGL)
    (sameReduction : Matrix.GeneralLinearGroup.map integralReduction first =
      Matrix.GeneralLinearGroup.map integralReduction second) :
    Matrix.GeneralLinearGroup.map integralEmbedding (first⁻¹ * second) ∈ finiteLevel := by
  refine ⟨first⁻¹ * second, ?_, rfl⟩
  change Matrix.GeneralLinearGroup.map integralReduction (first⁻¹ * second) ∈ rowStabilizer
  rw [map_mul, map_inv, sameReduction, inv_mul_cancel]
  exact rowStabilizer.one_mem

theorem planeCuspVector_same_integralReduction {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (basePoint : AdelicGL) (first second : IntegralFiniteGL)
    (sameReduction : Matrix.GeneralLinearGroup.map integralReduction first =
      Matrix.GeneralLinearGroup.map integralReduction second) :
    planeCuspVector inducedSection
        (basePoint * atFinite (Matrix.GeneralLinearGroup.map integralEmbedding first)) =
      planeCuspVector inducedSection
        (basePoint * atFinite (Matrix.GeneralLinearGroup.map integralEmbedding second)) := by
  have invariance := planeCuspVector_finiteLevel inducedSection
    (basePoint * atFinite (Matrix.GeneralLinearGroup.map integralEmbedding first))
    ⟨Matrix.GeneralLinearGroup.map integralEmbedding (first⁻¹ * second),
      same_integralReduction_mem_level first second sameReduction⟩
  change planeCuspVector inducedSection
    ((basePoint * atFinite (Matrix.GeneralLinearGroup.map integralEmbedding first)) *
      atFinite (Matrix.GeneralLinearGroup.map integralEmbedding (first⁻¹ * second))) = _ at invariance
  rw [mul_assoc, ← atFinite_mul, ← map_mul, mul_inv_cancel_left] at invariance
  exact invariance.symm

noncomputable def integralResidueRepresentative
    (residue : Set.range (Matrix.GeneralLinearGroup.map integralReduction (n := Fin 3))) : IntegralFiniteGL :=
  Classical.choose residue.property

theorem integralResidueRepresentative_reduction
    (residue : Set.range (Matrix.GeneralLinearGroup.map integralReduction (n := Fin 3))) :
    Matrix.GeneralLinearGroup.map integralReduction (integralResidueRepresentative residue) =
      residue.val := Classical.choose_spec residue.property

theorem flatSection_integralCompact_cuspVector_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 → ∀ integralMatrix : IntegralFiniteGL,
      ‖(planeCuspVector (flatSection.1 parameter)
        (atInfinity realMatrix * atFinite
          (Matrix.GeneralLinearGroup.map integralEmbedding integralMatrix))).val‖ ≤ bound := by
  classical
  let residues := Set.range (Matrix.GeneralLinearGroup.map integralReduction (n := Fin 3))
  let : Fintype residues := Fintype.ofFinite residues
  have pointwiseBounds (residue : residues) :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Compact.planeCuspVector_bound_on_orthogonal (flatSection.1 cohomologicalPoint)
      (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding (integralResidueRepresentative residue)))
  choose bounds nonnegativeBounds boundProperty using pointwiseBounds
  refine ⟨∑ residue, bounds residue,
    Finset.sum_nonneg (fun residue _ => nonnegativeBounds residue),
    fun parameter realMatrix orthogonality integralMatrix => ?_⟩
  let residue : residues :=
    ⟨Matrix.GeneralLinearGroup.map integralReduction integralMatrix, integralMatrix, rfl⟩
  let representative := integralResidueRepresentative residue
  have sameReduction : Matrix.GeneralLinearGroup.map integralReduction representative =
      Matrix.GeneralLinearGroup.map integralReduction integralMatrix :=
    integralResidueRepresentative_reduction residue
  have compactness : inMaximalCompact (atInfinity realMatrix *
      atFinite (Matrix.GeneralLinearGroup.map integralEmbedding representative)) := by
    rw [← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.combineGL_eq_mul]
    exact ⟨orthogonality, representative, rfl⟩
  rw [← planeCuspVector_same_integralReduction (flatSection.1 parameter) (atInfinity realMatrix)
    representative integralMatrix sameReduction,
    flatSection_planeCuspVector_eq flatSection parameter _ compactness,
    ← atFinite_atInfinity_commute]
  exact (boundProperty residue realMatrix orthogonality).trans
    (Finset.single_le_sum (fun residue _ => nonnegativeBounds residue) (Finset.mem_univ residue))

theorem flatSection_maximalCompact_cuspVector_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ compactElement : AdelicGL,
      inMaximalCompact compactElement →
      ‖(planeCuspVector (flatSection.1 parameter) compactElement).val‖ ≤ bound := by
  obtain ⟨bound, nonnegativeBound, integralBound⟩ :=
    flatSection_integralCompact_cuspVector_bound flatSection
  refine ⟨bound, nonnegativeBound, fun parameter compactElement compactness => ?_⟩
  obtain ⟨integralMatrix, finiteEquality⟩ := compactness.2
  have boundProperty := integralBound parameter (realGroup compactElement) compactness.1 integralMatrix
  rw [finiteEquality, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul] at boundProperty
  exact boundProperty

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
