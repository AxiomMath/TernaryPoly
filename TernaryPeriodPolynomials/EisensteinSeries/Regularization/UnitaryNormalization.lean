module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Norm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

/-- Shift to the unitary inducing parameter and remove the fixed central norm character. -/
noncomputable def unitaryNormalize (degree : ℕ) (family : ℂ → AdelicGL → ℂ) :
    ℂ → AdelicGL → ℂ := fun parameter groupElement =>
  normPower (GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) *
    family (parameter - ((degree : ℂ) + 3) / 2) groupElement

theorem unitaryPoint_shift (degree : ℕ) :
    (degree : ℂ) / 2 - ((degree : ℂ) + 3) / 2 = cohomologicalPoint := by
  rw [cohomologicalPoint]
  ring

theorem unitaryPoint_positive {degree : ℕ} (degree_positive : 0 < degree) :
    0 < ((degree : ℂ) / 2).re := by
  have degree_real_positive : 0 < (degree : ℝ) := by exact_mod_cast degree_positive
  simpa using div_pos degree_real_positive (by norm_num : (0 : ℝ) < 2)

theorem unitaryNormalize_order (degree : ℕ) (family : ℂ → AdelicGL → ℂ)
    (groupElement : AdelicGL) :
    meromorphicOrderAt (fun parameter => unitaryNormalize degree family parameter groupElement)
        ((degree : ℂ) / 2) =
      meromorphicOrderAt (fun parameter => family parameter groupElement) cohomologicalPoint := by
  unfold unitaryNormalize
  change meromorphicOrderAt
    ((fun _ => normPower (GeneralLinearGroup.det groupElement)
      (-((degree : ℂ) + 3) / 3)) *
      (fun parameter => family (parameter - ((degree : ℂ) + 3) / 2) groupElement)) _ = _
  rw [meromorphicOrderAt_mul_of_ne_zero analyticAt_const (normPower_ne_zero _ _),
    meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt
      (f := fun parameter => family parameter groupElement), unitaryPoint_shift]

theorem unitaryNormalize_meromorphic (degree : ℕ)
    {family : ℂ → AdelicGL → ℂ}
    (family_meromorphic : ∀ groupElement parameter,
      MeromorphicAt (fun nearbyParameter => family nearbyParameter groupElement) parameter)
    (groupElement : AdelicGL) (parameter : ℂ) :
    MeromorphicAt (fun nearbyParameter => unitaryNormalize degree family
      nearbyParameter groupElement) parameter := by
  apply MeromorphicAt.mul (MeromorphicAt.const _ _)
  exact (family_meromorphic groupElement _).comp_analyticAt
    (analyticAt_id.sub analyticAt_const)

theorem unitaryNormalize_analytic (degree : ℕ)
    {family : ℂ → AdelicGL → ℂ}
    (family_analytic : ∀ groupElement parameter,
      AnalyticAt ℂ (fun nearbyParameter => family nearbyParameter groupElement) parameter)
    (groupElement : AdelicGL) (parameter : ℂ) :
    AnalyticAt ℂ (fun nearbyParameter => unitaryNormalize degree family
      nearbyParameter groupElement) parameter := by
  apply AnalyticAt.mul analyticAt_const
  exact (family_analytic groupElement _).comp
    (analyticAt_id.sub analyticAt_const)

theorem det_planeLevi (binaryMatrix : BinaryAdelicGL) (idele : Adelesˣ) :
    GeneralLinearGroup.det (planeLevi binaryMatrix idele) =
      GeneralLinearGroup.det binaryMatrix * idele := by
  apply Units.ext
  change (planeBlock binaryMatrix.val idele.val).det = binaryMatrix.val.det * idele.val
  simp [planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem unitaryNormalize_central
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (family_induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (idele : Adelesˣ) (groupElement : AdelicGL) :
    unitaryNormalize degree family parameter
        (GeneralLinearGroup.scalar (Fin 3) idele * groupElement) =
      inducingData.chi.toMonoidHom idele * inducingData.cusp.centralCharacter idele *
        unitaryNormalize degree family parameter groupElement := by
  simp only [unitaryNormalize, map_mul, GeneralLinearGroup.det_scalar,
    Fintype.card_fin, normPower_mul, normPower_pow,
    induced_central_character (family_induced _)]
  have cancel_exponents : (3 : ℂ) * (-((degree : ℂ) + 3) / 3) +
      ((degree : ℂ) + 3) = 0 := by ring
  have cancel_powers :
      normPower idele ((3 : ℂ) * (-((degree : ℂ) + 3) / 3)) *
        normPower idele ((degree : ℂ) + 3) = 1 := by
    rw [← normPower_add, cancel_exponents, normPower_zero]
  calc
    _ = (normPower idele ((3 : ℂ) * (-((degree : ℂ) + 3) / 3)) *
          normPower idele ((degree : ℂ) + 3)) *
        (inducingData.chi.toMonoidHom idele * inducingData.cusp.centralCharacter idele *
          (normPower (GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) *
            family (parameter - ((degree : ℂ) + 3) / 2) groupElement)) := by
      push_cast
      ring
    _ = _ := by rw [cancel_powers, one_mul]

theorem unitaryNormalize_rankOne
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (family_induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (idele : Adelesˣ) (groupElement : AdelicGL) :
    unitaryNormalize degree family parameter (planeLevi 1 idele * groupElement) =
      inducingData.chi.toMonoidHom idele * normPower idele (-2 * inductionExponent .plane parameter) *
        unitaryNormalize degree family parameter groupElement := by
  simp only [unitaryNormalize, map_mul, det_planeLevi, map_one, one_mul, normPower_mul,
    (family_induced _).2.2.2.2.1]
  have exponents : -((degree : ℂ) + 3) / 3 +
      -2 * inductionExponent .plane (parameter - ((degree : ℂ) + 3) / 2) =
      -2 * inductionExponent .plane parameter := by
    simp only [inductionExponent]
    ring
  calc
    _ = inducingData.chi.toMonoidHom idele *
        (normPower idele (-((degree : ℂ) + 3) / 3) *
          normPower idele (-2 * inductionExponent .plane
            (parameter - ((degree : ℂ) + 3) / 2))) *
        (normPower (GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) *
          family (parameter - ((degree : ℂ) + 3) / 2) groupElement) := by ring
    _ = _ := by rw [← normPower_add, exponents]

theorem unitaryNormalize_central_norm
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (family_induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (idele : Adelesˣ) (groupElement : AdelicGL) :
    ‖unitaryNormalize degree family parameter
        (GeneralLinearGroup.scalar (Fin 3) idele * groupElement)‖ =
      ‖unitaryNormalize degree family parameter groupElement‖ := by
  rw [unitaryNormalize_central family_induced, norm_mul, norm_mul,
    inducingData.chi.unitary, inducingData.cusp.centralUnitary, one_mul, one_mul]

theorem unitaryNormalize_binary_orbit_value
    (degree : ℕ) (family : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (binaryMatrix : BinaryAdelicGL) (groupElement : AdelicGL) :
    normPower (GeneralLinearGroup.det binaryMatrix) (-inductionExponent .plane parameter) *
        unitaryNormalize degree family parameter (planeLevi binaryMatrix 1 * groupElement) =
      normPower (GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) *
        (normPower (GeneralLinearGroup.det binaryMatrix)
            (-binaryInductionExponent degree .plane (parameter - ((degree : ℂ) + 3) / 2)) *
          family (parameter - ((degree : ℂ) + 3) / 2) (planeLevi binaryMatrix 1 * groupElement)) := by
  simp only [unitaryNormalize, map_mul, det_planeLevi, mul_one, normPower_mul]
  have exponents : -inductionExponent .plane parameter + -((degree : ℂ) + 3) / 3 =
      -binaryInductionExponent degree .plane (parameter - ((degree : ℂ) + 3) / 2) := by
    simp only [binaryInductionExponent, inductionExponent]
    ring
  calc
    _ = normPower (GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) *
        ((normPower (GeneralLinearGroup.det binaryMatrix) (-inductionExponent .plane parameter) *
            normPower (GeneralLinearGroup.det binaryMatrix) (-((degree : ℂ) + 3) / 3)) *
          family (parameter - ((degree : ℂ) + 3) / 2)
            (planeLevi binaryMatrix 1 * groupElement)) := by ring
    _ = _ := by rw [← normPower_add, exponents]

theorem unitaryNormalize_binary_orbit
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (family_induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (groupElement : AdelicGL) :
    (fun binaryMatrix : BinaryAdelicGL =>
      normPower (GeneralLinearGroup.det binaryMatrix) (-inductionExponent .plane parameter) *
        unitaryNormalize degree family parameter (planeLevi binaryMatrix 1 * groupElement)) ∈
      cuspFunctions inducingData.cusp := by
  have orbit := (family_induced
    (parameter - ((degree : ℂ) + 3) / 2)).2.2.2.2.2 groupElement
  have values_equal :
      (fun binaryMatrix : BinaryAdelicGL =>
        normPower (GeneralLinearGroup.det binaryMatrix) (-inductionExponent .plane parameter) *
          unitaryNormalize degree family parameter (planeLevi binaryMatrix 1 * groupElement)) =
        normPower (GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) •
          (fun binaryMatrix : BinaryAdelicGL =>
            normPower (GeneralLinearGroup.det binaryMatrix)
                (-binaryInductionExponent degree .plane
                  (parameter - ((degree : ℂ) + 3) / 2)) *
              family (parameter - ((degree : ℂ) + 3) / 2)
                (planeLevi binaryMatrix 1 * groupElement)) := by
    funext binaryMatrix
    exact unitaryNormalize_binary_orbit_value degree family parameter binaryMatrix groupElement
  rw [values_equal]
  exact (cuspFunctions inducingData.cusp).smul_mem _ orbit

theorem unitaryNormalize_compact_orbit
    (degree : ℕ) (family : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (binaryMatrix : BinaryAdelicGL) (compactElement : AdelicGL)
    (compact_spec : inMaximalCompact compactElement) :
    normPower (GeneralLinearGroup.det binaryMatrix) (-inductionExponent .plane parameter) *
        unitaryNormalize degree family parameter (planeLevi binaryMatrix 1 * compactElement) =
      normPower (GeneralLinearGroup.det binaryMatrix)
          (-binaryInductionExponent degree .plane (parameter - ((degree : ℂ) + 3) / 2)) *
        family (parameter - ((degree : ℂ) + 3) / 2)
          (planeLevi binaryMatrix 1 * compactElement) := by
  rw [unitaryNormalize_binary_orbit_value,
    normPower_det_compact compactElement compact_spec, one_mul]

theorem unitaryNormalize_flat_compact_orbit
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData family)
    (parameter : ℂ) (binaryMatrix : BinaryAdelicGL) (compactElement : AdelicGL)
    (compact_spec : inMaximalCompact compactElement) :
    normPower (GeneralLinearGroup.det binaryMatrix) (-inductionExponent .plane parameter) *
        unitaryNormalize degree family parameter (planeLevi binaryMatrix 1 * compactElement) =
      normPower (GeneralLinearGroup.det binaryMatrix)
          (-inductionExponent .plane ((degree : ℂ) / 2)) *
        unitaryNormalize degree family ((degree : ℂ) / 2)
          (planeLevi binaryMatrix 1 * compactElement) := by
  rw [unitaryNormalize_compact_orbit degree family parameter binaryMatrix compactElement compact_spec,
    unitaryNormalize_compact_orbit degree family _ binaryMatrix compactElement compact_spec,
    unitaryPoint_shift]
  exact flat_family.2.2 _ binaryMatrix compactElement compact_spec

theorem det_planeUnipotent (first second : Adeles) :
    GeneralLinearGroup.det (planeUnipotent first second) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, planeUnipotent, Matrix.det_fin_three]

theorem unitaryNormalize_unipotent
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (family_induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (first second : Adeles) (groupElement : AdelicGL) :
    unitaryNormalize degree family parameter (planeUnipotent first second * groupElement) =
      unitaryNormalize degree family parameter groupElement := by
  simp only [unitaryNormalize, map_mul, det_planeUnipotent, one_mul,
    (family_induced _).2.2.2.1]

theorem unitaryNormalize_finite_level
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (family_induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (levelElement : finiteLevel) (groupElement : AdelicGL) :
    unitaryNormalize degree family parameter (groupElement * atFinite levelElement.val) =
      unitaryNormalize degree family parameter groupElement := by
  simp only [unitaryNormalize, map_mul, normPower_mul,
    normPower_det_compact _ (atFinite_level_compact levelElement), mul_one,
    (family_induced _).2.1 levelElement]

theorem unitaryNormalize_summand (degree : ℕ) (family : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (groupElement : AdelicGL) (flag : Flags .plane) :
    eisensteinSummand (unitaryNormalize degree family) parameter groupElement flag =
      normPower (Units.map rationalAdele (GeneralLinearGroup.det flag.out⁻¹))
          (-((degree : ℂ) + 3) / 3) *
        normPower (GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) *
        eisensteinSummand family (parameter - ((degree : ℂ) + 3) / 2) groupElement flag := by
  simp only [eisensteinSummand, unitaryNormalize, map_mul, rationalGroup,
    GeneralLinearGroup.map_det, normPower_mul]

theorem regularization_of_unitaryNormalize_order
    {degree : ℕ} {family continuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsEisensteinContinuation family continuation)
    (nonnegative_order : ∀ groupElement,
      0 ≤ meromorphicOrderAt
        (fun parameter => unitaryNormalize degree continuation parameter groupElement)
        ((degree : ℂ) / 2)) :
    ∃ repaired : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation family repaired ∧
        SameOffCohomologicalPoint continuation repaired ∧
        ∀ groupElement,
          AnalyticAt ℂ (fun parameter => repaired parameter groupElement) cohomologicalPoint := by
  apply regularization_of_nonnegative_order continuation_spec
  intro groupElement
  rw [← unitaryNormalize_order degree continuation groupElement]
  exact nonnegative_order groupElement

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
