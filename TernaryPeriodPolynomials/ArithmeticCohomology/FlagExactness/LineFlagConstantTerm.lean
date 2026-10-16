module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.FlagConstantTerm
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.LineRadicalEquivariance

@[expose] public section


/-!
# Real constant terms of line source cocycles at rational flags

Line-side analogue of `flag_real_constant_term`. Let `c` be a line source cocycle
and `q` a rational flag representative. For a suitable `M > 0`, every coefficient
of `c(x)(n'(M t) · q⁻¹)` has vanishing integral over `t ∈ [0,1)`. Here `n'` is the
unipotent of the `GL₂` block of the line Levi, with real coordinate only.

The adelic inputs are line versions of the plane facts of
`Proofs/EisensteinRegularization`: cuspidality, rational automorphy and
rational periodicity of line-induced sections along the line Levi unipotent.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

theorem lineLevi_binary_mul {R : Type*} [CommRing R]
    (first second : GeneralLinearGroup (Fin 2) R) :
    lineLevi 1 (first * second) = lineLevi 1 first * lineLevi 1 second := by
  change (lineLeviHom R) (1, first * second) =
    (lineLeviHom R) (1, first) * (lineLeviHom R) (1, second)
  simpa only [Prod.mk_mul_mk, one_mul] using (lineLeviHom R).map_mul (1, first) (1, second)

theorem lineLevi_one_one {R : Type*} [CommRing R] :
    lineLevi (1 : Rˣ) (1 : GeneralLinearGroup (Fin 2) R) = 1 :=
  (lineLeviHom R).map_one

/-- Cuspidality of line-induced sections along the line Levi unipotent. -/
theorem induced_line_unipotent_cuspidal
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .line parameter sectionValue)
    (groupElement : AdelicGL) :
    IntegrableOn (fun coordinate =>
      sectionValue (lineLevi 1 (binaryUnipotent coordinate) * groupElement))
      additiveDomain adeleMeasure ∧
    (∫ coordinate in additiveDomain,
      sectionValue (lineLevi 1 (binaryUnipotent coordinate) * groupElement)
        ∂adeleMeasure) = 0 := by
  obtain ⟨vector, realized⟩ := induced.2.2.2.2.2 groupElement
  have orbit_value : (fun coordinate =>
      sectionValue (lineLevi 1 (binaryUnipotent coordinate) * groupElement)) =
      (fun coordinate => inducingData.cusp.realize vector (binaryUnipotent coordinate * 1)) := by
    funext coordinate
    have value := congrFun realized (binaryUnipotent coordinate)
    simpa only [det_binaryUnipotent, normPower_one, one_mul, mul_one] using value.symm
  rw [orbit_value]
  exact inducingData.cusp.cuspidal vector 1

/-- Rational automorphy of line-induced sections in the `GL₂` block. -/
theorem induced_line_rational
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .line parameter sectionValue)
    (rationalMatrix : BinaryRationalGL) (groupElement : AdelicGL) :
    sectionValue (lineLevi 1 (GeneralLinearGroup.map rationalAdele rationalMatrix) *
      groupElement) = sectionValue groupElement := by
  obtain ⟨vector, realized⟩ := induced.2.2.2.2.2 groupElement
  have rational_value := congrFun realized (GeneralLinearGroup.map rationalAdele rationalMatrix)
  have identity_value := congrFun realized (1 : BinaryAdelicGL)
  have rational_invariance := inducingData.cusp.leftRational rationalMatrix vector 1
  rw [mul_one] at rational_invariance
  rw [rational_invariance, GeneralLinearGroup.map_det, normPower_rational,
    one_mul] at rational_value
  rw [map_one, normPower_one, one_mul, lineLevi_one_one, one_mul] at identity_value
  exact rational_value.symm.trans identity_value

theorem induced_line_unipotent_periodic
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .line parameter sectionValue)
    (groupElement : AdelicGL) (rational : ℚ) (coordinate : Adeles) :
    sectionValue (lineLevi 1 (binaryUnipotent (rationalAdele rational + coordinate)) * groupElement) =
      sectionValue (lineLevi 1 (binaryUnipotent coordinate) * groupElement) := by
  rw [binaryUnipotent_add, lineLevi_binary_mul, mul_assoc, ← map_binaryUnipotent rationalAdele]
  exact induced_line_rational induced (binaryUnipotent rational) _

/-- The real constant term along `n'(M t)` vanishes once the integrand is `M·Ẑ`-invariant. -/
theorem induced_line_real_constant_term {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .line parameter sectionValue)
    (groupElement : AdelicGL) (M : ℕ) (positive : 0 < M)
    (finiteInvariant : ∀ (t : ℝ) (z : FiniteAdeles), z ∈ Set.range integralEmbedding →
      sectionValue (lineLevi 1 (binaryUnipotent ((t, (M : FiniteAdeles) * z) : Adeles)) * groupElement) =
        sectionValue (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * groupElement))
    (measurable : Measurable (fun t : ℝ =>
      sectionValue (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * groupElement))) :
    (∫ t in Set.Ico (0 : ℝ) 1,
      sectionValue (lineLevi 1 (binaryUnipotent ((((M : ℝ) * t), 0) : Adeles)) * groupElement)) = 0 := by
  set F : ℝ → ℂ := fun t =>
    sectionValue (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * groupElement)
  have cusp := (induced_line_unipotent_cuspidal induced groupElement).2
  have scaled := adele_periodic_integral_rational_scaling
    (fun coordinate => sectionValue (lineLevi 1 (binaryUnipotent coordinate) * groupElement))
    (induced_line_unipotent_periodic induced groupElement) (Units.mk0 (M : ℚ) (by exact_mod_cast positive.ne'))
  rw [cusp] at scaled
  have measurable_domain : MeasurableSet additiveDomain :=
    measurableSet_Ico.prod integralLattice_isCompact.measurableSet
  have pointwise : ∀ value ∈ additiveDomain,
      sectionValue (lineLevi 1 (binaryUnipotent
        (rationalAdele (Units.mk0 (M : ℚ) (by exact_mod_cast positive.ne')).val * value)) * groupElement) =
      F ((M : ℝ) * value.1) := by
    intro value member
    have hvalue : rationalAdele (Units.mk0 (M : ℚ) (by exact_mod_cast positive.ne')).val * value =
        (((M : ℝ) * value.1, (M : FiniteAdeles) * value.2) : Adeles) := by
      apply Prod.ext
      · simp
      · simp
    rw [hvalue]
    exact finiteInvariant _ value.2 member.2
  have hcongr : (∫ value in additiveDomain, sectionValue (lineLevi 1 (binaryUnipotent
        (rationalAdele (Units.mk0 (M : ℚ) (by exact_mod_cast positive.ne')).val * value)) * groupElement)
          ∂adeleMeasure) =
      ∫ value in additiveDomain, F ((M : ℝ) * value.1) ∂adeleMeasure :=
    setIntegral_congr_fun measurable_domain pointwise
  rw [hcongr] at scaled
  have hmeas : Measurable (fun t : ℝ => F ((M : ℝ) * t)) :=
    measurable.comp (measurable_const.mul measurable_id)
  have projection := integral_map additiveDomain_real_projection.measurable.aemeasurable
    (hmeas.aestronglyMeasurable (μ := Measure.map (Prod.fst : Adeles → ℝ)
      (adeleMeasure.restrict additiveDomain)))
  rw [additiveDomain_real_projection.map_eq] at projection
  rw [← projection] at scaled
  exact scaled

/-- The elementary matrix of the line Levi unipotent. -/
def lineLeviNilpotent (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 0; 0, 0, 1; 0, 0, 0]

theorem lineLeviNilpotent_sq (R : Type*) [CommRing R] :
    lineLeviNilpotent R * lineLeviNilpotent R = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lineLeviNilpotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem lineLeviNilpotent_map :
    (lineLeviNilpotent ℚ).map (algebraMap ℚ FiniteAdeles) = lineLeviNilpotent FiniteAdeles := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lineLeviNilpotent]

theorem lineLevi_binaryUnipotent_val {R : Type*} [CommRing R] (w : R) :
    (lineLevi 1 (binaryUnipotent w)).val = 1 + w • lineLeviNilpotent R := by
  rw [lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryUnipotent, lineLeviNilpotent]

/-- The conjugated nilpotent `q E' q⁻¹`. -/
def lineFlagNilpotent (q : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ :=
  q.val * lineLeviNilpotent ℚ * (q⁻¹).val

theorem lineFlagNilpotent_sq (q : RationalGL3) : lineFlagNilpotent q * lineFlagNilpotent q = 0 := by
  have hinv : (q⁻¹).val * q.val = 1 := by
    rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
  unfold lineFlagNilpotent
  calc q.val * lineLeviNilpotent ℚ * (q⁻¹).val * (q.val * lineLeviNilpotent ℚ * (q⁻¹).val)
      = q.val * lineLeviNilpotent ℚ * ((q⁻¹).val * q.val) * lineLeviNilpotent ℚ * (q⁻¹).val := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by
        rw [hinv, Matrix.mul_one, Matrix.mul_assoc q.val, lineLeviNilpotent_sq, Matrix.mul_zero,
          Matrix.zero_mul]

theorem lineLeviUnipotent_continuous :
    Continuous (fun a : Adeles => lineLevi 1 (binaryUnipotent a)) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column <;>
    fin_cases row <;> fin_cases column <;>
    simp [lineLevi, planeLevi, planeBlock, weyl, binaryUnipotent, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    first | fun_prop | exact ⟨by fun_prop, by fun_prop⟩

/-- The finite line unipotent at a rational flag, conjugated to the right. -/
theorem lineLevi_finite_mul_rationalGroup (q : RationalGL3) (w : FiniteAdeles)
    (h : (w • (lineFlagNilpotent q).map (algebraMap ℚ FiniteAdeles)) *
      (w • (lineFlagNilpotent q).map (algebraMap ℚ FiniteAdeles)) = 0) :
    lineLevi 1 (binaryUnipotent (((0 : ℝ), w) : Adeles)) * rationalGroup q⁻¹ =
      rationalGroup q⁻¹ * atFinite (unipotentUnit _ h) := by
  apply adelic_ext
  · have hreal : realGroup (lineLevi 1 (binaryUnipotent (((0 : ℝ), w) : Adeles))) = 1 := by
      apply Units.ext
      change (lineLevi 1 (binaryUnipotent (((0 : ℝ), w) : Adeles))).val.map Prod.fst = 1
      rw [lineLevi_binaryUnipotent_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lineLeviNilpotent]
    have hfin : realGroup (atFinite (unipotentUnit _ h)) = 1 := by
      apply Units.ext
      rfl
    rw [realGroup.map_mul, realGroup.map_mul, hreal, hfin, one_mul, mul_one]
  · have hline : finiteGroup (lineLevi 1 (binaryUnipotent (((0 : ℝ), w) : Adeles))) =
        lineLevi 1 (binaryUnipotent w) := by
      apply Units.ext
      change (lineLevi 1 (binaryUnipotent (((0 : ℝ), w) : Adeles))).val.map Prod.snd = _
      rw [lineLevi_binaryUnipotent_val, lineLevi_binaryUnipotent_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lineLeviNilpotent]
    have hfin : finiteGroup (atFinite (unipotentUnit _ h)) = unipotentUnit _ h := by
      apply Units.ext
      rfl
    rw [finiteGroup.map_mul, finiteGroup.map_mul, hline, hfin, finiteGroup_rational]
    apply Units.ext
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, lineLevi_binaryUnipotent_val,
      unipotentUnit_val]
    have hqf : (rationalFinite q⁻¹).val * (rationalFinite q).val = 1 := by
      rw [← GeneralLinearGroup.coe_mul, ← map_mul, inv_mul_cancel, map_one,
        GeneralLinearGroup.coe_one]
    have hmap : (lineFlagNilpotent q).map (algebraMap ℚ FiniteAdeles) =
        (rationalFinite q).val * lineLeviNilpotent FiniteAdeles * (rationalFinite q⁻¹).val := by
      rw [lineFlagNilpotent, Matrix.map_mul, Matrix.map_mul, lineLeviNilpotent_map]
      rfl
    rw [hmap]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hqf, Matrix.one_mul]

/-- Vanishing of the real constant term of a line source cocycle at a rational flag. -/
theorem line_flag_real_constant_term {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3)
    (vertices : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ) :
    ∃ M : ℕ, 0 < M ∧
      (∫ t in Set.Ico (0 : ℝ) 1, (source vertices (lineLevi 1 (binaryUnipotent ((((M : ℝ) * t), 0) : Adeles)) *
          rationalGroup q⁻¹)).val.coeff monomial) = 0 := by
  obtain ⟨M, hM, hlevel⟩ := scaled_unipotent_mem_finiteLevel (lineFlagNilpotent q)
    (lineFlagNilpotent_sq q)
  refine ⟨M, hM, ?_⟩
  have induced := isSource.1 vertices monomial
  apply induced_line_real_constant_term induced (rationalGroup q⁻¹) M hM
  · intro t z hz
    obtain ⟨z', rfl⟩ := hz
    have hsplit : (((t, (M : FiniteAdeles) * integralEmbedding z') : Adeles)) =
        ((t, 0) : Adeles) + (((0 : ℝ), (M : FiniteAdeles) * integralEmbedding z') : Adeles) := by
      ext <;> simp
    have hsq : (((M : FiniteAdeles) * integralEmbedding z') •
        (lineFlagNilpotent q).map (algebraMap ℚ FiniteAdeles)) *
        (((M : FiniteAdeles) * integralEmbedding z') •
          (lineFlagNilpotent q).map (algebraMap ℚ FiniteAdeles)) = 0 := by
      rw [smul_mul_smul_comm, ← Matrix.map_mul, lineFlagNilpotent_sq, Matrix.map_zero _ (map_zero _),
        smul_zero]
    rw [hsplit, binaryUnipotent_add, lineLevi_binary_mul,
      mul_assoc, lineLevi_finite_mul_rationalGroup q _ hsq, ← mul_assoc]
    exact induced.2.1 ⟨_, hlevel z' hsq⟩ _
  · exact ((induced_continuous induced).comp ((lineLeviUnipotent_continuous.comp
        (continuous_id.prodMk continuous_const)).mul continuous_const)).measurable

end TernaryPeriodPolynomials.FlagExactness
