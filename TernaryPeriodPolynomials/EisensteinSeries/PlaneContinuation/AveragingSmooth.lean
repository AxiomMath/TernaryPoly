module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.Averaging
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.SupNorm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAveraging TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth

theorem atInfinity_one {size : ℕ} :
    atInfinity (1 : Matrix.GeneralLinearGroup (Fin size) ℝ) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  by_cases equality : row = column <;>
    simp [atInfinity, combineGL, pairMatrix, equality]

noncomputable def realInclusion : BinaryRealGL →* BinaryAdelicGL where
  toFun := atInfinity
  map_one' := atInfinity_one
  map_mul' := TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul

theorem atInfinity_inv (matrix : BinaryRealGL) :
    atInfinity matrix⁻¹ = (atInfinity matrix)⁻¹ := realInclusion.map_inv matrix

theorem unitary_inner_flip (data : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    (first second : data.H) :
    inner ℂ (data.π matrix first) second = inner ℂ first (data.π matrix⁻¹ second) := by
  let isometry : data.H →ₗᵢ[ℂ] data.H := ⟨data.π matrix, data.unitary matrix⟩
  have equality := isometry.inner_map_map first (data.π matrix⁻¹ second)
  change inner ℂ (data.π matrix first) (data.π matrix (data.π matrix⁻¹ second)) = _ at equality
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using equality

theorem averagingOperator_real (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (matrix : BinaryRealGL) (vector : data.H) :
    averagingOperator data level (data.π (atInfinity matrix) vector) =
      data.π (atInfinity matrix) (averagingOperator data level vector) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (fixedSubspace_real_stable data level matrix _
      (averagingOperator_mem_fixedSubspace data level vector))
  intro target targetFixed
  rw [← map_sub, unitary_inner_flip, ← atInfinity_inv]
  exact ((Submodule.mem_orthogonal' _ _).mp (Submodule.sub_starProjection_mem_orthogonal vector))
    _ (fixedSubspace_real_stable data level matrix⁻¹ target targetFixed)

theorem smooth_averaging {size count : ℕ} (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL)
    {family : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → data.H}
    (smoothFamily : Smooth family) :
    Smooth (fun matrices => averagingOperator data level (family matrices)) := by
  exact ((averagingOperator data level).restrictScalars ℝ).contDiff.comp_contDiffOn smoothFamily

theorem matrixDerivative_averaging {size count : ℕ} (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL)
    {family : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → data.H}
    (smoothFamily : Smooth family) (order : ℕ)
    (matrices : Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) :
    matrixDerivative order (fun values => averagingOperator data level (family values)) matrices =
      ((averagingOperator data level).restrictScalars ℝ).compContinuousMultilinearMap
        (matrixDerivative order family matrices) := by
  exact ((averagingOperator data level).restrictScalars ℝ).iteratedFDerivWithin_comp_left
    (smoothFamily _ (fun index => Matrix.GeneralLinearGroup.det_ne_zero (matrices index)))
    (matrixDomain_isOpen size count).uniqueDiffOn
    (fun index => Matrix.GeneralLinearGroup.det_ne_zero (matrices index)) le_top

theorem norm_matrixDerivative_averaging_le {size count : ℕ} (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL)
    {family : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → data.H}
    (smoothFamily : Smooth family) (order : ℕ)
    (matrices : Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) :
    ‖matrixDerivative order (fun values => averagingOperator data level (family values)) matrices‖ ≤
      ‖matrixDerivative order family matrices‖ := by
  rw [matrixDerivative_averaging data level smoothFamily]
  apply (((averagingOperator data level).restrictScalars ℝ).norm_compContinuousMultilinearMap_le _).trans
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact mul_le_of_le_one_left (norm_nonneg _) (averagingOperator_norm_le data level)

theorem fixed_mem_smooth_iff (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.H) (fixed : vector ∈ fixedSubspace data level) :
    vector ∈ data.smooth ↔
      Smooth (fun matrices : Fin 1 → BinaryRealGL => data.π (atInfinity (matrices 0)) vector) := by
  rw [data.smooth_exact]
  exact ⟨And.left, fun smoothOrbit => ⟨smoothOrbit, level, openness, compactness, fixed⟩⟩

theorem averaging_realSmooth_mem_smooth (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL)) (vector : data.H)
    (smoothOrbit : Smooth (fun matrices : Fin 1 → BinaryRealGL =>
      data.π (atInfinity (matrices 0)) vector)) :
    averagingOperator data level vector ∈ data.smooth := by
  apply (fixed_mem_smooth_iff data level openness compactness _
    (averagingOperator_mem_fixedSubspace data level vector)).mpr
  simpa only [averagingOperator_real] using smooth_averaging data level smoothOrbit

noncomputable def smoothAverage (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL)) :
    data.smooth →ₗ[ℂ] data.smooth where
  toFun vector := ⟨averagingOperator data level vector.val,
    averagingOperator_smooth data level compactness vector⟩
  map_add' first second := Subtype.ext (map_add (averagingOperator data level) first.val second.val)
  map_smul' scalar vector := Subtype.ext (map_smul (averagingOperator data level) scalar vector.val)

noncomputable def smoothOrbitElement (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (value : {value // value ∈ orbitFinset data level compactness vector}) :
    data.smooth := ⟨value.val, by
      obtain ⟨element, equality⟩ := (mem_orbitFinset data level compactness vector value.val).mp value.property
      rw [← equality]
      exact data.smooth_stable _ _ vector.property⟩

theorem smoothAverage_eq_sum (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) :
    smoothAverage data level compactness vector =
      ((orbitFinset data level compactness vector).card : ℂ)⁻¹ •
        ∑ value ∈ (orbitFinset data level compactness vector).attach,
          smoothOrbitElement data level compactness vector value := by
  apply Subtype.ext
  change averagingOperator data level vector.val = _
  rw [averagingOperator_eq_orbitAverage]
  change orbitAverage data level compactness vector =
    (data.smooth.subtype) (((orbitFinset data level compactness vector).card : ℂ)⁻¹ • _)
  rw [map_smul, map_sum]
  simp only [smoothOrbitElement, Submodule.subtype_apply, orbitAverage]
  congr 1
  exact (Finset.sum_attach _ id).symm

theorem smoothOrbitElement_cuspSupNorm (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (value : {value // value ∈ orbitFinset data level compactness vector}) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm (smoothOrbitElement data level compactness vector value) =
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm vector := by
  obtain ⟨element, equality⟩ := (mem_orbitFinset data level compactness vector value.val).mp value.property
  have vectorEquality : smoothOrbitElement data level compactness vector value =
      (⟨data.π (atFinite element.val) vector.val, data.smooth_stable _ _ vector.property⟩ : data.smooth) :=
    Subtype.ext equality.symm
  rw [vectorEquality]
  exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm_translate _ _

theorem smoothAverage_cuspSupNorm_le (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm (smoothAverage data level compactness vector) ≤
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm vector := by
  let orbit := orbitFinset data level compactness vector
  have cardNonzero : (orbit.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr (orbitFinset_nonempty data level compactness vector)))
  rw [smoothAverage_eq_sum, TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm_smul, norm_inv, Complex.norm_natCast]
  have sumBound :
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm (∑ value ∈ orbit.attach,
        smoothOrbitElement data level compactness vector value) ≤
      (orbit.card : ℝ) * TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm vector := by
    unfold TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm
    rw [map_sum]
    apply (norm_sum_le _ _).trans
    change (∑ value ∈ orbit.attach,
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm (smoothOrbitElement data level compactness vector value)) ≤ _
    simp only [smoothOrbitElement_cuspSupNorm, Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
    exact le_rfl
  calc
    (orbit.card : ℝ)⁻¹ * _ ≤ (orbit.card : ℝ)⁻¹ *
        ((orbit.card : ℝ) * TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm vector) :=
      mul_le_mul_of_nonneg_left sumBound (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm vector := by
      rw [inv_mul_cancel_left₀ cardNonzero]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth
