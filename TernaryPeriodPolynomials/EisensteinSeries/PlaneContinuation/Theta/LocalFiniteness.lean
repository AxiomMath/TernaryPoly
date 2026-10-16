module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.Theta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularLattice

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaLocalFiniteness

theorem finite_uniform_support (test : Rectangular Adeles → ℂ) (compactSupport : HasCompactSupport test)
    (points : Set AdelicGL) (pointsCompact : IsCompact points)
    (binaries : Set BinaryAdelicGL) (binariesCompact : IsCompact binaries) :
    {matrix : Rectangular ℚ | ∃ point ∈ points, ∃ binary ∈ binaries,
      matrixTerm test point binary matrix ≠ 0}.Finite := by
  let inverseTransform : AdelicGL × Rectangular Adeles × BinaryAdelicGL → Rectangular Adeles :=
    fun triple => triple.1.val * triple.2.1 * triple.2.2⁻¹.val
  have continuousTransform : Continuous inverseTransform :=
    ((Units.continuous_val.comp continuous_fst).matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      (Units.continuous_val.comp (continuous_snd.comp continuous_snd).inv)
  have compactHull : IsCompact (inverseTransform '' (points ×ˢ tsupport test ×ˢ binaries)) :=
    (pointsCompact.prod (compactSupport.prod binariesCompact)).image continuousTransform
  apply (finite_in_compact _ compactHull).subset
  rintro matrix ⟨point, pointMem, binary, binaryMem, nonzero⟩
  refine ⟨(point, CompactTheta.transform point binary (rationalMap matrix), binary),
    ⟨pointMem, ?_, binaryMem⟩, ?_⟩
  · exact subset_closure nonzero
  · exact (CompactTheta.transform point binary).symm_apply_apply (rationalMap matrix)

theorem matrixTerm_continuous (test : Rectangular Adeles → ℂ) (testContinuous : Continuous test)
    (matrix : Rectangular ℚ) :
    Continuous (fun pair : AdelicGL × BinaryAdelicGL => matrixTerm test pair.1 pair.2 matrix) :=
  testContinuous.comp (((Units.continuous_val.comp continuous_fst.inv).matrix_mul continuous_const).matrix_mul
    (Units.continuous_val.comp continuous_snd))

theorem fullTheta_continuousOn_compact (test : Rectangular Adeles → ℂ)
    (testContinuous : Continuous test) (compactSupport : HasCompactSupport test)
    (points : Set AdelicGL) (pointsCompact : IsCompact points)
    (binaries : Set BinaryAdelicGL) (binariesCompact : IsCompact binaries) :
    ContinuousOn (fun pair : AdelicGL × BinaryAdelicGL => fullTheta test pair.1 pair.2) (points ×ˢ binaries) := by
  classical
  let supportSet : Set (Rectangular ℚ) := {matrix | ∃ point ∈ points, ∃ binary ∈ binaries,
    matrixTerm test point binary matrix ≠ 0}
  have supportFinite : supportSet.Finite := finite_uniform_support test compactSupport points pointsCompact binaries binariesCompact
  have equality : Set.EqOn (fun pair : AdelicGL × BinaryAdelicGL => fullTheta test pair.1 pair.2)
      (fun pair => ∑ matrix ∈ supportFinite.toFinset, matrixTerm test pair.1 pair.2 matrix) (points ×ˢ binaries) := by
    intro pair membership
    apply tsum_eq_sum
    intro matrix outside
    by_contra nonzero
    exact outside (supportFinite.mem_toFinset.mpr ⟨pair.1, membership.1, pair.2, membership.2, nonzero⟩)
  exact (continuous_finsetSum _ (fun matrix _ => matrixTerm_continuous test testContinuous matrix)).continuousOn.congr equality

theorem fullTheta_continuous (test : Rectangular Adeles → ℂ)
    (testContinuous : Continuous test) (compactSupport : HasCompactSupport test) :
    Continuous (fun pair : AdelicGL × BinaryAdelicGL => fullTheta test pair.1 pair.2) := by
  let _ : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) Adeles) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → Adeles))
  let _ : LocallyCompactSpace AdelicGL :=
    inferInstanceAs (LocallyCompactSpace (Matrix (Fin 3) (Fin 3) Adeles)ˣ)
  apply continuous_iff_continuousAt.mpr
  intro pair
  obtain ⟨points, pointsCompact, pointsNeighborhood⟩ :=
    WeaklyLocallyCompactSpace.exists_compact_mem_nhds pair.1
  obtain ⟨binaries, binariesCompact, binariesNeighborhood⟩ :=
    WeaklyLocallyCompactSpace.exists_compact_mem_nhds pair.2
  apply (fullTheta_continuousOn_compact test testContinuous compactSupport points pointsCompact binaries binariesCompact).continuousAt
  rw [nhds_prod_eq]
  exact Filter.prod_mem_prod pointsNeighborhood binariesNeighborhood

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaLocalFiniteness
