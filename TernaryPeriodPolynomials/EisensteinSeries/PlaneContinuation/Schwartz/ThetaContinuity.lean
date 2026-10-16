module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Theta.ParameterBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicSchwartzTheta TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaParameterBounds

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzThetaContinuity

theorem exists_majorant (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (parameters : Set Parameter) (compact : IsCompact parameters) :
    ∃ majorant : Rectangular ℚ → ℝ, Summable majorant ∧ (∀ matrix, 0 ≤ majorant matrix) ∧
      ∀ parameter ∈ parameters, ∀ matrix,
        ‖matrixTerm (tensorTest realTest finiteTest) parameter.1 parameter.2 matrix‖ ≤ majorant matrix := by
  obtain ⟨hull, hullCompact, hullMembership⟩ := exists_finite_hull finiteTest finiteSupport parameters compact
  obtain ⟨distortion, distortionNonnegative, distortionBound⟩ := exists_distortion_bound parameters compact
  obtain ⟨majorant, majorantSummable, majorantNonnegative, majorantBound⟩ :=
    RectangularSchwartz.exists_uniform_majorant hull hullCompact realTest distortion distortionNonnegative
  obtain ⟨bound, bounded⟩ := finiteSupport.exists_bound_of_continuous finiteContinuous
  refine ⟨fun matrix => majorant matrix * max bound 0, majorantSummable.mul_right _,
    fun matrix => mul_nonneg (majorantNonnegative matrix) (le_max_right _ _), ?_⟩
  intro parameter membership matrix
  have factorization : matrixTerm (tensorTest realTest finiteTest) parameter.1 parameter.2 matrix =
      realTest (realAction parameter (realVector matrix)) * finiteTest (finiteAction parameter (finiteMatrix matrix)) :=
    matrixTerm_factorization realTest finiteTest parameter.1 parameter.2 matrix
  rw [factorization, norm_mul]
  by_cases finiteZero : finiteTest (finiteAction parameter (finiteMatrix matrix)) = 0
  · rw [finiteZero, norm_zero, mul_zero]
    exact mul_nonneg (majorantNonnegative matrix) (le_max_right _ _)
  · have realBound := majorantBound (realAction parameter).toContinuousLinearMap (distortionBound parameter membership)
      matrix (hullMembership parameter membership (finiteMatrix matrix) finiteZero)
    exact mul_le_mul realBound ((bounded _).trans (le_max_left _ _)) (norm_nonneg _) (majorantNonnegative matrix)

theorem uniformly_on_compact (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (parameters : Set Parameter) (compact : IsCompact parameters) :
    TendstoUniformlyOn
      (fun finiteSet : Finset (Rectangular ℚ) => fun parameter : Parameter =>
        ∑ matrix ∈ finiteSet, matrixTerm (tensorTest realTest finiteTest) parameter.1 parameter.2 matrix)
      (fun parameter => fullTheta (tensorTest realTest finiteTest) parameter.1 parameter.2)
      Filter.atTop parameters := by
  obtain ⟨majorant, summableMajorant, _, bound⟩ := exists_majorant realTest finiteTest finiteContinuous finiteSupport parameters compact
  exact tendstoUniformlyOn_tsum summableMajorant (fun matrix parameter membership => bound parameter membership matrix)

theorem subseries_continuousOn_compact (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (predicate : Rectangular ℚ → Prop)
    (parameters : Set Parameter) (compact : IsCompact parameters) :
    ContinuousOn (fun parameter : Parameter => ∑' matrix : {matrix // predicate matrix},
      matrixTerm (tensorTest realTest finiteTest) parameter.1 parameter.2 matrix.val) parameters := by
  obtain ⟨majorant, summableMajorant, _, bound⟩ := exists_majorant realTest finiteTest finiteContinuous finiteSupport parameters compact
  exact continuousOn_tsum (fun matrix =>
    (ThetaLocalFiniteness.matrixTerm_continuous _ (tensorTest_continuous realTest finiteTest finiteContinuous) matrix.val).continuousOn)
    (summableMajorant.subtype predicate) (fun matrix parameter membership => bound parameter membership matrix.val)

theorem fullTheta_continuousOn_compact (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (parameters : Set Parameter) (compact : IsCompact parameters) :
    ContinuousOn (fun parameter : Parameter => fullTheta (tensorTest realTest finiteTest) parameter.1 parameter.2) parameters := by
  obtain ⟨majorant, summableMajorant, _, bound⟩ := exists_majorant realTest finiteTest finiteContinuous finiteSupport parameters compact
  exact continuousOn_tsum (fun matrix =>
    (ThetaLocalFiniteness.matrixTerm_continuous _ (tensorTest_continuous realTest finiteTest finiteContinuous) matrix).continuousOn)
    summableMajorant (fun matrix parameter membership => bound parameter membership matrix)

theorem continuous_of_compact (function : Parameter → ℂ)
    (continuousOnCompact : ∀ compact : Set Parameter, IsCompact compact → ContinuousOn function compact) : Continuous function := by
  let _ : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) Adeles) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → Adeles))
  let _ : LocallyCompactSpace AdelicGL :=
    inferInstanceAs (LocallyCompactSpace (Matrix (Fin 3) (Fin 3) Adeles)ˣ)
  apply continuous_iff_continuousAt.mpr
  intro parameter
  obtain ⟨compact, compactIs, neighborhood⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds parameter
  exact (continuousOnCompact compact compactIs).continuousAt neighborhood

theorem fullTheta_continuous (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) :
    Continuous (fun parameter : Parameter => fullTheta (tensorTest realTest finiteTest) parameter.1 parameter.2) :=
  continuous_of_compact _ (fullTheta_continuousOn_compact realTest finiteTest finiteContinuous finiteSupport)

theorem subseries_continuous (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (predicate : Rectangular ℚ → Prop) :
    Continuous (fun parameter : Parameter => ∑' matrix : {matrix // predicate matrix},
      matrixTerm (tensorTest realTest finiteTest) parameter.1 parameter.2 matrix.val) :=
  continuous_of_compact _ (subseries_continuousOn_compact realTest finiteTest finiteContinuous finiteSupport predicate)

theorem theta_continuous (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) :
    Continuous (fun parameter : Parameter => RectangularKernel.theta (tensorTest realTest finiteTest) parameter.1 parameter.2) :=
  subseries_continuous realTest finiteTest finiteContinuous finiteSupport FullRank

theorem singularTheta_continuous (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) :
    Continuous (fun parameter : Parameter => singularTheta (tensorTest realTest finiteTest) parameter.1 parameter.2) :=
  subseries_continuous realTest finiteTest finiteContinuous finiteSupport (fun matrix => ¬ FullRank matrix)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzThetaContinuity
