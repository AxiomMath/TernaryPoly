module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.RectangularSchwartz
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Theta.ParameterBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaParameterBounds

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachAdelicTheta

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]

def tensorTest (realTest : SchwartzMap RealSpace Target)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (matrix : Rectangular Adeles) : Target :=
  finiteTest (finite matrix) • realTest (archimedean matrix)

def matrixTerm (test : Rectangular Adeles → Target) (point : AdelicGL)
    (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) : Target :=
  test (point⁻¹.val * matrix.map rationalAdele * binary.val)

def fullTheta (test : Rectangular Adeles → Target) (point : AdelicGL)
    (binary : BinaryAdelicGL) : Target := ∑' matrix : Rectangular ℚ, matrixTerm test point binary matrix

theorem matrixTerm_factorization (realTest : SchwartzMap RealSpace Target)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (parameter : Parameter) (matrix : Rectangular ℚ) :
    matrixTerm (tensorTest realTest finiteTest) parameter.1 parameter.2 matrix =
      finiteTest (finiteAction parameter (finiteMatrix matrix)) • realTest (realAction parameter (realVector matrix)) := by
  simp only [matrixTerm, tensorTest, archimedean_transport, finite_transport,
    archimedean_rational, finite_rational]
  rfl

theorem tensorTest_continuous (realTest : SchwartzMap RealSpace Target)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest) :
    Continuous (tensorTest realTest finiteTest) :=
  (finiteContinuous.comp AdelicSchwartzTheta.finite_continuous).smul
    (realTest.continuous.comp AdelicSchwartzTheta.archimedean_continuous)

omit [NormedSpace ℂ Target] in
theorem matrixTerm_continuous (test : Rectangular Adeles → Target) (testContinuous : Continuous test)
    (matrix : Rectangular ℚ) :
    Continuous (fun parameter : Parameter => matrixTerm test parameter.1 parameter.2 matrix) :=
  testContinuous.comp (((Units.continuous_val.comp continuous_fst.inv).matrix_mul continuous_const).matrix_mul
    (Units.continuous_val.comp continuous_snd))

theorem exists_majorant (realTest : SchwartzMap RealSpace Target)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (parameters : Set Parameter) (compact : IsCompact parameters) :
    ∃ majorant : Rectangular ℚ → ℝ, Summable majorant ∧ (∀ matrix, 0 ≤ majorant matrix) ∧
      ∀ parameter ∈ parameters, ∀ matrix,
        ‖matrixTerm (tensorTest realTest finiteTest) parameter.1 parameter.2 matrix‖ ≤ majorant matrix := by
  obtain ⟨hull, hullCompact, hullMembership⟩ := exists_finite_hull finiteTest finiteSupport parameters compact
  obtain ⟨distortion, distortionNonnegative, distortionBound⟩ := exists_distortion_bound parameters compact
  obtain ⟨majorant, majorantSummable, majorantNonnegative, majorantBound⟩ :=
    BanachRectangularSchwartz.exists_uniform_majorant hull hullCompact realTest distortion distortionNonnegative
  obtain ⟨bound, bounded⟩ := finiteSupport.exists_bound_of_continuous finiteContinuous
  refine ⟨fun matrix => max bound 0 * majorant matrix, majorantSummable.mul_left _,
    fun matrix => mul_nonneg (le_max_right _ _) (majorantNonnegative matrix), ?_⟩
  intro parameter membership matrix
  rw [matrixTerm_factorization, norm_smul]
  by_cases finiteZero : finiteTest (finiteAction parameter (finiteMatrix matrix)) = 0
  · rw [finiteZero, norm_zero, zero_mul]
    exact mul_nonneg (le_max_right _ _) (majorantNonnegative matrix)
  · have realBound := majorantBound (realAction parameter).toContinuousLinearMap (distortionBound parameter membership)
      matrix (hullMembership parameter membership (finiteMatrix matrix) finiteZero)
    exact mul_le_mul ((bounded _).trans (le_max_left _ _)) realBound (norm_nonneg _) (le_max_right _ _)

theorem summable_norm (realTest : SchwartzMap RealSpace Target)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (fun matrix => ‖matrixTerm (tensorTest realTest finiteTest) point binary matrix‖) := by
  obtain ⟨majorant, summableMajorant, _, bounded⟩ :=
    exists_majorant realTest finiteTest finiteContinuous finiteSupport {(point, binary)} isCompact_singleton
  exact summableMajorant.of_nonneg_of_le (fun _ => norm_nonneg _)
    (bounded (point, binary) (Set.mem_singleton _))

theorem summable [CompleteSpace Target] (realTest : SchwartzMap RealSpace Target)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (matrixTerm (tensorTest realTest finiteTest) point binary) :=
  (summable_norm realTest finiteTest finiteContinuous finiteSupport point binary).of_norm

theorem fullTheta_continuous [CompleteSpace Target] (realTest : SchwartzMap RealSpace Target)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) :
    Continuous (fun parameter : Parameter => fullTheta (tensorTest realTest finiteTest) parameter.1 parameter.2) := by
  let _ : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) Adeles) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → Adeles))
  let _ : LocallyCompactSpace AdelicGL :=
    inferInstanceAs (LocallyCompactSpace (Matrix (Fin 3) (Fin 3) Adeles)ˣ)
  apply continuous_iff_continuousAt.mpr
  intro parameter
  obtain ⟨compact, compactIs, neighborhood⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds parameter
  obtain ⟨majorant, summableMajorant, _, bounded⟩ :=
    exists_majorant realTest finiteTest finiteContinuous finiteSupport compact compactIs
  have continuousOn : ContinuousOn
      (fun parameter : Parameter => fullTheta (tensorTest realTest finiteTest) parameter.1 parameter.2) compact :=
    continuousOn_tsum (fun matrix =>
      (matrixTerm_continuous _ (tensorTest_continuous realTest finiteTest finiteContinuous) matrix).continuousOn)
      summableMajorant (fun matrix parameter membership => bounded parameter membership matrix)
  exact continuousOn.continuousAt neighborhood

theorem fullTheta_postcomp [CompleteSpace Target] (realTest : SchwartzMap RealSpace Target)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL)
    (functional : Target →L[ℂ] ℂ) :
    functional (fullTheta (tensorTest realTest finiteTest) point binary) =
      RectangularTheta.fullTheta (AdelicSchwartzTheta.tensorTest (SchwartzMap.postcompCLM functional realTest) finiteTest) point binary := by
  rw [fullTheta, functional.map_tsum (summable realTest finiteTest finiteContinuous finiteSupport point binary)]
  apply tsum_congr
  intro matrix
  simp only [matrixTerm, tensorTest, RectangularTheta.matrixTerm,
    AdelicSchwartzTheta.tensorTest, SchwartzMap.postcompCLM_apply, map_smul, smul_eq_mul]
  exact mul_comm _ _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachAdelicTheta
