module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaneLevelCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineIntegralRegion
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneFiniteLevel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem atFinite_planeUnipotent (first second : FiniteAdeles) :
    atFinite (planeUnipotent first second) = planeUnipotent (0, first) (0, second) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [atFinite, combineGL, pairMatrix, planeUnipotent]

theorem atFinite_planeLeviScalar (scalar : FiniteAdelesˣ) :
    atFinite (planeLevi 1 scalar) = planeLevi 1 (finiteAdeleUnit scalar) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [atFinite, combineGL, pairMatrix, planeLevi, planeBlock, finiteAdeleUnit]

theorem sourcePlane_scalar_invariant_trivial {degree : ℕ} (data : InducingData degree)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3)
    (scalar : Adelesˣ) (base : AdelicGL) :
    source vertices (planeLevi 1 scalar * base) = source vertices base := by
  have exponent : -2 * inductionExponent .plane cohomologicalPoint = 0 := by
    unfold inductionExponent cohomologicalPoint
    ring
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  have equality := (cocycle.1 vertices monomial).2.2.2.2.1 scalar base
  rw [trivial, exponent, normPower_zero_exponent] at equality
  simpa only [trivialCharacter, MonoidHom.one_apply, mul_one, one_mul] using equality

theorem sourcePlaneCuspidalValues_recover {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (vertices : Fin 3 → RealGL3) (base : AdelicGL) (block : BinaryAdelicGL) :
    normPower (GeneralLinearGroup.det block) (((degree : ℂ) + 3) / 2) •
        (sourcePlaneCuspidalValues data source cocycle vertices base).val block =
      source vertices (planeLevi block 1 * base) := by
  rw [sourcePlaneCuspidalValues_apply, smul_smul, ← normPower_add_exponents, add_neg_cancel,
    normPower_zero_exponent, one_smul]

theorem sourcePlaneCuspidalValues_real_translate {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (vertices : Fin 3 → RealGL3) (real : RealGL3) (block : BinaryAdelicGL) :
    (sourcePlaneCuspidalValues data source cocycle vertices (atInfinity real)).val block =
      realCoefficientComponent degree data.chi real⁻¹
        ((sourcePlaneCuspidalValues data source cocycle (fun index => real * vertices index) 1).val block) := by
  rw [sourcePlaneCuspidalValues_apply, sourcePlaneCuspidalValues_apply, map_smul, mul_one,
    cocycle.2.2.1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem combineGL_plane_level_coordinates (real : RealGL3) (finite : FiniteGL)
    (coords : FinitePlaneLevelCoordinates finite) :
    combineGL real finite = planeUnipotent (0, coords.first) (0, coords.second) *
      (planeLevi 1 (finiteAdeleUnit coords.scalar) *
        (planeLevi (atFinite coords.block) 1 * (atInfinity real * atFinite coords.compact.val))) := by
  rw [← atFinite_mul_atInfinity]
  conv_lhs => rw [coords.factorization]
  rw [atFinite_mul, atFinite_mul, atFinite_mul,
    atFinite_planeUnipotent, atFinite_planeLeviScalar, atFinite_planeLeviOne]
  rw [mul_assoc, mul_assoc, mul_assoc, (atInfinity_commute_atFinite real coords.compact.val).symm.eq]

/-- The finite argument is evaluated in the actual cusp tensor, at a binary matrix trivial at three. -/
theorem source_plane_level_coordinates {degree : ℕ} (data : InducingData degree)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3)
    (real : RealGL3) (finite : FiniteGL) (coords : FinitePlaneLevelCoordinates finite) :
    source vertices (combineGL real finite) =
      normPower (finiteAdeleUnit (GeneralLinearGroup.det coords.block)) (((degree : ℂ) + 3) / 2) •
        (sourcePlaneCuspidalValues data source cocycle vertices (atInfinity real)).val (atFinite coords.block) := by
  rw [combineGL_plane_level_coordinates real finite coords,
    sourcePlane_radical_invariant data source cocycle,
    sourcePlane_scalar_invariant_trivial data trivial source cocycle,
    ← mul_assoc, source_finiteLevel data .plane source cocycle vertices coords.compact,
    ← sourcePlaneCuspidalValues_recover data source cocycle vertices (atInfinity real) (atFinite coords.block),
    binary_det_atFinite]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
