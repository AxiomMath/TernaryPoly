module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.DetNormalizedSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneLevelCocycle

@[expose] public section


/-!
# The determinant-normalized source has the same arithmetic plane edge

All arithmetic plane-stabilizer elements have determinant `±1`, so the normalized source agrees
with the source on every simplex that enters the arithmetic restriction of the real-plane cocycle.
Hence Codexiom's comparison `sourcePlaneLevelBinaryEdge_compare` (arithmetic binary edge of the
source's real-plane class = binary edge of its rational cycle) also holds for the normalized source,
without a rational cycle for it.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem abs_det_of_mem_rationalLevel {g : RationalGL3} (hg : g ∈ rationalLevel) :
    |(GeneralLinearGroup.map (algebraMap ℚ ℝ) g).val.det| = 1 := by
  obtain ⟨⟨γ, hγ⟩, equality⟩ := hg
  have unit : IsUnit γ.val.det := (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
  have value : (GeneralLinearGroup.map (algebraMap ℚ ℝ) g).val.det = ((γ.val.det : ℤ) : ℝ) := by
    rw [← equality]
    have := RingHom.map_det ((algebraMap ℚ ℝ).comp (Int.castRingHom ℚ)) γ.val
    simp only [eq_intCast] at this
    rw [this]
    rfl
  rw [value]
  rcases Int.isUnit_iff.mp unit with h | h <;> simp [h]

variable {n : ℕ}

theorem identityPlaneRealGroup_abs_det
    (element : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :
    |(realPlaneMatrix (identityPlaneRealGroup element)).val.det| = 1 := by
  rw [identityPlaneRealGroup_matrix]
  exact abs_det_of_mem_rationalLevel element.property.1

/-- **The normalized source has the same arithmetic plane cocycle.** -/
theorem realPlaneArithmeticCocycle_normalized (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) :
    realPlaneArithmeticCocycle n data.cusp data.chi
        (sourcePlaneLevelGroupCocycle data (normalizedSource source)
          (normalizedSource_cocycle data trivial source cocycle)) =
      realPlaneArithmeticCocycle n data.cusp data.chi
        (sourcePlaneLevelGroupCocycle data source cocycle) := by
  apply groupCohomology.cocycles₂_ext
  intro first second
  rw [realPlaneArithmeticCocycle_apply, realPlaneArithmeticCocycle_apply]
  change (sourcePlaneGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle)
      (identityPlaneRealGroup first, identityPlaneRealGroup second)).val 1 =
    (sourcePlaneGroupCocycle data source cocycle
      (identityPlaneRealGroup first, identityPlaneRealGroup second)).val 1
  rw [sourcePlaneGroupCocycle_apply, sourcePlaneGroupCocycle_apply, normalizedSource_eq_of_abs_det]
  intro index
  fin_cases index
  · simp
  · exact identityPlaneRealGroup_abs_det first
  · change |(realPlaneMatrix (identityPlaneRealGroup first) *
      realPlaneMatrix (identityPlaneRealGroup second)).val.det| = 1
    rw [Units.val_mul, Matrix.det_mul, abs_mul, identityPlaneRealGroup_abs_det,
      identityPlaneRealGroup_abs_det, one_mul]

theorem realPlaneLevelArithmeticBinaryEdge_congr (positive : 0 < n) (odd : Odd n)
    (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter)
    (first second : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep n cusp character))
    (equal : realPlaneArithmeticCocycle n cusp character first =
      realPlaneArithmeticCocycle n cusp character second) :
    realPlaneLevelArithmeticBinaryEdge n positive odd cusp character trivial
        (groupCohomology.H2π _ first) =
      realPlaneLevelArithmeticBinaryEdge n positive odd cusp character trivial
        (groupCohomology.H2π _ second) := by
  subst trivial
  change identityPlaneFullBinaryEdge n positive odd
      (realPlaneArithmeticH2 n cusp trivialCharacter (groupCohomology.H2π _ first)) =
    identityPlaneFullBinaryEdge n positive odd
      (realPlaneArithmeticH2 n cusp trivialCharacter (groupCohomology.H2π _ second))
  rw [realPlaneArithmeticH2_apply, realPlaneArithmeticH2_apply, equal]

/-- **Codexiom's arithmetic edge comparison for the normalized source.** -/
theorem normalizedSourcePlaneLevelBinaryEdge_compare (positive : 0 < n) (odd : Odd n)
    (data : InducingData n) (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (cycle : MaximalCycles n data.chi .plane)
    (evaluates : Evaluates data .plane source cycle) :
    realPlaneLevelArithmeticBinaryEdge n positive odd data.cusp data.chi trivial
        (groupCohomology.H2π (realPlaneLevelCuspidalRep n data.cusp data.chi)
          (sourcePlaneLevelGroupCocycle data (normalizedSource source)
            (normalizedSource_cocycle data trivial source cocycle))) =
      identityPlaneAmbientBinaryEdge n positive odd data.chi trivial
        (evaluateFlagCycle data.chi .plane (QuotientGroup.mk (1 : RationalGL3)) cycle) := by
  rw [← sourcePlaneLevelBinaryEdge_compare positive odd data trivial source cocycle cycle evaluates]
  exact realPlaneLevelArithmeticBinaryEdge_congr positive odd data.cusp data.chi trivial _ _
    (realPlaneArithmeticCocycle_normalized data trivial source cocycle)

end TernaryPeriodPolynomials.AnalyticClasses
