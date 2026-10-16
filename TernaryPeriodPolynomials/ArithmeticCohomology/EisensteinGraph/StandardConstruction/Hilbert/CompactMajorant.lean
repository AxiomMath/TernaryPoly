module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Flat
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.Majorant

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertCompactMajorant

theorem compact_majorant {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (set : Set AdelicGL) (compact : IsCompact set) :
    ∃ majorant : Flags .plane → ℝ, (∀ flag, 0 ≤ majorant flag) ∧ Summable majorant ∧
      ∀ argument ∈ set, ∀ flag,
        HilbertHeight.normSummand data parameter function induced argument flag ≤ majorant flag := by
  obtain ⟨bound, bounded⟩ := CuspLift.bounded data .plane parameter function induced
  obtain ⟨majorant, nonnegative, summable, dominates⟩ := CompactMajorant.geometric_majorant set compact
    (-((degree : ℝ) + 6) / 2 - parameter.re) (HeightMajorant.exponent_lt degree parameter halfPlane)
  obtain ⟨determinantBound, determinantBounded⟩ := compact.exists_bound_of_continuousOn
    (AdelicNormContinuity.determinant_weight_continuous
      (binaryInductionExponent degree .plane parameter).re).continuousOn
  let factor : ℝ := |determinantBound| + 1
  have factorNonnegative : 0 ≤ factor := by dsimp [factor]; positivity
  refine ⟨fun flag => (factor * majorant flag) * max bound 0,
    fun flag => mul_nonneg (mul_nonneg factorNonnegative (nonnegative flag)) (le_max_right _ _),
    (summable.mul_left factor).mul_right _, ?_⟩
  intro argument argumentMembership flag
  obtain ⟨first, second, binary, unit, compactElement, membership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition
      (rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ)
        (IntegerRows.flagRepresentative flag))⁻¹) * argument)
  have estimate := HilbertHeight.decomposition_bound data parameter function induced (max bound 0)
    (fun compactElement membership => (bounded compactElement membership).trans (le_max_left _ _))
    first second binary unit compactElement membership
  rw [← decomposition, CompactMajorant.rational_mul_det_norm] at estimate
  have determinantEstimate :
      (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
        (binaryInductionExponent degree .plane parameter).re ≤ factor := by
    have normBound := determinantBounded argument argumentMembership
    rw [Real.norm_eq_abs] at normBound
    exact ((le_abs_self _).trans normBound).trans
      (by dsimp [factor]; linarith [le_abs_self determinantBound])
  rw [HilbertHeight.normSummand_integer]
  apply estimate.trans
  apply mul_le_mul_of_nonneg_right _ (le_max_right _ _)
  exact mul_le_mul determinantEstimate
    (dominates argument argumentMembership flag first second binary unit compactElement membership decomposition)
    (Real.rpow_nonneg (adeleNorm unit).property _) factorNonnegative

theorem strip_compact_majorant {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (lower upper : ℝ) (lowerHalfPlane : -(degree : ℝ) / 2 < lower)
    (upperHalfPlane : -(degree : ℝ) / 2 < upper)
    (set : Set AdelicGL) (compact : IsCompact set) :
    ∃ majorant : Flags .plane → ℝ, (∀ flag, 0 ≤ majorant flag) ∧ Summable majorant ∧
      ∀ pair ∈ {parameter : ℂ | lower ≤ parameter.re ∧ parameter.re ≤ upper} ×ˢ set, ∀ flag,
        HilbertHeight.normSummand data pair.1 (extension pair.1) (flat.1 pair.1) pair.2 flag ≤ majorant flag := by
  obtain ⟨lowerMajorant, lowerNonnegative, lowerSummable, lowerBounded⟩ :=
    compact_majorant data (lower : ℂ) (extension (lower : ℂ)) (flat.1 (lower : ℂ)) lowerHalfPlane set compact
  obtain ⟨upperMajorant, upperNonnegative, upperSummable, upperBounded⟩ :=
    compact_majorant data (upper : ℂ) (extension (upper : ℂ)) (flat.1 (upper : ℂ)) upperHalfPlane set compact
  refine ⟨fun flag => lowerMajorant flag + upperMajorant flag,
    fun flag => add_nonneg (lowerNonnegative flag) (upperNonnegative flag),
    lowerSummable.add upperSummable, ?_⟩
  intro pair membership flag
  exact (HilbertFlat.norm_strip_bound data extension flat _ lower upper pair.1 membership.1.1 membership.1.2).trans
    (add_le_add (lowerBounded pair.2 membership.2 flag) (upperBounded pair.2 membership.2 flag))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertCompactMajorant
