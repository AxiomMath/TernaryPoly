module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.NoFlatVanish
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.PairRelation
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.EvaluatorNonzero
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellSurjective
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.Nonvanish

@[expose] public section


/-!
# Lemma 3.3, G3: the global bridge between the apartment evaluator and the intersection with the flat

`flatIntersectionBridge_exists`: there is a nonzero rational `κ` with
`groupApartmentEvaluation W [z] = κ • intersectionSum W z` for every coefficient representation `W` and every
cellular top cycle `z` (`FlatIntersectionBridge κ`).  The constant is universal: fix the cycle `z₀` of the
coefficient system `ordinaryCyclesRep` with nonzero evaluator (`groupApartmentEvaluation_ne_zero`, surjectivity
of `cellGroupHomologyMap`); `pair_relation` against `z₀` determines the proportionality constant, the same for
all pairs, and it is nonzero because the evaluator of `z₀` is nonzero while a cycle with vanishing coefficient
at `T₀` has zero evaluator (`evaluation_eq_zero_of_coeff_zero`) and `dT0 ≠ 0`.

The value of `κ` (and of the combined constant `κ · dT0`) is not computed here: that is the orientation
constant of the Künneth identification of the Thom class of the flat with its Poincaré dual.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPeriodPolynomials.Argument.Lemma33.Retract TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Orient TernaryPoly.IntegralGL3Congruence

/-- **The intersection sum is a universal multiple of the evaluator.**  For the constant `r` below, and every
cycle of every coefficient system, `intersectionSum = r • groupApartmentEvaluation`, with `r ≠ 0`. -/
theorem exists_universal_ratio :
    ∃ r : ℚ, r ≠ 0 ∧ ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
      (hz : ((cellCoinv W).d 3 2).hom z = 0),
      (intersectionSum W).hom z =
        r • (groupApartmentEvaluation W).hom ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) := by
  have hex : ∃ x, (groupApartmentEvaluation ordinaryCyclesRep).hom x ≠ 0 := by
    by_contra h
    push Not at h
    apply groupApartmentEvaluation_ne_zero
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact h x
  obtain ⟨x, hx⟩ := hex
  obtain ⟨y, rfl⟩ := cellGroupHomologyMap_surjective ordinaryCyclesRep x
  obtain ⟨z₀, hz₀, rfl⟩ := exists_cellClass ordinaryCyclesRep y
  obtain ⟨r₀, h₀, -⟩ := pair_relation ordinaryCyclesRep ordinaryCyclesRep z₀ hz₀ z₀ hz₀ hx
  refine ⟨r₀, ?_, ?_⟩
  · intro hr
    rw [hr, zero_smul] at h₀
    have h1 : dT0 • (coeffAtT0 ordinaryCyclesRep).hom z₀ = 0 := h₀
    have h2 : (coeffAtT0 ordinaryCyclesRep).hom z₀ = 0 :=
      (smul_eq_zero.mp h1).resolve_left dT0_ne_zero
    exact hx (evaluation_eq_zero_of_coeff_zero ordinaryCyclesRep z₀ hz₀ h2)
  · intro W z hz
    obtain ⟨r, h₁, h₂⟩ := pair_relation W ordinaryCyclesRep z hz z₀ hz₀ hx
    have hr : r = r₀ := smul_left_injective ℚ hx (h₂.symm.trans h₀)
    rw [h₁, hr]

/-- **The global bridge** (`FlatIntersectionBridge`) holds with a nonzero universal constant. -/
theorem flatIntersectionBridge_exists : ∃ κ : ℚ, κ ≠ 0 ∧ FlatIntersectionBridge κ := by
  obtain ⟨r, hr, h⟩ := exists_universal_ratio
  refine ⟨r⁻¹, inv_ne_zero hr, ?_⟩
  intro W z hz
  rw [h W z hz, smul_smul, inv_mul_cancel₀ hr, one_smul]

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
