module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegralRationals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactDenominators

def denominatorSet (denominator : ℕ) : Set FiniteAdeles :=
  {value | (denominator : FiniteAdeles) * value ∈ Set.range integralEmbedding}

theorem denominatorSet_open (denominator : ℕ) : IsOpen (denominatorSet denominator) :=
  integralLattice_isOpen.preimage (continuous_const.mul continuous_id)

theorem natCast_integral (integer : ℕ) : (integer : FiniteAdeles) ∈ Set.range integralEmbedding :=
  ⟨integer, map_natCast integralEmbedding integer⟩

theorem exists_common_denominator (compact : Set FiniteAdeles) (compactIs : IsCompact compact) :
    ∃ denominator : ℕ, denominator ≠ 0 ∧ ∀ value ∈ compact,
      (denominator : FiniteAdeles) * value ∈ Set.range integralEmbedding := by
  classical
  have cover : compact ⊆ ⋃ denominator : {denominator : ℕ // denominator ≠ 0}, denominatorSet denominator.val := by
    intro value _
    obtain ⟨denominator, nonzero, integral⟩ := AdelicDenominators.exists_nat_denominator value
    exact Set.mem_iUnion.mpr ⟨⟨denominator, nonzero⟩, integral⟩
  obtain ⟨denominators, covers⟩ := compactIs.elim_finite_subcover
    (fun denominator : {denominator : ℕ // denominator ≠ 0} => denominatorSet denominator.val)
    (fun denominator => denominatorSet_open denominator.val) cover
  refine ⟨∏ denominator ∈ denominators, denominator.val,
    Finset.prod_ne_zero_iff.mpr (fun denominator _ => denominator.property), ?_⟩
  intro value membership
  obtain ⟨denominator, denominatorMem, integral⟩ := Set.mem_iUnion₂.mp (covers membership)
  have productEquality : (∏ other ∈ denominators, other.val) =
      denominator.val * ∏ other ∈ denominators.erase denominator, other.val :=
    (Finset.mul_prod_erase denominators (fun other => other.val) denominatorMem).symm
  rw [productEquality, Nat.cast_mul, mul_assoc, mul_comm _ value, ← mul_assoc]
  exact RationalDiscreteness.integral_mul integral (natCast_integral _)

theorem exists_integer_multiples (compact : Set FiniteAdeles) (compactIs : IsCompact compact) :
    ∃ denominator : ℕ, denominator ≠ 0 ∧ ∀ rational : ℚ,
      algebraMap ℚ FiniteAdeles rational ∈ compact → ∃ integer : ℤ, (denominator : ℚ) * rational = integer := by
  obtain ⟨denominator, nonzero, integral⟩ := exists_common_denominator compact compactIs
  refine ⟨denominator, nonzero, fun rational membership => ?_⟩
  apply (IntegralRationals.integral_iff_integer ((denominator : ℚ) * rational)).mp
  simpa only [map_mul, map_natCast] using integral _ membership

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactDenominators
