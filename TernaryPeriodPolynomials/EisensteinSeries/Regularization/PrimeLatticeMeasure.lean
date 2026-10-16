module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Integral.Reduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def primeLattice (prime : Nat.Primes) : Set FiniteAdeles :=
  Set.range (fun value : IntegralAdeles => integralEmbedding ((prime.val : IntegralAdeles) * value))

def primeLatticeCoset (prime : Nat.Primes) (residue : ZMod prime.val) : Set FiniteAdeles :=
  (fun value => (residue.val : FiniteAdeles) + value) '' primeLattice prime

theorem primeLattice_compact (prime : Nat.Primes) : IsCompact (primeLattice prime) := by
  apply isCompact_range
  have multiplication_eq :
      (fun value : IntegralAdeles => integralEmbedding ((prime.val : IntegralAdeles) * value)) =
        (fun value : IntegralAdeles => (prime.val : FiniteAdeles) * integralEmbedding value) := by
    funext value
    rw [map_mul, map_natCast]
  rw [multiplication_eq]
  exact continuous_const.mul integralEmbedding_isOpenEmbedding.continuous

theorem primeLatticeCoset_compact (prime : Nat.Primes) (residue : ZMod prime.val) :
    IsCompact (primeLatticeCoset prime residue) :=
  (primeLattice_compact prime).image (continuous_const.add continuous_id)

theorem integralLattice_eq_primeLatticeCosets (prime : Nat.Primes) :
    Set.range integralEmbedding = ⋃ residue : ZMod prime.val, primeLatticeCoset prime residue := by
  ext value
  constructor
  · rintro ⟨integralValue, rfl⟩
    let residue := primeIntegralReduction prime integralValue
    have reduction_zero :
        primeIntegralReduction prime (integralValue - (residue.val : IntegralAdeles)) = 0 := by
      simp only [map_sub, map_natCast, ZMod.natCast_zmod_val, residue, sub_self]
    obtain ⟨quotient, quotient_spec⟩ :=
      (primeIntegralReduction_eq_zero_iff prime _).mp reduction_zero
    apply Set.mem_iUnion.mpr
    refine ⟨residue, integralEmbedding ((prime.val : IntegralAdeles) * quotient), ⟨quotient, rfl⟩, ?_⟩
    rw [← quotient_spec, map_sub, map_natCast]
    abel_nf
  · intro in_union
    obtain ⟨residue, difference, ⟨quotient, rfl⟩, rfl⟩ := Set.mem_iUnion.mp in_union
    refine ⟨(residue.val : IntegralAdeles) + (prime.val : IntegralAdeles) * quotient, ?_⟩
    rw [map_add, map_natCast]

theorem primeLatticeCosets_disjoint (prime : Nat.Primes) :
    Pairwise (Function.onFun Disjoint (primeLatticeCoset prime)) := by
  intro firstResidue secondResidue different
  apply Set.disjoint_left.mpr
  intro value first_mem second_mem
  obtain ⟨firstDifference, ⟨firstQuotient, rfl⟩, first_eq⟩ := first_mem
  obtain ⟨secondDifference, ⟨secondQuotient, rfl⟩, second_eq⟩ := second_mem
  have embedded_equal := first_eq.trans second_eq.symm
  have integral_equal :
      (firstResidue.val : IntegralAdeles) + (prime.val : IntegralAdeles) * firstQuotient =
        (secondResidue.val : IntegralAdeles) + (prime.val : IntegralAdeles) * secondQuotient := by
    apply integralEmbedding_injective
    simpa only [map_add, map_natCast] using embedded_equal
  have residues_equal := congrArg (primeIntegralReduction prime) integral_equal
  simp only [map_add, map_mul, map_natCast, ZMod.natCast_zmod_val,
    CharP.cast_eq_zero, zero_mul, add_zero] at residues_equal
  exact different residues_equal

theorem primeLatticeCoset_measure (prime : Nat.Primes) (residue : ZMod prime.val) :
    finiteMeasure (primeLatticeCoset prime residue) = finiteMeasure (primeLattice prime) := by
  rw [primeLatticeCoset, Set.image_add_left, measure_preimage_add]

theorem prime_mul_primeLattice_measure (prime : Nat.Primes) :
    (prime.val : ENNReal) * finiteMeasure (primeLattice prime) = 1 := by
  calc
    (prime.val : ENNReal) * finiteMeasure (primeLattice prime) =
        ∑ residue : ZMod prime.val, finiteMeasure (primeLatticeCoset prime residue) := by
      simp only [primeLatticeCoset_measure, Finset.sum_const, Finset.card_univ,
        ZMod.card, nsmul_eq_mul]
    _ = finiteMeasure (⋃ residue : ZMod prime.val, primeLatticeCoset prime residue) := by
      simpa only [tsum_fintype] using
        (measure_iUnion (μ := finiteMeasure) (primeLatticeCosets_disjoint prime)
          (fun residue => (primeLatticeCoset_compact prime residue).measurableSet)).symm
    _ = 1 := by rw [← integralLattice_eq_primeLatticeCosets, finiteMeasure_integralLattice]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
