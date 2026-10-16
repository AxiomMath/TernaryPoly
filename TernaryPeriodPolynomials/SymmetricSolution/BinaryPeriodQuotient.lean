module

public import TernaryPeriodPolynomials.SymmetricSolution.BinaryPeriodLift
public import TernaryPeriodPolynomials.Analysis.CoordinateSumQuotient
public import TernaryPeriodPolynomials.SymmetricSolution.Factors

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- Separate oddness of the binary period makes its ternary numerator even under total negation. -/
theorem symmetricBinaryLift_even {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) :
    bind₁ ![-X 0,-X 1,-X 2] (binaryPeriodLift q) = binaryPeriodLift q := by
  change substitute3 (binaryPeriodLift q) (-X 0) (-X 1) (-X 2) = _
  rw [binaryPeriodLift_substitute3]
  simp only [symmetricBinaryEval_neg_first hq,symmetricBinaryEval_neg_second hq,neg_neg]
  rfl

/-- The symmetric binary numerator satisfies precisely the original cyclic and norm equations. -/
theorem symmetricBinaryLift_periodRelations {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) : PeriodRelations (binaryPeriodLift q) :=
  ⟨binaryPeriodLift_cyclic q,symmetricBinaryLift_norm hq⟩

/-- Every polynomial quotient retains the numerator's cyclic and swap symmetry. -/
theorem symmetricBinaryLift_quotient_symmetries {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (g : TernaryPolynomial)
    (hg : binaryPeriodLift q = (X 0+X 1+X 2)*g) : C g = g ∧ S g = g := by
  constructor
  · apply cyclic_of_coordinate_sum_pow_mul 1
    simpa only [pow_one,← hg] using binaryPeriodLift_cyclic q
  · have hs := symmetricBinaryLift_symmetric hq
    rw [hg,map_mul] at hs
    have hw : S (X 0+X 1+X 2) = (X 0+X 1+X 2 : TernaryPolynomial) := by
      simp [S]
      ring
    rw [hw] at hs
    exact mul_left_cancel₀ coordinate_sum_ne_zero hs

/-- The three opposite-pair factors divide the actual polynomial quotient. -/
theorem symmetricBinaryLift_quotient_factors {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (g : TernaryPolynomial)
    (hg : binaryPeriodLift q = (X 0+X 1+X 2)*g) :
    (X 0+X 1)*(X 0+X 2)*(X 1+X 2) ∣ g := by
  obtain ⟨k,hk⟩ := symmetric_total_pair_sum_product_dvd
    (symmetricBinaryLift_periodRelations hq) (symmetricBinaryLift_symmetric hq)
    (symmetricBinaryLift_even hq)
  refine ⟨k,?_⟩
  apply mul_left_cancel₀ coordinate_sum_ne_zero
  rw [← hg,hk,mul_assoc]

/-- Homogeneous division by W lowers the binary degree by one. -/
theorem symmetricBinaryLift_quotient_isHomogeneous {q : MvPolynomial (Fin 2) ℚ}
    {n : ℕ} (hq : q.IsHomogeneous n) (g : TernaryPolynomial)
    (hg : binaryPeriodLift q = (X 0+X 1+X 2)*g) : g.IsHomogeneous (n-1) := by
  apply isHomogeneous_quotient coordinate_sum_isHomogeneous coordinate_sum_ne_zero
  rw [← hg]
  exact binaryPeriodLift_isHomogeneous hq

/-- A symmetric binary period has a genuine symmetric, factored polynomial lift in the whole Todd kernel. -/
theorem symmetricBinaryPeriod_quotient_data {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) :
    ∃ g : TernaryPolynomial, binaryPeriodLift q = (X 0+X 1+X 2)*g ∧
      C g = g ∧ S g = g ∧ symmetricTodd g = 0 ∧
      (X 0+X 1)*(X 0+X 2)*(X 1+X 2) ∣ g := by
  obtain ⟨g,hg,hJ⟩ := symmetricBinaryLift_exists_quotient hq
  obtain ⟨hc,hs⟩ := symmetricBinaryLift_quotient_symmetries hq g hg
  exact ⟨g,hg,hc,hs,hJ,symmetricBinaryLift_quotient_factors hq g hg⟩

end TernaryPoly
