module

public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.Coordinates
public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.ReversalCount

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant
open BinaryHomogeneous

/-- The coordinate equivalence gives the exact homogeneous dimension. -/
theorem finrank_homogeneous (d : ℕ) : Module.finrank ℚ (H d)=d+1 := by
  rw [(coefficientEquiv ℚ d).finrank_eq]
  simp

/-- Every actual swap reflection has trace one in even degree. -/
theorem trace_swap (d : ℕ) (hd : Even d) : LinearMap.trace ℚ (H d) (swap d)=1 := by
  rw [trace_coordinates]
  simp only [swap_monomialVector,coordinates_monomialVector]
  simpa only [one_mul] using sum_reversal_fixed d hd (fun _ => 1)

/-- The first-coordinate sign has trace one in even degree. -/
theorem trace_negateFirst (d : ℕ) (hd : Even d) : LinearMap.trace ℚ (H d) (negateFirst d)=1 := by
  rw [trace_coordinates]
  simp only [negateFirst_monomialVector,map_smul,coordinates_monomialVector,Pi.smul_apply,
    Pi.single_eq_same,smul_eq_mul,mul_one]
  rw [Fin.sum_neg_one_pow]
  have hn : ¬Even (d+1) := by
    rw [Nat.even_iff] at hd ⊢
    omega
  simp [hn]

/-- The mixed involution sees the sign of the unique middle monomial. -/
theorem trace_swap_negateFirst (d : ℕ) (hd : Even d) :
    LinearMap.trace ℚ (H d) (swap d * negateFirst d)=(-1 : ℚ)^(d/2) := by
  rw [trace_coordinates]
  simp only [Module.End.mul_apply,negateFirst_monomialVector,map_smul,swap_monomialVector,
    coordinates_monomialVector,Pi.smul_apply,smul_eq_mul]
  exact sum_reversal_fixed d hd (fun i => (-1 : ℚ)^i.val)

end TernaryPoly.BinaryFiniteInvariant
