module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantQuotients

@[expose] public section


open MvPolynomial

noncomputable section
namespace TernaryPoly.RadicalCoinvariantAlgebra

theorem unary_exponent_degree (d : Fin 1 →₀ ℕ) : d.degree = d 0 := by
  simp [Finsupp.degree_eq_sum]

theorem unary_exponent_eq (d : Fin 1 →₀ ℕ) (n : ℕ) (h : d.degree = n) :
    d = Finsupp.single (0 : Fin 1) n := by
  apply Finsupp.ext
  intro i
  fin_cases i
  simpa [unary_exponent_degree] using h

/-- A homogeneous polynomial in one variable is exactly its one permitted monomial. -/
theorem unary_homogeneous_eq (n : ℕ) (p : UnaryH n) :
    (p : MvPolynomial (Fin 1) ℚ) =
      monomial (Finsupp.single (0 : Fin 1) n) ((p : MvPolynomial (Fin 1) ℚ).coeff (Finsupp.single (0 : Fin 1) n)) := by
  ext d
  by_cases hd : d = Finsupp.single (0 : Fin 1) n
  · subst d
    simp
  · have hdeg : d.degree ≠ n := fun h => hd (unary_exponent_eq d n h)
    rw [p.property.coeff_eq_zero hdeg]
    simp [coeff_monomial, Ne.symm hd]

/-- The axis quotient is a genuine one-dimensional coefficient space in every degree. -/
def unaryScalarEquiv (n : ℕ) : UnaryH n ≃ₗ[ℚ] ℚ where
  toFun p := (p : MvPolynomial (Fin 1) ℚ).coeff (Finsupp.single (0 : Fin 1) n)
  invFun c := ⟨monomial (Finsupp.single (0 : Fin 1) n) c,
    isHomogeneous_monomial c (by simp)⟩
  left_inv p := Subtype.ext (unary_homogeneous_eq n p).symm
  right_inv c := by simp
  map_add' p q := rfl
  map_smul' c p := coeff_smul _ _ _

def lineScalarQuotientEquiv (n : ℕ) : (H n ⧸ lineRelations n) ≃ₗ[ℚ] ℚ :=
  (lineQuotientEquiv n).trans (unaryScalarEquiv n)

end TernaryPoly.RadicalCoinvariantAlgebra
