module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HeckeTwist

@[expose] public section


/-!
# The paper's representatives are left-coset representatives

Formalized by Claude Sonnet 5.5.
Paper: "The Hecke transfer": "a complete set of right-coset representatives is
`(1 0 0; 0 1 0; b c p)`, `(1 0 0; a p 0; 0 0 1)`, `diag(p,1,1)`".

The matrices `(1 0 0; 0 1 0; b c p)`, `0 ≤ b, c < p`, all lie in ONE right coset `GL₃(ℤ)·δ`: for two of
them `δ_{b,c} δ_{b',c'}⁻¹ = (1 0 0; 0 1 0; b-b' c-c' 1)` is an integral matrix of determinant one
(`lowerFamily_same_right_coset`).  They are representatives of distinct LEFT cosets `δ·GL₃(ℤ)` (the
`p²+p+1` index-`p` column lattices, as the paper says in the next sentence), which is the right
decomposition for an operator on invariants (the Hom model) and the wrong one for an operator on
coinvariants (group homology), where one sums over right cosets `Γ δ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction

/-- The unimodular matrix `(1 0 0; 0 1 0; β γ 1)`. -/
def lowerUnipotent (β γ : ℤ) : IntegralGL :=
  ⟨!![1, 0, 0; 0, 1, 0; β, γ, 1], !![1, 0, 0; 0, 1, 0; -β, -γ, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- All the lower-triangular representatives `(1 0 0; 0 1 0; b c p)` lie in a single right coset
`GL₃(ℤ)·δ`. -/
theorem lowerFamily_same_right_coset (p : ℕ) [Fact p.Prime] (b c b' c' : ZMod p) :
    ∃ u : IntegralGL,
      (OrdinaryHeckeCosets.primeRepresentative p (Sum.inl (b, c))).val =
        (OrdinaryFullAction.integral u).val *
          (OrdinaryHeckeCosets.primeRepresentative p (Sum.inl (b', c'))).val := by
  refine ⟨lowerUnipotent ((b.val : ℤ) - b'.val) ((c.val : ℤ) - c'.val), ?_⟩
  rw [OrdinaryHeckeCosets.primeRepresentative_matrix, OrdinaryHeckeCosets.primeRepresentative_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [OrdinaryFullAction.integral, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.GeneralLinearGroup.map]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
