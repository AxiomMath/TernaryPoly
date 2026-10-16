module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.KernelSpan
public import TernaryPeriodPolynomials.Polynomial.CharTwo.CoefficientParity
public import TernaryPeriodPolynomials.Polynomial.CharTwo.MultiplierFactor

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoNorm

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Cancelling the common nonzero factor in the eight generators gives a basis expansion. -/
theorem basis_expansion_of_generatorSpan {g : Poly} (hg : a*cplus*g ∈ generatorSpan) :
    ∃ q : Fin 8 → Poly, g = ∑ i, invariantEval (q i)*basis i := by
  obtain ⟨q,hq⟩ := (mem_generatorSpan_iff _).mp hg
  refine ⟨q,?_⟩
  apply mul_left_cancel₀ (mul_ne_zero a_ne_zero cplus_ne_zero)
  rw [hq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [generator]
  ring

/-- The actual eight-generator span, together with even degree, gives the full even expansion. -/
theorem even_basis_expansion_of_generatorSpan {g : Poly} {n : ℕ}
    (hg : a*cplus*g ∈ generatorSpan) (hh : g.IsHomogeneous n) (he : Even n) :
    ∃ r : Fin 8 → Poly, g = ∑ i,
      (if basisOdd i then d7*invariantEvenEval (r i) else invariantEvenEval (r i))*basis i := by
  obtain ⟨q,hq⟩ := basis_expansion_of_generatorSpan hg
  exact even_basis_expansion (degreeEuler_eq_zero_of_even hh he) q hq

/-- The literal four even terms and four odd terms multiplied by d7. -/
theorem even_basis_expansion_explicit {g : Poly} {n : ℕ}
    (hg : a*cplus*g ∈ generatorSpan) (hh : g.IsHomogeneous n) (he : Even n) :
    ∃ r : Fin 8 → Poly, g =
      invariantEvenEval (r 0) + invariantEvenEval (r 2)*basis 2 +
        invariantEvenEval (r 5)*basis 5 + invariantEvenEval (r 7)*basis 7 +
      d7*(invariantEvenEval (r 1)*basis 1 + invariantEvenEval (r 3)*basis 3 +
        invariantEvenEval (r 4)*basis 4 + invariantEvenEval (r 6)*basis 6) := by
  obtain ⟨r,hr⟩ := even_basis_expansion_of_generatorSpan hg hh he
  refine ⟨r,?_⟩
  rw [hr]
  simp [Fin.sum_univ_succ, basisOdd, basis]
  ring

end TernaryPoly.CharTwoNorm
