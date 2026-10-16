module

public import TernaryPeriodPolynomials.AlternatingSolution.OddDegree.Source
public import TernaryPeriodPolynomials.Polynomial.CharTwo.SymbolInjective
public import TernaryPeriodPolynomials.AlternatingSolution.IntegralToddSymbol

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The only input is the exact integer Taylor-to-symbol reduction. -/
theorem odd_alternating_zero_of_integral_symbol_reduction
    (hReduction : ∀ P : MvPolynomial (Fin 3) ℤ,
      alternatingTodd (map (Int.castRingHom ℚ)
        (integerNineFactor*ternaryElementaryEval P))=0 →
      CharTwoToddSymbol.jSymbol (map (Int.castRingHom (ZMod 2)) P)=0)
    {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n)
    (hc : C f=f) (hs : S f= -f) (hn : N f=0) : f=0 := by
  by_contra hf0
  obtain ⟨P,hP,⟨q,hq⟩,hTodd⟩ := odd_alternating_formal_source hf0 hf hodd hc hs hn
  exact hP (CharTwoToddSymbol.zero_of_source_expansion q hq (hReduction P hTodd))

/-- Every odd homogeneous alternating solution of the exact relations is zero. -/
theorem odd_alternating_eq_zero {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n)
    (hc : C f=f) (hs : S f= -f) (hn : N f=0) : f=0 := by
  apply odd_alternating_zero_of_integral_symbol_reduction _ hf hodd hc hs hn
  intro P hP
  exact IntegralToddSymbol.jSymbol_zero_of_alternatingTodd P hP

end TernaryPoly
