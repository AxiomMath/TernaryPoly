module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Orbit.SymbolSystem
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Orbit.MatrixSpecialization

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoToddSymbol

/-- The literal first-order symbol is injective on the complete formal source. -/
theorem zero_of_source_expansion {H : Poly}
    (q : Fin 8 × Fin 2 × Fin 2 → Poly)
    (he : H=∑ i, formalSquaredInvariantEval (q i)*CharTwoFormal.source32 i)
    (hz : jSymbol H=0) : H=0 :=
  OrbitSymbolSystem.source_zero_of_det_ne_zero
    OrbitMatrixSpecialization.differentialMatrix_det_ne_zero q he hz

/-- All-degree injectivity for the exact even homogeneous norm source. -/
theorem zero_of_even_norm_source {H : Poly} {n : ℕ}
    (hh : (CharTwoNorm.elementaryEval H).IsHomogeneous n) (he : Even n)
    (hn : CharTwoNorm.norm ((CharTwoNorm.a^3*CharTwoNorm.cplus^2)*
      CharTwoNorm.elementaryEval H)=0) (hz : jSymbol H=0) : H=0 := by
  obtain ⟨q,hq⟩ := CharTwoFormal.complete_source_expansion hh he hn
  exact zero_of_source_expansion q hq hz

end TernaryPoly.CharTwoToddSymbol
