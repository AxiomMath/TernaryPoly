module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.CompleteSource
public import TernaryPeriodPolynomials.Polynomial.CharTwo.ToddSymbol

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoFormal

/-- The compressed inner generators, in the formal elementary source coordinates. -/
def compressedBasis : Fin 8 → Poly :=
  ![1,a^2,a*c,a*b*c,c*(a^3+c),a^3*c*(a^2+b),a*c^2*(a*b+c),
    a*c^2*(a*b+c)*(a^2+b)]

def compressedGenerator (i : Fin 8) : Poly := c*(a*b+c)*compressedBasis i

/-- Exact paper order of the 32 formal source columns. -/
def source32 (i : Fin 8 × Fin 2 × Fin 2) : Poly :=
  compressedGenerator i.1 * d4^i.2.1.val * d6^i.2.2.val

private theorem elementary_a : CharTwoNorm.elementaryEval a = CharTwoNorm.a := by
  simp [a,CharTwoNorm.elementaryEval]
private theorem elementary_b : CharTwoNorm.elementaryEval b = CharTwoNorm.b := by
  simp [b,CharTwoNorm.elementaryEval]
private theorem elementary_c : CharTwoNorm.elementaryEval c = CharTwoNorm.c := by
  simp [c,CharTwoNorm.elementaryEval]
private theorem elementary_d4 : CharTwoNorm.elementaryEval d4 = CharTwoNorm.d4 := by
  simp [d4,elementary_a,elementary_b,elementary_c,CharTwoNorm.d4]
private theorem elementary_d6 : CharTwoNorm.elementaryEval d6 = CharTwoNorm.d6 := by
  simp [d6,elementary_a,elementary_b,elementary_c,CharTwoNorm.d6]
private theorem elementary_d7 : CharTwoNorm.elementaryEval d7 = CharTwoNorm.d7 := by
  simp [d7,elementary_a,elementary_b,elementary_c,CharTwoNorm.d7,CharTwoNorm.cplus]

/-- Formal square-invariant coefficients evaluate to their actual counterparts. -/
theorem elementary_formalSquaredInvariantEval (p : Poly) :
    CharTwoNorm.elementaryEval (CharTwoToddSymbol.formalSquaredInvariantEval p) =
      CharTwoNorm.squaredInvariantEval p := by
  have he : CharTwoNorm.elementaryEval.comp CharTwoToddSymbol.formalSquaredInvariantEval =
      CharTwoNorm.squaredInvariantEval := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [CharTwoToddSymbol.formalSquaredInvariantEval,
      CharTwoNorm.squaredInvariantEval, elementary_d4,elementary_d6,elementary_d7]
  exact DFunLike.congr_fun he p

theorem elementary_compressedBasis (i : Fin 8) :
    CharTwoNorm.elementaryEval (compressedBasis i) = CharTwoNorm.compressedBasis i := by
  fin_cases i <;> simp [compressedBasis,CharTwoNorm.compressedBasis,elementary_a,elementary_b,
    elementary_c,CharTwoNorm.cplus]

theorem elementary_source32 (i : Fin 8 × Fin 2 × Fin 2) :
    CharTwoNorm.elementaryEval (source32 i) = CharTwoNorm.source32 i := by
  simp [source32,compressedGenerator,elementary_compressedBasis,elementary_a,elementary_b,
    elementary_c,elementary_d4,elementary_d6,CharTwoNorm.source32,
    CharTwoNorm.compressedGenerator,CharTwoNorm.cplus]

/-- The complete 32-generator source, transported back to formal elementary coordinates. -/
theorem complete_source_expansion {H : Poly} {n : ℕ}
    (hh : (CharTwoNorm.elementaryEval H).IsHomogeneous n) (he : Even n)
    (hn : CharTwoNorm.norm ((CharTwoNorm.a^3*CharTwoNorm.cplus^2)*
      CharTwoNorm.elementaryEval H) = 0) :
    ∃ q : Fin 8 × Fin 2 × Fin 2 → Poly,
      H = ∑ i, CharTwoToddSymbol.formalSquaredInvariantEval (q i)*source32 i := by
  obtain ⟨q,hq⟩ := CharTwoNorm.even_multiplier_source32_expansion hh he
    (CharTwoNorm.symmetric_elementaryEval H) hn
  refine ⟨q,?_⟩
  apply CharTwoNorm.elementaryEval_injective
  simpa only [map_sum,map_mul,elementary_formalSquaredInvariantEval,elementary_source32] using hq

end TernaryPoly.CharTwoFormal
