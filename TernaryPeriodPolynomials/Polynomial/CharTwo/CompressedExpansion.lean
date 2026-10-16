module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.CoefficientRestriction
public import TernaryPeriodPolynomials.Polynomial.CharTwo.EvenKernel

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoNorm

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The eight polynomial multipliers remaining after the forced `c*cplus` factor. -/
def compressedBasis : Fin 8 → Poly :=
  ![1, a^2, a*c, a*b*c, c*(a^3+c), a^3*c*(a^2+b), a*c^2*cplus,
    a*c^2*cplus*(a^2+b)]

/-- The corresponding generators of the original multiplier source. -/
def compressedGenerator (i : Fin 8) : Poly := c*cplus*compressedBasis i

private def formalBasis : Fin 8 → CharTwoFormal.Poly :=
  ![1, CharTwoFormal.a, CharTwoFormal.B2, CharTwoFormal.a*CharTwoFormal.b,
    CharTwoFormal.a^3+CharTwoFormal.c,
    CharTwoFormal.a*(CharTwoFormal.a*CharTwoFormal.b+CharTwoFormal.c),
    CharTwoFormal.a^3*CharTwoFormal.B2, CharTwoFormal.B7]

private theorem elementaryEval_formal_a : elementaryEval CharTwoFormal.a = a := by
  simp [CharTwoFormal.a, elementaryEval]
private theorem elementaryEval_formal_b : elementaryEval CharTwoFormal.b = b := by
  simp [CharTwoFormal.b, elementaryEval]
private theorem elementaryEval_formal_c : elementaryEval CharTwoFormal.c = c := by
  simp [CharTwoFormal.c, elementaryEval]

private theorem elementaryEval_formal_d4 : elementaryEval CharTwoFormal.d4 = d4 := by
  simp [CharTwoFormal.d4, elementaryEval_formal_a, elementaryEval_formal_b,
    elementaryEval_formal_c, d4]
private theorem elementaryEval_formal_d6 : elementaryEval CharTwoFormal.d6 = d6 := by
  simp [CharTwoFormal.d6, elementaryEval_formal_a, elementaryEval_formal_b,
    elementaryEval_formal_c, d6]
private theorem elementaryEval_formal_d7 : elementaryEval CharTwoFormal.d7 = d7 := by
  simp [CharTwoFormal.d7, elementaryEval_formal_a, elementaryEval_formal_b,
    elementaryEval_formal_c, d7, cplus]

/-- Formal even Dickson expressions evaluate to the actual invariant coefficient map. -/
theorem elementaryEval_formalEvenEval (p : Poly) :
    elementaryEval (CharTwoFormal.formalEvenEval p) = invariantEvenEval p := by
  have he : elementaryEval.comp CharTwoFormal.formalEvenEval = invariantEvenEval := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [CharTwoFormal.formalEvenEval, invariantEvenEval,
      elementaryEval_formal_d4, elementaryEval_formal_d6, elementaryEval_formal_d7]
  exact DFunLike.congr_fun he p

private theorem elementaryEval_formalBasis (i : Fin 8) :
    elementaryEval (formalBasis i) = basis i := by
  fin_cases i <;>
    simp [formalBasis, basis, CharTwoFormal.B2, CharTwoFormal.B7,
      elementaryEval_formal_a, elementaryEval_formal_b, elementaryEval_formal_c, cplus]

/-- The formal coefficient restriction applies to every actual symmetric even-basis expansion. -/
theorem coefficient_restriction_of_even_expansion {K : Poly}
    (hs : CharTwoProjector.Symmetric K) (r : Fin 8 → Poly)
    (hr : a*cplus*K =
      invariantEvenEval (r 0) + invariantEvenEval (r 2)*basis 2 +
        invariantEvenEval (r 5)*basis 5 + invariantEvenEval (r 7)*basis 7 +
      d7*(invariantEvenEval (r 1)*basis 1 + invariantEvenEval (r 3)*basis 3 +
        invariantEvenEval (r 4)*basis 4 + invariantEvenEval (r 6)*basis 6)) :
    ∃ u0 u2 : Poly, r 0 = X 1*r 7+X 2*u0 ∧ r 2 = X 0*r 7+X 2*u2 := by
  obtain ⟨P,hP⟩ := exists_elementaryEval hs
  have hf : CharTwoFormal.a*(CharTwoFormal.a*CharTwoFormal.b+CharTwoFormal.c)*P =
      CharTwoFormal.formalEvenEval (r 0) + CharTwoFormal.formalEvenEval (r 2)*formalBasis 2 +
        CharTwoFormal.formalEvenEval (r 5)*formalBasis 5 +
        CharTwoFormal.formalEvenEval (r 7)*formalBasis 7 +
      CharTwoFormal.d7*(CharTwoFormal.formalEvenEval (r 1)*formalBasis 1 +
        CharTwoFormal.formalEvenEval (r 3)*formalBasis 3 +
        CharTwoFormal.formalEvenEval (r 4)*formalBasis 4 +
        CharTwoFormal.formalEvenEval (r 6)*formalBasis 6) := by
    apply elementaryEval_injective
    simpa only [map_add, map_mul, elementaryEval_formal_a, elementaryEval_formal_b,
      elementaryEval_formal_c, hP, elementaryEval_formalEvenEval,
      elementaryEval_formalBasis, elementaryEval_formal_d7, cplus] using hr
  have ha0 : CharTwoFormal.restrictA CharTwoFormal.a = 0 := by
    simp [CharTwoFormal.restrictA, CharTwoFormal.a]
  have hd70 : CharTwoFormal.restrictA CharTwoFormal.d7 = 0 := by
    simp [CharTwoFormal.d7, ha0]
  have h50 : CharTwoFormal.restrictA (formalBasis 5) = 0 := by
    simp [formalBasis, ha0]
  have h := congrArg CharTwoFormal.restrictA hf
  apply CharTwoFormal.coefficient_restriction
  simpa only [map_add, map_mul, ha0, hd70, h50, zero_mul, mul_zero, zero_add, add_zero,
    show formalBasis 2 = CharTwoFormal.B2 from rfl,
    show formalBasis 7 = CharTwoFormal.B7 from rfl] using h.symm

/-- The actual basis relation is the image of the proved formal relation. -/
theorem basis_seven_add_d6_add_d4_mul_basis_two :
    basis 7+d6+d4*basis 2 = a^3*cplus := by
  have h := congrArg elementaryEval CharTwoFormal.B7_add_d6_add_d4_mul_B2
  have h2 : elementaryEval CharTwoFormal.B2 = basis 2 := elementaryEval_formalBasis 2
  have h7 : elementaryEval CharTwoFormal.B7 = basis 7 := elementaryEval_formalBasis 7
  simpa only [map_add, map_mul, map_pow, h2, h7, elementaryEval_formal_d4,
    elementaryEval_formal_d6, elementaryEval_formal_a, elementaryEval_formal_b,
    elementaryEval_formal_c, cplus] using h

private theorem compressed_factorization (R : Fin 8 → Poly) (U0 U2 : Poly) :
    (d6*R 7+d7^2*U0) + (d4*R 7+d7^2*U2)*basis 2 +
      R 5*basis 5 + R 7*basis 7 +
      d7*(R 1*basis 1+R 3*basis 3+R 4*basis 4+R 6*basis 6) =
    a*cplus*∑ i : Fin 8, (![R 5,R 7,R 1,R 3,R 4,R 6,U0,U2] i)*compressedBasis i := by
  have h := basis_seven_add_d6_add_d4_mul_basis_two
  simp only [d7]
  simp [Fin.sum_univ_succ, compressedBasis, basis] at h ⊢
  linear_combination R 7 * h

/-- Every actual even basis expansion compresses to these eight polynomial multipliers. -/
theorem compressed_expansion_of_even_expansion {K : Poly}
    (hs : CharTwoProjector.Symmetric K) (r : Fin 8 → Poly)
    (hr : a*cplus*K =
      invariantEvenEval (r 0) + invariantEvenEval (r 2)*basis 2 +
        invariantEvenEval (r 5)*basis 5 + invariantEvenEval (r 7)*basis 7 +
      d7*(invariantEvenEval (r 1)*basis 1 + invariantEvenEval (r 3)*basis 3 +
        invariantEvenEval (r 4)*basis 4 + invariantEvenEval (r 6)*basis 6)) :
    ∃ q : Fin 8 → Poly, K = ∑ i, invariantEvenEval (q i)*compressedBasis i := by
  obtain ⟨u0,u2,h0,h2⟩ := coefficient_restriction_of_even_expansion hs r hr
  let q : Fin 8 → Poly := ![r 5,r 7,r 1,r 3,r 4,r 6,u0,u2]
  refine ⟨q,?_⟩
  apply mul_left_cancel₀ (mul_ne_zero a_ne_zero cplus_ne_zero)
  rw [hr]
  have he0 : invariantEvenEval (r 0) =
      d6*invariantEvenEval (r 7)+d7^2*invariantEvenEval u0 := by
    rw [h0]
    simp [invariantEvenEval]
  have he2 : invariantEvenEval (r 2) =
      d4*invariantEvenEval (r 7)+d7^2*invariantEvenEval u2 := by
    rw [h2]
    simp [invariantEvenEval]
  rw [he0,he2]
  have hv (i : Fin 8) : invariantEvenEval (q i) =
      ![invariantEvenEval (r 5),invariantEvenEval (r 7),invariantEvenEval (r 1),
        invariantEvenEval (r 3),invariantEvenEval (r 4),invariantEvenEval (r 6),
        invariantEvenEval u0,invariantEvenEval u2] i := by
    fin_cases i <;> rfl
  simpa only [hv] using compressed_factorization (fun i => invariantEvenEval (r i))
    (invariantEvenEval u0) (invariantEvenEval u2)

/-- Membership in the actual generator span gives compressed spanning for an even multiplier. -/
theorem compressed_expansion_of_generatorSpan {K : Poly} {n : ℕ}
    (hs : CharTwoProjector.Symmetric K) (hg : a*cplus*(a*cplus*K) ∈ generatorSpan)
    (hh : (a*cplus*K).IsHomogeneous n) (he : Even n) :
    ∃ q : Fin 8 → Poly, K = ∑ i, invariantEvenEval (q i)*compressedBasis i := by
  obtain ⟨r,hr⟩ := even_basis_expansion_explicit hg hh he
  exact compressed_expansion_of_even_expansion hs r hr

/-- Multiplying a compressed basis expansion by its forced factor gives the source generators. -/
theorem compressedGenerator_expansion {H K : Poly} (hHK : H = c*cplus*K)
    (hK : ∃ q : Fin 8 → Poly, K = ∑ i, invariantEvenEval (q i)*compressedBasis i) :
    ∃ q : Fin 8 → Poly, H = ∑ i, invariantEvenEval (q i)*compressedGenerator i := by
  obtain ⟨q,hq⟩ := hK
  refine ⟨q,?_⟩
  rw [hHK,hq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [compressedGenerator]
  ring

end TernaryPoly.CharTwoNorm
