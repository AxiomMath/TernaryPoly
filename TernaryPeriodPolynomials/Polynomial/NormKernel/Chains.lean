module

public import TernaryPeriodPolynomials.Polynomial.NormKernel.AdaptedBasis

@[expose] public section


/-!
# Appendix D: the illustrative degree-five and degree-six chains, and the set `𝓜`

Formalized by Claude Haiku 5.5.

: "In degree five, for example, they successively give `a³b`, `a²c`, `ab²`, and `bc`.
Degree six gives `c²`, `abc`, `b³`, and `a²b²`." defines
`𝓜 = {1,a,b,a²,c,ab,a³,b²,ac,bc,ab²,a²c,c²,b³,a²b²,ac²,bc²,b⁴,b³c,bc³}` (twenty monomials).

Index convention: `standardMonomial k` (`TernaryPoly.DicksonQuotient`) is the `k`-th of the 28 standard
monomials in the paper's order, and `stdTriple k` is its exponent triple `(a,b,c)`. The weighted degree is
`a ↦ 1, b ↦ 2, c ↦ 3` (`wdeg`), the weights under which `d4 = a⁴+ac+b²`, `d6`, `d7` are homogeneous.
`nf` is the remainder on division by the printed Gröbner basis (`AdaptedBasis`), and `printedNFK`,
`printedNFExc`, `nf_K_j`, `nf_exc_i`, `nf_onePlusProjector_k` are the printed tables.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.AppendixDChains

open TernaryPeriodPolynomials.Argument.AppendixD
open TernaryPeriodPolynomials.Argument.CharTwoKernel (genAbs)
open TernaryPoly.DicksonQuotient (Poly a b c standardMonomial)

/-! ### The set `𝓜` and the complement, as indices of the standard monomials -/

/-- The exponent triples `(i, j, k)` of the twenty monomials of `𝓜`, in the order of the paper. -/
def Mtriples : List (ℕ × ℕ × ℕ) :=
  [(0,0,0), (1,0,0), (0,1,0), (2,0,0), (0,0,1), (1,1,0), (3,0,0), (0,2,0), (1,0,1), (0,1,1),
   (1,2,0), (2,0,1), (0,0,2), (0,3,0), (2,2,0), (1,0,2), (0,1,2), (0,4,0), (0,3,1), (0,1,3)]

/-- The weighted degree `a ↦ 1, b ↦ 2, c ↦ 3` of an exponent triple. -/
def wdeg (t : ℕ × ℕ × ℕ) : ℕ := t.1 + 2 * t.2.1 + 3 * t.2.2

/-- The standard monomials lying in `𝓜`, as indices. -/
theorem M_indices :
    Finset.univ.filter (fun k : Fin 28 => stdTriple k ∈ Mtriples) =
      ({0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 17, 19, 21, 22, 25, 27} : Finset (Fin 28)) := by
  decide

/-- The complement of `𝓜` among the standard monomials: `a²b, a³b, abc, b²c, ab³, ab²c, c³, b⁵`. -/
theorem complement_indices :
    Finset.univ.filter (fun k : Fin 28 => stdTriple k ∉ Mtriples) =
      ({9, 13, 16, 18, 20, 23, 24, 26} : Finset (Fin 28)) := by
  decide

/-- The exceptional indices `ab², a²c, b³, ac², bc²` are `excIndex`. -/
theorem exc_indices : Finset.univ.image excIndex = ({11, 12, 15, 19, 21} : Finset (Fin 28)) := by
  decide

/-- The fifteen non-exceptional monomials of `𝓜`. -/
theorem nonExc_indices :
    Finset.univ.filter (fun k : Fin 28 => stdTriple k ∈ Mtriples) \
        ({11, 12, 15, 19, 21} : Finset (Fin 28)) =
      ({0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 14, 17, 22, 25, 27} : Finset (Fin 28)) := by
  decide

/-- The degree-five standard monomials are `bc, ab², a²c, a³b`. -/
theorem deg5_indices :
    Finset.univ.filter (fun k : Fin 28 => wdeg (stdTriple k) = 5) =
      ({10, 11, 12, 13} : Finset (Fin 28)) := by
  decide

/-- The degree-six standard monomials are `c², b³, abc, a²b²`. -/
theorem deg6_indices :
    Finset.univ.filter (fun k : Fin 28 => wdeg (stdTriple k) = 6) =
      ({14, 15, 16, 17} : Finset (Fin 28)) := by
  decide

/-! ### The printed values used in the chains -/

theorem pK1 : printedNFK 1 = a ^ 3 * b + a ^ 2 * c := rfl
theorem pK2 : printedNFK 2 = a * b * c + b ^ 3 + c ^ 2 := rfl
theorem pE0 : printedNFExc 0 = a ^ 3 * b + a ^ 2 * c + a * b ^ 2 := rfl
theorem pE1 : printedNFExc 1 = a ^ 3 * b := rfl
theorem pE2 : printedNFExc 2 = a * b * c + c ^ 2 := rfl

theorem s10 : standardMonomial 10 = b * c := rfl
theorem s14 : standardMonomial 14 = c ^ 2 := rfl
theorem s17 : standardMonomial 17 = a ^ 2 * b ^ 2 := rfl

/-! ### Uniform forms of the printed tables over `𝓜` -/

/-- `(1 + π)m = m` for the fifteen non-exceptional `m ∈ 𝓜`. -/
theorem nf_onePlusProjector_nonExc (k : Fin 28)
    (hk : k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 14, 17, 22, 25, 27} : Finset (Fin 28))) :
    nf (standardMonomial k + projS (standardMonomial k)) = standardMonomial k := by
  fin_cases k
  · exact nf_onePlusProjector_0
  · exact nf_onePlusProjector_1
  · exact nf_onePlusProjector_2
  · exact nf_onePlusProjector_3
  · exact nf_onePlusProjector_4
  · exact nf_onePlusProjector_5
  · exact nf_onePlusProjector_6
  · exact nf_onePlusProjector_7
  · exact nf_onePlusProjector_8
  · exact absurd hk (by decide)
  · exact nf_onePlusProjector_10
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact nf_onePlusProjector_14
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact nf_onePlusProjector_17
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact nf_onePlusProjector_22
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact nf_onePlusProjector_25
  · exact absurd hk (by decide)
  · exact nf_onePlusProjector_27

/-- The printed normal form of `(1 + π)m` for the five exceptional `m`, indexed by `excIndex`. -/
theorem nf_exc_all (i : Fin 5) :
    nf (standardMonomial (excIndex i) + projS (standardMonomial (excIndex i))) = printedNFExc i := by
  fin_cases i
  · exact nf_exc_0
  · exact nf_exc_1
  · exact nf_exc_2
  · exact nf_exc_3
  · exact nf_exc_4

/-! ### The illustrative chains -/

/-- **Degree five:** the normal forms of the degree-five spanning elements give, successively,
`a³b`, `a²c`, `ab²`, `bc`. Here `(1+π)a²c ↦ a³b`, `K₁ ↦ a³b + a²c`, `(1+π)ab² ↦ a³b+a²c+ab²`,
`(1+π)bc ↦ bc`. -/
theorem chain_deg5 :
    nf (standardMonomial 12 + projS (standardMonomial 12)) = a ^ 3 * b ∧
    nf (genAbs 1) - nf (standardMonomial 12 + projS (standardMonomial 12)) = a ^ 2 * c ∧
    nf (standardMonomial 11 + projS (standardMonomial 11)) - nf (genAbs 1) = a * b ^ 2 ∧
    nf (standardMonomial 10 + projS (standardMonomial 10)) = b * c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nf_exc_1, pE1]
  · rw [nf_K_1, nf_exc_1, pK1, pE1]; ring
  · rw [nf_exc_0, nf_K_1, pE0, pK1]; ring
  · rw [nf_onePlusProjector_10, s10]

/-- **Degree six:** the normal forms of the degree-six spanning elements give, successively,
`c²`, `abc`, `b³`, `a²b²`. Here `(1+π)c² ↦ c²`, `(1+π)b³ ↦ abc + c²`, `K₂ ↦ abc+b³+c²`,
`(1+π)a²b² ↦ a²b²`. -/
theorem chain_deg6 :
    nf (standardMonomial 14 + projS (standardMonomial 14)) = c ^ 2 ∧
    nf (standardMonomial 15 + projS (standardMonomial 15)) -
        nf (standardMonomial 14 + projS (standardMonomial 14)) = a * b * c ∧
    nf (genAbs 2) - nf (standardMonomial 15 + projS (standardMonomial 15)) = b ^ 3 ∧
    nf (standardMonomial 17 + projS (standardMonomial 17)) = a ^ 2 * b ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nf_onePlusProjector_14, s14]
  · rw [nf_exc_2, nf_onePlusProjector_14, pE2, s14]; ring
  · rw [nf_K_2, nf_exc_2, pK2, pE2]; ring
  · rw [nf_onePlusProjector_17, s17]

end TernaryPeriodPolynomials.Argument.Identities.AppendixDChains
