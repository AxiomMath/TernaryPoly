module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.FullKernel
public import TernaryPeriodPolynomials.Polynomial.CharTwo.CompressedExpansion
public import TernaryPeriodPolynomials.Polynomial.CharTwo.SquaredCoefficients

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoNorm

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The complete even multiplier source has the eight compressed generators over R0. -/
theorem even_multiplier_compressed_expansion {H : Poly} {n : ℕ}
    (hh : H.IsHomogeneous n) (he : Even n) (hs : CharTwoProjector.Symmetric H)
    (hn : norm ((a^3*cplus^2)*H) = 0) :
    ∃ q : Fin 8 → Poly, H = ∑ i, invariantEvenEval (q i)*compressedGenerator i := by
  obtain ⟨K,hK,hKh,hKs,hKn⟩ := exists_factored_even_multiplier hh he hs hn
  have hmem : a*cplus*(a*cplus*K) ∈ generatorSpan := by
    apply norm_kernel_mem_generatorSpan
    · exact symmetric_mul (symmetric_mul a_symmetric cplus_symmetric)
        (symmetric_mul (symmetric_mul a_symmetric cplus_symmetric) hKs)
    · convert hKn using 1
      congr 1
      ring
  have hhom : (a*cplus*K).IsHomogeneous (4+(n-6)) :=
    (a_homogeneous.mul cplus_homogeneous).mul hKh
  have heven : Even (4+(n-6)) := (by decide : Even (4 : ℕ)).add (he.tsub (by decide : Even (6 : ℕ)))
  exact compressedGenerator_expansion hK
    (compressed_expansion_of_generatorSpan hKs hmem hhom heven)

/-- The complete 32-column source; this order is inner generator, then d4 parity, then d6 parity. -/
def source32 (i : Fin 8 × Fin 2 × Fin 2) : Poly :=
  compressedGenerator i.1 * d4^i.2.1.val * d6^i.2.2.val

/-- The complete source as eight times four columns over square invariants. -/
theorem even_multiplier_squared_expansion {H : Poly} {n : ℕ}
    (hh : H.IsHomogeneous n) (he : Even n) (hs : CharTwoProjector.Symmetric H)
    (hn : norm ((a^3*cplus^2)*H) = 0) :
    ∃ q : Fin 8 × Fin 4 → Poly,
      H = ∑ i, squaredInvariantEval (q i)*(fourFactor i.2*compressedGenerator i.1) := by
  obtain ⟨q,hq⟩ := even_multiplier_compressed_expansion hh he hs hn
  obtain ⟨r,hr⟩ := expansion_over_squared_invariants q compressedGenerator
  exact ⟨r,hq.trans hr⟩

/-- The same complete expansion in the exact paper column order. -/
theorem even_multiplier_source32_expansion {H : Poly} {n : ℕ}
    (hh : H.IsHomogeneous n) (he : Even n) (hs : CharTwoProjector.Symmetric H)
    (hn : norm ((a^3*cplus^2)*H) = 0) :
    ∃ q : Fin 8 × Fin 2 × Fin 2 → Poly,
      H = ∑ i, squaredInvariantEval (q i)*source32 i := by
  obtain ⟨q,hq⟩ := even_multiplier_squared_expansion hh he hs hn
  let r : Fin 8 × Fin 2 × Fin 2 → Poly := fun i =>
    if i.2.1 = 0 then (if i.2.2 = 0 then q (i.1,0) else q (i.1,2))
    else (if i.2.2 = 0 then q (i.1,1) else q (i.1,3))
  refine ⟨r,?_⟩
  rw [hq,Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fintype.sum_prod_type,Fin.sum_univ_succ,r,fourFactor,source32]
  ring

end TernaryPoly.CharTwoNorm
