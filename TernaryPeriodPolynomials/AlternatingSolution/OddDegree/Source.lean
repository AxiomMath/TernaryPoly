module

public import TernaryPeriodPolynomials.AlternatingSolution.OddDegree.Integral
public import TernaryPeriodPolynomials.ArithmeticGroup.ElementaryCoordinates
public import TernaryPeriodPolynomials.Polynomial.CharTwo.FormalSource

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- A nonzero odd alternating rational solution yields a nonzero formal characteristic-two
multiplier in the complete 32-column source, with a genuine integral lift and whole Todd zero. -/
theorem odd_alternating_formal_source {f : TernaryPolynomial} {n : ℕ}
    (hf0 : f ≠ 0) (hf : f.IsHomogeneous n) (hodd : Odd n)
    (hc : C f = f) (hs : S f = -f) (hn : N f = 0) :
    ∃ P : MvPolynomial (Fin 3) ℤ,
      map (Int.castRingHom (ZMod 2)) P ≠ 0 ∧
      (∃ q : Fin 8 × Fin 2 × Fin 2 → CharTwoNorm.Poly,
        map (Int.castRingHom (ZMod 2)) P = ∑ i,
          CharTwoToddSymbol.formalSquaredInvariantEval (q i)*CharTwoFormal.source32 i) ∧
      alternatingTodd (map (Int.castRingHom ℚ)
        (integerNineFactor * ternaryElementaryEval P)) = 0 := by
  obtain ⟨m,s,p,hs0,hmap,hph,hpc,hps,hp2,hj,hrel,hpn⟩ :=
    odd_alternating_integral_reduction hf0 hf hodd hc hs hn
  obtain ⟨P,hP⟩ := exists_ternaryElementaryEval (isSymmetric_of_cyclic_swap hpc hps)
  have hP2 : CharTwoNorm.elementaryEval (map (Int.castRingHom (ZMod 2)) P) =
      map (Int.castRingHom (ZMod 2)) p := by
    rw [← hP,map_ternaryElementaryEval]
    rfl
  refine ⟨P,?_,?_,?_⟩
  · intro hz
    apply hp2
    rw [← hP2,hz,map_zero]
  · apply CharTwoFormal.complete_source_expansion (n := 2*m)
    · rw [hP2]
      exact hph.map _
    · exact even_two_mul m
    · simpa only [hP2] using hpn
  · simpa only [hP] using hj

end TernaryPoly
