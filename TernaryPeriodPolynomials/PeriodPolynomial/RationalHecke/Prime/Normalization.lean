module

public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Arithmetic.FiniteIndex
public import Mathlib.Algebra.Field.ZMod

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryRationalHeckePrime
open BinaryModularSymbol (GL2)
open Matrix RankTwoAugmentedFrames BinaryRationalHeckeArithmetic

/-- Two actual projective charts over the prime field. -/
abbrev PrimeIndex (p : ℕ) := ZMod p ⊕ Unit

def normalCovector {p : ℕ} : PrimeIndex p → Fin 2 → ZMod p
  | .inl a => ![-a,1]
  | .inr _ => ![1,0]

theorem normalCovector_ne_zero {p : ℕ} [Fact p.Prime] (i : PrimeIndex p) : normalCovector i ≠ 0 := by
  rcases i with a|u
  · intro he
    exact one_ne_zero (congrFun he 1)
  · intro he
    exact one_ne_zero (congrFun he 0)

theorem covector_normalization {p : ℕ} [Fact p.Prime] (v : Fin 2 → ZMod p) (hv : v ≠ 0) :
    ∃ i : PrimeIndex p, ∃ s : ZMod p, s ≠ 0 ∧ v=s • normalCovector i := by
  by_cases h1 : v 1=0
  · have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      funext j
      fin_cases j <;> assumption
    refine ⟨.inr (),v 0,h0,?_⟩
    funext j
    fin_cases j <;> simp [normalCovector,h1]
  · refine ⟨.inl (-v 0/v 1),v 1,h1,?_⟩
    funext j
    fin_cases j <;> simp [normalCovector,div_eq_mul_inv,h1,mul_comm,mul_left_comm]

theorem normalCovector_unique {p : ℕ} [Fact p.Prime] (i j : PrimeIndex p)
    (s : ZMod p) (hs : s ≠ 0) (h : normalCovector i=s • normalCovector j) : i=j := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rcases i with a|u <;> rcases j with c|v <;> dsimp [normalCovector] at h0 h1
  all_goals simp only [mul_one,mul_zero] at h0 h1
  · have hs1 : s=1 := h1.symm
    simp only [hs1,one_mul,neg_inj] at h0
    cases h0
    rfl
  · exact False.elim (one_ne_zero h1)
  · exact False.elim (hs h1.symm)
  · congr

theorem primeIndex_card (p : ℕ) [Fact p.Prime] : Fintype.card (PrimeIndex p)=p+1 := by
  simp [PrimeIndex,Fintype.card_sum,ZMod.card]

end TernaryPoly.BinaryRationalHeckePrime
