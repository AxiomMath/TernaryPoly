module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.ArithmeticFiniteIndex
public import Mathlib.Algebra.Field.ZMod

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHeckeCosets
open Matrix PolynomialGLAction ModThreeGoodAction OrdinaryHeckeArithmetic

/-- Three affine charts for a projective nonzero covector over the prime field. -/
abbrev PrimeIndex (p : ℕ) := (ZMod p × ZMod p) ⊕ (ZMod p ⊕ Unit)

/-- Last-nonzero-coordinate normalization, with signs matching the lower triangular representatives. -/
def normalCovector {p : ℕ} : PrimeIndex p → Fin 3 → ZMod p
  | .inl (b,c) => ![-b,-c,1]
  | .inr (.inl a) => ![-a,1,0]
  | .inr (.inr _) => ![1,0,0]

theorem normalCovector_ne_zero {p : ℕ} [Fact p.Prime] (i : PrimeIndex p) : normalCovector i ≠ 0 := by
  rcases i with ⟨b,c⟩|a|u
  · intro he
    have h := congrFun he 2
    exact one_ne_zero h
  · intro he
    have h := congrFun he 1
    exact one_ne_zero h
  · intro he
    have h := congrFun he 0
    exact one_ne_zero h

/-- Every nonzero covector has a normalized chart and a nonzero scalar. -/
theorem covector_normalization {p : ℕ} [Fact p.Prime] (v : Fin 3 → ZMod p) (hv : v ≠ 0) :
    ∃ i : PrimeIndex p, ∃ s : ZMod p, s ≠ 0 ∧ v=s • normalCovector i := by
  by_cases h2 : v 2=0
  · by_cases h1 : v 1=0
    · have h0 : v 0 ≠ 0 := by
        intro h0
        apply hv
        funext j
        fin_cases j <;> assumption
      refine ⟨.inr (.inr ()),v 0,h0,?_⟩
      funext j
      fin_cases j <;> simp [normalCovector,h1,h2]
    · refine ⟨.inr (.inl (-v 0/v 1)),v 1,h1,?_⟩
      funext j
      fin_cases j <;> simp [normalCovector,h2,div_eq_mul_inv,h1,mul_comm,mul_left_comm]
  · refine ⟨.inl (-v 0/v 2,-v 1/v 2),v 2,h2,?_⟩
    funext j
    fin_cases j <;> simp [normalCovector,div_eq_mul_inv,h2,mul_comm,mul_left_comm]

/-- Scalar proportionality cannot identify two distinct normalized charts. -/
theorem normalCovector_unique {p : ℕ} [Fact p.Prime] (i j : PrimeIndex p)
    (s : ZMod p) (hs : s ≠ 0) (h : normalCovector i=s • normalCovector j) : i=j := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  rcases i with ⟨a,b⟩|a|u <;> rcases j with ⟨c,d⟩|c|v <;>
    dsimp [normalCovector] at h0 h1 h2
  all_goals simp only [mul_one,mul_zero] at h0 h1 h2
  · have hs1 : s=1 := h2.symm
    simp only [hs1,one_mul,neg_inj] at h0 h1
    cases h0
    cases h1
    rfl
  · exact False.elim (one_ne_zero h2)
  · exact False.elim (one_ne_zero h2)
  · exact False.elim (hs h2.symm)
  · have hs1 : s=1 := h1.symm
    simp only [hs1,one_mul,neg_inj] at h0
    cases h0
    rfl
  · exact False.elim (one_ne_zero h1)
  · exact False.elim (hs h2.symm)
  · exact False.elim (hs h1.symm)
  · congr

/-- The explicit chart set has the exact prime Hecke degree. -/
theorem primeIndex_card (p : ℕ) [Fact p.Prime] : Fintype.card (PrimeIndex p)=p^2+p+1 := by
  simp [PrimeIndex,Fintype.card_sum,Fintype.card_prod,ZMod.card,pow_two,add_assoc]

end TernaryPoly.OrdinaryHeckeCosets
