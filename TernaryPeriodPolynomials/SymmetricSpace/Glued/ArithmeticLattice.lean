module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticBorel

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceRationalAction SymmetricSpaceRationalGluing
open SymmetricSpaceBorelCorner

/-- One actual integral denominator for every entry of a real matrix. -/
def HasIntegralDenominator (d : ℕ) (r : RealGL) : Prop :=
  ∀ i j,∃ z : ℤ,(z : ℝ)=(d : ℝ)*r.val i j

theorem real_denominator_lower_bound (d : ℕ) (hd : d≠0) (x : ℝ)
    (hx : x≠0) (h : ∃ z : ℤ,(z : ℝ)=(d : ℝ)*x) : 1/(d : ℝ)≤|x| := by
  obtain ⟨z,hz⟩ := h
  have hdR : 0<(d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hzR : (z : ℝ)≠0 := by rw [hz]; exact mul_ne_zero (ne_of_gt hdR) hx
  have hz0 : z≠0 := by exact_mod_cast hzR
  have hz1 : (1 : ℤ)≤|z| := by have := abs_pos.mpr hz0; omega
  have hz1R : (1 : ℝ)≤|(z : ℝ)| := by exact_mod_cast hz1
  rw [hz,abs_mul,abs_of_pos hdR] at hz1R
  exact (div_le_iff₀ hdR).mpr (by simpa only [mul_comm] using hz1R)

/-- Every two-by-two minor has the square of the common entry denominator. -/
theorem minor_denominator (d : ℕ) (r : RealGL) (h : HasIntegralDenominator d r)
    (i j k l : Fin 3) :
    ∃ z : ℤ,(z : ℝ)=((d^2 : ℕ) : ℝ)*(r.val i j*r.val k l-r.val i l*r.val k j) := by
  obtain ⟨a,ha⟩ := h i j
  obtain ⟨b,hb⟩ := h k l
  obtain ⟨c,hc⟩ := h i l
  obtain ⟨e,he⟩ := h k j
  refine ⟨a*b-c*e,?_⟩
  push_cast
  rw [ha,hb,hc,he]
  ring

/-- Relative arithmetic matrices satisfy the real denominator property. -/
theorem relative_hasIntegralDenominator (a b : RationalGL) :
    ∃ d : ℕ,d≠0 ∧ ∀ g : IntegralGL,HasIntegralDenominator d (realRational (relative a b g)) := by
  obtain ⟨d,hd,h⟩ := relative_denominator a b
  refine ⟨d,hd,?_⟩
  intro g i j
  obtain ⟨z,hz⟩ := h g i j
  refine ⟨z,?_⟩
  change (z : ℝ)=(d : ℝ)*((relative a b g).val i j : ℝ)
  exact_mod_cast hz

/-- Real Borel matrices with fixed denominator and bounded determinant have bounded diagonals. -/
theorem real_borel_diagonal_bound (d : ℕ) (hd : d≠0) (D : ℝ) (hD : 0<D) :
    ∃ B : ℝ,0<B ∧ ∀ (r : BorelGroup),HasIntegralDenominator d r.val →
      |r.val.val.det|≤D → ∀ i,|r.val.val i i|≤B := by
  let ε : ℝ := 1/(d : ℝ)
  have hε : 0<ε := one_div_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hd)
  refine ⟨D/ε^2,div_pos hD (sq_pos_of_pos hε),?_⟩
  intro r hr hdet
  have hlo (i : Fin 3) (hi : r.val.val i i≠0) : ε≤|r.val.val i i| :=
    real_denominator_lower_bound d hd _ hi (hr i i)
  have h0 := hlo 0 (diagonal_nonzero r).1
  have h1 := hlo 1 (diagonal_nonzero r).2.1
  have h2 := hlo 2 (diagonal_nonzero r).2.2
  have hp : |r.val.val 0 0| * |r.val.val 1 1| * |r.val.val 2 2|=|r.val.val.det| := by
    conv_rhs => rw [matrix_eq_upper,upperMatrix_det,abs_mul,abs_mul]
  have hdiv : |r.val.val.det|/ε^2≤D/ε^2 := div_le_div_of_nonneg_right hdet (sq_nonneg ε)
  intro i
  fin_cases i
  · exact (triple_factor_bound ε _ _ _ _ hε (abs_nonneg _) h1 h2 hp).trans hdiv
  · change |r.val.val 1 1|≤D/ε^2
    exact (triple_factor_bound ε _ _ _ _ hε (abs_nonneg _) h0 h2 (by nlinarith only [hp])).trans hdiv
  · change |r.val.val 2 2|≤D/ε^2
    exact (triple_factor_bound ε _ _ _ _ hε (abs_nonneg _) h0 h1 (by nlinarith only [hp])).trans hdiv

end TernaryPoly.SymmetricSpaceGluedArithmetic
