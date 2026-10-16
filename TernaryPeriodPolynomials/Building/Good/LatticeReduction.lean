module

public import TernaryPeriodPolynomials.Building.ModThreeGoodAction
public import Mathlib.Tactic.Linarith

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodLatticeReduction
open ModThreeGoodAction Matrix

/-- A normalized frame has every column sum equal to one modulo three. -/
def NormalizedColumns (M : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  ∀ j, ∑ i, (M i j : ZMod 3) = 1

/-- A nonzero fractional lattice point can be moved by one frame column to be good,
while keeping all three coefficient absolute values strictly below one. -/
theorem good_reduction_coefficients (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : NormalizedColumns M) (w : IntegralVector) (a : Fin 3 → ℚ)
    (ha : ∀ i, 0 ≤ a i ∧ a i < 1) (hpos : ∃ k, 0 < a k)
    (hw : rationalVector w = (M.map (Int.castRingHom ℚ)).mulVec a) :
    ∃ (w' : IntegralVector) (a' : Fin 3 → ℚ),
      rationalVector w' = (M.map (Int.castRingHom ℚ)).mulVec a' ∧
      (∑ i, (w' i : ZMod 3)) ≠ 0 ∧ ∀ i, |a' i| < 1 := by
  classical
  by_cases hs : (∑ i, (w i : ZMod 3)) = 0
  · obtain ⟨k,hk⟩ := hpos
    let w' : IntegralVector := fun i => w i - M i k
    let a' : Fin 3 → ℚ := a - Pi.single k 1
    refine ⟨w',a',?_,?_,?_⟩
    · have hc : rationalVector (fun i => M i k) =
          (M.map (Int.castRingHom ℚ)).mulVec (Pi.single k 1) := by
        rw [Matrix.mulVec_single_one]
        rfl
      have hv : rationalVector w' = rationalVector w - rationalVector (fun i => M i k) := by
        funext i
        simp [w',rationalVector]
      rw [hv,hw,hc,← Matrix.mulVec_sub]
    · have hsum : (∑ i, (w' i : ZMod 3)) = -1 := by
        simp only [w',Int.cast_sub,Finset.sum_sub_distrib,hs,hM k,zero_sub]
      rw [hsum]
      exact neg_ne_zero.mpr one_ne_zero
    · intro i
      apply abs_lt.mpr
      by_cases hi : i = k
      · subst i
        have hai := ha k
        simp only [a',Pi.sub_apply,Pi.single_eq_same]
        constructor <;> linarith
      · have hai := ha i
        simp only [a',Pi.sub_apply,Pi.single_eq_of_ne hi,sub_zero]
        constructor <;> linarith
  · refine ⟨w,a,hw,hs,?_⟩
    intro i
    have hai := ha i
    exact abs_lt.mpr ⟨by linarith,hai.2⟩

end TernaryPoly.GoodLatticeReduction
