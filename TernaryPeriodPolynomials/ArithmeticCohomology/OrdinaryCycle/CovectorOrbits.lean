module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Covectors
public import TernaryPeriodPolynomials.Building.Reference.CoefficientMatrices

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryCovectorOrbits
open OrdinaryCovectors ModThreeGoodAction

/-- The actual right covector action of the norm matrix. -/
def stepA (r : Covector) : Covector := ![r 1,-r 0-r 1,r 2]
def sign12 (r : Covector) : Covector := ![-r 0,-r 1,r 2]
def sign3 (r : Covector) : Covector := ![r 0,r 1,-r 2]

theorem stepA_matrix (r : Covector) :
    stepA r=Matrix.vecMul r (reduction ReferenceCoefficientMatrices.a).val := by
  funext i
  fin_cases i
  all_goals
    simp only [stepA,Matrix.vecMul,dotProduct,Fin.sum_univ_three,reduction,
      Matrix.GeneralLinearGroup.map_apply,ReferenceCoefficientMatrices.a,
      ReferenceCoefficientMatrices.aMatrix,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      map_zero,map_one,map_neg,mul_zero,mul_one,mul_neg,zero_add,add_zero]
  all_goals ring

theorem stepA_cube (r : Covector) : stepA (stepA (stepA r))=r := by
  funext i
  fin_cases i <;> simp [stepA] <;> ring

theorem stepA_sign12 (r : Covector) : stepA (sign12 r)=sign12 (stepA r) := by
  funext i
  fin_cases i <;> simp [stepA,sign12,add_comm]

theorem stepA_sign3 (r : Covector) : stepA (sign3 r)=sign3 (stepA r) := by
  funext i
  fin_cases i <;> simp [stepA,sign3]

/-- Five literal representatives; no zero covector is included. -/
def representative (i : Fin 5) : Covector :=
  ![![0,0,1],![1,1,0],![1,1,1],![1,0,1],![1,0,0]] i

/-- A bounded word in exactly the three generators used for norm propagation. -/
def orbitWord (i : Fin 5) (a : Fin 3) (b c : Fin 2) : Covector :=
  sign3^[c.val] (sign12^[b.val] (stepA^[a.val] (representative i)))

/-- Exhaustive residue certificate. -/
theorem five_orbits_cover : ∀ r : Covector, r≠0 →
    ∃ i : Fin 5,∃ a : Fin 3,∃ b c : Fin 2,orbitWord i a b c=r := by
  decide +kernel

/-- Any predicate propagated by the three actual generators is determined by five fibers. -/
theorem five_fiber_induction (P : Covector → Prop)
    (hA : ∀ r,P r → P (stepA r))
    (h12 : ∀ r,P r → P (sign12 r))
    (h3 : ∀ r,P r → P (sign3 r))
    (hbase : ∀ i,P (representative i)) (r : Covector) (hr : r≠0) : P r := by
  obtain ⟨i,a,b,c,rfl⟩ := five_orbits_cover r hr
  have iter {f : Covector → Covector} (hf : ∀ r,P r → P (f r))
      (n : ℕ) (r : Covector) (h : P r) : P (f^[n] r) := by
    induction n with
    | zero => exact h
    | succ n ih => rw [Function.iterate_succ_apply']; exact hf _ ih
  exact iter h3 c.val _ (iter h12 b.val _ (iter hA a.val _ (hbase i)))

end TernaryPoly.OrdinaryCovectorOrbits
