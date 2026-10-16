module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Control.Basic
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspHeckeEndomorphism

/-- Fourier index multiplication, the U_p term. -/
def U (p : ℕ) (a : ℕ → ℂ) : ℕ → ℂ := fun n => a (p*n)

/-- Fourier index division with zero insertion, the V_p term. -/
def V (p : ℕ) (a : ℕ → ℂ) : ℕ → ℂ := fun n => if p ∣ n then a (n/p) else 0

@[simp] theorem U_add (p : ℕ) (a b : ℕ → ℂ) : U p (a+b) = U p a + U p b := rfl
@[simp] theorem U_smul (p : ℕ) (c : ℂ) (a : ℕ → ℂ) : U p (c • a) = c • U p a := rfl
@[simp] theorem V_add (p : ℕ) (a b : ℕ → ℂ) : V p (a+b) = V p a + V p b := by
  funext n
  simp only [V,Pi.add_apply]
  split_ifs <;> simp
@[simp] theorem V_smul (p : ℕ) (c : ℂ) (a : ℕ → ℂ) : V p (c • a) = c • V p a := by
  funext n
  simp only [V,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> simp

/-- The U operators commute for all natural indices. -/
theorem U_commute (p q : ℕ) (a : ℕ → ℂ) : U p (U q a) = U q (U p a) := by
  funext n
  simp only [U]
  rw [Nat.mul_left_comm]

/-- Two zero-insertion operators compose by multiplying the indices. -/
theorem V_mul (p q : ℕ) (a : ℕ → ℂ) : V p (V q a) = V (p*q) a := by
  funext n
  by_cases hp : p ∣ n
  · simp only [V,ite_eq_left hp]
    simp only [Nat.dvd_div_iff_mul_dvd hp,Nat.div_div_eq_div_mul]
  · have hpq : ¬p*q ∣ n := fun h => hp (dvd_trans (dvd_mul_right p q) h)
    simp only [V,ite_eq_right hp,ite_eq_right hpq]

/-- The V operators commute for all natural indices. -/
theorem V_commute (p q : ℕ) (a : ℕ → ℂ) : V p (V q a) = V q (V p a) := by
  rw [V_mul,V_mul,Nat.mul_comm p q]

/-- Distinct-prime multiplication and zero insertion commute, with every divisibility condition proved. -/
theorem U_V_commute (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a : ℕ → ℂ) :
    U p (V q a) = V q (U p a) := by
  have hqp : ¬q ∣ p := by
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  funext n
  simp only [U,V,hq.dvd_mul,hqp,false_or]
  split_ifs with hn
  · rw [Nat.mul_div_assoc p hn]
  · rfl

/-- The arithmetic operator matching the actual prime-expression coefficients. -/
def coefficientOperator (d p : ℕ) (a : ℕ → ℂ) : ℕ → ℂ := U p a + (p : ℂ)^(d+1) • V p a

@[simp] theorem coefficientOperator_apply (d p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    coefficientOperator d p a n = a (p*n) + (p : ℂ)^(d+1) * (if p ∣ n then a (n/p) else 0) := rfl

/-- The exact prime coefficient operators commute, including the equal-prime case. -/
theorem coefficientOperator_commute (d p q : ℕ) (hp : p.Prime) (hq : q.Prime) (a : ℕ → ℂ) :
    coefficientOperator d p (coefficientOperator d q a) =
      coefficientOperator d q (coefficientOperator d p a) := by
  by_cases hpq : p=q
  · subst q; rfl
  simp only [coefficientOperator,U_add,U_smul,V_add,V_smul]
  rw [U_commute p q a,V_commute p q a,U_V_commute p q hp hq hpq a,
    U_V_commute q p hq hp (Ne.symm hpq) a]
  funext n
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

end TernaryPoly.BinaryCuspHeckeEndomorphism
