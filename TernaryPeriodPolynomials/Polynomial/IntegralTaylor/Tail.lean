module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


namespace TernaryPoly.IntegralTaylorTail

variable {R : Type*} [CommRing R]

/-- A Taylor monomial in the two coordinate differences. -/
def powerTerm (B C : R) (i j : ℕ) : R := B^i*C^j

/-- Its first chain derivative, with arbitrary values of the coordinate derivatives. -/
def firstTerm (B C B1 C1 : R) (i j : ℕ) : R :=
  (i : R)*B^(i-1)*C^j*B1 + (j : R)*B^i*C^(j-1)*C1

/-- Its second chain derivative; every exponent subtraction is natural truncation. -/
def secondTerm (B C B1 C1 B2 C2 : R) (i j : ℕ) : R :=
  (i : R)*((i-1 : ℕ) : R)*B^(i-2)*C^j*B1^2 +
    2*(i : R)*(j : R)*B^(i-1)*C^(j-1)*B1*C1 +
    (j : R)*((j-1 : ℕ) : R)*B^i*C^(j-2)*C1^2 +
    (i : R)*B^(i-1)*C^j*B2 + (j : R)*B^i*C^(j-1)*C2

/-- Powers of two in both coordinate differences accumulate by total Taylor order. -/
theorem two_pow_dvd_power {B C : R} (hB : (2 : R) ∣ B) (hC : (2 : R) ∣ C)
    (i j n : ℕ) (hn : n ≤ i+j) : (2 : R)^n ∣ B^i*C^j := by
  apply (pow_dvd_pow (2 : R) hn).trans
  rw [pow_add]
  exact mul_dvd_mul (pow_dvd_pow_of_dvd hB i) (pow_dvd_pow_of_dvd hC j)

/-- The undifferentiated tail has at least three factors of two. -/
theorem eight_dvd_powerTerm {B C : R} (hB : (2 : R) ∣ B) (hC : (2 : R) ∣ C)
    (i j : ℕ) (hij : 3 ≤ i+j) : (8 : R) ∣ powerTerm B C i j := by
  have h := two_pow_dvd_power hB hC i j 3 hij
  norm_num at h
  exact h

private theorem four_dvd_first_piece {B C : R} (hB : (2 : R) ∣ B) (hC : (2 : R) ∣ C)
    (T : R) (i j : ℕ) (hij : 3 ≤ i+j) : (4 : R) ∣ (i : R)*B^(i-1)*C^j*T := by
  by_cases hi : i = 0
  · simp [hi]
  have h := two_pow_dvd_power hB hC (i-1) j 2 (by omega)
  norm_num at h
  simpa only [mul_assoc] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h (i : R)) T

/-- Differentiating once loses at most one of the three factors of two. -/
theorem four_dvd_firstTerm {B C : R} (hB : (2 : R) ∣ B) (hC : (2 : R) ∣ C)
    (B1 C1 : R) (i j : ℕ) (hij : 3 ≤ i+j) : (4 : R) ∣ firstTerm B C B1 C1 i j := by
  apply dvd_add (four_dvd_first_piece hB hC B1 i j hij)
  convert four_dvd_first_piece hC hB C1 j i (by omega) using 1
  ring

private theorem two_dvd_cast_mul_pred (i : ℕ) : (2 : R) ∣ (i : R)*((i-1 : ℕ) : R) := by
  obtain ⟨k,hk⟩ := Nat.two_dvd_mul_sub_one i
  refine ⟨(k : R),?_⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using congrArg (fun n : ℕ => (n : R)) hk

private theorem four_dvd_second_piece {B C : R} (hB : (2 : R) ∣ B) (hC : (2 : R) ∣ C)
    (T : R) (i j : ℕ) (hij : 3 ≤ i+j) :
    (4 : R) ∣ (i : R)*((i-1 : ℕ) : R)*B^(i-2)*C^j*T^2 := by
  by_cases hi : i < 2
  · have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl <;> simp
  have hm : (2 : R) ∣ B^(i-2)*C^j := by
    simpa only [pow_one] using two_pow_dvd_power hB hC (i-2) j 1 (by omega)
  have h := mul_dvd_mul (two_dvd_cast_mul_pred (R := R) i) hm
  norm_num at h
  simpa only [mul_assoc] using dvd_mul_of_dvd_left h (T^2)

private theorem four_dvd_cross_piece {B C : R} (hB : (2 : R) ∣ B) (hC : (2 : R) ∣ C)
    (B1 C1 : R) (i j : ℕ) (hij : 3 ≤ i+j) :
    (4 : R) ∣ 2*(i : R)*(j : R)*B^(i-1)*C^(j-1)*B1*C1 := by
  by_cases hi : i = 0
  · simp [hi]
  by_cases hj : j = 0
  · simp [hj]
  have hm : (2 : R) ∣ B^(i-1)*C^(j-1) := by
    simpa only [pow_one] using two_pow_dvd_power hB hC (i-1) (j-1) 1 (by omega)
  have hn : (2 : R) ∣ 2*(i : R)*(j : R) := by
    exact ⟨(i : R)*(j : R),by ring⟩
  have h := mul_dvd_mul hn hm
  norm_num at h
  simpa only [mul_assoc] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h B1) C1

/-- In second derivatives, the even falling-factorial coefficients restore one lost factor. -/
theorem four_dvd_secondTerm {B C : R} (hB : (2 : R) ∣ B) (hC : (2 : R) ∣ C)
    (B1 C1 B2 C2 : R) (i j : ℕ) (hij : 3 ≤ i+j) :
    (4 : R) ∣ secondTerm B C B1 C1 B2 C2 i j := by
  have hss : (4 : R) ∣ (j : R)*((j-1 : ℕ) : R)*B^i*C^(j-2)*C1^2 := by
    convert four_dvd_second_piece hC hB C1 j i (by omega) using 1
    ring
  have hfirst := four_dvd_firstTerm hB hC B2 C2 i j hij
  unfold secondTerm
  rw [add_assoc _ _ ((j : R)*B^i*C^(j-1)*C2)]
  exact dvd_add (dvd_add (dvd_add (four_dvd_second_piece hB hC B1 i j hij)
    (four_dvd_cross_piece hB hC B1 C1 i j hij)) hss) hfirst

private theorem four_dvd_of_eight_dvd {r : R} (h : (8 : R) ∣ r) : (4 : R) ∣ r :=
  (show (4 : R) ∣ 8 from ⟨2,by norm_num⟩).trans h

private theorem eight_dvd_two_mul {r : R} (h : (4 : R) ∣ r) : (8 : R) ∣ 2*r := by
  obtain ⟨s,hs⟩ := h
  exact ⟨s,by rw [hs]; ring⟩

/-- Every Taylor order at least three vanishes modulo eight in all three derivative records. -/
theorem tail_record_divisibility {B C : R} (hB : (2 : R) ∣ B) (hC : (2 : R) ∣ C)
    (B1 C1 B2 C2 F F1 F2 : R) (i j : ℕ) (hij : 3 ≤ i+j) :
    (8 : R) ∣ F*powerTerm B C i j ∧
      (8 : R) ∣ 2*(F1*powerTerm B C i j+F*firstTerm B C B1 C1 i j) ∧
      (8 : R) ∣ 2*(F2*powerTerm B C i j+2*F1*firstTerm B C B1 C1 i j+
        F*secondTerm B C B1 C1 B2 C2 i j) := by
  have hp := eight_dvd_powerTerm hB hC i j hij
  have hp4 := four_dvd_of_eight_dvd hp
  have hd := four_dvd_firstTerm hB hC B1 C1 i j hij
  have hdd := four_dvd_secondTerm hB hC B1 C1 B2 C2 i j hij
  refine ⟨dvd_mul_of_dvd_right hp F,?_,?_⟩
  · apply eight_dvd_two_mul
    exact dvd_add (dvd_mul_of_dvd_right hp4 F1) (dvd_mul_of_dvd_right hd F)
  · apply eight_dvd_two_mul
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right hp4 F2)
      (dvd_mul_of_dvd_right hd (2*F1))) (dvd_mul_of_dvd_right hdd F)

/-- Arbitrary finite weighted Taylor tails retain the same uniform divisibility. -/
theorem finite_tail_record_divisibility {ι : Type*} (s : Finset ι)
    (B C B1 C1 B2 C2 F F1 F2 m0 m1 m2 : ι → R) (i j : ι → ℕ)
    (hB : ∀ k ∈ s, (2 : R) ∣ B k) (hC : ∀ k ∈ s, (2 : R) ∣ C k)
    (hij : ∀ k ∈ s, 3 ≤ i k+j k) :
    (8 : R) ∣ ∑ k ∈ s, m0 k*(F k*powerTerm (B k) (C k) (i k) (j k)) ∧
      (8 : R) ∣ ∑ k ∈ s, m1 k*(2*(F1 k*powerTerm (B k) (C k) (i k) (j k)+
        F k*firstTerm (B k) (C k) (B1 k) (C1 k) (i k) (j k))) ∧
      (8 : R) ∣ ∑ k ∈ s, m2 k*(2*(F2 k*powerTerm (B k) (C k) (i k) (j k)+
        2*F1 k*firstTerm (B k) (C k) (B1 k) (C1 k) (i k) (j k)+
        F k*secondTerm (B k) (C k) (B1 k) (C1 k) (B2 k) (C2 k) (i k) (j k))) := by
  have h k hk := tail_record_divisibility (hB k hk) (hC k hk)
    (B1 k) (C1 k) (B2 k) (C2 k) (F k) (F1 k) (F2 k) (i k) (j k) (hij k hk)
  refine ⟨Finset.dvd_sum (fun k hk => dvd_mul_of_dvd_right (h k hk).1 (m0 k)),?_,?_⟩
  · exact Finset.dvd_sum (fun k hk => dvd_mul_of_dvd_right (h k hk).2.1 (m1 k))
  · exact Finset.dvd_sum (fun k hk => dvd_mul_of_dvd_right (h k hk).2.2 (m2 k))

open Polynomial

/-- The first placeholder is the genuine polynomial chain derivative. -/
theorem derivative_powerTerm (B C : Polynomial R) (i j : ℕ) :
    derivative (powerTerm B C i j) = firstTerm B C B.derivative C.derivative i j := by
  simp only [powerTerm,firstTerm,derivative_mul,derivative_pow,C_eq_natCast]
  ring

/-- The second placeholder is the genuine iterated chain derivative, including small exponents. -/
theorem derivative_firstTerm (B C : Polynomial R) (i j : ℕ) :
    derivative (firstTerm B C B.derivative C.derivative i j) =
      secondTerm B C B.derivative C.derivative B.derivative.derivative C.derivative.derivative i j := by
  simp only [firstTerm,secondTerm,derivative_add,derivative_mul,derivative_pow,
    derivative_natCast,zero_mul,zero_add,C_eq_natCast,Nat.sub_sub]
  norm_num only [Nat.reduceAdd]
  ring

/-- The first product derivative has the stated Taylor record. -/
theorem derivative_mul_powerTerm (F B C : Polynomial R) (i j : ℕ) :
    derivative (F*powerTerm B C i j) =
      F.derivative*powerTerm B C i j+F*firstTerm B C B.derivative C.derivative i j := by
  rw [derivative_mul,derivative_powerTerm]

/-- The second product derivative has the stated Taylor record. -/
theorem derivative_twice_mul_powerTerm (F B C : Polynomial R) (i j : ℕ) :
    derivative (derivative (F*powerTerm B C i j)) =
      F.derivative.derivative*powerTerm B C i j+
        2*F.derivative*firstTerm B C B.derivative C.derivative i j+
        F*secondTerm B C B.derivative C.derivative B.derivative.derivative C.derivative.derivative i j := by
  rw [derivative_mul_powerTerm,derivative_add,derivative_mul,derivative_mul,
    derivative_powerTerm,derivative_firstTerm]
  ring

variable {S : Type*} [CommRing S]

/-- Taylor monomials commute with every ring homomorphism. -/
theorem map_powerTerm (φ : R →+* S) (B C : R) (i j : ℕ) :
    φ (powerTerm B C i j) = powerTerm (φ B) (φ C) i j := by
  simp only [powerTerm,map_mul,map_pow]

/-- First Taylor chain records commute with every ring homomorphism. -/
theorem map_firstTerm (φ : R →+* S) (B C B1 C1 : R) (i j : ℕ) :
    φ (firstTerm B C B1 C1 i j) = firstTerm (φ B) (φ C) (φ B1) (φ C1) i j := by
  simp only [firstTerm,map_add,map_mul,map_pow,map_natCast]

/-- Second Taylor chain records commute with every ring homomorphism. -/
theorem map_secondTerm (φ : R →+* S) (B C B1 C1 B2 C2 : R) (i j : ℕ) :
    φ (secondTerm B C B1 C1 B2 C2 i j) =
      secondTerm (φ B) (φ C) (φ B1) (φ C1) (φ B2) (φ C2) i j := by
  simp only [secondTerm,map_add,map_mul,map_pow,map_natCast,map_ofNat]

/-- Evaluated polynomial derivatives satisfy the uniform omitted-tail estimate.
The evaluation hom may specialize a separate differentiation variable, so the reference pair
can be held fixed as coefficient data throughout differentiation. -/
theorem polynomial_tail_record_divisibility (φ : Polynomial R →+* S)
    (F B C : Polynomial R) (hB : (2 : S) ∣ φ B) (hC : (2 : S) ∣ φ C)
    (i j : ℕ) (hij : 3 ≤ i+j) :
    (8 : S) ∣ φ (F*powerTerm B C i j) ∧
      (8 : S) ∣ 2*φ (derivative (F*powerTerm B C i j)) ∧
      (8 : S) ∣ 2*φ (derivative (derivative (F*powerTerm B C i j))) := by
  have h := tail_record_divisibility hB hC (φ B.derivative) (φ C.derivative)
    (φ B.derivative.derivative) (φ C.derivative.derivative)
    (φ F) (φ F.derivative) (φ F.derivative.derivative) i j hij
  rw [derivative_twice_mul_powerTerm,derivative_mul_powerTerm]
  simpa only [map_add,map_mul,map_ofNat,map_powerTerm,map_firstTerm,map_secondTerm] using h

/-- A finite sum of arbitrary weighted evaluated polynomial tail records is a multiple of eight. -/
theorem finite_polynomial_tail_record_divisibility {ι : Type*} (s : Finset ι)
    (φ : Polynomial R →+* S) (F B C : ι → Polynomial R)
    (m0 m1 m2 : ι → S) (i j : ι → ℕ)
    (hB : ∀ k ∈ s, (2 : S) ∣ φ (B k)) (hC : ∀ k ∈ s, (2 : S) ∣ φ (C k))
    (hij : ∀ k ∈ s, 3 ≤ i k+j k) :
    (8 : S) ∣ ∑ k ∈ s, m0 k*φ (F k*powerTerm (B k) (C k) (i k) (j k)) ∧
      (8 : S) ∣ ∑ k ∈ s, m1 k*(2*φ (derivative (F k*powerTerm (B k) (C k) (i k) (j k)))) ∧
      (8 : S) ∣ ∑ k ∈ s, m2 k*(2*φ (derivative (derivative
        (F k*powerTerm (B k) (C k) (i k) (j k))))) := by
  have h k hk := polynomial_tail_record_divisibility φ (F k) (B k) (C k)
    (hB k hk) (hC k hk) (i k) (j k) (hij k hk)
  refine ⟨Finset.dvd_sum (fun k hk => dvd_mul_of_dvd_right (h k hk).1 (m0 k)),?_,?_⟩
  · exact Finset.dvd_sum (fun k hk => dvd_mul_of_dvd_right (h k hk).2.1 (m1 k))
  · exact Finset.dvd_sum (fun k hk => dvd_mul_of_dvd_right (h k hk).2.2 (m2 k))

end TernaryPoly.IntegralTaylorTail
