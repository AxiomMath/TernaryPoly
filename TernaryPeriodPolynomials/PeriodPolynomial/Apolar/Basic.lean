module

public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryHomogeneousCoordinates
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryApolar
open BinaryHomogeneous

variable (K : Type*) [Field K]

/-- The inverse binomial antidiagonal weight in the degree-d apolar pairing. -/
def weight (d : ℕ) (i : Fin (d+1)) : K := (-1 : K)^i.val/(d.choose i.val : K)

theorem weight_ne_zero [CharZero K] (d : ℕ) (i : Fin (d+1)) : weight K d i ≠ 0 := by
  apply div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ i.isLt)).ne'

/-- The actual finite coefficient contraction underlying apolar duality. -/
def value (d : ℕ) (p q : H K d) : K :=
  ∑ i : Fin (d+1),weight K d i * coordinates K d p i * coordinates K d q i.rev

/-- The apolar contraction is bilinear on actual homogeneous binary polynomials. -/
def form (d : ℕ) : LinearMap.BilinForm K (H K d) :=
  LinearMap.mk₂ K (value K d)
    (by intro p q r; simp [value,map_add,add_mul,mul_add,Finset.sum_add_distrib])
    (by
      intro a p q
      simp only [value,map_smul,Pi.smul_apply,smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by intro p q r; simp [value,map_add,mul_add,Finset.sum_add_distrib])
    (by
      intro a p q
      simp only [value,map_smul,Pi.smul_apply,smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

@[simp] theorem form_apply (d : ℕ) (p q : H K d) : form K d p q=value K d p q := rfl

/-- Testing against a genuine coordinate monomial recovers one coefficient with nonzero weight. -/
theorem form_right_monomial (d : ℕ) (p : H K d) (j : Fin (d+1)) :
    form K d p (polynomial K d (Pi.single j.rev 1)) =
      weight K d j * coordinates K d p j := by
  classical
  simp only [form_apply,value,coordinates_polynomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have he : i.rev ≠ j.rev := by
      intro h
      exact hij (Fin.rev_injective h)
    simp [he]
  · simp

/-- Left nondegeneracy follows from the literal coefficient basis, uniformly in degree. -/
theorem separating_left [CharZero K] (d : ℕ) (p : H K d) (hp : ∀ q,form K d p q=0) : p=0 := by
  apply (coefficientEquiv K d).injective
  ext i
  change coordinates K d p i=0
  have he := hp (polynomial K d (Pi.single i.rev 1))
  rw [form_right_monomial] at he
  exact (mul_eq_zero.mp he).resolve_left (weight_ne_zero K d i)

/-- Testing in the first slot has the equally explicit antidiagonal value. -/
theorem form_left_monomial (d : ℕ) (q : H K d) (j : Fin (d+1)) :
    form K d (polynomial K d (Pi.single j 1)) q =
      weight K d j * coordinates K d q j.rev := by
  classical
  simp only [form_apply,value,coordinates_polynomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

theorem separating_right [CharZero K] (d : ℕ) (q : H K d) (hq : ∀ p,form K d p q=0) : q=0 := by
  apply (coefficientEquiv K d).injective
  ext i
  change coordinates K d q i=0
  have he := hq (polynomial K d (Pi.single i.rev 1))
  rw [form_left_monomial,Fin.rev_rev] at he
  exact (mul_eq_zero.mp he).resolve_left (weight_ne_zero K d i.rev)

/-- Nondegeneracy is established for the actual form, not assumed in later dimension arguments. -/
theorem nondegenerate [CharZero K] (d : ℕ) : (form K d).Nondegenerate :=
  ⟨separating_left K d,separating_right K d⟩

end TernaryPoly.BinaryApolar
