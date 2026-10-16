module

public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.RotationCoefficients
public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.TraceInvolutions
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodNormMap

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant

/-- Exact trace of rotation on every even homogeneous degree. -/
theorem trace_rotation (d : ℕ) (hd : Even d) :
    LinearMap.trace ℚ (H d) (rotation d) = if d%3=0 then 1 else if d%3=1 then -1 else 0 := by
  rw [trace_rotation_sum d hd,rotationSum_mod_six]
  have hd2 : d%2=0 := Nat.even_iff.mp hd
  have h : d%6=0 ∨ d%6=2 ∨ d%6=4 := by omega
  rcases h with h | h | h
  · rw [h]
    have h3 : d%3=0 := by omega
    simp [h3]
  · rw [h]
    have h3 : d%3=2 := by omega
    norm_num [h3,rotationSum,Finset.sum_range_succ]
  · rw [h]
    have h3 : d%3=1 := by omega
    norm_num [h3,rotationSum,Finset.sum_range_succ]
    decide

/-- Conjugate rotations have equal traces. -/
theorem trace_rotation_sq (d : ℕ) :
    LinearMap.trace ℚ (H d) (rotation d*rotation d) = LinearMap.trace ℚ (H d) (rotation d) := by
  rw [←swap_rotation_swap]
  rw [LinearMap.trace_mul_comm ℚ (swap d*rotation d) (swap d)]
  rw [←mul_assoc,swap_sq,one_mul]

/-- The third reflection is conjugate to swap. -/
theorem trace_swap_rotation_sq (d : ℕ) (hd : Even d) :
    LinearMap.trace ℚ (H d) (swap d*(rotation d*rotation d))=1 := by
  have hr : rotation d*swap d*rotation d=swap d := by
    rw [←swap_rotation_sq,mul_assoc,rotation_cube,mul_one]
  rw [←mul_assoc,LinearMap.trace_mul_comm ℚ (swap d*rotation d) (rotation d),←mul_assoc,hr]
  exact trace_swap d hd

/-- All three actual reflections have trace one in even degree. -/
theorem trace_swap_rotation (d : ℕ) (hd : Even d) :
    LinearMap.trace ℚ (H d) (swap d*rotation d)=1 := by
  rw [LinearMap.trace_mul_comm ℚ (swap d) (rotation d),←swap_rotation_sq]
  exact trace_swap_rotation_sq d hd

end TernaryPoly.BinaryFiniteInvariant
