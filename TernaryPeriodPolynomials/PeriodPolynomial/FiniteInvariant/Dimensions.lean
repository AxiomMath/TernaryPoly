module

public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.TraceRotation
public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.Projectors
public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.Arithmetic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant

private theorem trace_one (d : ℕ) :
    LinearMap.trace ℚ (H d) (1 : Module.End ℚ (H d))=(d+1 : ℕ) := by
  rw [show (1 : Module.End ℚ (H d))=LinearMap.id by rfl,LinearMap.trace_id,finrank_homogeneous]

/-- The odd-symmetric averaging projector has its exact character trace. -/
theorem trace_oddProjector (d : ℕ) (hd : Even d) :
    LinearMap.trace ℚ (H d) (oddProjector d) =
      (1/4 : ℚ)*((d+1 : ℕ)-(-1 : ℚ)^(d/2)) := by
  rw [oddProjector,add_mul,
    mul_sub (1 : Module.End ℚ (H d)) 1 (negateFirst d),
    mul_sub (swap d) 1 (negateFirst d),one_mul,one_mul,mul_one]
  simp only [map_smul,map_add,smul_eq_mul]
  rw [map_sub (LinearMap.trace ℚ (H d)) (1 : Module.End ℚ (H d)) (negateFirst d),
    map_sub (LinearMap.trace ℚ (H d)) (swap d) (swap d*negateFirst d)]
  rw [trace_one,trace_swap d hd,trace_negateFirst d hd,trace_swap_negateFirst d hd]
  ring

/-- The six-term invariant projector has its exact character trace. -/
theorem trace_invariantProjector (d : ℕ) (hd : Even d) :
    LinearMap.trace ℚ (H d) (invariantProjector d) =
      (1/6 : ℚ)*((d+4 : ℕ)+2*(if d%3=0 then 1 else if d%3=1 then -1 else 0)) := by
  simp only [invariantProjector,norm,add_mul,mul_add,one_mul,mul_one,map_smul,map_add,
    smul_eq_mul,trace_one,trace_rotation_sq,trace_rotation d hd,trace_swap d hd,
    trace_swap_rotation d hd,trace_swap_rotation_sq d hd]
  push_cast
  ring

/-- Exact dimension of the actual symmetric, separately odd homogeneous polynomials. -/
theorem oddSymmetric_finrank (d : ℕ) (hd : Even d) :
    Module.finrank ℚ (oddSymmetric d)=(d+2)/4 := by
  let : Module.Free ℚ (oddSymmetric d) := Module.Free.of_divisionRing ℚ (oddSymmetric d)
  let : Module.Free ℚ (oddProjector d).ker := Module.Free.of_divisionRing ℚ (oddProjector d).ker
  have h := (oddProjector_isProj d hd).trace
  rw [trace_oddProjector d hd,odd_count_arithmetic d hd] at h
  exact_mod_cast h.symm

/-- Exact dimension of the actual simultaneous swap-and-rotation invariants. -/
theorem invariants_finrank (d : ℕ) (hd : Even d) :
    Module.finrank ℚ (invariants d)=d/6+1 := by
  let : Module.Free ℚ (invariants d) := Module.Free.of_divisionRing ℚ (invariants d)
  let : Module.Free ℚ (invariantProjector d).ker := Module.Free.of_divisionRing ℚ (invariantProjector d).ker
  have h := (invariantProjector_isProj d).trace
  rw [trace_invariantProjector d hd,invariant_count_arithmetic d hd] at h
  exact_mod_cast h.symm

end TernaryPoly.BinaryFiniteInvariant
