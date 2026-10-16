module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalPlaneJets
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RelativeEdgeCohomologyPolynomials

/-- Euler's identity on the literal binary face of a homogeneous ternary polynomial. -/
theorem plane_erased_euler {n : ℕ} (a : Poly) (ha : a.IsHomogeneous n) :
    X 0*pderiv 0 (erase 2 a)+X 1*pderiv 1 (erase 2 a)=C (n : ℚ)*erase 2 a := by
  have h := congrArg (erase 2) ha.sum_X_mul_pderiv
  simp only [Fin.sum_univ_three,map_add,map_mul,map_nsmul] at h
  rw [erase_pderiv_of_ne 2 0 (by decide),erase_pderiv_of_ne 2 1 (by decide)] at h
  simpa [← Nat.cast_smul_eq_nsmul ℚ,Algebra.smul_def] using h

/-- The degree-raised contraction detects closed erased plane pairs even in degree zero. -/
theorem plane_erased_contract_kernel {n : ℕ} (a b : Poly)
    (ha : a.IsHomogeneous n) (hb : b.IsHomogeneous n)
    (hclosed : pderiv 0 (erase 2 b)=pderiv 1 (erase 2 a))
    (hq : X 0*erase 2 a+X 1*erase 2 b=0) : erase 2 a=0 ∧ erase 2 b=0 := by
  have he0 := plane_erased_euler a ha
  have he1 := plane_erased_euler b hb
  have h0 := congrArg (pderiv 0) hq
  have h1 := congrArg (pderiv 1) hq
  simp only [map_add,pderiv_mul,pderiv_X_self,pderiv_X_of_ne (by decide : (1 : Fin 3)≠0),
    pderiv_X_of_ne (by decide : (0 : Fin 3)≠1),one_mul,zero_mul,zero_add,map_zero] at h0 h1
  rw [hclosed] at h0
  rw [← hclosed] at h1
  have ha0 : C ((n : ℚ)+1)*erase 2 a=0 := by
    rw [map_add,map_one]
    linear_combination h0-he0
  have hb0 : C ((n : ℚ)+1)*erase 2 b=0 := by
    rw [map_add,map_one]
    linear_combination h1-he1
  have hn : C ((n : ℚ)+1)≠(0 : Poly) := C_ne_zero.mpr (by positivity)
  exact ⟨(mul_eq_zero.mp ha0).resolve_left hn,(mul_eq_zero.mp hb0).resolve_left hn⟩

/-- A single degree-raised polynomial detects exactness of every closed rational-step plane pair. -/
theorem plane_pair_exact_of_contract_zero {n : ℕ} (t : ℚ) (ht : t≠0) (a b : Poly)
    (ha : a.IsHomogeneous n) (hb : b.IsHomogeneous n)
    (hclosed : shearStep 0 2 t b-b=shearStep 1 2 t a-a)
    (hq : X 0*erase 2 a+X 1*erase 2 b=0) :
    ∃ v : Poly,v.IsHomogeneous n ∧
      shearStep 0 2 t v-v=a ∧ shearStep 1 2 t v-v=b := by
  obtain ⟨ha0,hb0⟩ := plane_erased_contract_kernel a b ha hb
    (plane_pair_erased_closed t ht a b hclosed) hq
  exact plane_pair_exact_of_erase_zero t ht a b ha hb hclosed ha0 hb0

end TernaryPoly.OrdinaryFaceRadical
