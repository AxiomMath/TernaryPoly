module

public import TernaryPeriodPolynomials.Polynomial.Translation
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.ScalarCoboundary
abbrev Poly := MvPolynomial (Fin 2) ℚ
abbrev y : Poly := X 0
abbrev z : Poly := X 1

def A : Poly →ₐ[ℚ] Poly := bind₁ ![-2*y+z,-3*y+z]
def B : Poly →ₐ[ℚ] Poly := bind₁ ![-y,-3*y+z]
def R : Poly →ₐ[ℚ] Poly := bind₁ ![-y,z]
def U : Poly →ₐ[ℚ] Poly := bind₁ ![y,z+3*y]
def axis : Poly →ₐ[ℚ] Poly := bind₁ ![y,0]
def lowerAxis : Poly →ₐ[ℚ] Poly := bind₁ ![0,z]
def flip : Poly →ₐ[ℚ] Poly := bind₁ ![z,y]

private theorem bind_vec (v : Fin 2 → Poly) (a b : Poly) :
    (fun i => bind₁ v (![a,b] i)) = ![bind₁ v a,bind₁ v b] := by
  funext i
  fin_cases i <;> rfl

private theorem finSucc_X_one : finSuccEquiv ℚ 1 (X (1:Fin 2)) =
    Polynomial.C (X (0:Fin 1)) := finSuccEquiv_X_succ (R:=ℚ) (n:=1) (j:=0)

private theorem bind_identity (p : Poly) : bind₁ ![X 0,X 1] p=p := by
  have he : (![y,z]:Fin 2 → Poly)=X := by funext i; fin_cases i <;> rfl
  rw [he,bind₁_X_left]
  rfl

/-- A nontrivial polynomial translation cannot preserve dependence on the translated variable. -/
theorem triple_shear_first (p : Poly)
    (hp : bind₁ ![y+3*z,z] p=p) : bind₁ ![0,z] p=p := by
  have ht (g : Poly) : finSuccEquiv ℚ 1 (bind₁ ![y+3*z,z] g) =
      (finSuccEquiv ℚ 1 g).comp (Polynomial.X+Polynomial.C (3*X (0:Fin 1))) := by
    induction g using MvPolynomial.induction_on with
    | C r => simp [finSuccEquiv_apply]
    | add f g hf hg => simp only [map_add,Polynomial.add_comp,hf,hg]
    | mul_X f i hf =>
      fin_cases i <;> simp [map_mul,hf,Polynomial.mul_comp,y,z,
        finSuccEquiv_X_zero,finSucc_X_one,map_ofNat]
  have ht' := ht p
  rw [hp] at ht'
  have hne : (3*X (0:Fin 1):MvPolynomial (Fin 1) ℚ) ≠ 0 :=
    mul_ne_zero (by norm_num) (X_ne_zero 0)
  have hc := polynomial_eq_constant_of_translation (finSuccEquiv ℚ 1 p)
    (3*X (0:Fin 1)) hne ht'.symm
  have hzero (g : Poly) : finSuccEquiv ℚ 1 (bind₁ ![0,z] g) =
      Polynomial.C ((finSuccEquiv ℚ 1 g).coeff 0) := by
    induction g using MvPolynomial.induction_on with
    | C r => simp [finSuccEquiv_apply]
    | add f g hf hg => simp only [map_add,hf,hg,Polynomial.coeff_add]
    | mul_X f i hf =>
      fin_cases i <;> simp [map_mul,hf,z,finSuccEquiv_X_zero,finSucc_X_one]
  apply (finSuccEquiv ℚ 1).injective
  rw [hzero,hc]
  simp

/-- The two actual involution stabilizers force their common invariant to omit Z. -/
theorem common_fixed_axis {p : Poly} (hb : B p=p) (hr : R p=p) : axis p=p := by
  have hu : U p=p := by
    have h := congrArg R hb
    rw [hr] at h
    simpa [R,B,U,bind₁_bind₁,bind_vec,y,z,map_ofNat,add_comm] using h
  have hflip : bind₁ ![y+3*z,z] (flip p)=flip p := by
    have h := congrArg flip hu
    simpa [flip,U,bind₁_bind₁,bind_vec,y,z,map_ofNat,add_comm] using h
  have ha := congrArg flip (triple_shear_first (flip p) hflip)
  simpa [flip,axis,bind₁_bind₁,bind_vec,y,z,bind_identity] using ha

/-- The literal lower-axis zero kills every scalar coboundary with the two zero path values. -/
theorem zero_of_coboundary {J p : Poly}
    (hb : B p=p) (hr : R p=p) (hj : J=p-A p) (hz : lowerAxis J=0) : J=0 := by
  have ha := common_fixed_axis hb hr
  have haxis : lowerAxis (p-A p) = bind₁ ![0,0] p-bind₁ ![z,0] p := by
    conv_lhs => rw [←ha]
    simp [lowerAxis,A,axis,bind₁_bind₁,bind_vec,y,z]
  rw [hj,haxis] at hz
  have he : bind₁ ![z,0] p=bind₁ ![0,0] p := (sub_eq_zero.mp hz).symm
  have he' := congrArg flip he
  have hc : p=bind₁ ![0,0] p := by
    have h : axis p=bind₁ ![0,0] p := by
      simpa [flip,axis,bind₁_bind₁,bind_vec,y,z,map_ofNat,add_comm] using he'
    rwa [ha] at h
  rw [hj,hc]
  simp [A,bind₁_bind₁,bind_vec,y,z]

end TernaryPoly.ScalarCoboundary
