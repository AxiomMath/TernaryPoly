module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
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
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.MultivariateIntegral

variable {σ : Type*} [DecidableEq σ]

/-- Coordinatewise normalized integration on rational multivariate polynomials. -/
def integral (i : σ) : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ :=
  (Finsupp.lsum ℚ fun d : σ →₀ ℕ =>
    ((d i : ℚ)+1)⁻¹ • (monomial (d+Finsupp.single i 1) : ℚ →ₗ[ℚ] MvPolynomial σ ℚ)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

omit [DecidableEq σ] in
theorem integral_monomial (i : σ) (d : σ →₀ ℕ) (r : ℚ) :
    integral i (monomial d r)=monomial (d+Finsupp.single i 1) (((d i : ℚ)+1)⁻¹*r) := by
  change (Finsupp.lsum ℚ (fun e : σ →₀ ℕ =>
    ((e i : ℚ)+1)⁻¹ • (monomial (e+Finsupp.single i 1) : ℚ →ₗ[ℚ] MvPolynomial σ ℚ)))
    (Finsupp.single d r)=_
  rw [Finsupp.lsum_single]
  simp only [LinearMap.smul_apply,smul_monomial,smul_eq_mul]

omit [DecidableEq σ] in
/-- Coordinatewise integration is a right inverse of the corresponding partial derivative. -/
theorem pderiv_integral (i : σ) (p : MvPolynomial σ ℚ) :
    pderiv i (integral i p)=p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial d r =>
    rw [integral_monomial,pderiv_monomial]
    simp only [Finsupp.add_apply,Finsupp.single_eq_same,Nat.cast_add,Nat.cast_one,
      add_tsub_cancel_right]
    congr 1
    field_simp

/-- Integration in one coordinate commutes with differentiation in another. -/
theorem pderiv_integral_of_ne {i j : σ} (hij : i≠j) (p : MvPolynomial σ ℚ) :
    pderiv j (integral i p)=integral i (pderiv j p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial d r =>
    rw [integral_monomial,pderiv_monomial,pderiv_monomial,integral_monomial]
    have he : d+Finsupp.single i 1-Finsupp.single j 1=
        d-Finsupp.single j 1+Finsupp.single i 1 := by
      ext k
      by_cases hki : k=i
      · subst k
        simp [Finsupp.tsub_apply,hij]
      · by_cases hkj : k=j
        · subst k
          simp [Finsupp.tsub_apply,hki]
        · simp [Finsupp.tsub_apply,hki,hkj]
    rw [he]
    simp only [Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_eq_of_ne hij.symm,
      Finsupp.single_eq_of_ne hij,add_zero,Nat.sub_zero]
    congr 1
    ring

/-- Mixed coordinate derivatives commute literally. -/
theorem pderiv_commute (i j : σ) (p : MvPolynomial σ ℚ) :
    pderiv i (pderiv j p)=pderiv j (pderiv i p) := by
  by_cases h : i=j
  · subst j; rfl
  ext d
  simp only [coeff_pderiv]
  simp [Finsupp.add_apply,Finsupp.single_eq_of_ne h,Finsupp.single_eq_of_ne (Ne.symm h),
    add_comm,add_left_comm,mul_comm,mul_left_comm]

/-- A closed polynomial pair in distinct coordinates has a polynomial potential. -/
theorem exists_potential {i j : σ} (hij : i≠j) (a b : MvPolynomial σ ℚ)
    (h : pderiv j a=pderiv i b) :
    ∃ F : MvPolynomial σ ℚ, pderiv i F=a ∧ pderiv j F=b := by
  let r := b-pderiv j (integral i a)
  have hr : pderiv i r=0 := by
    dsimp [r]
    rw [map_sub,pderiv_commute,pderiv_integral,h,sub_self]
  refine ⟨integral i a+integral j r,?_,?_⟩
  · rw [map_add,pderiv_integral,pderiv_integral_of_ne hij.symm,hr,map_zero,add_zero]
  · rw [map_add,pderiv_integral]
    dsimp [r]
    ring

omit [DecidableEq σ] in
/-- Integration increases the total homogeneous degree by one. -/
theorem integral_homogeneous (i : σ) {p : MvPolynomial σ ℚ} {n : ℕ}
    (hp : p.IsHomogeneous n) : (integral i p).IsHomogeneous (n+1) := by
  change ((Finsupp.lsum ℚ (fun d : σ →₀ ℕ =>
    ((d i : ℚ)+1)⁻¹ • (monomial (d+Finsupp.single i 1) : ℚ →ₗ[ℚ] MvPolynomial σ ℚ)))
    (AddMonoidAlgebra.coeff p)).IsHomogeneous (n+1)
  rw [Finsupp.lsum_apply]
  apply IsHomogeneous.sum
  intro d hd
  have he := hp (Finsupp.mem_support_iff.mp hd)
  change (((d i : ℚ)+1)⁻¹ • monomial (d+Finsupp.single i 1)
    (AddMonoidAlgebra.coeff p d)).IsHomogeneous (n+1)
  rw [smul_monomial]
  apply isWeightedHomogeneous_monomial
  simp only [map_add,Finsupp.weight_single,Pi.one_apply,one_smul,he]

omit [DecidableEq σ] in
/-- A partial derivative lowers a positive homogeneous degree by one. -/
theorem pderiv_homogeneous (i : σ) {p : MvPolynomial σ ℚ} {n : ℕ}
    (hp : p.IsHomogeneous (n+1)) : (pderiv i p).IsHomogeneous n := by
  intro d hd
  rw [coeff_pderiv] at hd
  have he := hp (mul_ne_zero_iff.mp hd).1
  simp only [map_add,Finsupp.weight_single,Pi.one_apply,one_smul] at he
  exact Nat.add_right_cancel he

/-- A homogeneous closed pair has a potential of exactly the required next degree. -/
theorem exists_homogeneous_potential {i j : σ} (hij : i≠j)
    {a b : MvPolynomial σ ℚ} {n : ℕ} (ha : a.IsHomogeneous n)
    (hb : b.IsHomogeneous n) (h : pderiv j a=pderiv i b) :
    ∃ F : MvPolynomial σ ℚ, F.IsHomogeneous (n+1) ∧ pderiv i F=a ∧ pderiv j F=b := by
  let r := b-pderiv j (integral i a)
  have hr : pderiv i r=0 := by
    dsimp [r]
    rw [map_sub,pderiv_commute,pderiv_integral,h,sub_self]
  refine ⟨integral i a+integral j r,?_,?_,?_⟩
  · exact (integral_homogeneous i ha).add
      (integral_homogeneous j (hb.sub (pderiv_homogeneous j (integral_homogeneous i ha))))
  · rw [map_add,pderiv_integral,pderiv_integral_of_ne hij.symm,hr,map_zero,add_zero]
  · rw [map_add,pderiv_integral]
    dsimp [r]
    ring

end TernaryPoly.MultivariateIntegral
