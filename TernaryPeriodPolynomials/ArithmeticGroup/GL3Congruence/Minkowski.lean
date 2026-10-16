module

public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Descent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Batteries.Data.List.Count
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Data.Fintype.Order
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.IntegralGL3Congruence
variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Congruence to the identity modulo three is literal divisibility of the difference matrix. -/
theorem matrix_modThree_difference (M : Matrix ι ι ℤ)
    (hM : M.map (Int.castRingHom (ZMod 3))=1) :
    ∃ B : Matrix ι ι ℤ,M-1=(3 : ℤ) • B := by
  have hentry : ∀ i j,(3 : ℤ) ∣ M i j-(1 : Matrix ι ι ℤ) i j := by
    intro i j
    have h := congrArg (fun A : Matrix ι ι (ZMod 3) => A i j) hM
    have hone : (((1 : Matrix ι ι ℤ) i j : ℤ) : ZMod 3)=(1 : Matrix ι ι (ZMod 3)) i j := by
      by_cases hij : i=j <;> simp [Matrix.one_apply,hij]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    change (M i j : ZMod 3)=(1 : Matrix ι ι (ZMod 3)) i j at h
    rw [Int.cast_sub,hone,h,sub_self]
  choose B hB using hentry
  refine ⟨B,?_⟩
  ext i j
  exact hB i j

/-- Elementary Minkowski lemma for arbitrary finite integral matrices. -/
theorem integralMatrix_periodic_modThree_eq_one (M : Matrix ι ι ℤ) (m : ℕ) (hm : 0<m)
    (hp : M^m=1) (hM : M.map (Int.castRingHom (ZMod 3))=1) : M=1 := by
  obtain ⟨B,hB⟩ := matrix_modThree_difference M hM
  have hperiod : M.toLin'^m=1 := by
    rw [←Matrix.toLin'_pow,hp,Matrix.toLin'_one]
    rfl
  have hcong : ∀ v : ι → ℤ,∃w : ι → ℤ,M.toLin' v-v=(3 : ℤ) • w := by
    intro v
    refine ⟨B.mulVec v,?_⟩
    change M.mulVec v-v=(3 : ℤ) • B.mulVec v
    have h := congrArg (fun A : Matrix ι ι ℤ => A.mulVec v) hB
    simpa only [Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec] using h
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_one]
  exact periodic_modThree_eq_one M.toLin' m hm hperiod hcong

/-- The actual level-three kernel in every integral general linear group has no nonidentity
finite-order element. This is ordinary group torsion-freeness, with no unique-root claim. -/
theorem generalLinear_modThree_finiteOrder_eq_one (g : GeneralLinearGroup ι ℤ)
    (hg : GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) g=1)
    (hfin : IsOfFinOrder g) : g=1 := by
  obtain ⟨m,hm,hpow⟩ := hfin.exists_pow_eq_one
  have hp : g.val^m=1 := by
    simpa using congrArg (fun h : GeneralLinearGroup ι ℤ => h.val) hpow
  have hr : g.val.map (Int.castRingHom (ZMod 3))=1 := by
    exact congrArg (fun h : GeneralLinearGroup ι (ZMod 3) => h.val) hg
  apply Units.ext
  exact integralMatrix_periodic_modThree_eq_one g.val m hm hp hr

end TernaryPoly.IntegralGL3Congruence
