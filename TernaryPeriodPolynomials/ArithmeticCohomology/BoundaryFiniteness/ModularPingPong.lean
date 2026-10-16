module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.BinaryPingPong
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Batteries.Data.List.Count
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.WithTopology

@[expose] public section


namespace TernaryPeriodPolynomials.BoundaryFiniteness.ModularPingPong

noncomputable section

open Matrix ModularGroup
open scoped Pointwise

abbrev Modular := SpecialLinearGroup (Fin 2) ℤ

def action : Modular →* Equiv.Perm UpperHalfPlane :=
  MulAction.toPermHom Modular UpperHalfPlane

def inversion : Equiv.Perm UpperHalfPlane := action S

def rotation : Equiv.Perm UpperHalfPlane := action (S * T)

theorem action_neg (g : Modular) : action (-g) = action g := by
  apply Equiv.ext
  intro z
  exact SL_neg_smul g z

theorem S_square : S ^ 2 = -(1 : Modular) := by
  apply Subtype.ext
  simpa [pow_two] using S_mul_S_eq

theorem ST_cube : (S * T) ^ 3 = -(1 : Modular) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, SpecialLinearGroup.coe_mul, coe_S, coe_T, Matrix.mul_apply, Fin.sum_univ_two]

theorem inversion_square : inversion ^ 2 = 1 := by
  rw [inversion, ← map_pow, S_square, action_neg, map_one]

theorem rotation_cube : rotation ^ 3 = 1 := by
  rw [rotation, ← map_pow, ST_cube, action_neg, map_one]

theorem inversion_re (z : UpperHalfPlane) :
    (inversion z).re = -z.re / Complex.normSq (z : ℂ) := by
  change (S • z).re = _
  rw [UpperHalfPlane.modular_S_smul]
  simp [Complex.inv_re, neg_div]

theorem translation_re (z : UpperHalfPlane) : (T • z).re = z.re + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.vadd_re, add_comm]

theorem rotation_re (z : UpperHalfPlane) :
    (rotation z).re = -(z.re + 1) / Complex.normSq ((T • z : UpperHalfPlane) : ℂ) := by
  change ((S * T) • z).re = _
  rw [mul_smul]
  rw [← show inversion (T • z) = S • (T • z) from rfl, inversion_re]
  rw [translation_re]

theorem rotation_square (z : UpperHalfPlane) :
    (rotation ^ 2) z = T⁻¹ • (inversion z) := by
  have relation : (S * T) ^ 2 = -(T⁻¹ * S⁻¹) := by
    have h := congrArg (fun g : Modular => g * (S * T)⁻¹) ST_cube
    change ((S * T) ^ 2 * (S * T)) * (S * T)⁻¹ = _ at h
    rw [mul_inv_cancel_right] at h
    simpa only [_root_.mul_inv_rev, neg_mul, one_mul] using h
  rw [rotation, ← map_pow]
  rw [relation, action_neg]
  change (T⁻¹ * S⁻¹) • z = _
  rw [mul_smul]
  rw [S_inv, SL_neg_smul]
  rfl

theorem rotation_square_re (z : UpperHalfPlane) :
    ((rotation ^ 2) z).re = -z.re / Complex.normSq (z : ℂ) - 1 := by
  rw [rotation_square]
  have translate (w : UpperHalfPlane) : (T⁻¹ • w).re = w.re - 1 := by
    have h := translation_re (T⁻¹ • w)
    simp only [smul_inv_smul] at h
    linarith
  rw [translate, inversion_re]

theorem inversion_positive (z : UpperHalfPlane) (negative : z.re < 0) :
    0 < (inversion z).re := by
  rw [inversion_re]
  exact div_pos (neg_pos.mpr negative) z.normSq_pos

theorem rotation_negative (z : UpperHalfPlane) (positive : 0 < z.re) :
    (rotation z).re < 0 := by
  rw [rotation_re]
  exact div_neg_of_neg_of_pos (by linarith) (T • z).normSq_pos

theorem rotation_square_negative (z : UpperHalfPlane) (positive : 0 < z.re) :
    ((rotation ^ 2) z).re < 0 := by
  rw [rotation_square_re]
  have h := div_neg_of_neg_of_pos (neg_neg_of_pos positive) z.normSq_pos
  linarith

def positivePoint : UpperHalfPlane := ⟨1 + Complex.I, by simp⟩

theorem positivePoint_re : positivePoint.re = 1 := by simp [positivePoint]

theorem inversion_ne_one : inversion ≠ 1 := by
  intro equality
  have h := inversion_re positivePoint
  rw [equality] at h
  norm_num [positivePoint, Complex.normSq_apply] at h

theorem rotation_ne_one : rotation ≠ 1 := by
  intro equality
  have h := rotation_negative positivePoint (by rw [positivePoint_re]; norm_num)
  rw [equality] at h
  norm_num [positivePoint] at h

theorem inversion_order : orderOf inversion = 2 := orderOf_eq_prime inversion_square inversion_ne_one

theorem rotation_order : orderOf rotation = 3 := orderOf_eq_prime rotation_cube rotation_ne_one

instance inversion_finite : Finite (Subgroup.zpowers inversion) :=
  (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, inversion_square⟩).finite_zpowers

instance rotation_finite : Finite (Subgroup.zpowers rotation) :=
  (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, rotation_cube⟩).finite_zpowers

theorem inversion_cases (g : Subgroup.zpowers inversion) : g.val = 1 ∨ g.val = inversion := by
  classical
  have finiteOrder := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, inversion_square⟩
  have h := finiteOrder.mem_zpowers_iff_mem_range_orderOf.mp g.property
  rw [inversion_order] at h
  obtain ⟨n, hn, equation⟩ := Finset.mem_image.mp h
  have bound := Finset.mem_range.mp hn
  interval_cases n
  · exact Or.inl (by simpa using equation.symm)
  · exact Or.inr (by simpa using equation.symm)

theorem rotation_cases (g : Subgroup.zpowers rotation) :
    g.val = 1 ∨ g.val = rotation ∨ g.val = rotation ^ 2 := by
  classical
  have finiteOrder := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, rotation_cube⟩
  have h := finiteOrder.mem_zpowers_iff_mem_range_orderOf.mp g.property
  rw [rotation_order] at h
  obtain ⟨n, hn, equation⟩ := Finset.mem_image.mp h
  have bound := Finset.mem_range.mp hn
  interval_cases n
  · exact Or.inl (by simpa using equation.symm)
  · exact Or.inr (Or.inl (by simpa using equation.symm))
  · exact Or.inr (Or.inr equation.symm)

def freeAction : Monoid.Coprod (Subgroup.zpowers inversion) (Subgroup.zpowers rotation) →*
    Equiv.Perm UpperHalfPlane :=
  Monoid.Coprod.lift (Subgroup.zpowers inversion).subtype (Subgroup.zpowers rotation).subtype

theorem freeAction_injective : Function.Injective freeAction := by
  classical
  let _ := Fintype.ofFinite (Subgroup.zpowers rotation)
  have cardinal : 3 ≤ Cardinal.mk (Subgroup.zpowers rotation) := by
    rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card, Nat.card_zpowers, rotation_order]
    norm_num
  apply BinaryPingPong.lift_injective _ _ cardinal
    {z : UpperHalfPlane | 0 < z.re} {z : UpperHalfPlane | z.re < 0}
  · exact ⟨positivePoint, by change 0 < positivePoint.re; rw [positivePoint_re]; norm_num⟩
  · exact ⟨rotation positivePoint, rotation_negative _ (by rw [positivePoint_re]; norm_num)⟩
  · exact Set.disjoint_left.mpr fun z positive negative =>
      (lt_asymm (show 0 < z.re from positive) (show z.re < 0 from negative)).elim
  · intro g nonidentity z membership
    rcases membership with ⟨w, negative, rfl⟩
    rcases inversion_cases g with identity | generator
    · exact (nonidentity (Subtype.ext identity)).elim
    · change 0 < (g.val w).re
      rw [generator]
      exact inversion_positive w negative
  · intro g nonidentity z membership
    rcases membership with ⟨w, positive, rfl⟩
    rcases rotation_cases g with identity | generator | square
    · exact (nonidentity (Subtype.ext identity)).elim
    · change (g.val w).re < 0
      rw [generator]
      exact rotation_negative w positive
    · change (g.val w).re < 0
      rw [square]
      exact rotation_square_negative w positive

theorem action_range_le_freeAction : action.range ≤ freeAction.range := by
  have inversion_mem : inversion ∈ freeAction.range := by
    refine ⟨Monoid.Coprod.inl ⟨inversion, Subgroup.mem_zpowers inversion⟩, ?_⟩
    simp [freeAction]
  have rotation_mem : rotation ∈ freeAction.range := by
    refine ⟨Monoid.Coprod.inr ⟨rotation, Subgroup.mem_zpowers rotation⟩, ?_⟩
    simp [freeAction]
  have generators : Subgroup.closure ({S, T} : Set Modular) ≤ freeAction.range.comap action := by
    rw [Subgroup.closure_le]
    intro g membership
    rcases membership with rfl | membership
    · exact inversion_mem
    · have equality : g = T := Set.mem_singleton_iff.mp membership
      subst g
      have h := freeAction.range.mul_mem (freeAction.range.inv_mem inversion_mem) rotation_mem
      change action T ∈ freeAction.range
      simpa only [inversion, rotation, map_mul, inv_mul_cancel_left] using h
  rw [_root_.SpecialLinearGroup.SL2Z_generators] at generators
  rintro g ⟨matrix, rfl⟩
  exact generators (Subgroup.mem_top matrix)

def restrictedFreeAction :
    Monoid.Coprod (Subgroup.zpowers inversion) (Subgroup.zpowers rotation) →* action.range :=
  Monoid.Coprod.lift
    ((Subgroup.zpowers inversion).inclusion (Subgroup.zpowers_le.mpr ⟨S, rfl⟩))
    ((Subgroup.zpowers rotation).inclusion (Subgroup.zpowers_le.mpr ⟨S * T, rfl⟩))

theorem restrictedFreeAction_val : action.range.subtype.comp restrictedFreeAction = freeAction := by
  apply Monoid.Coprod.hom_ext <;> ext g <;> simp [restrictedFreeAction, freeAction]

theorem restrictedFreeAction_bijective : Function.Bijective restrictedFreeAction := by
  constructor
  · intro x y equality
    apply freeAction_injective
    have values := congrArg Subtype.val equality
    change (action.range.subtype.comp restrictedFreeAction) x =
      (action.range.subtype.comp restrictedFreeAction) y at values
    rwa [restrictedFreeAction_val] at values
  · intro g
    obtain ⟨word, equation⟩ := action_range_le_freeAction g.property
    refine ⟨word, Subtype.ext ?_⟩
    rw [← equation]
    exact DFunLike.congr_fun restrictedFreeAction_val word

def projectiveEquiv :
    Monoid.Coprod (Subgroup.zpowers inversion) (Subgroup.zpowers rotation) ≃* action.range :=
  MulEquiv.ofBijective restrictedFreeAction restrictedFreeAction_bijective

theorem projective_finitelyPresented : Group.IsFinitelyPresented action.range :=
  Group.IsFinitelyPresented.equiv projectiveEquiv

end

end TernaryPeriodPolynomials.BoundaryFiniteness.ModularPingPong
