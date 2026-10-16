module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
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
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.WithTopology

@[expose] public section


open scoped BigOperators

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfiniteCharacter

theorem eq_one_of_powers_near_one (value : ℂ)
    (near : ∀ power : ℕ, ‖value ^ power - 1‖ < 1 / 2) : value = 1 := by
  by_contra different
  have positive : 0 < ‖value - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr different)
  obtain ⟨power, powerBound⟩ := exists_nat_gt (1 / ‖value - 1‖)
  have lower : ∀ index : ℕ, (1 / 2 : ℝ) ≤ (value ^ index).re := by
    intro index
    have reBound := Complex.re_le_norm (1 - value ^ index)
    rw [Complex.sub_re, Complex.one_re, norm_sub_rev] at reBound
    linarith [near index]
  have sumLower : (power : ℝ) / 2 ≤ (∑ index ∈ Finset.range power, value ^ index).re := by
    rw [Complex.re_sum]
    calc
      _ = ∑ _index ∈ Finset.range power, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun index _ => lower index)
  have normLower : (power : ℝ) / 2 ≤ ‖∑ index ∈ Finset.range power, value ^ index‖ :=
    sumLower.trans (Complex.re_le_norm _)
  have product := congrArg norm (geom_sum_mul value power)
  rw [norm_mul] at product
  have big : 1 < (power : ℝ) * ‖value - 1‖ := (div_lt_iff₀ positive).mp powerBound
  have multiplied := mul_le_mul_of_nonneg_right normLower positive.le
  rw [product] at multiplied
  linarith [near power]

theorem locallyConstant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (character : G →* ℂ) (continuous : Continuous character) : IsLocallyConstant character := by
  let neighborhood : Set G := {point | ‖character point - 1‖ < 1 / 2}
  have openNeighborhood : IsOpen neighborhood :=
    isOpen_lt ((continuous.sub continuous_const).norm) continuous_const
  have oneIn : (1 : G) ∈ neighborhood := by simp [neighborhood]
  obtain ⟨subgroup, contained⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one openNeighborhood oneIn
  have trivial : ∀ point ∈ subgroup, character point = 1 := by
    intro point membership
    apply eq_one_of_powers_near_one
    intro power
    have result := contained (subgroup.pow_mem membership power)
    simpa only [neighborhood, Set.mem_ofPred_eq, map_pow] using result
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro point
  refine ⟨(fun other => point⁻¹ * other) ⁻¹' (subgroup : Set G),
    subgroup.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change point⁻¹ * point ∈ subgroup.toOpenSubgroup.toSubgroup
    rw [inv_mul_cancel]
    exact subgroup.one_mem
  · intro other membership
    have equality := trivial (point⁻¹ * other) membership
    calc
      character other = character (point * (point⁻¹ * other)) := by rw [mul_inv_cancel_left]
      _ = character point := by rw [map_mul, equality, mul_one]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfiniteCharacter
