module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Control.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Exactness of a complex filtered by a well-founded order

Original work by Claude Opus 5.5.

Let `δ` be a differential on the chains `X →₀ ℂ` of a set `X`, with an augmentation `ε`, and let
every cell `x` have an *owner* `o x` in a well-founded linear order, such that `δ` never raises
owners. If for every value `v` the quotient complex of the cells owned by `v` carries a
contracting homotopy, except for a minimal value owning a single cell that the augmentation
detects, then every cycle of augmentation zero is a boundary. This is the discrete Morse
argument: a cycle is pushed down the filtration by subtracting the boundary of the homotopy of
its top piece.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

section Morse

variable {X V : Type} [LinearOrder V]

/-- Every cell in the support of `w` has owner at most `u`. -/
def OwnersLE (o : X → V) (u : V) (w : X →₀ ℂ) : Prop := ∀ y ∈ w.support, o y ≤ u

/-- Every cell in the support of `w` has owner below `u`. -/
def OwnersLT (o : X → V) (u : V) (w : X →₀ ℂ) : Prop := ∀ y ∈ w.support, o y < u

theorem eq_sum_smul_single (w : X →₀ ℂ) :
    w = ∑ x ∈ w.support, w x • Finsupp.single x (1 : ℂ) := by
  conv_lhs => rw [← Finsupp.sum_single w]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.smul_single_one]

/-- A linear map lowering owners on basis cells lowers them on all chains. -/
theorem support_map_le (F : (X →₀ ℂ) →ₗ[ℂ] (X →₀ ℂ)) (w : X →₀ ℂ) {y : X}
    (hy : y ∈ (F w).support) : ∃ x ∈ w.support, y ∈ (F (Finsupp.single x 1)).support := by
  classical
  have e : F w = ∑ x ∈ w.support, w x • F (Finsupp.single x 1) := by
    conv_lhs => rw [eq_sum_smul_single w]
    rw [map_sum]
    simp only [map_smul]
  rw [e] at hy
  obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hy)
  exact ⟨x, hx, Finsupp.support_smul hyx⟩

theorem OwnersLE.map {o : X → V} {F : (X →₀ ℂ) →ₗ[ℂ] (X →₀ ℂ)}
    (hF : ∀ x y : X, y ∈ (F (Finsupp.single x 1)).support → o y ≤ o x) {u : V}
    {w : X →₀ ℂ} (hw : OwnersLE o u w) : OwnersLE o u (F w) := by
  intro y hy
  obtain ⟨x, hx, hyx⟩ := support_map_le F w hy
  exact le_trans (hF x y hyx) (hw x hx)

theorem OwnersLT.map {o : X → V} {F : (X →₀ ℂ) →ₗ[ℂ] (X →₀ ℂ)}
    (hF : ∀ x y : X, y ∈ (F (Finsupp.single x 1)).support → o y ≤ o x) {u : V}
    {w : X →₀ ℂ} (hw : OwnersLT o u w) : OwnersLT o u (F w) := by
  intro y hy
  obtain ⟨x, hx, hyx⟩ := support_map_le F w hy
  exact lt_of_le_of_lt (hF x y hyx) (hw x hx)

/-- The part of a chain owned by `v`. -/
def ownedPart (o : X → V) (v : V) : (X →₀ ℂ) →ₗ[ℂ] (X →₀ ℂ) where
  toFun w := w.filter (fun y => o y = v)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

theorem ownedPart_apply (o : X → V) (v : V) (w : X →₀ ℂ) (y : X) :
    ownedPart o v w y = if o y = v then w y else 0 :=
  Finsupp.filter_apply _ _ _

theorem ownedPart_eq_zero {o : X → V} {v : V} {w : X →₀ ℂ} (hw : OwnersLT o v w) :
    ownedPart o v w = 0 := by
  ext y
  rw [ownedPart_apply, Finsupp.zero_apply]
  split_ifs with h
  · by_contra hy
    exact (hw y (Finsupp.mem_support_iff.mpr hy)).ne h
  · rfl

theorem ownersLT_sub_ownedPart {o : X → V} {v : V} {w : X →₀ ℂ} (hw : OwnersLE o v w) :
    OwnersLT o v (w - ownedPart o v w) := by
  intro y hy
  rw [Finsupp.mem_support_iff, Finsupp.sub_apply, ownedPart_apply] at hy
  split_ifs at hy with h
  · exact absurd (sub_self _) hy
  · rw [sub_zero] at hy
    exact lt_of_le_of_ne (hw y (Finsupp.mem_support_iff.mpr hy)) h

/-- Exactness of an augmented complex filtered by a well-founded linear order, when each
filtration quotient is contractible except the bottom one, which is a single cell detected by
the augmentation. -/
theorem morse_exact [WellFoundedLT V]
    (δ : (X →₀ ℂ) →ₗ[ℂ] (X →₀ ℂ)) (δ_δ : δ ∘ₗ δ = 0)
    (ε : (X →₀ ℂ) →ₗ[ℂ] ℂ) (ε_δ : ε ∘ₗ δ = 0)
    (o : X → V)
    (hδ : ∀ x y : X, y ∈ (δ (Finsupp.single x 1)).support → o y ≤ o x)
    (hstep : ∀ v : V,
      (∃ m : X, (∀ x, o x = v → x = m) ∧ (∀ x, ¬ o x < v) ∧ ε (Finsupp.single m 1) ≠ 0) ∨
      ∃ h : X → (X →₀ ℂ), (∀ x, o x = v → ∀ y ∈ (h x).support, o y = v) ∧
        ∀ x, o x = v →
          (δ (h x)).filter (fun y => o y = v) +
            Finsupp.linearCombination ℂ h ((δ (Finsupp.single x 1)).filter (fun y => o y = v)) =
          Finsupp.single x 1)
    (z : X →₀ ℂ) (hz : δ z = 0) (hε : ε z = 0) : ∃ y, δ y = z := by
  have δδ : ∀ w, δ (δ w) = 0 := fun w => by
    have := LinearMap.congr_fun δ_δ w
    rwa [LinearMap.comp_apply, LinearMap.zero_apply] at this
  have εδ : ∀ w, ε (δ w) = 0 := fun w => by
    have := LinearMap.congr_fun ε_δ w
    rwa [LinearMap.comp_apply, LinearMap.zero_apply] at this
  -- The maximal owner of a nonzero chain.
  have maxOwner : ∀ w : X →₀ ℂ, w ≠ 0 → ∃ u, OwnersLE o u w ∧ ∃ y ∈ w.support, o y = u := by
    intro w hw
    have hne : (w.support.image o).Nonempty :=
      (Finsupp.support_nonempty_iff.mpr hw).image o
    refine ⟨(w.support.image o).max' hne,
      fun y hy => Finset.le_max' _ _ (Finset.mem_image_of_mem o hy), ?_⟩
    obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
    exact ⟨y, hy, hyv⟩
  have claim : ∀ v : V, ∀ z : X →₀ ℂ, δ z = 0 → ε z = 0 → OwnersLE o v z →
      ∃ y, δ y = z := by
    intro v
    induction v using WellFoundedLT.induction
    rename_i v ih
    intro z hz hε hle
    have below : ∀ z', δ z' = 0 → ε z' = 0 → OwnersLT o v z' → ∃ y, δ y = z' := by
      intro z' hz' hε' hlt
      by_cases h0 : z' = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      · obtain ⟨u, hu, y, hy, hyu⟩ := maxOwner z' h0
        exact ih u (by rw [← hyu]; exact hlt y hy) z' hz' hε' hu
    rcases hstep v with ⟨m, hm, hmin, hεm⟩ | ⟨h, hsupp, hhom⟩
    · have hz_eq : z = Finsupp.single m (z m) := by
        classical
        ext y
        rw [Finsupp.single_apply]
        split_ifs with hmy
        · rw [hmy]
        · by_contra hy
          have hyv : o y = v :=
            le_antisymm (hle y (Finsupp.mem_support_iff.mpr hy)) (not_lt.mp (hmin y))
          exact hmy (hm y hyv).symm
      have hzm : z m = 0 := by
        have e : ε z = z m * ε (Finsupp.single m 1) := by
          conv_lhs => rw [hz_eq]
          rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
        rw [e] at hε
        exact (mul_eq_zero.mp hε).resolve_right hεm
      refine ⟨0, ?_⟩
      rw [map_zero, hz_eq, hzm, Finsupp.single_zero]
    · let P := ownedPart o v
      let H := Finsupp.linearCombination ℂ h
      have hL1 : ∀ x, o x = v →
          P (δ (H (Finsupp.single x 1))) + H (P (δ (Finsupp.single x 1))) =
            Finsupp.single x 1 := by
        intro x hx
        have e : H (Finsupp.single x 1) = h x := by
          simp only [H, Finsupp.linearCombination_single, one_smul]
        rw [e]
        exact hhom x hx
      have hL : ∀ w : X →₀ ℂ, (∀ y ∈ w.support, o y = v) →
          P (δ (H w)) + H (P (δ w)) = w := by
        intro w hw
        let L : (X →₀ ℂ) →ₗ[ℂ] (X →₀ ℂ) := P ∘ₗ δ ∘ₗ H + H ∘ₗ P ∘ₗ δ
        have hLw : L w = w := by
          conv_lhs => rw [eq_sum_smul_single w]
          conv_rhs => rw [eq_sum_smul_single w]
          rw [map_sum]
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [map_smul]
          congr 1
          exact hL1 x (hw x hx)
        exact hLw
      let zv := P z
      have hzv : ∀ y ∈ zv.support, o y = v := by
        intro y hy
        rw [Finsupp.mem_support_iff] at hy
        by_contra hne
        apply hy
        show ownedPart o v z y = 0
        rw [ownedPart_apply, ite_eq_right hne]
      have hlt : OwnersLT o v (z - zv) := ownersLT_sub_ownedPart hle
      have hPz : P (δ zv) = 0 := by
        have h1 : P (δ (z - zv)) = 0 := ownedPart_eq_zero (hlt.map hδ)
        have h2 : δ zv + δ (z - zv) = 0 := by
          have e : zv + (z - zv) = z := by abel
          rw [← map_add, e, hz]
        have h3 := congrArg P h2
        rw [map_add, h1, add_zero, map_zero] at h3
        exact h3
      have hPy : P (δ (H zv)) = zv := by
        have := hL zv hzv
        rw [hPz, map_zero, add_zero] at this
        exact this
      have hHle : OwnersLE o v (H zv) := by
        intro y hy
        obtain ⟨x, hx, hyx⟩ := support_map_le H zv hy
        have e : H (Finsupp.single x 1) = h x := by
          simp only [H, Finsupp.linearCombination_single, one_smul]
        rw [e] at hyx
        exact le_of_eq (hsupp x (hzv x hx) y hyx)
      have hδHle : OwnersLE o v (δ (H zv)) := hHle.map hδ
      have hz'lt : OwnersLT o v (z - δ (H zv)) := by
        intro y hy
        rw [Finsupp.mem_support_iff, Finsupp.sub_apply] at hy
        have hle_y : o y ≤ v := by
          by_cases hzy : z y = 0
          · rw [hzy, zero_sub, neg_ne_zero] at hy
            exact hδHle y (Finsupp.mem_support_iff.mpr hy)
          · exact hle y (Finsupp.mem_support_iff.mpr hzy)
        refine lt_of_le_of_ne hle_y fun hyv => hy ?_
        have e1 : zv y = z y := by
          show ownedPart o v z y = z y
          rw [ownedPart_apply, ite_eq_left hyv]
        have e2 : P (δ (H zv)) y = δ (H zv) y := by
          show ownedPart o v (δ (H zv)) y = δ (H zv) y
          rw [ownedPart_apply, ite_eq_left hyv]
        rw [← e1, ← e2, hPy, sub_self]
      obtain ⟨y', hy'⟩ := below (z - δ (H zv))
        (by rw [map_sub, hz, δδ, sub_zero]) (by rw [map_sub, hε, εδ, sub_zero]) hz'lt
      exact ⟨H zv + y', by rw [map_add, hy']; abel⟩
  by_cases h0 : z = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  · obtain ⟨u, hu, -⟩ := maxOwner z h0
    exact claim u z hz hε hu

end Morse

end TernaryPeriodPolynomials.FreeResolution
