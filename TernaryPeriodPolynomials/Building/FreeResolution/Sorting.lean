module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
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
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Determinants of rows sorted by labels

Original work by Claude Opus 5.5.

For a family of rows `r x` indexed by natural-number labels and a six-element set `X` of
labels, `labelDet r X` is the determinant of the rows listed in increasing order of the labels.
Inserting a new label `y` into a five-element set moves the new row to position
`#{x ∈ X | x < y}`; by Laplace expansion along that row this is the sign `(-1) ^ #{x ∈ X | x < y}`
times the determinant with the new row on top. These are the orientation signs of the
augmentation of the well-rounded complex.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

variable {K : Type} [CommRing K]

/-- The rows `r x`, `x ∈ X`, in increasing order of `x`. -/
def sortedRows {m n : ℕ} (r : ℕ → Fin n → K) (X : Finset ℕ) (h : X.card = m) :
    Fin m → Fin n → K :=
  fun i => r (X.orderEmbOfFin h i)

/-- The determinant of the rows indexed by a six-element set of labels, in increasing order
(zero for sets of another size). -/
def labelDet (r : ℕ → Fin 6 → K) (X : Finset ℕ) : K :=
  if h : X.card = 6 then (Matrix.of (sortedRows r X h)).det else 0

/-- Inserting a label: the determinant with the new row moved to the top changes by the sign of
the number of smaller labels. -/
theorem labelDet_insert (r : ℕ → Fin 6 → K) (X : Finset ℕ) (hX : X.card = 5) (y : ℕ)
    (hy : y ∉ X) :
    labelDet r (insert y X) = (-1) ^ (X.filter (· < y)).card *
      (Matrix.of (Fin.cons (r y) (sortedRows r X hX) : Fin 6 → Fin 6 → K)).det := by
  have h6 : (insert y X).card = 6 := by rw [Finset.card_insert_of_notMem hy, hX]
  rw [labelDet, dite_eq_left h6]
  unfold sortedRows
  have hmemE : ∀ i, (insert y X).orderEmbOfFin h6 i ∈ insert y X :=
    fun i => Finset.orderEmbOfFin_mem _ h6 i
  have hrangeE : ∀ x ∈ insert y X, ∃ i, (insert y X).orderEmbOfFin h6 i = x := by
    intro x hx
    have : x ∈ Set.range ((insert y X).orderEmbOfFin h6) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    exact this
  have huniqX : ∀ f : Fin 5 → ℕ, (∀ j, f j ∈ X) → StrictMono f → f = X.orderEmbOfFin hX :=
    fun f h1 h2 => Finset.orderEmbOfFin_unique hX h1 h2
  generalize (insert y X).orderEmbOfFin h6 = E at hmemE hrangeE ⊢
  generalize X.orderEmbOfFin hX = e at huniqX ⊢
  obtain ⟨q, hq⟩ := hrangeE y (Finset.mem_insert_self y X)
  have himg : (insert y X).filter (· < y) = (Finset.Iio q).image E := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hxy⟩
      obtain ⟨i, rfl⟩ := hrangeE x hx
      refine ⟨i, ?_, rfl⟩
      rw [← hq] at hxy
      exact E.lt_iff_lt.mp hxy
    · rintro ⟨i, hi, rfl⟩
      refine ⟨hmemE i, ?_⟩
      rw [← hq]
      exact E.lt_iff_lt.mpr hi
  have hqcard : (q : ℕ) = (X.filter (· < y)).card := by
    have h1 : (insert y X).filter (· < y) = X.filter (· < y) := by
      rw [Finset.filter_insert, ite_eq_right (lt_irrefl y)]
    rw [← h1, himg, Finset.card_image_of_injective _ E.injective, Fin.card_Iio]
  have hrest : ∀ j : Fin 5, E (q.succAbove j) = e j := by
    have hfs : ∀ j : Fin 5, E (q.succAbove j) ∈ X := by
      intro j
      rcases Finset.mem_insert.mp (hmemE (q.succAbove j)) with h | h
      · exact absurd (E.injective (h.trans hq.symm)) (Fin.succAbove_ne q j)
      · exact h
    have hmono : StrictMono fun j : Fin 5 => E (q.succAbove j) :=
      E.strictMono.comp (Fin.strictMono_succAbove q)
    have := huniqX _ hfs hmono
    intro j
    exact congrFun this j
  rw [Matrix.det_succ_row _ q,
    Matrix.det_succ_row_zero (Matrix.of (Fin.cons (r y) fun i => r (e i) :
      Fin 6 → Fin 6 → K)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsub : (Matrix.of fun i => r (E i)).submatrix q.succAbove j.succAbove =
      (Matrix.of (Fin.cons (r y) fun i => r (e i) : Fin 6 → Fin 6 → K)).submatrix
        Fin.succ j.succAbove := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.cons_succ, hrest a]
  rw [hsub]
  simp only [Matrix.of_apply, Fin.cons_zero, hq]
  rw [hqcard, pow_add]
  ring

/-- Changing the top row by a combination of the other rows and negating it negates the
determinant. -/
theorem det_cons_eq_neg_of_add_mem_span {n : ℕ} (R : Fin n → Fin (n + 1) → K)
    (u w : Fin (n + 1) → K) (hw : w + u ∈ Submodule.span K (Set.range R)) :
    (Matrix.of (Fin.cons w R : Fin (n + 1) → Fin (n + 1) → K)).det =
      -(Matrix.of (Fin.cons u R : Fin (n + 1) → Fin (n + 1) → K)).det := by
  let f : (Fin (n + 1) → K) →ₗ[K] K :=
    (Matrix.detRowAlternating :
      (Fin (n + 1) → K) [⋀^Fin (n + 1)]→ₗ[K] K).toMultilinearMap.toLinearMap (Fin.cons 0 R) 0
  have hf : ∀ v, f v = (Matrix.of (Fin.cons v R : Fin (n + 1) → Fin (n + 1) → K)).det := by
    intro v
    simp only [f, MultilinearMap.toLinearMap_apply, AlternatingMap.coe_multilinearMap,
      Fin.update_cons_zero]
    rfl
  have hker : Submodule.span K (Set.range R) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hf]
    exact Matrix.det_zero_of_row_eq (Fin.succ_ne_zero k).symm (by
      show (Fin.cons (R k) R : Fin (n + 1) → Fin (n + 1) → K) 0 =
        (Fin.cons (R k) R : Fin (n + 1) → Fin (n + 1) → K) k.succ
      simp)
  have h0 : f (w + u) = 0 := hker hw
  rw [map_add, hf, hf] at h0
  exact eq_neg_of_add_eq_zero_left h0

end TernaryPeriodPolynomials.FreeResolution
