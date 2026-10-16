module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Data.Fin.Parity
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
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothLocalDeRham
open Set ContinuousAlternatingMap
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ambient representatives of vector-valued differential forms. -/
abbrev RawForm (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) := E → E [⋀^Fin n]→L[ℝ] F

/-- Smooth chart forms have the canonical zero extension outside their domain.
No regularity across the boundary of the domain is required. -/
def formSubmodule (s : Set E) (n : ℕ) : Submodule ℝ (RawForm E F n) where
  carrier := {w | ContDiffOn ℝ ∞ w s ∧ ∀ x ∉ s, w x = 0}
  zero_mem' := ⟨contDiffOn_const, by simp⟩
  add_mem' hw hη := ⟨hw.1.add hη.1, by
    intro x hx
    simp [hw.2 x hx, hη.2 x hx]⟩
  smul_mem' c w hw := ⟨hw.1.const_smul c, by
    intro x hx
    simp [hw.2 x hx]⟩

abbrev Form (s : Set E) (n : ℕ) := formSubmodule (F := F) s n

theorem Form.smooth {s : Set E} {n : ℕ} (w : Form (F := F) s n) :
    ContDiffOn ℝ ∞ (w : RawForm E F n) s := w.property.1

theorem Form.outside {s : Set E} {n : ℕ} (w : Form (F := F) s n)
    {x : E} (hx : x ∉ s) : (w : RawForm E F n) x = 0 := w.property.2 x hx

@[ext] theorem Form.ext {s : Set E} {n : ℕ} {w η : Form (F := F) s n}
    (h : ∀ x ∈ s, (w : RawForm E F n) x = (η : RawForm E F n) x) : w = η := by
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ s
  · exact h x hx
  · rw [Form.outside w hx, Form.outside η hx]

/-- Canonical chart restriction of an ambient smooth-on-domain form. -/
def restrictForm (s : Set E) {n : ℕ} (w : RawForm E F n)
    (hw : ContDiffOn ℝ ∞ w s) : Form (F := F) s n :=
  ⟨s.indicator w, hw.congr (by intro x hx; simp [hx]), by
    intro x hx
    simp [hx]⟩

@[simp] theorem restrictForm_apply {s : Set E} {n : ℕ} (w : RawForm E F n)
    (hw : ContDiffOn ℝ ∞ w s) {x : E} (hx : x ∈ s) :
    (restrictForm s w hw : RawForm E F n) x = w x := by simp [restrictForm, hx]

theorem smooth_extDeriv {s : Set E} (hs : IsOpen s) {n : ℕ}
    {w : RawForm E F n} (hw : ContDiffOn ℝ ∞ w s) :
    ContDiffOn ℝ ∞ (extDeriv w) s := by
  unfold extDeriv
  change ContDiffOn ℝ ∞ ((alternatizeUncurryFinCLM ℝ E F (n := n)) ∘ fderiv ℝ w) s
  exact (alternatizeUncurryFinCLM ℝ E F (n := n)).contDiff.comp_contDiffOn
    ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hw).2

/-- The chart differential is exactly Mathlib's exterior derivative at every chart point. -/
def d {s : Set E} (hs : IsOpen s) (n : ℕ) :
    Form (F := F) s n →ₗ[ℝ] Form (F := F) s (n + 1) where
  toFun w := restrictForm s (extDeriv (w : RawForm E F n)) (smooth_extDeriv hs (Form.smooth w))
  map_add' w η := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, AddMemClass.coe_add, Pi.add_apply]
    exact extDeriv_add ((((Form.smooth w) x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp))
      ((((Form.smooth η) x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp))
  map_smul' c w := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
    exact extDeriv_smul c _

@[simp] theorem d_apply {s : Set E} (hs : IsOpen s) {n : ℕ}
    (w : Form (F := F) s n) {x : E} (hx : x ∈ s) :
    (d hs n w : RawForm E F (n + 1)) x = extDeriv (w : RawForm E F n) x :=
  restrictForm_apply _ (smooth_extDeriv hs (Form.smooth w)) hx

theorem d_squared {s : Set E} (hs : IsOpen s) (n : ℕ)
    (w : Form (F := F) s n) : d hs (n + 1) (d hs n w) = 0 := by
  apply Form.ext
  intro x hx
  rw [d_apply hs _ hx]
  have heq : (d hs n w : RawForm E F (n + 1)) =ᶠ[𝓝 x]
      extDeriv (w : RawForm E F n) := by
    filter_upwards [hs.mem_nhds hx] with y hy using d_apply hs w hy
  rw [heq.extDeriv_eq]
  exact extDeriv_extDeriv_apply (((Form.smooth w) x hx).contDiffAt (hs.mem_nhds hx)) (by simp)

/-- The genuine smooth chart de Rham complex in every nonnegative degree. -/
def complex {s : Set E} (hs : IsOpen s) : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℝ (Form (F := F) s n))
    (fun n => ModuleCat.ofHom (d hs n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact d_squared hs n w)

end TernaryPoly.SmoothLocalDeRham
