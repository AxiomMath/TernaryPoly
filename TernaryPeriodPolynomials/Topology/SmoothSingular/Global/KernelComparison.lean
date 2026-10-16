module

/- Explicit real base-ring port of the SingularCochainKernelComparison.lean;
its actual kernel and short-exact hypotheses are retained unchanged. -/
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal.RealCochainExcision
open CategoryTheory Limits HomologicalComplex ComposableArrows HomologySequence

/-- In a map of short exact cochain sequences, quasi-isomorphisms on the middle and right
complexes give a quasi-isomorphism on the left, including degree zero. -/
theorem quasiIso_left {S T : ShortComplex (CochainComplex (ModuleCat.{0} ℝ) ℕ)}
    (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)
    [QuasiIso φ.τ₂] [QuasiIso φ.τ₃] : QuasiIso φ.τ₁ := by
  have : Mono S.f := hS.mono_f
  have : Mono T.f := hT.mono_f
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  cases k with
  | zero =>
    have hs : Mono (homologyMap S.f 0) :=
      mono_homologyMap_of_mono_of_not_rel S.f 0 (by intro i hi; exact Nat.not_succ_le_zero i (Nat.le_of_eq hi))
    have ht : Mono (homologyMap T.f 0) :=
      mono_homologyMap_of_mono_of_not_rel T.f 0 (by intro i hi; exact Nat.not_succ_le_zero i (Nat.le_of_eq hi))
    have he : homologyMap φ.τ₁ 0 ≫ homologyMap T.f 0 =
        homologyMap S.f 0 ≫ homologyMap φ.τ₂ 0 := by
      rw [← homologyMap_comp,← homologyMap_comp,φ.comm₁₂]
    have : Mono (homologyMap φ.τ₁ 0) := mono_of_mono_fac he
    have : Epi (homologyMap φ.τ₁ 0) := by
      apply Abelian.epi_of_mono_of_epi_of_mono (mapComposableArrows₂ φ 0)
        (composableArrows₂_exact hS 0) (composableArrows₂_exact hT 0)
      · exact ht
      · exact inferInstanceAs (Epi (homologyMap φ.τ₂ 0))
      · exact inferInstanceAs (Mono (homologyMap φ.τ₃ 0))
    exact isIso_of_mono_of_epi _
  | succ n =>
    apply Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
      (composableArrows₅_exact hS n (n+1) rfl).δ₀
      (composableArrows₅_exact hT n (n+1) rfl).δ₀
      (δ₀Functor.map (mapComposableArrows₅ φ hS hT n (n+1) rfl))
    · exact inferInstanceAs (Epi (homologyMap φ.τ₂ n))
    · exact inferInstanceAs (IsIso (homologyMap φ.τ₃ n))
    · exact inferInstanceAs (IsIso (homologyMap φ.τ₂ (n+1)))
    · exact inferInstanceAs (Mono (homologyMap φ.τ₃ (n+1)))

/-- The actual kernel and a surjective cochain restriction form a short exact sequence. -/
theorem kernel_sequence_shortExact {C D : CochainComplex (ModuleCat.{0} ℝ) ℕ}
    (r : C ⟶ D) [Epi r] : (ShortComplex.mk (kernel.ι r) r (kernel.condition r)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel r)
  mono_f := inferInstance
  epi_g := inferInstance

/-- A square of surjective cochain restrictions with quasi-isomorphisms on absolute terms
induces a quasi-isomorphism between the actual relative kernels. -/
theorem kernel_map_quasiIso {C D C' D' : CochainComplex (ModuleCat.{0} ℝ) ℕ}
    (r : C ⟶ D) (r' : C' ⟶ D') [Epi r] [Epi r']
    (p : C ⟶ C') (q : D ⟶ D') (h : r ≫ q = p ≫ r')
    [QuasiIso p] [QuasiIso q] : QuasiIso (kernel.map r r' p q h) := by
  let φ : ShortComplex.mk (kernel.ι r) r (kernel.condition r) ⟶
      ShortComplex.mk (kernel.ι r') r' (kernel.condition r') :=
    { τ₁ := kernel.map r r' p q h
      τ₂ := p
      τ₃ := q
      comm₁₂ := by simp [kernel.map]
      comm₂₃ := h.symm }
  exact quasiIso_left φ (kernel_sequence_shortExact r) (kernel_sequence_shortExact r')

end TernaryPoly.SmoothSingularGlobal.RealCochainExcision
