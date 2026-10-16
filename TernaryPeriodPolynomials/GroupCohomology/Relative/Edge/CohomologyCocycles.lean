module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

noncomputable section
namespace TernaryPoly.RelativeEdgeCohomologyCocycles
open CategoryTheory CategoryTheory.Limits groupCohomology

variable {G : Type} [Group G] (A : Rep.{0} ℚ G)

/-- The genuine coboundary of a coefficient vector. -/
def coboundary (v : A) : cocycles₁ A :=
  ⟨d₀₁ A v, d₀₁_apply_mem_cocycles₁ v⟩

@[simp] lemma coboundary_apply (v : A) (g : G) :
    coboundary A v g = A.ρ g v - v := rfl

lemma cocycle_mul (f : cocycles₁ A) (g h : G) :
    f (g*h) = A.ρ g (f h) + f g := (mem_cocycles₁_iff _).mp f.property g h

/-- Zero values of an actual crossed homomorphism form a subgroup. -/
def zeroSubgroup (f : cocycles₁ A) : Subgroup G where
  carrier := {g | f g = 0}
  one_mem' := cocycles₁_map_one f
  mul_mem' := by
    intro g h hg hh
    change f g = 0 at hg
    change f h = 0 at hh
    change f (g*h) = 0
    rw [cocycle_mul, hg, hh, map_zero, add_zero]
  inv_mem' := by
    intro g hg
    change f g = 0 at hg
    change f g⁻¹ = 0
    have h := cocycles₁_map_inv f g⁻¹
    simpa [hg] using h.symm

/-- If a cocycle vanishes on an element and its sign conjugate, the element fixes the sign value. -/
lemma fixed_value_of_zero_conjugate (f : cocycles₁ A) (s g : G)
    (hg : f g = 0) (hc : f (s⁻¹*g*s) = 0) : A.ρ g (f s) = f s := by
  have he : g*s = s*(s⁻¹*g*s) := by simp [mul_assoc]
  have h := congrArg f he
  simpa [cocycle_mul, hg, hc] using h

/-- An involution's cocycle value is anti-invariant. -/
lemma involution_value (f : cocycles₁ A) (s : G) (hs : s*s = 1) :
    A.ρ s (f s) = -f s := by
  have h := cocycle_mul A f s s
  rw [hs, cocycles₁_map_one] at h
  exact (eq_neg_iff_add_eq_zero).mpr h.symm

/-- Explicit normalization at a sign involution. -/
def normalize (f : cocycles₁ A) (s : G) : cocycles₁ A :=
  f - coboundary A ((-1/2 : ℚ) • f s)

lemma normalize_sign (f : cocycles₁ A) (s : G) (hs : s*s = 1) :
    normalize A f s s = 0 := by
  change f s - (A.ρ s ((-1/2 : ℚ) • f s) - (-1/2 : ℚ) • f s) = 0
  rw [map_smul, involution_value A f s hs]
  module

/-- Sign normalization preserves any killed root together with its sign conjugate. -/
lemma normalize_preserves_zero (f : cocycles₁ A) (s g : G)
    (hg : f g = 0) (hc : f (s⁻¹*g*s) = 0) : normalize A f s g = 0 := by
  change f g - (A.ρ g ((-1/2 : ℚ) • f s) - (-1/2 : ℚ) • f s) = 0
  rw [map_smul, fixed_value_of_zero_conjugate A f s g hg hc, hg]
  simp

/-- Principal cocycles represent zero in the actual H¹ quotient. -/
lemma H1_coboundary (v : A) : H1π A (coboundary A v) = 0 := by
  apply (H1π_eq_zero_iff _).mpr
  exact ⟨v, rfl⟩

/-- Subtraction of a genuine coboundary preserves the actual cohomology class. -/
lemma H1_sub_coboundary (f : cocycles₁ A) (v : A) :
    H1π A (f - coboundary A v) = H1π A f := by
  rw [map_sub, H1_coboundary, sub_zero]

lemma H1_normalize (f : cocycles₁ A) (s : G) : H1π A (normalize A f s) = H1π A f :=
  H1_sub_coboundary A f _

/-- Simultaneous normalization at two commuting involutions preserves actual H¹. -/
lemma normalize_two (f : cocycles₁ A) (s t : G)
    (hs : s*s=1) (ht : t*t=1) (hst : s*t=t*s) :
    ∃ f' : cocycles₁ A, f' s = 0 ∧ f' t = 0 ∧ H1π A f' = H1π A f := by
  let f' := normalize A (normalize A f s) t
  refine ⟨f', ?_, normalize_sign A _ t ht, ?_⟩
  · apply normalize_preserves_zero
    · exact normalize_sign A f s hs
    · have hc : t⁻¹*s*t=s := by rw [mul_assoc, hst]; simp
      rw [hc]
      exact normalize_sign A f s hs
  · change H1π A (normalize A (normalize A f s) t) = _
    rw [H1_normalize, H1_normalize]

/-- A cocycle vanishing on generators of the actual group is zero. -/
lemma eq_zero_of_generators (f : cocycles₁ A) (S : Set G)
    (hS : Subgroup.closure S = ⊤) (hf : ∀ g ∈ S, f g = 0) : f = 0 := by
  have h : Subgroup.closure S ≤ zeroSubgroup A f := (Subgroup.closure_le _).mpr hf
  rw [hS] at h
  apply cocycles₁_ext
  intro g
  exact h (show g ∈ (⊤ : Subgroup G) from trivial)

/-- A normalized sign gives literal conjugation equivariance of the cocycle. -/
lemma conjugation_value (f : cocycles₁ A) (s g : G) (hs : f s = 0) :
    f (s*g*s⁻¹) = A.ρ s (f g) := by
  have hsi : f s⁻¹ = 0 := (zeroSubgroup A f).inv_mem hs
  simp [cocycle_mul, hs, hsi]

/-- A killed commuting element fixes the other cocycle value. -/
lemma commuting_fixed (f : cocycles₁ A) (a b : G) (ha : f a = 0)
    (hab : a*b=b*a) : A.ρ a (f b) = f b := by
  have h := congrArg f hab
  simpa [cocycle_mul, ha] using h

/-- A central-root correction with zero cocycle value gives the same fixed-vector relation. -/
lemma commutator_fixed (f : cocycles₁ A) (a b c : G)
    (ha : f a = 0) (hc : f c = 0) (hab : a*b=b*a*c) : A.ρ a (f b) = f b := by
  have h := congrArg f hab
  simpa [cocycle_mul, ha, hc] using h

/-- A root inverted by a normalized sign cannot have a value fixed by both actions. -/
lemma inverted_root_zero (f : cocycles₁ A) (s g : G) (hs : f s = 0)
    (hsg : s*g*s⁻¹=g⁻¹) (hg : A.ρ g (f g) = f g)
    (hfix : A.ρ s (f g) = f g) : f g = 0 := by
  have hi : f g⁻¹ = f g := by
    rw [← hsg, conjugation_value A f s g hs, hfix]
  have h := cocycles₁_map_inv f g
  rw [hi, hg] at h
  have h2 : (2 : ℚ) • f g = 0 := by
    rw [two_smul]
    exact (add_eq_zero_iff_eq_neg).mpr h
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- A proof that all actual cocycles are coboundaries gives actual H¹ vanishing. -/
theorem isZero_H1_of_coboundaries
    (h : ∀ f : cocycles₁ A, ∃ v : A, ∀ g, f g = A.ρ g v - v) :
    IsZero (groupCohomology A 1) := by
  apply (ModuleCat.isZero_of_iff_subsingleton).mpr
  have hz (x : H1 A) : x = 0 := by
    induction x using H1_induction_on with | h f =>
      apply (H1π_eq_zero_iff f).mpr
      obtain ⟨v, hv⟩ := h f
      exact ⟨v, funext (fun g => (hv g).symm)⟩
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end TernaryPoly.RelativeEdgeCohomologyCocycles
