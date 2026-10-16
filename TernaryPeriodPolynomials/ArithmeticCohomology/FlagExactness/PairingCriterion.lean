module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
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
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# A pairing criterion for second group cohomology

Let `A` be a finite-dimensional complex representation of an arbitrary group `G`. An
inhomogeneous 2-cocycle `f` is a coboundary as soon as it pairs to zero with every
finitely supported 2-cycle with coefficients in the dual `A*`. This is the
elementary half of `H²(G, A) ≅ H₂(G, A*)*`: a functional on chains that vanishes on
cycles factors through the boundary and extends from its range.

This lets one detect vanishing of `H²` classes, such as those in `FlagExact`, through
finitely many cocycle values at a time.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

variable {G : Type} [Group G] (A : Rep ℂ G)

/-- Finitely supported 2-chains with dual coefficients. -/
abbrev DualChains₂ := (G × G) →₀ Module.Dual ℂ A

/-- Finitely supported 1-chains with dual coefficients. -/
abbrev DualChains₁ := G →₀ Module.Dual ℂ A

/-- Pairing of an inhomogeneous 2-cochain with 2-chains. -/
def pairing₂ (f : G × G → A) : DualChains₂ A →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun pair => Module.Dual.eval ℂ A (f pair))

/-- Pairing of an inhomogeneous 1-cochain with 1-chains. -/
def pairing₁ (b : G → A) : DualChains₁ A →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun element => Module.Dual.eval ℂ A (b element))

/-- The boundary of dual 2-chains, adjoint to `d₁₂`. -/
def dualBoundary : DualChains₂ A →ₗ[ℂ] DualChains₁ A :=
  Finsupp.lsum ℂ (fun pair =>
    (Finsupp.lsingle pair.2).comp (A.ρ pair.1).dualMap -
      Finsupp.lsingle (pair.1 * pair.2) + Finsupp.lsingle pair.1)

theorem pairing₂_single (f : G × G → A) (pair : G × G) (μ : Module.Dual ℂ A) :
    pairing₂ A f (Finsupp.single pair μ) = μ (f pair) := by
  rw [pairing₂, Finsupp.lsum_single, Module.Dual.eval_apply]

theorem pairing₁_single (b : G → A) (element : G) (μ : Module.Dual ℂ A) :
    pairing₁ A b (Finsupp.single element μ) = μ (b element) := by
  rw [pairing₁, Finsupp.lsum_single, Module.Dual.eval_apply]

/-- Adjointness of `dualBoundary` and `d₁₂`. -/
theorem pairing₂_d₁₂ (b : G → A) (chain : DualChains₂ A) :
    pairing₂ A ((d₁₂ A).hom b) chain = pairing₁ A b (dualBoundary A chain) := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add first second hfirst hsecond => rw [map_add, map_add, map_add, hfirst, hsecond]
  | single pair μ =>
    rw [pairing₂_single, d₁₂_hom_apply]
    simp only [dualBoundary, Finsupp.lsum_single, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, Finsupp.lsingle_apply, map_add, map_sub, pairing₁_single,
      LinearMap.dualMap_apply]

/-- **Pairing criterion.** A 2-cochain killed by every finitely supported dual 2-cycle
is a coboundary. -/
theorem mem_coboundaries₂_of_pairing [FiniteDimensional ℂ A] (f : G × G → A)
    (vanishes : ∀ chain : DualChains₂ A, dualBoundary A chain = 0 → pairing₂ A f chain = 0) :
    ∃ b : G → A, (d₁₂ A).hom b = f := by
  have hle : LinearMap.ker (dualBoundary A) ≤ LinearMap.ker (pairing₂ A f) := by
    intro chain hchain
    exact vanishes chain hchain
  -- factor the pairing through the range of the boundary and extend
  let onRange : LinearMap.range (dualBoundary A) →ₗ[ℂ] ℂ :=
    ((LinearMap.ker (dualBoundary A)).liftQ (pairing₂ A f) hle).comp
      (dualBoundary A).quotKerEquivRange.symm.toLinearMap
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend onRange
  have hfactor : ∀ chain, φ (dualBoundary A chain) = pairing₂ A f chain := by
    intro chain
    have := LinearMap.congr_fun hφ ⟨dualBoundary A chain, LinearMap.mem_range_self _ chain⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    simp only [onRange, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show (dualBoundary A).quotKerEquivRange.symm ⟨dualBoundary A chain, _⟩ =
        Submodule.Quotient.mk chain from
      (dualBoundary A).quotKerEquivRange.symm_apply_eq.mpr rfl]
    rfl
  let b : G → A := fun element =>
    (Module.evalEquiv ℂ A).symm (φ.comp (Finsupp.lsingle element))
  have hb : ∀ element (μ : Module.Dual ℂ A), μ (b element) = φ (Finsupp.single element μ) := by
    intro element μ
    simp [b]
  have hpair : ∀ chain : DualChains₁ A, pairing₁ A b chain = φ chain := by
    intro chain
    induction chain using Finsupp.induction_linear with
    | zero => simp
    | add first second hfirst hsecond => rw [map_add, map_add, hfirst, hsecond]
    | single element μ => rw [pairing₁_single, hb]
  refine ⟨b, ?_⟩
  funext pair
  rw [← sub_eq_zero]
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro μ
  rw [map_sub, sub_eq_zero, ← pairing₂_single A ((d₁₂ A).hom b) pair μ, pairing₂_d₁₂,
    ← pairing₂_single A f pair μ, ← hfactor, hpair]

end TernaryPeriodPolynomials.FlagExactness
