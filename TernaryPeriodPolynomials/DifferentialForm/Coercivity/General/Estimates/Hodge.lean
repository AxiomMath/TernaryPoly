module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Operators
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Main
public import TernaryPeriodPolynomials.Analysis.JointEmbeddedGraphClosure
public import TernaryPeriodPolynomials.Analysis.Embedded.AdjointTest

@[expose] public section


/-! # General coercivity, Tier B: Hodge exactness in the `L²` completion, given Gaffney's lemma

The joint graph closure of the triple `(a, d a, δ a)` of compactly supported forms, coercivity on
it (from `general_coercivity`, one constant for every admissible group), the weak-test description
of the maximal operators, and the abstract Hodge criterion
`HilbertClosedOperator.exact_of_graph_energy`.  The analytic input that the maximal operators are
jointly approximated by compactly supported smooth forms (Gaffney's lemma) is the explicit
hypothesis `GaffneyAt`; it is proved in the later files of this directory.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Filter Topology TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.PolynomialCoefficientMetric
open scoped LinearPMap

variable {Γ : Subgroup RealGL} {n : ℕ}

section Joint

variable (Γ n) (k : ℕ) [hΓ : Fact (Admissible Γ)]

/-- The closed submodule of simultaneous `L²` limits of triples `(a, d a, δ a)`, `a` compactly
supported of degree `k + 1`. -/
def jointGraph : Submodule ℝ (Hilbert Γ n (k + 1) × Hilbert Γ n (k + 2) × Hilbert Γ n k) :=
  JointEmbeddedGraphClosure.graph (incl Γ n (k + 1))
    ((incl Γ n (k + 2)).comp (CForm.d Γ n (k + 1))) ((incl Γ n k).comp (CForm.delta Γ n k))

/-- Gaffney's lemma in degree `k + 1`: every element of the joint maximal graph lies in the joint
minimal graph. -/
def GaffneyAt : Prop :=
  ∀ (x : Hilbert Γ n (k + 1)) (y : Hilbert Γ n (k + 2)) (z : Hilbert Γ n k),
    (x, y) ∈ (maxD Γ n (k + 1)).graph → (x, z) ∈ (maxDelta Γ n k).graph →
      (x, y, z) ∈ jointGraph Γ n k

theorem mem_maxD_graph_iff (x : Hilbert Γ n k) (z : Hilbert Γ n (k + 1)) :
    (x, z) ∈ (maxD Γ n k).graph ↔ ∀ b : CForm Γ n (k + 1),
      inner ℝ z (incl Γ n (k + 1) b) = inner ℝ x (incl Γ n k (CForm.delta Γ n k b)) :=
  EmbeddedLinearOperator.mem_adjoint_graph_iff (incl Γ n (k + 1)) (incl_injective Γ n (k + 1))
    (incl_dense Γ n (k + 1)) ((incl Γ n k).comp (CForm.delta Γ n k)) x z

theorem mem_maxDelta_graph_iff (x : Hilbert Γ n (k + 1)) (z : Hilbert Γ n k) :
    (x, z) ∈ (maxDelta Γ n k).graph ↔ ∀ b : CForm Γ n k,
      inner ℝ z (incl Γ n k b) = inner ℝ x (incl Γ n (k + 1) (CForm.d Γ n k b)) :=
  EmbeddedLinearOperator.mem_adjoint_graph_iff (incl Γ n k) (incl_injective Γ n k)
    (incl_dense Γ n k) ((incl Γ n (k + 1)).comp (CForm.d Γ n k)) x z

end Joint

/-- Generic: an inequality on a core persists on the closure of its graph. -/
theorem graph_coercive_of_core {V E F G : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (i : V →ₗ[ℝ] E) (d : V →ₗ[ℝ] F) (a : V →ₗ[ℝ] G) (c : ℝ)
    (h : ∀ v, c * ‖i v‖ ^ 2 ≤ ‖a v‖ ^ 2 + ‖d v‖ ^ 2) {x : E} {y : F} {z : G}
    (hmem : (x, y, z) ∈ JointEmbeddedGraphClosure.graph i d a) :
    c * ‖x‖ ^ 2 ≤ ‖z‖ ^ 2 + ‖y‖ ^ 2 := by
  obtain ⟨u, hx, hy, hz⟩ := JointEmbeddedGraphClosure.exists_sequence _ _ _ hmem
  exact le_of_tendsto_of_tendsto (hx.norm.pow 2 |>.const_mul c)
    ((hz.norm.pow 2).add (hy.norm.pow 2)) (Eventually.of_forall fun j => h (u j))

/-- Coercivity persists on the joint graph closure, with the constant of `general_coercivity`. -/
theorem jointGraph_coercive (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Γ : Subgroup RealGL) [Fact (Admissible Γ)]
      (x : Hilbert Γ n (1 + 1)) (y : Hilbert Γ n (1 + 2)) (z : Hilbert Γ n 1),
      (x, y, z) ∈ jointGraph Γ n 1 → c * ‖x‖ ^ 2 ≤ ‖z‖ ^ 2 + ‖y‖ ^ 2 := by
  have key := general_coercivity n hn
  refine ⟨key.choose, key.choose_spec.1, ?_⟩
  intro Γ hΓ x y z hmem
  have H := key.choose_spec.2 Γ hΓ.out
  have hcore : ∀ a : CForm Γ n (1 + 1),
      key.choose * ‖incl Γ n (1 + 1) a‖ ^ 2 ≤ ‖((incl Γ n 1).comp (CForm.delta Γ n 1)) a‖ ^ 2 +
        ‖((incl Γ n (1 + 2)).comp (CForm.d Γ n (1 + 1))) a‖ ^ 2 := by
    intro a
    simp only [LinearMap.comp_apply, norm_incl_sq]
    exact H.2 1 a
  exact graph_coercive_of_core (incl Γ n (1 + 1)) ((incl Γ n (1 + 2)).comp (CForm.d Γ n (1 + 1)))
    ((incl Γ n 1).comp (CForm.delta Γ n 1)) key.choose hcore hmem

/-- Hodge exactness in degree two: the kernel of the maximal derivative is the range of the minimal
derivative, given Gaffney's lemma. -/
theorem kernel_maxD_eq_range_minD (hn : 0 < n) [Fact (Admissible Γ)] (hJ : GaffneyAt Γ n 1) :
    (HilbertClosedOperator.kernel (maxD Γ n 2) : Set (Hilbert Γ n 2)) =
      Set.range (minD Γ n 1) :=
  HilbertClosedOperator.exact_of_graph_energy (minD Γ n 1) (maxD Γ n 2) (maxDelta Γ n 1)
    (minD_isClosed Γ n 1) (minD_domain_dense Γ n 1) (maxD_isClosed Γ n 2)
    (fun a => LinearPMap.le_graph_of_le (minD_le_maxD Γ n 2) (minD_complex Γ n 1 a))
    (minD_adjoint Γ n 1) (jointGraph_coercive hn).choose (jointGraph_coercive hn).choose_spec.1
    (fun x y z hy hz => (jointGraph_coercive hn).choose_spec.2 Γ x y z (hJ x y z hy hz))

/-- **T1, conditional on Gaffney's lemma.**  Every closed compactly supported equivariant two-form
has a weak `L²` primitive. -/
theorem Admissible.closed_has_weak_primitive_of_gaffney [hΓ : Fact (Admissible Γ)] (hn : 0 < n)
    (hJ : GaffneyAt Γ n 1) (ω : CForm Γ n 2) (hω : CForm.d Γ n 2 ω = 0) :
    ∃ u : Hilbert Γ n 1, (u, incl Γ n 2 ω) ∈ (maxD Γ n 1).graph := by
  have hmem : incl Γ n 2 ω ∈ HilbertClosedOperator.kernel (maxD Γ n 2) :=
    (mem_maxD_graph_iff Γ n 2 (incl Γ n 2 ω) 0).mpr fun b =>
      (inner_zero_left (incl Γ n (2 + 1) b)).trans
        (((congrArg (fun u => l2Form Γ n (2 + 1) u b) hω).trans
          (LinearMap.map_zero₂ (l2Form Γ n (2 + 1)) b)).symm.trans
          ((hΓ.out.l2Form_d ω b).trans (inner_incl Γ n 2 ω (CForm.delta Γ n 2 b)).symm))
  have hr : incl Γ n 2 ω ∈ Set.range (minD Γ n 1) :=
    (Set.ext_iff.mp (kernel_maxD_eq_range_minD hn hJ) (incl Γ n 2 ω)).mp hmem
  obtain ⟨a, ha⟩ := hr
  have hg := LinearPMap.le_graph_of_le (minD_le_maxD Γ n 1) ((minD Γ n 1).mem_graph a)
  exact ⟨a, (congrArg (fun y : Hilbert Γ n 2 => ((a : Hilbert Γ n 1), y) ∈ (maxD Γ n 1).graph) ha).mp hg⟩

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
