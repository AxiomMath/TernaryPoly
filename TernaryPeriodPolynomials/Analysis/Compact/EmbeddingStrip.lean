module

public import TernaryPeriodPolynomials.Analysis.Compact.EmbeddingNeighborhood
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section

noncomputable section
namespace TernaryPoly.CompactEmbeddingNeighborhood
open Set Topology

/-- A compact zero slice on which a continuous open map is injective has a uniform real strip
of injectivity, provided the map is locally injective along that slice. -/
theorem exists_strip_open_embedding {K Y : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace Y] [T2Space Y] (f : K × ℝ → Y) (hf : Continuous f) (hopen : IsOpenMap f)
    (hzero : Function.Injective (fun x : K => f (x, 0)))
    (hloc : ∀ x : K, ∃ U : Set (K × ℝ), IsOpen U ∧ (x, 0) ∈ U ∧ Set.InjOn f U) :
    ∃ ε : ℝ, 0 < ε ∧
      IsOpenEmbedding ((Set.univ ×ˢ Set.Ioo (-ε) ε).domRestrict f) := by
  have hinj : Set.InjOn f (Set.univ ×ˢ ({0} : Set ℝ)) := by
    rintro ⟨x, t⟩ ⟨_, ht⟩ ⟨y, s⟩ ⟨_, hs⟩ h
    obtain rfl : t = 0 := ht
    obtain rfl : s = 0 := hs
    exact congrArg (fun x : K => (x, (0 : ℝ))) (hzero h)
  obtain ⟨U, hU, hSU, hUi⟩ := exists_open_injOn f hf
    (Set.univ ×ˢ ({0} : Set ℝ)) (isCompact_univ.prod isCompact_singleton) hinj
    (by rintro ⟨x, t⟩ ⟨_, ht⟩; obtain rfl : t = 0 := ht; exact hloc x)
  obtain ⟨A, B, _, hB, hA, h0, hAB⟩ := generalized_tube_lemma
    isCompact_univ isCompact_singleton hU hSU
  obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds (h0 (show (0 : ℝ) ∈ ({0} : Set ℝ) from rfl)))
  have hsub : Set.univ ×ˢ Set.Ioo (-ε) ε ⊆ U := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    apply hAB
    refine ⟨hA (Set.mem_univ x), hεB ?_⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, Set.mem_Ioo] using ht
  refine ⟨ε, hε, IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hf.comp continuous_subtype_val) ?_ (hopen.domRestrict (isOpen_univ.prod isOpen_Ioo))⟩
  exact (hUi.mono hsub).injective

end TernaryPoly.CompactEmbeddingNeighborhood
