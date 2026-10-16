module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.MatrixApartment
public import TernaryPeriodPolynomials.Building.BoundaryApartments.FunctionalExtension

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

def edgePathDefect (paths : BuildingVertices → EdgeChains) (edge : Edges) : EdgeChains :=
  Finsupp.single edge 1 - paths (Sum.inl (endpoint .plane edge)) +
    paths (Sum.inr (endpoint .line edge))

theorem edgePathDefect_linearCombination (paths : BuildingVertices → EdgeChains) :
    Finsupp.linearCombination ℂ (edgePathDefect paths) =
      LinearMap.id - (Finsupp.linearCombination ℂ paths).comp chainBoundary := by
  apply Finsupp.lhom_ext
  intro edge scalar
  simp [edgePathDefect, chainBoundary, Finsupp.linearCombination_single,
    smul_add, smul_sub, Finsupp.smul_single]
  abel

theorem cycle_eq_sum_edgePathDefects (paths : BuildingVertices → EdgeChains)
    (chain : EdgeChains) (cycle : chainBoundary chain = 0) :
    chain = ∑ edge ∈ chain.support, chain edge • edgePathDefect paths edge := by
  have value := LinearMap.congr_fun (edgePathDefect_linearCombination paths) chain
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.comp_apply, cycle, map_zero, sub_zero] using value.symm

theorem goodCycle_mem_of_edgePathDefects (submodule : Submodule ℂ EdgeChains)
    (paths : BuildingVertices → EdgeChains)
    (defects : ∀ edge : Edges, GoodFlag .plane (endpoint .plane edge) →
      GoodFlag .line (endpoint .line edge) → edgePathDefect paths edge ∈ submodule)
    {chain : EdgeChains} (cycle : GoodCycle chain) : chain ∈ submodule := by
  rw [cycle_eq_sum_edgePathDefects paths chain cycle.1]
  apply Submodule.sum_mem
  intro edge edge_mem
  exact submodule.smul_mem _ (defects edge (cycle.2 edge edge_mem).1 (cycle.2 edge edge_mem).2)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
