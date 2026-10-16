module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.Building.GoodPaths.Helpers

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.GoodBuildingPaths

theorem good_building_paths : ∃ τ : rationalLevel → EdgeChains, IsPathFamily τ := by
  classical
  refine ⟨fun group => Classical.choose (Helpers.chain_to_translate group), ?_⟩
  intro group
  exact Classical.choose_spec (Helpers.chain_to_translate group)

end TernaryPeriodPolynomials.GoodBuildingPaths
