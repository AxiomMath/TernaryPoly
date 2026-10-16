module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProfiniteCharacter

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfiniteClopenExtension

variable {Source Ambient Target : Type*}
variable [TopologicalSpace Source] [CompactSpace Source]
variable [TopologicalSpace Ambient] [CompactSpace Ambient] [T2Space Ambient] [TotallyDisconnectedSpace Ambient]

theorem fiber_extension (map : Source → Ambient) (continuous : Continuous map)
    (function : Source → Target) (locallyConstant : IsLocallyConstant function)
    (compatible : ∀ first second, map first = map second → function first = function second)
    (value : Target) :
    ∃ region : Set Ambient, IsClopen region ∧ ∀ point : Source, map point ∈ region ↔ function point = value := by
  let first : Set Ambient := map '' {point | function point = value}
  let second : Set Ambient := map '' {point | function point ≠ value}
  have firstCompact : IsCompact first :=
    (locallyConstant.isClosed_fiber value).isCompact.image continuous
  have secondCompact : IsCompact second :=
    (locallyConstant.isOpen_fiber value).isClosed_compl.isCompact.image continuous
  have separated : first ⊆ secondᶜ := by
    rintro _ ⟨left, leftMembership, rfl⟩ ⟨right, rightMembership, equality⟩
    exact rightMembership ((compatible right left equality).trans leftMembership)
  obtain ⟨region, clopen, contains, contained⟩ := exists_clopen_of_closed_subset_open
    firstCompact.isClosed secondCompact.isClosed.isOpen_compl separated
  refine ⟨region, clopen, fun point => ⟨?_, ?_⟩⟩
  · intro membership
    by_contra different
    exact contained membership ⟨point, different, rfl⟩
  · intro equality
    exact contains ⟨point, equality, rfl⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfiniteClopenExtension
