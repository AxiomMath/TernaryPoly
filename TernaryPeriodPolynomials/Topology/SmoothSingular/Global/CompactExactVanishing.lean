module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.OriginalSmoothComparison
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactExactHomology

@[expose] public section


/-! Smooth exactness detects vanishing of the original rational compactForget. -/
noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
open SmoothCoveringDeRham SymmetricSpaceCovering SingularLocalSupport CompactInteriorRelativeBoundary

local instance compactExactOriginalCoverFact :
    Fact (IsQuotientCoveringMap singularCoveringProjection DeckGroup) :=
  ⟨quotientProjection_quotientCovering⟩

variable (A : Rep.{0} ℚ DeckGroup) [FiniteDimensional ℚ A] (C : CompactConvexCover)
attribute [local instance] realCoefficientNorm realCoefficientNormedSpace

include C in
theorem originalCompactForget_eq_zero_of_smooth_exact
    (h : CompactExactInDegree (realRep A).ρ 1) :
    compactForget singularCoveringProjection A 2 = 0 := by
  have hz := compactInclusion_homology_two_eq_zero (realRep A).ρ h
  have hs := originalSmooth_compact_square A C
  rw [hz, Functor.map_zero, comp_zero] at hs
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply originalSmoothOrdinary_injective A C
  have hx := congrArg (fun f => f.hom x) hs
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero] using hx

end TernaryPoly.SmoothSingularGlobal
