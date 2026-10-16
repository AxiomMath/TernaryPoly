module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryStages
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Representatives

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport EquivariantSingularSmall SingularBoundaryRestriction
open SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence

variable (V : Rep.{0} ℚ principalSix)

/-- The endpoint deformation is interpreted at the literal compact complement of its
smaller neighborhood without transporting any relative chain complex along a set equality. -/
def compactEndpoint {W : Set BordifiedOrbit} (c : SymmetricSpaceBoundaryNeighborhood.Collapse W) :
    ambientRelativeCochains (boundary principalSix) V ⟶
      ambientRelativeCochains (outsideCompact (neighborhoodCompact c.neighborhood c.isOpen c.contains_boundary)) V :=
  endpointPullback c V ≫ boundaryNeighborhoodMap c.neighborhood
    (outsideCompact (neighborhoodCompact c.neighborhood c.isOpen c.contains_boundary))
    (by rw [outside_neighborhoodCompact]) V

/-- The actual compact-complement endpoint retracts the literal boundary comparison. -/
theorem compactEndpoint_retraction {W : Set BordifiedOrbit}
    (c : SymmetricSpaceBoundaryNeighborhood.Collapse W) (k : ℕ) :
    homologyMap (compactEndpoint V c) k ≫ homologyMap
      (boundaryRelativeMap (outsideCompact (neighborhoodCompact c.neighborhood c.isOpen c.contains_boundary))
        (boundary_subset_outsideCompact _) V) k = 𝟙 _ := by
  unfold compactEndpoint
  rw [homologyMap_comp,Category.assoc,← homologyMap_comp,boundaryRelativeMap_transition]
  exact endpointPullback_retraction c V k

/-- Boundary restriction and the actual compact-complement endpoint equal the literal
transition after enlarging a compact support. -/
theorem compactEndpoint_transition (K : Compacts interiorOpen)
    (c : SymmetricSpaceBoundaryNeighborhood.Collapse (outsideCompact K)) (k : ℕ) :
    homologyMap (boundaryRelativeMap (outsideCompact K) (boundary_subset_outsideCompact K) V) k ≫
      homologyMap (compactEndpoint V c) k = homologyMap
        (boundaryNeighborhoodMap (outsideCompact K)
          (outsideCompact (neighborhoodCompact c.neighborhood c.isOpen c.contains_boundary))
          (outsideCompact_antitone (compact_le_neighborhoodCompact K c.neighborhood c.isOpen
            c.contains_boundary c.subset)) V) k := by
  unfold compactEndpoint
  rw [homologyMap_comp,← Category.assoc,endpointPullback_transition,← homologyMap_comp,
    boundaryNeighborhoodMap_comp]

/-- Every actual boundary-relative class has a representative with genuine compact interior support. -/
theorem compactToBoundary_surjective (k : ℕ) : Function.Surjective (compactToBoundary V k) := by
  intro x
  let c := SymmetricSpaceBoundaryNeighborhood.collapse Set.univ isOpen_univ (Set.subset_univ _)
  let L := neighborhoodCompact c.neighborhood c.isOpen c.contains_boundary
  let z := homologyMap (compactEndpoint V c) k x
  refine ⟨compactClassMap (restrictedProjection wholeProjection interiorOpen) V L k
    ((fixedSupportIso V L k).hom z),?_⟩
  have h := congrArg (fun f => f ((fixedSupportIso V L k).hom z)) (compactToBoundary_classMap V L k)
  change compactToBoundary V k _ = _ at h
  refine h.trans ?_
  change homologyMap (boundaryRelativeMap (outsideCompact L) (boundary_subset_outsideCompact L) V) k
    ((fixedSupportIso V L k).inv ((fixedSupportIso V L k).hom z)) = x
  have hi := congrArg (fun f => f z) (fixedSupportIso V L k).hom_inv_id
  change (fixedSupportIso V L k).inv ((fixedSupportIso V L k).hom z) = z at hi
  exact (congrArg (homologyMap (boundaryRelativeMap (outsideCompact L)
    (boundary_subset_outsideCompact L) V) k) hi).trans
      (congrArg (fun f => f x) (compactEndpoint_retraction V c k))

/-- A compact-support class whose actual boundary-relative image vanishes already vanishes
after enlarging its genuine compact support by the actual boundary-neighborhood deformation. -/
theorem compactToBoundary_injective (k : ℕ) : Function.Injective (compactToBoundary V k) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  obtain ⟨K,z,rfl⟩ := compactClass_exists_rep (restrictedProjection wholeProjection interiorOpen) V k x
  have hx' : compactToBoundary V k (compactClassMap (restrictedProjection wholeProjection interiorOpen) V K k z) = 0 := hx
  have hz : fixedToBoundary V K k z = 0 :=
    (congrArg (fun f => f z) (compactToBoundary_classMap V K k)).symm.trans hx'
  let c := SymmetricSpaceBoundaryNeighborhood.collapse (outsideCompact K)
    (outsideCompact_open K) (boundary_subset_outsideCompact K)
  let L := neighborhoodCompact c.neighborhood c.isOpen c.contains_boundary
  have hKL : K ≤ L := compact_le_neighborhoodCompact K c.neighborhood c.isOpen c.contains_boundary c.subset
  apply (compactClass_zero_iff (restrictedProjection wholeProjection interiorOpen) V k K z).mpr
  refine ⟨L,hKL,?_⟩
  have ht := congrArg (fun f => f ((fixedSupportIso V K k).inv z)) (compactEndpoint_transition V K c k)
  change homologyMap (compactEndpoint V c) k (fixedToBoundary V K k z) = _ at ht
  rw [hz,map_zero] at ht
  have hn := congrArg (fun f => f z) (fixedSupportIso_inv_natural V K L hKL k)
  change (fixedSupportIso V L k).inv (homologyMap (supportMap (restrictedProjection wholeProjection interiorOpen) V K L hKL) k z) = _ at hn
  have he := hn.trans ht.symm
  exact (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (fixedSupportIso V L k).inv)
    (he.trans (map_zero (fixedSupportIso V L k).inv.hom).symm)

/-- The actual compact-support comparison to the actual boundary-relative Hom complex is
an isomorphism for every representation and every cohomological degree. -/
theorem compactToBoundary_isIso (k : ℕ) : IsIso (compactToBoundary V k) := by
  let e := LinearEquiv.ofBijective (compactToBoundary V k).hom
    ⟨compactToBoundary_injective V k,compactToBoundary_surjective V k⟩
  change IsIso e.toModuleIso.hom
  infer_instance

/-- The actual compact-to-boundary cohomology isomorphism uses the literal descended map. -/
def openCompactBoundaryIso (k : ℕ) :
    compactCohomology (restrictedProjection wholeProjection interiorOpen) V k ≅
      (ambientRelativeCochains (boundary principalSix) V).homology k := by
  have := compactToBoundary_isIso V k
  exact asIso (compactToBoundary V k)

end TernaryPoly.CompactInteriorRelativeBoundary
