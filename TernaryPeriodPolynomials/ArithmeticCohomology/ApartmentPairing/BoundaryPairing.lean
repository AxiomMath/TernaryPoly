module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ConnectingPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ConnectingRepresentative
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Apartment

@[expose] public section


/-!
# Lemma 3.3 (`lem:apartment-boundary-pairing`), step (b): the pairing depends only on `∂a`

The boundary top evaluation `z ↦ φ(F_z)` on classes `z = j_* c` of the boundary equals the Kronecker
pairing of the Poincaré–Lefschetz dual of `j_* c` with ANY relative homology class `a` whose boundary
is the coordinate apartment:

* `evaluation_connecting`: the Kronecker evaluation intertwines the cohomology connecting map
  (`boundaryConnecting`, represented by `relativeConnectingCocycle`) with the homology connecting map
  `δ : H₂(M,∂M) → H₁(∂M)`, `⟨δ^* ω, a⟩ = ⟨ω, ∂a⟩` (sign `+1`), for every `a`;
* `boundaryDualRelative c`, `cap_boundaryDualRelative`, `boundaryDualRelative_eq`: the relative class
  `δ^*(PD_∂ c)` is the Poincaré–Lefschetz dual of `j_* c` (its cap with the relative fundamental class is
  `j_* c`, from `ordinary_cap_connecting`);
* `apartment_evaluation_eq_pairing`: for `δ a = identityApartmentBoundaryClass`,
  `groupApartmentEvaluation W (j_* c) = ⟨PL-dual(j_* c), a⟩`.

Consequently the (geometric) relative class of the compactified flat enters only through its boundary,
the ambiguity of lifts (the image of `H₂(M)`) is irrelevant, and step G2 is free: it suffices to
construct a relative 2-chain whose boundary is the apartment cycle.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex
open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.OrdinaryTopBoundaryComparison
  TernaryPoly.EquivariantSingularSmall
  TernaryPoly.OrdinaryBoundaryActualEvaluation TernaryPoly.SymmetricSpaceBoundaryManifold
  TernaryPoly.SymmetricSpaceBoundaryOrientation TernaryPoly.SingularLocalHomology
  TernaryPoly.SymmetricSpaceBoundaryDuality TernaryPoly.SymmetricSpaceRelativeCapConnecting
  TernaryPoly.CompactInteriorRelativeBoundary TernaryPoly.SingularLocalCoefficient

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33

variable (W : Rep.{0} ℚ principalSix)

/-- **Kronecker evaluation intertwines the cohomology and homology connecting maps** (sign `+1`):
for every boundary cohomology class `ω` and every relative homology class `a`,
`⟨δ^* ω, a⟩ = ⟨ω, ∂ a⟩`. -/
theorem evaluation_connecting (ω : (homCochains boundaryChains W).homology 1)
    (a : upstairsRelativeChains.homology 2) :
    (homologyEvaluation upstairsRelativeChains W 2
        (homologyMap (relativeHomKernelIso W).inv 2 (boundaryConnecting W 1 ω))).hom a =
      (homologyEvaluation boundaryChains W 1 ω).hom
        (upstairsRelativeSequence_shortExact.δ 2 1 rfl a) := by
  obtain ⟨x, rfl⟩ := ((ModuleCat.epi_iff_surjective
    ((homCochains boundaryChains W).homologyπ 1)).mp inferInstance) ω
  rw [relativeConnectingCocycle_class]
  have hinv : homologyMap (relativeHomKernelIso W).inv 2
      (homologyMap (relativeHomKernelIso W).hom 2
        ((homCochains upstairsRelativeChains W).homologyπ 2 (relativeConnectingCocycle W x))) =
      (homCochains upstairsRelativeChains W).homologyπ 2 (relativeConnectingCocycle W x) := by
    rw [← ConcreteCategory.comp_apply, ← homologyMap_comp, Iso.hom_inv_id, homologyMap_id]
    rfl
  rw [hinv]
  have hL : homologyEvaluation upstairsRelativeChains W 2
      ((homCochains upstairsRelativeChains W).homologyπ 2 (relativeConnectingCocycle W x)) =
      cocycleEvaluation upstairsRelativeChains W 2 (relativeConnectingCocycle W x) :=
    congrArg (fun f => f (relativeConnectingCocycle W x))
      (homologyEvaluation_projection upstairsRelativeChains W 2)
  have hR : homologyEvaluation boundaryChains W 1
      ((homCochains boundaryChains W).homologyπ 1 x) = cocycleEvaluation boundaryChains W 1 x :=
    congrArg (fun f => f x) (homologyEvaluation_projection boundaryChains W 1)
  rw [hL, hR, relativeConnectingCocycle_evaluation W x]
  rfl


/-- The Poincaré–Lefschetz dual of the image `j_* c` of a boundary top class is the connecting image
of its boundary dual: the relative class `x_c` with `cap(x_c) = j_* c`. -/
def boundaryDualRelative (c : (boundaryLocalChains W).homology 3) :
    (homCochains upstairsRelativeChains W).homology 2 :=
  homologyMap (relativeHomKernelIso W).inv 2 (boundaryConnecting W 1
    ((boundaryCohomologyIso W).inv ((boundaryH1CapIso W boundaryOrientation).inv c)))

theorem cap_boundaryDualRelative (c : (boundaryLocalChains W).homology 3) :
    (relativeHomCapIso W).hom (boundaryDualRelative W c) =
      homologyMap (boundaryInclusionMap W) 3 c := by
  set P := (boundaryH1CapIso W boundaryOrientation).inv c with hP
  have hcap : homologyMap (boundaryInclusionMap W) 3 c =
      relativeFundamentalCap W (geometricBoundaryConnecting W 1 P) := by
    have h := congrArg (fun f => f P) (ordinary_cap_connecting W)
    change homologyMap (boundaryInclusionMap W) 3 ((boundaryH1CapIso W boundaryOrientation).hom P) =
      relativeFundamentalCap W (geometricBoundaryConnecting W 1 P) at h
    rw [hP, Iso.inv_hom_id_apply] at h
    exact h
  rw [hcap, relativeHomCapIso_hom]
  change relativeFundamentalCap W (homologyMap (relativeHomGeometricIso W).hom 2
    (homologyMap (relativeHomKernelIso W).inv 2 (boundaryConnecting W 1
      ((boundaryCohomologyIso W).inv P)))) = _
  have h2 : homologyMap (relativeHomGeometricIso W).hom 2
      (homologyMap (relativeHomKernelIso W).inv 2 (boundaryConnecting W 1
        ((boundaryCohomologyIso W).inv P))) =
      homologyMap (boundaryGeometricIso W).hom 2 (boundaryConnecting W 1
        ((boundaryCohomologyIso W).inv P)) := by
    have hcomp : (relativeHomKernelIso W).inv ≫ (relativeHomGeometricIso W).hom =
        (boundaryGeometricIso W).hom := by
      change (relativeHomKernelIso W).inv ≫ ((relativeHomKernelIso W) ≪≫ boundaryGeometricIso W).hom = _
      simp
    rw [← ConcreteCategory.comp_apply, ← homologyMap_comp, hcomp]
  rw [h2]
  have h3 := congrArg (fun f => f ((boundaryCohomologyIso W).inv P)) (boundaryConnecting_geometric W)
  change homologyMap (boundaryGeometricIso W).hom 2 (boundaryConnecting W 1 ((boundaryCohomologyIso W).inv P)) =
    geometricBoundaryConnecting W 1 (homologyMap (cochainIso boundaryProjection boundaryQuotientCovering W).hom 1
      ((boundaryCohomologyIso W).inv P)) at h3
  rw [h3]
  congr 2
  exact Iso.inv_hom_id_apply (boundaryCohomologyIso W) P


/-- The dual relative class is the Poincaré–Lefschetz dual of `j_* c`. -/
theorem boundaryDualRelative_eq (c : (boundaryLocalChains W).homology 3) :
    boundaryDualRelative W c =
      (relativeHomCapIso W).inv (homologyMap (boundaryInclusionMap W) 3 c) := by
  rw [← cap_boundaryDualRelative W c]
  exact ((relativeHomCapIso W).hom_inv_id_apply _).symm

/-- **Lemma 3.3, step (b): the pairing depends only on `∂a`.** For every boundary top class `c` and
every relative homology class `a` whose boundary is the identity apartment, the top evaluation
`φ(F_{j_* c})` equals the Kronecker pairing of the Poincaré–Lefschetz dual of `j_* c` with `a`.
In particular the value does not depend on the choice of the lift `a` of the apartment. -/
theorem apartment_evaluation_eq_pairing (c : (boundaryLocalChains W).homology 3)
    (a : upstairsRelativeChains.homology 2)
    (ha : upstairsRelativeSequence_shortExact.δ 2 1 rfl a = identityApartmentBoundaryClass) :
    groupApartmentEvaluation W (boundaryToGroup W 3 c) =
      (homologyEvaluation upstairsRelativeChains W 2
        ((relativeHomCapIso W).inv (homologyMap (boundaryInclusionMap W) 3 c))).hom a := by
  rw [← boundaryDualRelative_eq, boundary_image_apartment]
  change _ = (homologyEvaluation upstairsRelativeChains W 2
    (homologyMap (relativeHomKernelIso W).inv 2 (boundaryConnecting W 1
      ((boundaryCohomologyIso W).inv ((boundaryH1CapIso W boundaryOrientation).inv c))))).hom a
  rw [evaluation_connecting, ha]

end TernaryPeriodPolynomials.Argument.Lemma33
