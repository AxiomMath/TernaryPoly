module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.ManifoldAtlas
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientManifold
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open Topology Set
open scoped Manifold ContDiff

/-- The global coordinate map is smooth for the actual singleton chart structure. -/
theorem coordinateChart_contMDiff :
    ContMDiff 𝓘(ℝ,Coordinates) 𝓘(ℝ,Coordinates) ∞ coordinateChart := by
  have h : coordinateChart∈atlas Coordinates Space := Set.mem_singleton _
  have hh := contMDiffOn_of_mem_maximalAtlas (I := 𝓘(ℝ,Coordinates)) (n := ∞)
    (IsManifold.subset_maximalAtlas h)
  simpa only [coordinateChart_source,contMDiffOn_univ] using hh

/-- Inverse coordinates are smooth on the actual positive domain. -/
theorem coordinateChart_symm_contMDiffOn :
    ContMDiffOn 𝓘(ℝ,Coordinates) 𝓘(ℝ,Coordinates) ∞ coordinateChart.symm coordinateChart.target := by
  have h : coordinateChart∈atlas Coordinates Space := Set.mem_singleton _
  exact contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h)

/-- The exact local covering sections are smooth in the quotient atlas. -/
theorem localLift_contMDiffOn (S : Space) :
    ContMDiffOn 𝓘(ℝ,Coordinates) 𝓘(ℝ,Coordinates) ∞ (localLift S) (localLift S).source := by
  rw [←quotientChart_source]
  have hcomp := coordinateChart_symm_contMDiffOn.comp (quotientChart_contMDiffOn S)
    (fun x hx => coordinateChart_target.symm ▸
      quotientChart_target_subset S ((quotientChart S).map_source hx))
  apply hcomp.congr
  intro x _
  exact (coordinateChart.left_inv (by rw [coordinateChart_source]; trivial)).symm

/-- On a given covering sheet, projection followed by the quotient chart is the global chart. -/
theorem quotientChart_projection (S P : Space) (hP : P∈(localLift S).target) :
    quotientChart S (quotientProjection P)=coordinateChart P := by
  change coordinateChart (localLift S (quotientProjection P))=coordinateChart P
  rw [←localLift_symm S,(localLift S).right_inv hP]

/-- The actual quotient projection is smooth on every covering sheet. -/
theorem projection_contMDiffOn (S : Space) :
    ContMDiffOn 𝓘(ℝ,Coordinates) 𝓘(ℝ,Coordinates) ∞ quotientProjection (localLift S).target := by
  have hsource (P : Space) (hP : P∈(localLift S).target) :
      quotientProjection P∈(quotientChart S).source := by
    rw [quotientChart_source,←localLift_symm S]
    exact (localLift S).map_target hP
  have hmap : MapsTo coordinateChart (localLift S).target (quotientChart S).target := by
    intro P hP
    rw [←quotientChart_projection S P hP]
    exact (quotientChart S).map_source (hsource P hP)
  have hcomp := (quotientChart_symm_contMDiffOn S).comp coordinateChart_contMDiff.contMDiffOn hmap
  apply hcomp.congr
  intro P hP
  rw [Function.comp_apply,←quotientChart_projection S P hP,
    (quotientChart S).left_inv (hsource P hP)]

/-- The actual local covering projection, bundled as a smooth partial diffeomorphism. -/
def projectionPartialDiffeomorph (S : Space) :
    PartialDiffeomorph 𝓘(ℝ,Coordinates) 𝓘(ℝ,Coordinates) Space OrbitSpace ∞ where
  toPartialEquiv := (localLift S).symm.toPartialEquiv
  open_source := (localLift S).open_target
  open_target := (localLift S).open_source
  contMDiffOn_toFun := by
    change ContMDiffOn _ _ _ (localLift S).symm (localLift S).target
    rw [localLift_symm]
    exact projection_contMDiffOn S
  contMDiffOn_invFun := localLift_contMDiffOn S

/-- The exact quotient map is a smooth local diffeomorphism at every actual positive form. -/
theorem quotientProjection_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℝ,Coordinates) 𝓘(ℝ,Coordinates) ∞ quotientProjection := by
  intro S
  have hS : S ∈ (projectionPartialDiffeomorph S).source := by
    change S∈(localLift S).target
    simpa only [localLift_self] using (localLift S).map_source (self_mem_localLift S)
  have h := (projectionPartialDiffeomorph S).isLocalDiffeomorphAt _ _ _ hS
  have heq : (fun P => projectionPartialDiffeomorph S P) = quotientProjection := by
    funext P
    exact congrFun (localLift_symm S) P
  exact heq ▸ h

/-- Smoothness of the actual arithmetic quotient projection. -/
theorem quotientProjection_contMDiff :
    ContMDiff 𝓘(ℝ,Coordinates) 𝓘(ℝ,Coordinates) ∞ quotientProjection :=
  quotientProjection_isLocalDiffeomorph.contMDiff

/-- Every tangent space of the actual quotient manifold has real dimension five. -/
theorem orbit_tangent_finrank (x : OrbitSpace) :
    Module.finrank ℝ (TangentSpace 𝓘(ℝ,Coordinates) x)=5 := model_finrank

end TernaryPoly.SymmetricSpaceQuotientManifold
