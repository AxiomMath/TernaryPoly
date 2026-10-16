module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Isometries
public import TernaryPeriodPolynomials.Topology.LocalDiffeomorphLiftSmooth
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit

@[expose] public section


/-! Genuine smooth path lifting and equal lengths for the arithmetic covering. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold Manifold Bundle
open scoped ContDiff Manifold Bundle Topology ENNReal

/-- Every globally smooth real path has an actual smooth lift with a prescribed initial point. -/
theorem exists_smooth_path_lift (γ : ℝ → OrbitSpace)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Coordinates) 1 γ)
    (S : Space) (hS : quotientProjection S = γ 0) :
    ∃ Γ : ℝ → Space, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Coordinates) 1 Γ ∧ Γ 0 = S ∧ quotientProjection ∘ Γ = γ := by
  obtain ⟨Γ, hΓ, _⟩ := quotientProjection_covering.existsUnique_continuousMap_lifts
    ⟨γ, hγ.continuous⟩ (0 : ℝ) S hS
  refine ⟨Γ, ?_, hΓ.1, hΓ.2⟩
  exact LocalDiffeomorphLiftSmooth.contMDiff_lift
    (LocalDiffeomorphLiftSmooth.isLocalDiffeomorph_of_le
      quotientProjection_isLocalDiffeomorph (by simp)) hγ Γ.continuous hΓ.2

/-- A lifted smooth path has exactly the same length as its projection. -/
theorem pathELength_lift (γ : ℝ → OrbitSpace) (Γ : ℝ → Space)
    (hΓ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Coordinates) 1 Γ)
    (he : quotientProjection ∘ Γ = γ) (a b : ℝ) :
    pathELength 𝓘(ℝ, Coordinates) Γ a b = pathELength 𝓘(ℝ, Coordinates) γ a b := by
  rw [← he]
  exact (RiemannianMapLength.pathELength_comp quotientProjection
    (quotientProjection_contMDiff.mdifferentiable (by simp)) enorm_mfderiv_projection Γ
    (hΓ.mdifferentiable one_ne_zero) a b).symm

/-- Every strict quotient-distance bound has a lift satisfying the same bound. -/
theorem exists_lift_riemannianEDist_lt (S : Space) (q : OrbitSpace) (r : ℝ≥0∞)
    (hr : riemannianEDist 𝓘(ℝ, Coordinates) (quotientProjection S) q < r) :
    ∃ T : Space, quotientProjection T = q ∧ riemannianEDist 𝓘(ℝ, Coordinates) S T < r := by
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨Γ, hΓ, hΓ0, hproj⟩ := exists_smooth_path_lift γ hγ S h0.symm
  refine ⟨Γ 1, ?_, ?_⟩
  · exact (congrFun hproj 1).trans h1
  · have hle := riemannianEDist_le_pathELength hΓ.contMDiffOn hΓ0 rfl zero_le_one
    rw [pathELength_lift γ Γ hΓ hproj] at hle
    exact hle.trans_lt hlen

end TernaryPoly.SymmetricSpaceRiemannian
