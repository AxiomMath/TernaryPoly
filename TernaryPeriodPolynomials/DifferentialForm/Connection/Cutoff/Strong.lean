module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Hilbert
public import TernaryPeriodPolynomials.DifferentialForm.Connection.BoundedCutoffs
public import TernaryPeriodPolynomials.Analysis.Bounded.CompletionStrongLimit

@[expose] public section


/-! Strong convergence of the genuine global cutoff multipliers on the actual L2 completion. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Filter SmoothCoveringDeRham PolynomialFormHilbert SymmetricSpaceCharts
  SymmetricSpaceCovering SymmetricSpaceRiemannian
open scoped ContDiff Manifold SymmetricSpaceRiemannian Topology

/-- The actual geometric cutoff, extended from actual compact forms to their Hilbert completion. -/
def cutoffMultiplier (n k : ℕ) (c : BoundedCutoffSequence) (j : ℕ) : Hilbert n k →L[ℝ] Hilbert n k :=
  scalarMultiplier n k (c.toFun j) (c.smooth j) 1 zero_le_one
    (fun q => by rw [abs_of_nonneg (c.range j q).1]; exact (c.range j q).2)

theorem cutoffMultiplier_inclusion (n k : ℕ) (c : BoundedCutoffSequence) (j : ℕ) (a : Core n k) :
    cutoffMultiplier n k c j (inclusion n k a) =
      inclusion n k (coreScalarMultiply n k (c.toFun j) (c.smooth j) a) :=
  scalarMultiplier_inclusion n k (c.toFun j) (c.smooth j) 1 zero_le_one _ a

theorem cutoffMultiplier_opNorm_le (n k : ℕ) (c : BoundedCutoffSequence) (j : ℕ) :
    ‖cutoffMultiplier n k c j‖ ≤ 1 :=
  scalarMultiplier_opNorm_le n k (c.toFun j) (c.smooth j) 1 zero_le_one _

/-- Every compact core input is eventually fixed exactly. -/
theorem cutoffMultiplier_eventually_inclusion (n k : ℕ) (c : BoundedCutoffSequence) (a : Core n k) :
    ∀ᶠ j : ℕ in atTop, cutoffMultiplier n k c j (inclusion n k a) = inclusion n k a := by
  filter_upwards [c.eventually_one (quotientSupport a.val) a.property.1] with j hj
  exact (cutoffMultiplier_inclusion n k c j a).trans
    (congrArg (inclusion n k) (coreScalarMultiply_eq_self n k (c.toFun j) (c.smooth j) a hj))

/-- Uniform boundedness and density upgrade exact core stabilization to strong convergence. -/
theorem cutoffMultiplier_tendsto (n k : ℕ) (c : BoundedCutoffSequence) (a : Hilbert n k) :
    Tendsto (fun j => cutoffMultiplier n k c j a) atTop (𝓝 a) := by
  have heq : Equicontinuous (fun j x => cutoffMultiplier n k c j x) :=
    (LipschitzWith.uniformEquicontinuous (fun j x => cutoffMultiplier n k c j x) 1
      (fun j => ContinuousLinearMap.opNorm_le_iff_lipschitz.mp (cutoffMultiplier_opNorm_le n k c j))).equicontinuous
  refine (inclusion_dense n k).induction_on a
    (heq.isClosed_setOfPred_tendsto continuous_id) ?_
  intro v
  have he : (fun j => cutoffMultiplier n k c j (inclusion n k v)) =ᶠ[atTop]
      (fun _ => inclusion n k v) := cutoffMultiplier_eventually_inclusion n k c v
  exact tendsto_const_nhds.congr' he.symm

end TernaryPoly.PolynomialFormConnection
