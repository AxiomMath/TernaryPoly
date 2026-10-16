module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Weak
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Strong
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section


/-! The actual bounded geometric cutoffs converge in both maximal graph norms simultaneously. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Filter PolynomialFormHilbert SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open scoped ContDiff Manifold SymmetricSpaceRiemannian LinearPMap Topology

/-- The existing completion module instance. -/
@[instance_reducible] def cutoffHilbertModule (n k : ℕ) : Module ℝ (Hilbert n k) := inferInstance

attribute [local instance] cutoffHilbertModule
attribute [local irreducible] maximalDifferential maximalCodifferential

/-- The bounded extension of the literal exterior commutator for the j-th geometric cutoff. -/
def cutoffExteriorCommutator (n k : ℕ) (c : BoundedCutoffSequence) (j : ℕ) :
    Hilbert n k →L[ℝ] Hilbert n (k + 1) :=
  exteriorCommutator n k (c.toFun j) (c.smooth j) (c.bound / ((j : ℝ) + 1))
    (div_nonneg c.bound_pos.le (by positivity)) (cutoff_scalarSlope_bound c j)

theorem cutoffExteriorCommutator_bound (n k : ℕ) (c : BoundedCutoffSequence) (j : ℕ) (u : Hilbert n k) :
    ‖cutoffExteriorCommutator n k c j u‖ ≤
      exteriorCommutatorConstant n k * (c.bound / ((j : ℝ) + 1)) * ‖u‖ :=
  exteriorCommutator_bound n k (c.toFun j) (c.smooth j) (c.bound / ((j : ℝ) + 1))
    (div_nonneg c.bound_pos.le (by positivity)) (cutoff_scalarSlope_bound c j) u

theorem cutoffExteriorCommutator_adjoint_bound (n k : ℕ) (c : BoundedCutoffSequence) (j : ℕ)
    (u : Hilbert n (k + 1)) :
    ‖(cutoffExteriorCommutator n k c j).adjoint u‖ ≤
      exteriorCommutatorConstant n k * (c.bound / ((j : ℝ) + 1)) * ‖u‖ :=
  exteriorCommutator_adjoint_bound n k (c.toFun j) (c.smooth j) (c.bound / ((j : ℝ) + 1))
    (div_nonneg c.bound_pos.le (by positivity)) (cutoff_scalarSlope_bound c j) u

theorem cutoffSlope_tendsto_zero (c : BoundedCutoffSequence) :
    Tendsto (fun j : ℕ => c.bound / ((j : ℝ) + 1)) atTop (𝓝 0) := by
  simpa only [mul_zero, mul_one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c.bound

theorem cutoffExteriorCommutator_tendsto_zero (n k : ℕ) (c : BoundedCutoffSequence) (u : Hilbert n k) :
    Tendsto (fun j => cutoffExteriorCommutator n k c j u) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun j => cutoffExteriorCommutator_bound n k c j u)
  simpa only [mul_zero, zero_mul] using
    ((cutoffSlope_tendsto_zero c).const_mul (exteriorCommutatorConstant n k)).mul_const ‖u‖

theorem cutoffExteriorCommutator_adjoint_tendsto_zero (n k : ℕ) (c : BoundedCutoffSequence)
    (u : Hilbert n (k + 1)) :
    Tendsto (fun j => (cutoffExteriorCommutator n k c j).adjoint u) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun j => cutoffExteriorCommutator_adjoint_bound n k c j u)
  simpa only [mul_zero, zero_mul] using
    ((cutoffSlope_tendsto_zero c).const_mul (exteriorCommutatorConstant n k)).mul_const ‖u‖

/-- The explicit cutoff derivative value in the full maximal domain. -/
def cutoffDifferentialValue (n k : ℕ) (c : BoundedCutoffSequence) (j : ℕ)
    (u : Hilbert n k) (du : Hilbert n (k + 1)) : Hilbert n (k + 1) :=
  cutoffMultiplier n (k + 1) c j du + cutoffExteriorCommutator n k c j u

/-- The explicit cutoff codifferential value in the full maximal domain. -/
def cutoffCodifferentialValue (n k : ℕ) (c : BoundedCutoffSequence) (j : ℕ)
    (u : Hilbert n (k + 1)) (δu : Hilbert n k) : Hilbert n k :=
  cutoffMultiplier n k c j δu - (cutoffExteriorCommutator n k c j).adjoint u

theorem cutoff_maximalDifferential_graph (n k : ℕ) (c : BoundedCutoffSequence)
    (u : Hilbert n k) (du : Hilbert n (k + 1))
    (hu : (u, du) ∈ (maximalDifferential n k).graph) (j : ℕ) :
    (cutoffMultiplier n k c j u, cutoffDifferentialValue n k c j u du) ∈
      (maximalDifferential n k).graph :=
  maximalDifferential_scalarMultiply n k (c.toFun j) (c.smooth j) (c.bound / ((j : ℝ) + 1))
    (div_nonneg c.bound_pos.le (by positivity)) (cutoff_scalarSlope_bound c j) 1 zero_le_one
    (fun q => by rw [abs_of_nonneg (c.range j q).1]; exact (c.range j q).2) u du hu

theorem cutoff_maximalCodifferential_graph (n k : ℕ) (c : BoundedCutoffSequence)
    (u : Hilbert n (k + 1)) (δu : Hilbert n k)
    (hu : (u, δu) ∈ (maximalCodifferential n k).graph) (j : ℕ) :
    (cutoffMultiplier n (k + 1) c j u, cutoffCodifferentialValue n k c j u δu) ∈
      (maximalCodifferential n k).graph :=
  maximalCodifferential_scalarMultiply n k (c.toFun j) (c.smooth j) (c.bound / ((j : ℝ) + 1))
    (div_nonneg c.bound_pos.le (by positivity)) (cutoff_scalarSlope_bound c j) 1 zero_le_one
    (fun q => by rw [abs_of_nonneg (c.range j q).1]; exact (c.range j q).2) u δu hu

theorem cutoffDifferentialValue_tendsto (n k : ℕ) (c : BoundedCutoffSequence)
    (u : Hilbert n k) (du : Hilbert n (k + 1)) :
    Tendsto (fun j => cutoffDifferentialValue n k c j u du) atTop (𝓝 du) := by
  simpa only [cutoffDifferentialValue, add_zero] using (cutoffMultiplier_tendsto n (k + 1) c du).add
    (cutoffExteriorCommutator_tendsto_zero n k c u)

theorem cutoffCodifferentialValue_tendsto (n k : ℕ) (c : BoundedCutoffSequence)
    (u : Hilbert n (k + 1)) (δu : Hilbert n k) :
    Tendsto (fun j => cutoffCodifferentialValue n k c j u δu) atTop (𝓝 δu) := by
  simpa only [cutoffCodifferentialValue, sub_zero] using (cutoffMultiplier_tendsto n k c δu).sub
    (cutoffExteriorCommutator_adjoint_tendsto_zero n k c u)

attribute [local irreducible] cutoffMultiplier cutoffDifferentialValue cutoffCodifferentialValue
  PolynomialFormHilbert.pairingData

/-- The same actual cutoff sequence approximates a simultaneous maximal-domain input in both graphs. -/
theorem simultaneous_cutoff_graph_convergence (n k : ℕ) (c : BoundedCutoffSequence)
    (u : Hilbert n (k + 1)) (du : Hilbert n ((k + 1) + 1)) (δu : Hilbert n k)
    (hdu : (u, du) ∈ (maximalDifferential n (k + 1)).graph)
    (hδu : (u, δu) ∈ (maximalCodifferential n k).graph) :
    let w : ℕ → Hilbert n (k + 1) := fun j => cutoffMultiplier n (k + 1) c j u
    let dw : ℕ → Hilbert n ((k + 1) + 1) := fun j => cutoffDifferentialValue n (k + 1) c j u du
    let δw : ℕ → Hilbert n k := fun j => cutoffCodifferentialValue n k c j u δu
    (∀ j : ℕ, (maximalDifferential n (k + 1)).graph.carrier (w j, dw j)) ∧
    (∀ j : ℕ, (maximalCodifferential n k).graph.carrier (w j, δw j)) ∧
    Tendsto w atTop (𝓝 u) ∧ Tendsto dw atTop (𝓝 du) ∧ Tendsto δw atTop (𝓝 δu) :=
  ⟨cutoff_maximalDifferential_graph n (k + 1) c u du hdu,
    cutoff_maximalCodifferential_graph n k c u δu hδu,
    cutoffMultiplier_tendsto n (k + 1) c u,
    cutoffDifferentialValue_tendsto n (k + 1) c u du,
    cutoffCodifferentialValue_tendsto n k c u δu⟩

end TernaryPoly.PolynomialFormConnection
