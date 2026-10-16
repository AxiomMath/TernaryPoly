module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.GraphLimit
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Support

@[expose] public section


/-! Unconditional compact weak-support approximation in both actual maximal graphs. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Filter PolynomialFormHilbert SymmetricSpaceCovering SymmetricSpaceRiemannian
open scoped LinearPMap Topology

attribute [local instance] cutoffHilbertModule
attribute [local irreducible] maximalDifferential maximalCodifferential
  cutoffMultiplier cutoffDifferentialValue cutoffCodifferentialValue PolynomialFormHilbert.pairingData

/-- Each simultaneous cutoff graph triple has one actual compact weak-support set. -/
theorem simultaneous_cutoff_compact_support (n k : ℕ) (c : BoundedCutoffSequence)
    (u : Hilbert n (k + 1)) (du : Hilbert n ((k + 1) + 1)) (δu : Hilbert n k)
    (hdu : (u, du) ∈ (maximalDifferential n (k + 1)).graph)
    (hδu : (u, δu) ∈ (maximalCodifferential n k).graph) (j : ℕ) :
    ∃ K : Set OrbitSpace, IsCompact K ∧
      HasWeakSupportIn n (k + 1) K (cutoffMultiplier n (k + 1) c j u) ∧
      HasWeakSupportIn n ((k + 1) + 1) K (cutoffDifferentialValue n (k + 1) c j u du) ∧
      HasWeakSupportIn n k K (cutoffCodifferentialValue n k c j u δu) := by
  have h := cutoffMultiplier_weakSupport n (k + 1) c j u
  exact ⟨tsupport (c.toFun j), c.compact j, h,
    h.maximalDifferential (cutoff_maximalDifferential_graph n (k + 1) c u du hdu j),
    h.maximalCodifferential (cutoff_maximalCodifferential_graph n k c u δu hδu j)⟩

/-- The proved actual geometry unconditionally gives simultaneous compact weak-support graph approximation. -/
theorem exists_simultaneous_compact_weak_graph_approximation (n k : ℕ)
    (u : Hilbert n (k + 1)) (du : Hilbert n ((k + 1) + 1)) (δu : Hilbert n k)
    (hdu : (u, du) ∈ (maximalDifferential n (k + 1)).graph)
    (hδu : (u, δu) ∈ (maximalCodifferential n k).graph) :
    ∃ w : ℕ → Hilbert n (k + 1), ∃ dw : ℕ → Hilbert n ((k + 1) + 1), ∃ δw : ℕ → Hilbert n k,
      (∀ j : ℕ, (w j, dw j) ∈ (maximalDifferential n (k + 1)).graph) ∧
      (∀ j : ℕ, (w j, δw j) ∈ (maximalCodifferential n k).graph) ∧
      (∀ j : ℕ, ∃ K : Set OrbitSpace, IsCompact K ∧ HasWeakSupportIn n (k + 1) K (w j) ∧
        HasWeakSupportIn n ((k + 1) + 1) K (dw j) ∧ HasWeakSupportIn n k K (δw j)) ∧
      Tendsto w atTop (𝓝 u) ∧ Tendsto dw atTop (𝓝 du) ∧ Tendsto δw atTop (𝓝 δu) := by
  let c := boundedCutoffSequence
  exact ⟨fun j => cutoffMultiplier n (k + 1) c j u,
    fun j => cutoffDifferentialValue n (k + 1) c j u du,
    fun j => cutoffCodifferentialValue n k c j u δu,
    cutoff_maximalDifferential_graph n (k + 1) c u du hdu,
    cutoff_maximalCodifferential_graph n k c u δu hδu,
    simultaneous_cutoff_compact_support n k c u du δu hdu hδu,
    cutoffMultiplier_tendsto n (k + 1) c u,
    cutoffDifferentialValue_tendsto n (k + 1) c u du,
    cutoffCodifferentialValue_tendsto n k c u δu⟩

end TernaryPoly.PolynomialFormConnection
