module

public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.Completion

@[expose] public section


/-! Hilbert completion of the integral norm on compactly supported continuous scalar pairings. -/
noncomputable section
namespace TernaryPoly.CompactPairingCompletion

open MeasureTheory
variable {X V : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [AddCommGroup V] [Module ℝ V]

/-- Explicit pointwise data, to be instantiated by genuine compact smooth forms. -/
structure Data (X V : Type*) [TopologicalSpace X] [AddCommGroup V] [Module ℝ V] where
  scalarPairing : V →ₗ[ℝ] V →ₗ[ℝ] C(X, ℝ)
  compact : ∀ v w, HasCompactSupport (scalarPairing v w)
  symmetric : ∀ v w x, scalarPairing v w x = scalarPairing w v x
  nonneg : ∀ v x, 0 ≤ scalarPairing v v x
  positive : ∀ v, v ≠ 0 → ∃ x, 0 < scalarPairing v v x

/-- A fresh type gives the integral norm without overwriting any preexisting smooth topology. -/
def Space (_μ : Measure X) (_d : Data X V) := V

variable (μ : Measure X) (d : Data X V)

instance spaceAddCommGroup : AddCommGroup (Space μ d) := inferInstanceAs (AddCommGroup V)
instance spaceModule : Module ℝ (Space μ d) := inferInstanceAs (Module ℝ V)

variable [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

@[instance_reducible] def spaceCore : InnerProductSpace.Core ℝ (Space μ d) :=
  CompactPairingInnerProduct.innerCore (μ := μ) d.scalarPairing d.compact d.symmetric d.nonneg d.positive

instance spaceNormedAddCommGroup : NormedAddCommGroup (Space μ d) := by
  letI := spaceCore μ d
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance spaceInnerProduct : InnerProductSpace ℝ (Space μ d) := by
  letI := spaceCore μ d
  exact InnerProductSpace.ofCore (spaceCore μ d).toCore

/-- The actual completion of the integral norm; no abstract Hilbert space is substituted. -/
abbrev Hilbert := UniformSpace.Completion (Space μ d)

/-- Compact fields embed linearly and isometrically into this actual Hilbert completion. -/
def inclusion : Space μ d →ₗᵢ[ℝ] Hilbert μ d :=
  UniformSpace.Completion.toComplₗᵢ

/-- The Hilbert inner product of embedded fields is their original integral. -/
theorem inner_inclusion (v w : Space μ d) :
    inner ℝ (inclusion μ d v) (inclusion μ d w) =
      ∫ x, d.scalarPairing v w x ∂μ := by
  change inner ℝ (v : UniformSpace.Completion (Space μ d)) (w : UniformSpace.Completion (Space μ d)) = _
  rw [UniformSpace.Completion.inner_coe]
  rfl

/-- The defining compact fields have dense image. -/
theorem denseRange_inclusion : DenseRange (inclusion μ d) := by
  change DenseRange (fun v : Space μ d => (v : UniformSpace.Completion (Space μ d)))
  exact UniformSpace.Completion.denseRange_coe

end TernaryPoly.CompactPairingCompletion
