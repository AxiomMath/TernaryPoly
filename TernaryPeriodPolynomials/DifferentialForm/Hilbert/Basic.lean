module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Support
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactSupport
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.VolumePositive
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.Completion

@[expose] public section


/-! The genuine L² completion of compact polynomial-coefficient forms on the arithmetic quotient. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open MeasureTheory PolynomialCoefficientMetric PolynomialFormMetric SmoothCoveringDeRham
open SymmetricSpaceCovering SymmetricSpaceRiemannian
open scoped SymmetricSpaceRiemannian

/-- These are the actual compactly supported smooth equivariant forms, in every degree. -/
abbrev Core (n k : ℕ) := CompactSupportForm (deckRepresentation n) Set.univ k

/-- The genuine descended pointwise metric, bundled as a continuous scalar bilinear pairing. -/
def scalarBilinear (n k : ℕ) : Core n k →ₗ[ℝ] Core n k →ₗ[ℝ] C(OrbitSpace, ℝ) where
  toFun a :=
    { toFun := fun b => ⟨scalarPairing n k a.val b.val, continuous_scalarPairing n k a.val b.val⟩
      map_add' := by
        intro b c
        apply ContinuousMap.ext
        intro q
        exact congrFun (scalarPairing_add_right n k a.val b.val c.val) q
      map_smul' := by
        intro t b
        apply ContinuousMap.ext
        intro q
        exact congrFun (scalarPairing_smul_right n k t a.val b.val) q }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    apply ContinuousMap.ext
    intro q
    exact congrFun (scalarPairing_add_left n k a.val b.val c.val) q
  map_smul' := by
    intro t a
    apply LinearMap.ext
    intro b
    apply ContinuousMap.ext
    intro q
    exact congrFun (scalarPairing_smul_left n k t a.val b.val) q

/-- Every hypothesis of the integral inner-product construction is proved for actual forms. -/
def pairingData (n k : ℕ) : CompactPairingCompletion.Data OrbitSpace (Core n k) where
  scalarPairing := scalarBilinear n k
  compact a b := hasCompactSupport_scalarPairing n k a.val b.val a.property.1
  symmetric a b q := scalarPairing_symm n k a.val b.val q
  nonneg a q := scalarPairing_nonneg n k a.val q
  positive a ha := by
    by_contra h
    push Not at h
    apply ha
    apply Subtype.ext
    apply (scalarPairing_self_identically_zero n k a.val).mp
    funext q
    exact le_antisymm (h q) (scalarPairing_nonneg n k a.val q)

/-- The actual Hilbert space is the completion for the integral of the genuine form metric. -/
abbrev Hilbert (n k : ℕ) := CompactPairingCompletion.Hilbert orbitVolume (pairingData n k)

/-- The canonical inclusion of actual compact smooth forms into their L² completion. -/
def inclusion (n k : ℕ) : Core n k →ₗ[ℝ] Hilbert n k :=
  (CompactPairingCompletion.inclusion orbitVolume (pairingData n k)).toLinearMap

theorem inclusion_injective (n k : ℕ) : Function.Injective (inclusion n k) :=
  (CompactPairingCompletion.inclusion orbitVolume (pairingData n k)).injective

theorem inclusion_dense (n k : ℕ) : DenseRange (inclusion n k) :=
  CompactPairingCompletion.denseRange_inclusion orbitVolume (pairingData n k)

/-- This is the literal metric-and-volume L² formula on actual compact forms. -/
theorem inner_inclusion (n k : ℕ) (a b : Core n k) :
    inner ℝ (inclusion n k a) (inclusion n k b) =
      ∫ q, scalarPairing n k a.val b.val q ∂orbitVolume :=
  CompactPairingCompletion.inner_inclusion orbitVolume (pairingData n k) a b

end TernaryPoly.PolynomialFormHilbert
