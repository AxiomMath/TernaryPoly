module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingCompactNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set SmoothCoveringDeRham SymmetricSpaceCovering CategoryTheory
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U V : Set OrbitSpace}

/-- Downstream genuine ordinary Mayer-Vietoris interface. -/
theorem deRham_ordinary_mayerVietoris (hU : IsOpen U) (hV : IsOpen V) :
    (ordinarySequence ρ hU hV).ShortExact := ordinarySequence_shortExact ρ hU hV

/-- Downstream genuine compact-support Mayer-Vietoris interface. -/
theorem deRham_compact_mayerVietoris (hU : IsOpen U) (hV : IsOpen V) :
    (compactSequence ρ hU hV).ShortExact := compactSequence_shortExact ρ hU hV

/-- The source support is unchanged by actual compact-support zero extension. -/
theorem deRham_extension_support (hU : IsOpen U) (hUV : U ⊆ V) (n : ℕ)
    (w : CompactSupportForm ρ U n) :
    quotientSupport (compactZeroExtend hU hUV n w).val = quotientSupport w.val := rfl

/-- Compact-support locality for arbitrary directed open exhaustions. -/
theorem deRham_compact_exhaustion {ι : Type*} [Nonempty ι]
    (D : ι → Set OrbitSpace) (hD : ∀ i, IsOpen (D i)) (hDU : ∀ i, D i ⊆ U)
    (hcover : U ⊆ ⋃ i, D i) (hdir : Directed (· ⊆ ·) D) (n : ℕ) (w : CompactSupportForm ρ U n) :
    ∃ i, ∃ z : CompactSupportForm ρ (D i) n, compactZeroExtend (hD i) (hDU i) n z = w :=
  compactSupport_directed_exhaustion D hD hDU hcover hdir w

end TernaryPoly.SmoothDeRhamGluing
