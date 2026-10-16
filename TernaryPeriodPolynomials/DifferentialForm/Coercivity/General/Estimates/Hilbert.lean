module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Forms.Pairing
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Calculus.IntegrationByParts
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.Completion
public import TernaryPeriodPolynomials.Analysis.ContinuousDensityOpenPositive

@[expose] public section


/-! # General coercivity, Tier B: the `L²` completions of the spaces of compactly supported forms

For an admissible group `Γ` the `L²` pairing of `Forms/Pairing` makes `CForm Γ n k` a pre-Hilbert
space.  Its completion `Hilbert Γ n k` is built with the generic
`TernaryPoly.CompactPairingCompletion`, exactly as `TernaryPoly.PolynomialFormHilbert.Hilbert` is
for the cover.  Admissibility enters through `[Fact (Admissible Γ)]`.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set Topology TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpaceRiemannian
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open scoped ContDiff Pointwise

/-- The Riemannian volume of `Space` charges every nonempty open set. -/
instance instIsOpenPosMeasureSpaceVolume : spaceVolume.IsOpenPosMeasure := by
  constructor
  intro V hV hne
  obtain ⟨S, hS⟩ := hne
  have hx : coordinateChart S ∈ positiveCoordinates := extract_mem S
  have hcont : ContinuousAt coordinateDensity (coordinateChart S) :=
    (contDiffOn_coordinateDensity.continuousOn _ hx).continuousAt
      (isOpen_positiveCoordinates.mem_nhds hx)
  have hopen : IsOpen (coordinateChart '' V) :=
    coordinateChart.isOpen_image_of_subset_source hV (by simp)
  have hpos : 0 < coordinateVolume (coordinateChart '' V) :=
    TernaryPoly.ContinuousDensityOpenPositive.withDensity_pos hcont (coordinateDensity_pos _ hx)
      (hopen.mem_nhds ⟨S, hS, rfl⟩)
  rw [spaceVolume_apply]
  exact ne_of_gt hpos

variable {Γ : Subgroup RealGL}

/-- The orbit-space volume charges every nonempty open set. -/
theorem Admissible.quotientVolume_isOpenPos (h : Admissible Γ) :
    (quotientVolume Γ).IsOpenPosMeasure := by
  constructor
  intro U hU hne h0
  have : Countable Γ := h.countable
  obtain ⟨t, htm, ht⟩ := h.exists_isFundamentalDomain
  have := h.quotientMeasureEq
  rw [ht.projection_respects_measure_apply (quotientVolume Γ) hU.measurableSet] at h0
  have hinv : ∀ γ : Γ, γ • (proj Γ ⁻¹' U) = proj Γ ⁻¹' U := by
    intro γ
    ext S
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [mem_preimage, proj_smul]
  have h0' : spaceVolume (proj Γ ⁻¹' U ∩ t) = 0 := h0
  have hz : spaceVolume (proj Γ ⁻¹' U) = 0 := by
    rw [ht.measure_eq_tsum (proj Γ ⁻¹' U)]
    simp only [hinv]
    simp [h0']
  have hopen : IsOpen (proj Γ ⁻¹' U) := hU.preimage continuous_proj
  obtain ⟨q, hq⟩ := hne
  obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
  exact hopen.measure_ne_zero spaceVolume ⟨S, hq⟩ hz

instance instIsFiniteMeasureOnCompactsQuotientVolume [hΓ : Fact (Admissible Γ)] :
    IsFiniteMeasureOnCompacts (quotientVolume Γ) :=
  ⟨fun _ hQ => hΓ.out.quotientVolume_lt_top hQ⟩

instance instIsOpenPosMeasureQuotientVolume [hΓ : Fact (Admissible Γ)] :
    (quotientVolume Γ).IsOpenPosMeasure :=
  hΓ.out.quotientVolume_isOpenPos

/-! ### The pairing data and the completion -/

variable (Γ) (n k : ℕ) [hΓ : Fact (Admissible Γ)]

/-- The descended pointwise metric, bundled as a continuous bilinear pairing. -/
def scalarBilinear : CForm Γ n k →ₗ[ℝ] CForm Γ n k →ₗ[ℝ] C(OrbitSpace Γ, ℝ) where
  toFun a :=
    { toFun := fun b => ⟨scalarPairing a b, continuous_scalarPairing hΓ.out a b⟩
      map_add' := fun b c => ContinuousMap.ext fun q => congrFun (scalarPairing_add_right a b c) q
      map_smul' := fun t b => ContinuousMap.ext fun q =>
        congrFun (scalarPairing_smul_right t a b) q }
  map_add' a b := LinearMap.ext fun c => ContinuousMap.ext fun q =>
    congrFun (scalarPairing_add_left a b c) q
  map_smul' t a := LinearMap.ext fun b => ContinuousMap.ext fun q =>
    congrFun (scalarPairing_smul_left t a b) q

/-- Every hypothesis of the integral inner-product construction holds for compactly supported
equivariant forms. -/
def pairingData : TernaryPoly.CompactPairingCompletion.Data (OrbitSpace Γ) (CForm Γ n k) where
  scalarPairing := scalarBilinear Γ n k
  compact a b := hasCompactSupport_scalarPairing a b
  symmetric a b q := congrFun (scalarPairing_comm a b) q
  nonneg a q := scalarPairing_self_nonneg a q
  positive a ha := by
    by_contra hcon
    push Not at hcon
    apply ha
    apply CForm.ext
    intro x hx
    obtain ⟨S, rfl⟩ : ∃ S : Space, coordinateChart S = x :=
      ⟨coordinateChart.symm x, coordinateChart.right_inv (by simpa using hx)⟩
    have h1 : scalarPairing a a (proj Γ S) = 0 :=
      le_antisymm (hcon _) (scalarPairing_self_nonneg a _)
    rw [scalarPairing_proj hΓ.out] at h1
    exact (formPairing_self_eq_zero n k _ hx _).mp h1

/-- The `L²` completion of the compactly supported equivariant forms of degree `k`. -/
abbrev Hilbert : Type :=
  TernaryPoly.CompactPairingCompletion.Hilbert (quotientVolume Γ) (pairingData Γ n k)

/-- The canonical inclusion of compactly supported forms into their `L²` completion. -/
def incl : CForm Γ n k →ₗ[ℝ] Hilbert Γ n k :=
  (TernaryPoly.CompactPairingCompletion.inclusion (quotientVolume Γ) (pairingData Γ n k)).toLinearMap

theorem incl_injective : Function.Injective (incl Γ n k) :=
  (TernaryPoly.CompactPairingCompletion.inclusion (quotientVolume Γ) (pairingData Γ n k)).injective

theorem incl_dense : DenseRange (incl Γ n k) :=
  TernaryPoly.CompactPairingCompletion.denseRange_inclusion (quotientVolume Γ) (pairingData Γ n k)

/-- The inner product of embedded forms is the `L²` pairing of the orbit space. -/
theorem inner_incl (a b : CForm Γ n k) :
    inner ℝ (incl Γ n k a) (incl Γ n k b) = l2Form Γ n k a b :=
  TernaryPoly.CompactPairingCompletion.inner_inclusion (quotientVolume Γ) (pairingData Γ n k) a b

theorem norm_incl_sq (a : CForm Γ n k) : ‖incl Γ n k a‖ ^ 2 = normSq a := by
  have h := inner_incl Γ n k a a
  have h2 : inner ℝ (incl Γ n k a) (incl Γ n k a) = ‖incl Γ n k a‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  exact h2.symm.trans h

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
