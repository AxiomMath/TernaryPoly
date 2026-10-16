module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualPairing

@[expose] public section


/-!
# General coercivity, dual coefficients: transport of the orbit-space volume

The Cartan involution carries a measurable fundamental domain of `Γ` to one of `θΓ` and preserves the
Riemannian volume, hence the induced homeomorphism of orbit spaces carries `quotientVolume Γ` to
`quotientVolume (θΓ)`.  Consequently the dual `L²` pairing of `Γ` is the standard `L²` pairing of the
Cartan images (`dualL2_eq`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering
open MeasureTheory Set Filter

variable {Γ : Subgroup RealGL} {n k : ℕ}

theorem iota_injective : Function.Injective iota := Function.LeftInverse.injective iota_iota

theorem measurableEmbedding_iota : MeasurableEmbedding iota := iotaHomeo.measurableEmbedding

theorem measurable_proj (Γ : Subgroup RealGL) : Measurable (proj Γ) :=
  measurable_quotient_mk' (s := MulAction.orbitRel Γ Space)

theorem measurable_qIota (Γ : Subgroup RealGL) : Measurable (qIota Γ) :=
  measurable_from_quotient.mpr
    ((measurable_proj (thetaImage Γ)).comp continuous_iota.measurable)

/-- The Cartan image of a fundamental domain is a fundamental domain of the Cartan image. -/
theorem isFundamentalDomain_iota_image {t : Set Space} (ht : MeasurableSet t)
    (hu : ∀ x : Space, ∃! g : Γ, g • x ∈ t) :
    IsFundamentalDomain (thetaImage Γ) (iota '' t) spaceVolume := by
  refine IsFundamentalDomain.mk' (measurableEmbedding_iota.measurableSet_image.mpr ht).nullMeasurableSet
    (fun y => ?_)
  obtain ⟨γ, hγ, huniq⟩ := hu (iota y)
  refine ⟨⟨thetaHom (γ : RealGL), theta_mem_thetaImage γ.2⟩, ?_, ?_⟩
  · refine ⟨iota (act (thetaHom (γ : RealGL)) y), ?_, iota_iota _⟩
    rw [iota_act, thetaHom_thetaHom]
    exact hγ
  · rintro ⟨_, δ, hδ, rfl⟩ ⟨z, hz, hzy⟩
    have hz' : z = act δ (iota y) := by
      have := congrArg iota hzy
      rw [iota_iota] at this
      change z = iota (act (thetaHom δ) y) at this
      rw [this, iota_act, thetaHom_thetaHom]
    have hmem : (⟨δ, hδ⟩ : Γ) • iota y ∈ t := by
      show act δ (iota y) ∈ t
      rw [← hz']
      exact hz
    have := huniq _ hmem
    apply Subtype.ext
    show thetaHom δ = thetaHom (γ : RealGL)
    rw [← this]

/-- The Cartan involution carries the volume of the orbit space of `Γ` to that of `θΓ`. -/
theorem map_qIota_quotientVolume (h : Admissible Γ) :
    (quotientVolume Γ).map (qIota Γ) = quotientVolume (thetaImage Γ) := by
  obtain ⟨t, ht, hu⟩ := h.exists_unique_section
  have hFD : IsFundamentalDomain Γ t spaceVolume := IsFundamentalDomain.mk' ht.nullMeasurableSet hu
  have hFD' := isFundamentalDomain_iota_image ht hu
  rw [h.quotientVolume_eq hFD, h.theta.quotientVolume_eq hFD']
  have hrestr : (spaceVolume.restrict t).map iota = spaceVolume.restrict (iota '' t) := by
    have := measurableEmbedding_iota.restrict_map spaceVolume (iota '' t)
    rw [measurePreserving_iota.map_eq, iota_injective.preimage_image] at this
    exact this.symm
  calc ((spaceVolume.restrict t).map (proj Γ)).map (qIota Γ)
      = (spaceVolume.restrict t).map (qIota Γ ∘ proj Γ) :=
        Measure.map_map (measurable_qIota Γ) (measurable_proj Γ)
    _ = (spaceVolume.restrict t).map (proj (thetaImage Γ) ∘ iota) := rfl
    _ = ((spaceVolume.restrict t).map iota).map (proj (thetaImage Γ)) :=
        (Measure.map_map (measurable_proj _) continuous_iota.measurable).symm
    _ = (spaceVolume.restrict (iota '' t)).map (proj (thetaImage Γ)) := by rw [hrestr]

/-- The dual `L²` pairing is the standard `L²` pairing of the Cartan images. -/
theorem dualL2_eq (h : Admissible Γ) (a b : DForm Γ n k) :
    dualL2 a b = l2Form (thetaImage Γ) n k (toStd h n k a) (toStd h n k b) := by
  unfold dualL2
  rw [l2Form_apply]
  have hcongr : (fun q => dualScalar a b q) =
      fun q => scalarPairing (toStd h n k a) (toStd h n k b) (qIota Γ q) :=
    funext (dualScalar_eq_std h a b)
  have hmeas : Measurable (scalarPairing (toStd h n k a) (toStd h n k b)) :=
    (continuous_scalarPairing h.theta _ _).measurable
  have e1 := congrArg (fun F : OrbitSpace Γ → ℝ => ∫ q, F q ∂quotientVolume Γ) hcongr
  have e2 := (integral_map (μ := quotientVolume Γ) (measurable_qIota Γ).aemeasurable
    hmeas.aestronglyMeasurable).symm
  have e3 := congrArg
    (fun μ : Measure (OrbitSpace (thetaImage Γ)) =>
      ∫ q', scalarPairing (toStd h n k a) (toStd h n k b) q' ∂μ) (map_qIota_quotientVolume h)
  exact e1.trans (e2.trans e3)

theorem dualNormSq_eq (h : Admissible Γ) (a : DForm Γ n k) :
    dualNormSq a = normSq (toStd h n k a) := dualL2_eq h a a

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
