module

public import TernaryPeriodPolynomials.Building.Ambient.HeightStep
public import TernaryPeriodPolynomials.Building.Ambient.HeightInduction
public import TernaryPeriodPolynomials.Building.Ambient.LowLinkFilling

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientTwoFilling
open ModThreeGoodAction AugmentedFrameComplex PrimitiveLineHeight
open OrientedListChains AmbientHeightFiltration

/-- Every actual high vertex has the lower-link filling required for finite height descent. -/
theorem low_link_filling (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hN : 0 < N) :
    AmbientHeightStep.LowLinkFilling F N := by
  intro a ha u hu hz
  exact AmbientLowLinkFilling.descending_one_cycle_filling F a (ha ▸ hN) hu hz

/-- All three finite surgeries discharge the literal height-step premise. -/
theorem height_step (F : IntegralVector →ₗ[ℤ] ℤ) : AmbientHeightInduction.HeightStep F := by
  intro N hN c hc hd
  obtain ⟨t,r,ht,hr,he,hdr⟩ :=
    AmbientHeightStep.lower_height F N hN (low_link_filling F N hN) hc hd
  exact ⟨t,r,chains_mono (bounded_le_ambient F N) 4 ht,hr,he,hdr⟩

/-- Every finite actual rank-three augmented-frame two-cycle bounds. -/
theorem ambient_two_filling : GoodChainFilling.AmbientTwoFilling :=
  AmbientHeightInduction.ambient_two_filling (height_step lastCoordinate)

/-- Every finite actual Good augmented-frame two-cycle bounds in Good chains. -/
theorem good_two_filling {c : Chain RationalLine}
    (hc : c ∈ chains good 3) (hd : boundary c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = c :=
  GoodChainFilling.good_two_filling_of_ambient ambient_two_filling hc hd

end TernaryPoly.AmbientTwoFilling
