module

public import TernaryPeriodPolynomials.Building.RankTwo.GoodOne
public import TernaryPeriodPolynomials.Building.RankTwo.GoodPaths
public import TernaryPeriodPolynomials.Building.RankTwo.HeightZero

@[expose] public section


noncomputable section
namespace TernaryPoly.RankTwoGoodFilling
open RankTwoAugmentedFrames RankTwoGoodComplex OrientedListChains

/-- Every finite reduced Good zero-chain bounds a finite actual Good edge chain. -/
theorem zero_cycle_filling (φ : Functional) (hφ : φ ≠ 0) {c : Chain RationalLine2}
    (hc : c ∈ chains (good φ) 1) (hd : boundary c = 0) :
    ∃ b : Chain RationalLine2, b ∈ chains (good φ) 2 ∧ boundary b = c := by
  obtain ⟨b,hb,hdb⟩ := RankTwoHeightZero.ambient_reduced_zero_filling
    (chains_mono (good_le_ambient φ) 1 hc) hd
  obtain ⟨e,he,hde⟩ := RankTwoGoodPaths.chain_replacement φ hφ hb
  exact ⟨e,he,by rw [hdb,RankTwoGoodPaths.replacement_map_good φ hφ 1 hc] at hde; exact hde⟩

/-- The actual Good triangle differential is injective. -/
theorem differential_two_injective (φ : Functional) :
    Function.Injective (differential (good φ) 2) := by
  intro c d he
  apply Subtype.ext
  exact RankTwoGoodComplex.top_boundary_injective φ c.property d.property (congrArg Subtype.val he)

/-- Actual finite reduced H0, H1, and top-boundary injectivity for every nonzero residue functional. -/
theorem good_exactness (φ : Functional) (hφ : φ ≠ 0) :
    (∀ c : Chain RationalLine2, c ∈ chains (good φ) 1 → boundary c = 0 →
      ∃ b : Chain RationalLine2, b ∈ chains (good φ) 2 ∧ boundary b = c) ∧
    (∀ c : Chain RationalLine2, c ∈ chains (good φ) 2 → boundary c = 0 →
      ∃ b : Chain RationalLine2, b ∈ chains (good φ) 3 ∧ boundary b = c) ∧
    Function.Injective (differential (good φ) 2) :=
  ⟨fun _ hc hd => zero_cycle_filling φ hφ hc hd,
    fun _ hc hd => RankTwoGoodOne.one_cycle_filling φ hc hd,differential_two_injective φ⟩

end TernaryPoly.RankTwoGoodFilling
