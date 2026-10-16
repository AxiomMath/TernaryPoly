module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyAction
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyEdge

@[expose] public section


/-!
# Summation over the orbit of the base triangle

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeOrbit

open TernaryPoly TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree
open scoped Classical

theorem fiber_eq (t : Tri) (g : IntegralGL) (hg : g • triPlus = t) :
    {y : IntegralGL | y • triPlus = t} = (fun s => g * s) '' (MulAction.stabilizer IntegralGL triPlus : Set IntegralGL) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    refine ⟨g⁻¹ * y, ?_, by group⟩
    rw [mul_smul, h, ← hg, inv_smul_smul]
  · rintro ⟨s, hs, rfl⟩
    rw [mul_smul, hs, hg]

theorem fiber_finite (t : Tri) : {y : IntegralGL | y • triPlus = t}.Finite := by
  obtain ⟨g, hg⟩ := tri_transitive t
  rw [fiber_eq t g hg]
  have := tri_stabilizer_finite triPlus
  exact (Set.toFinite _).image _

theorem preimage_finite {F : Set Tri} (hF : F.Finite) : {y : IntegralGL | y • triPlus ∈ F}.Finite := by
  have : {y : IntegralGL | y • triPlus ∈ F} = (fun y : IntegralGL => y • triPlus) ⁻¹' F := rfl
  rw [this]
  exact hF.preimage' (fun t _ => fiber_finite t)

theorem fiber_ncard (t : Tri) : {y : IntegralGL | y • triPlus = t}.ncard = Nat.card (MulAction.stabilizer IntegralGL triPlus) := by
  obtain ⟨g, hg⟩ := tri_transitive t
  rw [fiber_eq t g hg, Set.ncard_image_of_injective _ (mul_right_injective g)]
  exact (Nat.card_coe_set_eq _).symm

theorem finsum_orbit (φ : Tri → ℚ) (hφ : (Function.support φ).Finite) :
    ∑ᶠ y : IntegralGL, φ (y • triPlus) =
      (Nat.card (MulAction.stabilizer IntegralGL triPlus) : ℚ) * ∑ᶠ t, φ t := by
  have hY : (Function.support fun y : IntegralGL => φ (y • triPlus)).Finite :=
    (preimage_finite hφ).subset (fun y hy => hy)
  rw [finsum_eq_sum_of_support_subset _ (s := hY.toFinset) (by simp),
    finsum_eq_sum_of_support_subset _ (s := hφ.toFinset) (by simp)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun y : IntegralGL => y • triPlus) (t := hφ.toFinset)
    (s := hY.toFinset) (fun y hy => by simpa using hy)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have h1 : ∀ y ∈ hY.toFinset.filter (fun y : IntegralGL => y • triPlus = t), φ (y • triPlus) = φ t := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [hy.2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  have h2 : hY.toFinset.filter (fun y : IntegralGL => y • triPlus = t) = (fiber_finite t).toFinset := by
    ext y
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support, Set.mem_ofPred_eq]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      simpa using ht
  rw [h2, ← Set.ncard_eq_toFinset_card _ (fiber_finite t), fiber_ncard]

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeOrbit
