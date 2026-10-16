module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.MixedNormalForm
public import Mathlib.GroupTheory.GroupExtension.Basic

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N L : Type} [Group N] [Group L] (action : L →* MulAut N)

theorem semidirectRadicalCoefficient_commute (representation : Rep ℂ (N ⋊[action] L))
    (element : N ⋊[action] L) (radical : N) (vector : representation) :
    representation.ρ element (representation.ρ (SemidirectProduct.inl radical) vector) =
      representation.ρ (SemidirectProduct.inl element.left)
        (representation.ρ (SemidirectProduct.inl (action element.right radical))
          (representation.ρ (SemidirectProduct.inr element.right) vector)) := by
  have equality : element * SemidirectProduct.inl radical =
      SemidirectProduct.inl element.left * SemidirectProduct.inl (action element.right radical) *
        SemidirectProduct.inr element.right := by
    apply SemidirectProduct.ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right]
  simpa only [map_mul, Module.End.mul_apply] using
    congrArg (fun input => representation.ρ input vector) equality

def semidirectMixedTwoValue (representation : Rep ℂ (N ⋊[action] L))
    (family : L → groupCohomology.cocycles₁ (Rep.res SemidirectProduct.inl representation))
    (pair : (N ⋊[action] L) × (N ⋊[action] L)) : representation :=
  representation.ρ (SemidirectProduct.inl pair.1.left)
    (family pair.1.right (action pair.1.right pair.2.left))

theorem semidirectMixedTwoValue_cocycle (representation : Rep ℂ (N ⋊[action] L))
    (family : L → groupCohomology.cocycles₁ (Rep.res SemidirectProduct.inl representation))
    (law : ∀ first second radical, family (first * second) radical =
      representation.ρ (SemidirectProduct.inr first) (family second (action first⁻¹ radical)) +
        family first radical) :
    semidirectMixedTwoValue action representation family ∈ groupCohomology.cocycles₂ representation := by
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro first second third
  simp only [semidirectMixedTwoValue, SemidirectProduct.mul_left, SemidirectProduct.mul_right]
  rw [law]
  have cancel : action first.right⁻¹ (action (first.right * second.right) third.left) =
      action second.right third.left := by simp [map_mul]
  have transport : action first.right (second.left * action second.right third.left) =
      action first.right second.left * action (first.right * second.right) third.left := by simp [map_mul]
  rw [cancel, transport, oneCocycle_mul, semidirectRadicalCoefficient_commute]
  simp only [map_mul, Module.End.mul_apply, map_add, MulAut.mul_apply]
  change _ = _ + (representation.ρ (SemidirectProduct.inl first.left)
    (representation.ρ (SemidirectProduct.inl (action first.right second.left))
      (family first.right (action first.right (action second.right third.left)))) +
    representation.ρ (SemidirectProduct.inl first.left) (family first.right (action first.right second.left)))
  abel

def semidirectMixedTwoCycle (representation : Rep ℂ (N ⋊[action] L))
    (family : L → groupCohomology.cocycles₁ (Rep.res SemidirectProduct.inl representation))
    (law : ∀ first second radical, family (first * second) radical =
      representation.ρ (SemidirectProduct.inr first) (family second (action first⁻¹ radical)) +
        family first radical) : groupCohomology.cocycles₂ representation :=
  ⟨semidirectMixedTwoValue action representation family, semidirectMixedTwoValue_cocycle action representation family law⟩

theorem semidirectMixedFamily_one (representation : Rep ℂ (N ⋊[action] L))
    (family : L → groupCohomology.cocycles₁ (Rep.res SemidirectProduct.inl representation))
    (law : ∀ first second radical, family (first * second) radical =
      representation.ρ (SemidirectProduct.inr first) (family second (action first⁻¹ radical)) +
        family first radical) (radical : N) : family 1 radical = 0 := by
  have equality := law 1 1 radical
  simp only [one_mul, inv_one, map_one, MulAut.one_apply, Module.End.one_apply] at equality
  exact add_left_cancel (equality.symm.trans (add_zero (family 1 radical)).symm)

def semidirectMixedRelativeCycle (representation : Rep ℂ (N ⋊[action] L))
    (family : L → groupCohomology.cocycles₁ (Rep.res SemidirectProduct.inl representation))
    (law : ∀ first second radical, family (first * second) radical =
      representation.ρ (SemidirectProduct.inr first) (family second (action first⁻¹ radical)) +
        family first radical) : relativeTwoCocycles SemidirectProduct.inl representation :=
  ⟨semidirectMixedTwoCycle action representation family law, by
    intro first second
    change representation.ρ (SemidirectProduct.inl first) (family 1 (action 1 second)) = 0
    rw [semidirectMixedFamily_one action representation family law, map_zero]⟩

theorem semidirectMixedRelativeCycle_radical_levi (representation : Rep ℂ (N ⋊[action] L))
    (family : L → groupCohomology.cocycles₁ (Rep.res SemidirectProduct.inl representation))
    (law : ∀ first second radical, family (first * second) radical =
      representation.ρ (SemidirectProduct.inr first) (family second (action first⁻¹ radical)) +
        family first radical) (radical : N) (levi : L) :
    (semidirectMixedRelativeCycle action representation family law).val
      (SemidirectProduct.inl radical, SemidirectProduct.inr levi) = 0 := by
  change representation.ρ (SemidirectProduct.inl radical) (family 1 (action 1 1)) = 0
  rw [semidirectMixedFamily_one action representation family law, map_zero]

theorem semidirectMixedRelativeCycle_levi_levi (representation : Rep ℂ (N ⋊[action] L))
    (family : L → groupCohomology.cocycles₁ (Rep.res SemidirectProduct.inl representation))
    (law : ∀ first second radical, family (first * second) radical =
      representation.ρ (SemidirectProduct.inr first) (family second (action first⁻¹ radical)) +
        family first radical) (first second : L) :
    (semidirectMixedRelativeCycle action representation family law).val
      (SemidirectProduct.inr first, SemidirectProduct.inr second) = 0 := by
  change representation.ρ (SemidirectProduct.inl (1 : N)) (family first (action first 1)) = 0
  simp

theorem semidirectMixedRelativeCycle_levi_radical (representation : Rep ℂ (N ⋊[action] L))
    (family : L → groupCohomology.cocycles₁ (Rep.res SemidirectProduct.inl representation))
    (law : ∀ first second radical, family (first * second) radical =
      representation.ρ (SemidirectProduct.inr first) (family second (action first⁻¹ radical)) +
        family first radical) (levi : L) (radical : N) :
    (semidirectMixedRelativeCycle action representation family law).val
      (SemidirectProduct.inr levi, SemidirectProduct.inl (action levi⁻¹ radical)) = family levi radical := by
  change representation.ρ (SemidirectProduct.inl (1 : N)) (family levi (action levi (action levi⁻¹ radical))) = _
  simp

end TernaryPeriodPolynomials.SphericalDetection.Helpers
