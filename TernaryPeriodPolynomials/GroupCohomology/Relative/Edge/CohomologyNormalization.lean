module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyCocycles

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeEdgeCohomologyCocycles
open CategoryTheory CategoryTheory.Limits groupCohomology
variable {G : Type} [Group G] (A : Rep.{0} ℚ G)

lemma normalize_preserves_zero_or_inverse (f : cocycles₁ A) (s g : G)
    (hs : s*s=1) (hg : f g=0) (hc : s*g=g*s ∨ s*g=g⁻¹*s) :
    normalize A f s g = 0 := by
  apply normalize_preserves_zero A f s g hg
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_right hs
  rw [hsi]
  rcases hc with hc | hc
  · rw [hc, mul_assoc, hs, mul_one]; exact hg
  · rw [hc, mul_assoc, hs, mul_one]; exact (zeroSubgroup A f).inv_mem hg

/-- Sign normalization preserves every specified root zero up to root inversion. -/
lemma normalize_two_preserving (f : cocycles₁ A) (s t : G)
    (hs : s*s=1) (ht : t*t=1) (hst : s*t=t*s) (S : Set G)
    (hS : ∀ g ∈ S, f g=0)
    (hsc : ∀ g ∈ S, s*g=g*s ∨ s*g=g⁻¹*s)
    (htc : ∀ g ∈ S, t*g=g*t ∨ t*g=g⁻¹*t) :
    ∃ f' : cocycles₁ A, f' s=0 ∧ f' t=0 ∧
      (∀ g ∈ S, f' g=0) ∧ H1π A f'=H1π A f := by
  let f' := normalize A (normalize A f s) t
  refine ⟨f', ?_, normalize_sign A _ t ht, ?_, ?_⟩
  · exact normalize_preserves_zero_or_inverse A _ t s ht
      (normalize_sign A f s hs) (Or.inl hst.symm)
  · intro g hg
    exact normalize_preserves_zero_or_inverse A _ t g ht
      (normalize_preserves_zero_or_inverse A f s g hs (hS g hg) (hsc g hg)) (htc g hg)
  · change H1π A (normalize A (normalize A f s) t)=_
    rw [H1_normalize, H1_normalize]

lemma inverted_quotient {V : Type} [AddCommGroup V] [Module ℚ V]
    (L : A →ₗ[ℚ] V) (f : cocycles₁ A) (s g : G) (hs : f s=0)
    (hc : s*g*s⁻¹=g⁻¹) (hL : ∀ v, L (A.ρ g v)=L v) :
    L (A.ρ s (f g)) = -L (f g) := by
  have h := cocycles₁_map_inv f g
  have h' := congrArg L h
  rw [hL, map_neg] at h'
  rw [← hc, conjugation_value A f s g hs] at h'
  exact h'

lemma zero_of_neg_eq_self {V : Type} [AddCommGroup V] [Module ℚ V]
    (v : V) (h : v = -v) : v=0 := by
  have h2 : (2 : ℚ) • v = 0 := by
    rw [two_smul]
    exact (add_eq_zero_iff_eq_neg).mpr h
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

lemma isZero_H1_of_classes (h : ∀ f : cocycles₁ A, H1π A f=0) :
    IsZero (groupCohomology A 1) := by
  apply (ModuleCat.isZero_of_iff_subsingleton).mpr
  have hz (x : H1 A) : x=0 := by
    induction x using H1_induction_on with | h f => exact h f
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end TernaryPoly.RelativeEdgeCohomologyCocycles
