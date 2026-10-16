module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.FlagCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def associateFlagMatrix : Option ℚ ⊕ (ℚ × ℚ) → RationalGL3
  | .inl none => 1
  | .inl (some offset) => planeUnipotent 0 offset * swapLastTwo
  | .inr (first, second) => lineUnipotent first second * weyl

def associateFlag (index : Option ℚ ⊕ (ℚ × ℚ)) : Flags .plane :=
  QuotientGroup.mk (associateFlagMatrix index)

theorem associateFlag_injective : Function.Injective associateFlag := by
  intro first second equal
  have relation : InPlaneParabolic ((associateFlagMatrix first)⁻¹ * associateFlagMatrix second) :=
    QuotientGroup.eq.mp equal
  rcases first with (_ | firstOffset) | ⟨firstOne, firstTwo⟩ <;>
    rcases second with (_ | secondOffset) | ⟨secondOne, secondTwo⟩ <;>
    simp [associateFlagMatrix, InPlaneParabolic, _root_.mul_inv_rev, planeUnipotent,
      lineUnipotent, upperUnipotent, weyl, swapLastTwo, Matrix.mul_apply, Fin.sum_univ_three] at relation
  all_goals simp_all
  · linarith
  · constructor <;> linarith [relation.1, relation.2]

theorem associateFlag_surjective : Function.Surjective associateFlag := by
  intro flag
  have same_flag (index : Option ℚ ⊕ (ℚ × ℚ))
      (parabolic : InPlaneParabolic (flag.out⁻¹ * associateFlagMatrix index)) :
      associateFlag index = flag := by
    have same_coset : (QuotientGroup.mk flag.out : Flags .plane) = associateFlag index :=
      QuotientGroup.eq.mpr parabolic
    exact same_coset.symm.trans (QuotientGroup.out_eq' flag)
  by_cases first_zero : flag.out.val⁻¹ 2 0 = 0
  · by_cases second_zero : flag.out.val⁻¹ 2 1 = 0
    · refine ⟨.inl none, same_flag (.inl none) ?_⟩
      simpa only [associateFlagMatrix, mul_one, InPlaneParabolic, GeneralLinearGroup.coe_inv]
        using And.intro first_zero second_zero
    · refine ⟨.inl (some (-(flag.out.val⁻¹ 2 2 / flag.out.val⁻¹ 2 1))), same_flag _ ?_⟩
      constructor <;>
        simp [associateFlagMatrix, planeUnipotent, swapLastTwo,
          Matrix.mul_apply, Fin.sum_univ_three, first_zero]
      all_goals field_simp
      all_goals ring
  · refine ⟨.inr (-(flag.out.val⁻¹ 2 1 / flag.out.val⁻¹ 2 0),
      -(flag.out.val⁻¹ 2 2 / flag.out.val⁻¹ 2 0)), same_flag _ ?_⟩
    constructor <;>
      simp [associateFlagMatrix, lineUnipotent, upperUnipotent, weyl,
        Matrix.mul_apply, Fin.sum_univ_three]
    all_goals field_simp
    all_goals ring

noncomputable def associateFlagEquiv : Option ℚ ⊕ (ℚ × ℚ) ≃ Flags .plane :=
  Equiv.ofBijective associateFlag ⟨associateFlag_injective, associateFlag_surjective⟩

theorem associateFlag_tsum (function : Flags .plane → ℂ) (summable : Summable function) :
    (∑' flag, function flag) =
      (∑' index : Option ℚ, function (associateFlag (.inl index))) +
        ∑' index : ℚ × ℚ, function (associateFlag (.inr index)) := by
  have indexed_summable : Summable (fun index => function (associateFlag index)) :=
    associateFlagEquiv.summable_iff.mpr summable
  rw [← associateFlagEquiv.tsum_eq function]
  exact (indexed_summable.comp_injective Sum.inl_injective).tsum_sum
    (indexed_summable.comp_injective Sum.inr_injective)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
