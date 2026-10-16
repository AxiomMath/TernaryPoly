module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalBruhat

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def planeFlagMatrix : Option (Option ℚ × ℚ) → RationalGL3
  | none => 1
  | some (none, offset) => planeUnipotent offset 0 * swapFirstTwo * swapLastTwo
  | some (some slope, offset) => planeUnipotent 0 offset * planeLowerShear slope * swapLastTwo

def planeFlag (index : Option (Option ℚ × ℚ)) : Flags .plane :=
  QuotientGroup.mk (planeFlagMatrix index)

theorem planeFlag_injective : Function.Injective planeFlag := by
  intro first second equal
  have relation : InPlaneParabolic ((planeFlagMatrix first)⁻¹ * planeFlagMatrix second) :=
    QuotientGroup.eq.mp equal
  rcases first with _ | ⟨_ | firstSlope, firstOffset⟩ <;>
    rcases second with _ | ⟨_ | secondSlope, secondOffset⟩ <;>
    simp [planeFlagMatrix, InPlaneParabolic, _root_.mul_inv_rev, planeUnipotent,
      planeLowerShear, swapFirstTwo, swapLastTwo, Matrix.mul_apply, Fin.sum_univ_three] at relation
  all_goals simp_all
  · linarith
  · constructor <;> linarith [relation.1, relation.2]

theorem planeFlag_surjective : Function.Surjective planeFlag := by
  intro flag
  have same_flag (index : Option (Option ℚ × ℚ))
      (parabolic : InPlaneParabolic (flag.out⁻¹ * planeFlagMatrix index)) :
      planeFlag index = flag := by
    have same_coset : (QuotientGroup.mk flag.out : Flags .plane) = planeFlag index :=
      QuotientGroup.eq.mpr parabolic
    exact same_coset.symm.trans (QuotientGroup.out_eq' flag)
  by_cases second_zero : flag.out.val⁻¹ 2 1 = 0
  · by_cases first_zero : flag.out.val⁻¹ 2 0 = 0
    · refine ⟨none, same_flag none ?_⟩
      simpa only [planeFlagMatrix, mul_one, InPlaneParabolic, GeneralLinearGroup.coe_inv]
        using And.intro first_zero second_zero
    · refine ⟨some (none, -(flag.out.val⁻¹ 2 2 / flag.out.val⁻¹ 2 0)), same_flag _ ?_⟩
      constructor <;>
        simp [planeFlagMatrix, planeUnipotent, swapFirstTwo, swapLastTwo,
          Matrix.mul_apply, Fin.sum_univ_three, second_zero]
      all_goals field_simp
      all_goals ring
  · refine ⟨some (some (-(flag.out.val⁻¹ 2 0 / flag.out.val⁻¹ 2 1)),
      -(flag.out.val⁻¹ 2 2 / flag.out.val⁻¹ 2 1)), same_flag _ ?_⟩
    constructor <;>
      simp [planeFlagMatrix, planeUnipotent, planeLowerShear, swapLastTwo,
        Matrix.mul_apply, Fin.sum_univ_three]
    all_goals field_simp
    all_goals ring

noncomputable def planeFlagEquiv : Option (Option ℚ × ℚ) ≃ Flags .plane :=
  Equiv.ofBijective planeFlag ⟨planeFlag_injective, planeFlag_surjective⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
