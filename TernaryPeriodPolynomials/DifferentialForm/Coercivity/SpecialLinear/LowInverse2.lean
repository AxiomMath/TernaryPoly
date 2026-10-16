module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse2Part1
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse2Part2

@[expose] public section

/-! Exact inverse-row certificates for the actual low-degree Hodge coordinates.
The individual row certificates live in `SL3PolynomialCoercivityLowInverse2Part1`..`SL3PolynomialCoercivityLowInverse2Part2`; this module
re-exports them and keeps the final combined kernel theorem. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

theorem lowHodgeAction2_kernel (x : Fin 10 → Fin 6 → ℝ)
    (hx : lowHodgeAction2 x = 0) : x = 0 := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact lowHodgeAction2_kernel_0 x hx
  · exact lowHodgeAction2_kernel_1 x hx
  · exact lowHodgeAction2_kernel_2 x hx
  · exact lowHodgeAction2_kernel_3 x hx
  · exact lowHodgeAction2_kernel_4 x hx
  · exact lowHodgeAction2_kernel_5 x hx
  · exact lowHodgeAction2_kernel_6 x hx
  · exact lowHodgeAction2_kernel_7 x hx
  · exact lowHodgeAction2_kernel_8 x hx
  · exact lowHodgeAction2_kernel_9 x hx
  · exact lowHodgeAction2_kernel_10 x hx
  · exact lowHodgeAction2_kernel_11 x hx
  · exact lowHodgeAction2_kernel_12 x hx
  · exact lowHodgeAction2_kernel_13 x hx
  · exact lowHodgeAction2_kernel_14 x hx
  · exact lowHodgeAction2_kernel_15 x hx
  · exact lowHodgeAction2_kernel_16 x hx
  · exact lowHodgeAction2_kernel_17 x hx
  · exact lowHodgeAction2_kernel_18 x hx
  · exact lowHodgeAction2_kernel_19 x hx
  · exact lowHodgeAction2_kernel_20 x hx
  · exact lowHodgeAction2_kernel_21 x hx
  · exact lowHodgeAction2_kernel_22 x hx
  · exact lowHodgeAction2_kernel_23 x hx
  · exact lowHodgeAction2_kernel_24 x hx
  · exact lowHodgeAction2_kernel_25 x hx
  · exact lowHodgeAction2_kernel_26 x hx
  · exact lowHodgeAction2_kernel_27 x hx
  · exact lowHodgeAction2_kernel_28 x hx
  · exact lowHodgeAction2_kernel_29 x hx
  · exact lowHodgeAction2_kernel_30 x hx
  · exact lowHodgeAction2_kernel_31 x hx
  · exact lowHodgeAction2_kernel_32 x hx
  · exact lowHodgeAction2_kernel_33 x hx
  · exact lowHodgeAction2_kernel_34 x hx
  · exact lowHodgeAction2_kernel_35 x hx
  · exact lowHodgeAction2_kernel_36 x hx
  · exact lowHodgeAction2_kernel_37 x hx
  · exact lowHodgeAction2_kernel_38 x hx
  · exact lowHodgeAction2_kernel_39 x hx
  · exact lowHodgeAction2_kernel_40 x hx
  · exact lowHodgeAction2_kernel_41 x hx
  · exact lowHodgeAction2_kernel_42 x hx
  · exact lowHodgeAction2_kernel_43 x hx
  · exact lowHodgeAction2_kernel_44 x hx
  · exact lowHodgeAction2_kernel_45 x hx
  · exact lowHodgeAction2_kernel_46 x hx
  · exact lowHodgeAction2_kernel_47 x hx
  · exact lowHodgeAction2_kernel_48 x hx
  · exact lowHodgeAction2_kernel_49 x hx
  · exact lowHodgeAction2_kernel_50 x hx
  · exact lowHodgeAction2_kernel_51 x hx
  · exact lowHodgeAction2_kernel_52 x hx
  · exact lowHodgeAction2_kernel_53 x hx
  · exact lowHodgeAction2_kernel_54 x hx
  · exact lowHodgeAction2_kernel_55 x hx
  · exact lowHodgeAction2_kernel_56 x hx
  · exact lowHodgeAction2_kernel_57 x hx
  · exact lowHodgeAction2_kernel_58 x hx
  · exact lowHodgeAction2_kernel_59 x hx

end TernaryPoly.SL3PolynomialCoercivity
