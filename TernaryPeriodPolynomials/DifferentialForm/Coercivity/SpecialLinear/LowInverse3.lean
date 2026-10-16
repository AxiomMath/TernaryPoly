module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse3Part1
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse3Part2
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse3Part3
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse3Part4
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse3Part5
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowInverse3Part6

@[expose] public section

/-! Exact inverse-row certificates for the actual low-degree Hodge coordinates.
The individual row certificates live in `SL3PolynomialCoercivityLowInverse3Part1`..`SL3PolynomialCoercivityLowInverse3Part6`; this module
re-exports them and keeps the final combined kernel theorem. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

theorem lowHodgeAction3_kernel (x : Fin 10 → Fin 10 → ℝ)
    (hx : lowHodgeAction3 x = 0) : x = 0 := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact lowHodgeAction3_kernel_0 x hx
  · exact lowHodgeAction3_kernel_1 x hx
  · exact lowHodgeAction3_kernel_2 x hx
  · exact lowHodgeAction3_kernel_3 x hx
  · exact lowHodgeAction3_kernel_4 x hx
  · exact lowHodgeAction3_kernel_5 x hx
  · exact lowHodgeAction3_kernel_6 x hx
  · exact lowHodgeAction3_kernel_7 x hx
  · exact lowHodgeAction3_kernel_8 x hx
  · exact lowHodgeAction3_kernel_9 x hx
  · exact lowHodgeAction3_kernel_10 x hx
  · exact lowHodgeAction3_kernel_11 x hx
  · exact lowHodgeAction3_kernel_12 x hx
  · exact lowHodgeAction3_kernel_13 x hx
  · exact lowHodgeAction3_kernel_14 x hx
  · exact lowHodgeAction3_kernel_15 x hx
  · exact lowHodgeAction3_kernel_16 x hx
  · exact lowHodgeAction3_kernel_17 x hx
  · exact lowHodgeAction3_kernel_18 x hx
  · exact lowHodgeAction3_kernel_19 x hx
  · exact lowHodgeAction3_kernel_20 x hx
  · exact lowHodgeAction3_kernel_21 x hx
  · exact lowHodgeAction3_kernel_22 x hx
  · exact lowHodgeAction3_kernel_23 x hx
  · exact lowHodgeAction3_kernel_24 x hx
  · exact lowHodgeAction3_kernel_25 x hx
  · exact lowHodgeAction3_kernel_26 x hx
  · exact lowHodgeAction3_kernel_27 x hx
  · exact lowHodgeAction3_kernel_28 x hx
  · exact lowHodgeAction3_kernel_29 x hx
  · exact lowHodgeAction3_kernel_30 x hx
  · exact lowHodgeAction3_kernel_31 x hx
  · exact lowHodgeAction3_kernel_32 x hx
  · exact lowHodgeAction3_kernel_33 x hx
  · exact lowHodgeAction3_kernel_34 x hx
  · exact lowHodgeAction3_kernel_35 x hx
  · exact lowHodgeAction3_kernel_36 x hx
  · exact lowHodgeAction3_kernel_37 x hx
  · exact lowHodgeAction3_kernel_38 x hx
  · exact lowHodgeAction3_kernel_39 x hx
  · exact lowHodgeAction3_kernel_40 x hx
  · exact lowHodgeAction3_kernel_41 x hx
  · exact lowHodgeAction3_kernel_42 x hx
  · exact lowHodgeAction3_kernel_43 x hx
  · exact lowHodgeAction3_kernel_44 x hx
  · exact lowHodgeAction3_kernel_45 x hx
  · exact lowHodgeAction3_kernel_46 x hx
  · exact lowHodgeAction3_kernel_47 x hx
  · exact lowHodgeAction3_kernel_48 x hx
  · exact lowHodgeAction3_kernel_49 x hx
  · exact lowHodgeAction3_kernel_50 x hx
  · exact lowHodgeAction3_kernel_51 x hx
  · exact lowHodgeAction3_kernel_52 x hx
  · exact lowHodgeAction3_kernel_53 x hx
  · exact lowHodgeAction3_kernel_54 x hx
  · exact lowHodgeAction3_kernel_55 x hx
  · exact lowHodgeAction3_kernel_56 x hx
  · exact lowHodgeAction3_kernel_57 x hx
  · exact lowHodgeAction3_kernel_58 x hx
  · exact lowHodgeAction3_kernel_59 x hx
  · exact lowHodgeAction3_kernel_60 x hx
  · exact lowHodgeAction3_kernel_61 x hx
  · exact lowHodgeAction3_kernel_62 x hx
  · exact lowHodgeAction3_kernel_63 x hx
  · exact lowHodgeAction3_kernel_64 x hx
  · exact lowHodgeAction3_kernel_65 x hx
  · exact lowHodgeAction3_kernel_66 x hx
  · exact lowHodgeAction3_kernel_67 x hx
  · exact lowHodgeAction3_kernel_68 x hx
  · exact lowHodgeAction3_kernel_69 x hx
  · exact lowHodgeAction3_kernel_70 x hx
  · exact lowHodgeAction3_kernel_71 x hx
  · exact lowHodgeAction3_kernel_72 x hx
  · exact lowHodgeAction3_kernel_73 x hx
  · exact lowHodgeAction3_kernel_74 x hx
  · exact lowHodgeAction3_kernel_75 x hx
  · exact lowHodgeAction3_kernel_76 x hx
  · exact lowHodgeAction3_kernel_77 x hx
  · exact lowHodgeAction3_kernel_78 x hx
  · exact lowHodgeAction3_kernel_79 x hx
  · exact lowHodgeAction3_kernel_80 x hx
  · exact lowHodgeAction3_kernel_81 x hx
  · exact lowHodgeAction3_kernel_82 x hx
  · exact lowHodgeAction3_kernel_83 x hx
  · exact lowHodgeAction3_kernel_84 x hx
  · exact lowHodgeAction3_kernel_85 x hx
  · exact lowHodgeAction3_kernel_86 x hx
  · exact lowHodgeAction3_kernel_87 x hx
  · exact lowHodgeAction3_kernel_88 x hx
  · exact lowHodgeAction3_kernel_89 x hx
  · exact lowHodgeAction3_kernel_90 x hx
  · exact lowHodgeAction3_kernel_91 x hx
  · exact lowHodgeAction3_kernel_92 x hx
  · exact lowHodgeAction3_kernel_93 x hx
  · exact lowHodgeAction3_kernel_94 x hx
  · exact lowHodgeAction3_kernel_95 x hx
  · exact lowHodgeAction3_kernel_96 x hx
  · exact lowHodgeAction3_kernel_97 x hx
  · exact lowHodgeAction3_kernel_98 x hx
  · exact lowHodgeAction3_kernel_99 x hx

end TernaryPoly.SL3PolynomialCoercivity
