module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.Identity.A_P5

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

variable {g : Poly2}


theorem projector_norm_zero (hg : g.IsSymmetric) :
    TernaryPoly.CharTwoNorm.norm (substitutionProjector g) = 0 := by
  simp only [TernaryPoly.CharTwoNorm.norm, TernaryPoly.CharTwoNorm.sub₁,
    TernaryPoly.CharTwoNorm.sub₂, substitutionProjector, sum_univ_perm3, sum_univ_zmod2,
    map_add, MvPolynomial.bind₁_bind₁]
  linear_combination (norm := (ring_nf; simp [ofNat_mod2'])) hpairA_0 hg + hpairA_1 hg + hpairA_2 hg + hpairA_3 hg + hpairA_4 hg + hpairA_5 hg + hpairA_6 hg + hpairA_7 hg + hpairA_8 hg + hpairA_9 hg + hpairA_10 hg + hpairA_11 hg + hpairA_12 hg + hpairA_13 hg + hpairA_14 hg + hpairA_15 hg + hpairA_16 hg + hpairA_17 hg + hpairA_18 hg + hpairA_19 hg + hpairA_20 hg + hpairA_21 hg + hpairA_22 hg + hpairA_23 hg + hpairA_24 hg + hpairA_25 hg + hpairA_26 hg + hpairA_27 hg + hpairA_28 hg + hpairA_29 hg + hpairA_30 hg + hpairA_31 hg + hpairA_32 hg + hpairA_33 hg + hpairA_34 hg + hpairA_35 hg + hpairA_36 hg + hpairA_37 hg + hpairA_38 hg + hpairA_39 hg + hpairA_40 hg + hpairA_41 hg + hpairA_42 hg + hpairA_43 hg + hpairA_44 hg + hpairA_45 hg + hpairA_46 hg + hpairA_47 hg + hpairA_48 hg + hpairA_49 hg + hpairA_50 hg + hpairA_51 hg + hpairA_52 hg + hpairA_53 hg + hpairA_54 hg + hpairA_55 hg + hpairA_56 hg + hpairA_57 hg + hpairA_58 hg + hpairA_59 hg + hpairA_60 hg + hpairA_61 hg + hpairA_62 hg + hpairA_63 hg + hpairA_64 hg + hpairA_65 hg + hpairA_66 hg + hpairA_67 hg + hpairA_68 hg + hpairA_69 hg + hpairA_70 hg + hpairA_71 hg

end TernaryPeriodPolynomials.Argument.CharTwoKernel
