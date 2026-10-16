module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.Identity.B_P3

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

variable {g : Poly2}


theorem projector_eq_g_add_theta_norm (hg : g.IsSymmetric) :
    substitutionProjector g = g + thetaOperator (TernaryPoly.CharTwoNorm.norm g) := by
  simp only [TernaryPoly.CharTwoNorm.norm, TernaryPoly.CharTwoNorm.sub₁,
    TernaryPoly.CharTwoNorm.sub₂, substitutionProjector, thetaOperator, thetaSubstitutions,
    sum_univ_perm3, sum_univ_zmod2, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, map_add, MvPolynomial.bind₁_bind₁]
  linear_combination (norm := (ring_nf; simp [ofNat_mod2'])) hpairB_0 hg + hpairB_1 hg + hpairB_2 hg + hpairB_3 hg + hpairB_4 hg + hpairB_5 hg + hpairB_6 hg + hpairB_7 hg + hpairB_8 hg + hpairB_9 hg + hpairB_10 hg + hpairB_11 hg + hpairB_12 hg + hpairB_13 hg + hpairB_14 hg + hpairB_15 hg + hpairB_16 hg + hpairB_17 hg + hpairB_18 hg + hpairB_19 hg + hpairB_20 hg + hpairB_21 hg + hpairB_22 hg + hpairB_23 hg + hpairB_24 hg + hpairB_25 hg + hpairB_26 hg + hpairB_27 hg + hpairB_28 hg + hpairB_29 hg + hpairB_30 hg + hpairB_31 hg + hpairB_32 hg + hpairB_33 hg + hpairB_34 hg + hpairB_35 hg + hpairB_36 hg + hpairB_37 hg + hpairB_38 hg + hpairB_39 hg + hpairB_40 hg + hpairB_41 hg + hpairB_42 hg + hpairB_43 hg + hpairB_44 hg + hpairB_45 hg + hpairB_46 hg

end TernaryPeriodPolynomials.Argument.CharTwoKernel
