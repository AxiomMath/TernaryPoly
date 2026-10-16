module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallFlagCoefficients

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal.InvariantSetCover
open CategoryTheory

variable {G S ι F : Type} [Group G] [MulAction G S] [AddCommGroup F] [Module ℝ F]
  (U : InvariantSetCover G S ι) (ρ : Representation ℝ G F)

/-- The genuine augmented flag differential evaluates at the actual underlying empty flag. -/
theorem flagD_zero_value (w : U.flagCochains ρ 0) (x : U.Flag 1) :
    (U.flagD ρ 0 w).val x = w.val (U.zeroFlag x.point) := by
  rw [U.flagD_apply,Fin.sum_univ_one]
  simp only [Fin.val_zero,pow_zero,one_smul]
  exact congrArg w.val (U.zeroFlag_point (U.select (0 : Fin 1).succAbove x)).symm

/-- The true degree-zero augmented flag differential is a horizontally closed cochain. -/
theorem flagD_one_zero (w : U.flagCochains ρ 0) : U.flagD ρ 1 (U.flagD ρ 0 w) = 0 := by
  apply Subtype.ext
  funext x
  rw [U.flagD_apply,Fin.sum_univ_two,U.flagD_zero_value,U.flagD_zero_value]
  change (1 : ℤ) • w.val (U.zeroFlag x.point) + (-1 : ℤ) • w.val (U.zeroFlag x.point) = 0
  simp only [one_smul,neg_smul,add_neg_cancel]

end TernaryPoly.SmoothSingularGlobal.InvariantSetCover
