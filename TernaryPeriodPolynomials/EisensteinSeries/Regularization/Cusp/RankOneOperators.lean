module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.DerivedLieAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

attribute [local instance] LieRing.ofAssociativeRing
attribute [local instance] lieRingSelfModule

set_option backward.isDefEq.respectTransparency false

def binaryRotationDirection : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
def binarySplitDirection : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def binarySymmetricDirection : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem binaryRotation_split_bracket :
    ⁅binaryRotationDirection, binarySplitDirection⁆ = -(2 • binarySymmetricDirection) := by
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Ring.lie_def, binaryRotationDirection, binarySplitDirection, binarySymmetricDirection,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem binaryRotation_symmetric_bracket :
    ⁅binaryRotationDirection, binarySymmetricDirection⁆ = 2 • binarySplitDirection := by
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Ring.lie_def, binaryRotationDirection, binarySplitDirection, binarySymmetricDirection,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem binarySplit_symmetric_bracket :
    ⁅binarySplitDirection, binarySymmetricDirection⁆ = 2 • binaryRotationDirection := by
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Ring.lie_def, binaryRotationDirection, binarySplitDirection, binarySymmetricDirection,
      Matrix.mul_apply, Fin.sum_univ_two]

noncomputable def cuspRotationOperator (cusp : CuspidalRepresentation) : Module.End ℂ cusp.smooth :=
  cuspDerivedAction cusp binaryRotationDirection

noncomputable def cuspSplitOperator (cusp : CuspidalRepresentation) : Module.End ℂ cusp.smooth :=
  cuspDerivedAction cusp binarySplitDirection

noncomputable def cuspSymmetricOperator (cusp : CuspidalRepresentation) : Module.End ℂ cusp.smooth :=
  cuspDerivedAction cusp binarySymmetricDirection

theorem cuspRotation_split_bracket (cusp : CuspidalRepresentation) :
    ⁅cuspRotationOperator cusp, cuspSplitOperator cusp⁆ = -(2 • cuspSymmetricOperator cusp) := by
  simpa only [cuspRotationOperator, cuspSplitOperator, cuspSymmetricOperator,
    binaryRotation_split_bracket, map_neg, map_nsmul] using
    (cuspDerivedAction cusp).map_lie binaryRotationDirection binarySplitDirection |>.symm

theorem cuspRotation_symmetric_bracket (cusp : CuspidalRepresentation) :
    ⁅cuspRotationOperator cusp, cuspSymmetricOperator cusp⁆ = 2 • cuspSplitOperator cusp := by
  simpa only [cuspRotationOperator, cuspSplitOperator, cuspSymmetricOperator,
    binaryRotation_symmetric_bracket, map_nsmul] using
    (cuspDerivedAction cusp).map_lie binaryRotationDirection binarySymmetricDirection |>.symm

theorem cuspSplit_symmetric_bracket (cusp : CuspidalRepresentation) :
    ⁅cuspSplitOperator cusp, cuspSymmetricOperator cusp⁆ = 2 • cuspRotationOperator cusp := by
  simpa only [cuspRotationOperator, cuspSplitOperator, cuspSymmetricOperator,
    binarySplit_symmetric_bracket, map_nsmul] using
    (cuspDerivedAction cusp).map_lie binarySplitDirection binarySymmetricDirection |>.symm

noncomputable def cuspRaisingOperator (cusp : CuspidalRepresentation) : Module.End ℂ cusp.smooth :=
  cuspSplitOperator cusp + Complex.I • cuspSymmetricOperator cusp

noncomputable def cuspLoweringOperator (cusp : CuspidalRepresentation) : Module.End ℂ cusp.smooth :=
  cuspSplitOperator cusp - Complex.I • cuspSymmetricOperator cusp

theorem cuspOperator_lie_smul (cusp : CuspidalRepresentation) (scalar : ℂ)
    (first second : Module.End ℂ cusp.smooth) :
    ⁅first, scalar • second⁆ = scalar • ⁅first, second⁆ := by
  simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem cuspOperator_smul_lie (cusp : CuspidalRepresentation) (scalar : ℂ)
    (first second : Module.End ℂ cusp.smooth) :
    ⁅scalar • first, second⁆ = scalar • ⁅first, second⁆ := by
  simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem cuspRotation_raising_bracket (cusp : CuspidalRepresentation) :
    ⁅cuspRotationOperator cusp, cuspRaisingOperator cusp⁆ =
      (2 * Complex.I) • cuspRaisingOperator cusp := by
  rw [cuspRaisingOperator, lie_add, cuspOperator_lie_smul,
    cuspRotation_split_bracket, cuspRotation_symmetric_bracket]
  simp only [smul_add, smul_smul]
  have coefficient : (2 : ℂ) * Complex.I * Complex.I = -2 := by norm_num [mul_assoc]
  rw [coefficient]
  module

theorem cuspRotation_lowering_bracket (cusp : CuspidalRepresentation) :
    ⁅cuspRotationOperator cusp, cuspLoweringOperator cusp⁆ =
      (-2 * Complex.I) • cuspLoweringOperator cusp := by
  rw [cuspLoweringOperator, lie_sub, cuspOperator_lie_smul,
    cuspRotation_split_bracket, cuspRotation_symmetric_bracket]
  simp only [smul_sub, smul_smul]
  have coefficient : (-2 : ℂ) * Complex.I * Complex.I = 2 := by norm_num [mul_assoc]
  rw [coefficient]
  module

theorem cuspRaising_lowering_bracket (cusp : CuspidalRepresentation) :
    ⁅cuspRaisingOperator cusp, cuspLoweringOperator cusp⁆ =
      (-4 * Complex.I) • cuspRotationOperator cusp := by
  rw [cuspRaisingOperator, cuspLoweringOperator]
  simp only [add_lie, lie_sub, cuspOperator_lie_smul, cuspOperator_smul_lie, lie_self, zero_add, add_zero]
  rw [← lie_skew (cuspSymmetricOperator cusp) (cuspSplitOperator cusp), cuspSplit_symmetric_bracket]
  module

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
