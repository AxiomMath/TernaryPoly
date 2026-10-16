module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.LatticeShapeBounds
public import Mathlib.Algebra.Module.ZLattice.Covolume

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def realRowAction (matrix : RealGL3) : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toLinearMap := matrix.val.vecMulLinear
  invFun row := row ᵥ* matrix.inv
  left_inv row := by
    change (row ᵥ* matrix.val) ᵥ* matrix.inv = row
    rw [vecMul_vecMul, matrix.val_inv, vecMul_one]
  right_inv row := by
    change (row ᵥ* matrix.inv) ᵥ* matrix.val = row
    rw [vecMul_vecMul, matrix.inv_val, vecMul_one]

noncomputable def realRowBasis (matrix : RealGL3) : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) :=
  (Pi.basisFun ℝ (Fin 3)).map (realRowAction matrix)

theorem realRowBasis_apply (matrix : RealGL3) (index : Fin 3) : realRowBasis matrix index = matrix.val index := by
  ext column
  simp [realRowBasis, realRowAction, Matrix.vecMul, dotProduct, Pi.single_apply]

noncomputable def transformedRowLattice (matrix : RealGL3) : Submodule ℤ (Fin 3 → ℝ) :=
  Submodule.span ℤ (Set.range (realRowBasis matrix))

instance transformedRowLattice_discrete (matrix : RealGL3) : DiscreteTopology (transformedRowLattice matrix) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (realRowBasis matrix))))

instance transformedRowLattice_isZLattice (matrix : RealGL3) : IsZLattice ℝ (transformedRowLattice matrix) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (realRowBasis matrix))))

noncomputable def transformedRowLatticeBasis (matrix : RealGL3) :
    Module.Basis (Fin 3) ℤ (transformedRowLattice matrix) := (realRowBasis matrix).restrictScalars ℤ

theorem transformedRowLattice_covolume (matrix : RealGL3) :
    ZLattice.covolume (transformedRowLattice matrix) volume = |matrix.val.det| := by
  rw [ZLattice.covolume_eq_det (transformedRowLattice matrix) (transformedRowLatticeBasis matrix)]
  congr 2
  ext index column
  exact congrFun ((Module.Basis.restrictScalars_apply ℤ (realRowBasis matrix) index).trans
    (realRowBasis_apply matrix index)) column

noncomputable def transformedRowEquiv (matrix : RealGL3) : (Fin 3 → ℤ) ≃ₗ[ℤ] transformedRowLattice matrix :=
  (transformedRowLatticeBasis matrix).equivFun.symm

theorem transformedRowEquiv_val (matrix : RealGL3) (row : Fin 3 → ℤ) :
    (transformedRowEquiv matrix row).val = (fun index => (row index : ℝ)) ᵥ* matrix.val := by
  rw [transformedRowEquiv, Module.Basis.equivFun_symm_apply]
  have basis_value (index : Fin 3) : (transformedRowLatticeBasis matrix index).val = matrix.val index :=
    (Module.Basis.restrictScalars_apply ℤ (realRowBasis matrix) index).trans (realRowBasis_apply matrix index)
  simp only [Submodule.coe_sum, Submodule.coe_smul, basis_value]
  ext column
  simp only [Finset.sum_apply, zsmul_eq_mul]
  rfl

theorem transformedRowLattice_finite_ball (matrix : RealGL3) (radius : ℝ) :
    {vector : transformedRowLattice matrix | ‖vector‖ < radius}.Finite := by
  let : DiscreteTopology (transformedRowLattice matrix).toAddSubgroup := transformedRowLattice_discrete matrix
  have closed : IsClosed (transformedRowLattice matrix : Set (Fin 3 → ℝ)) :=
    AddSubgroup.isClosed_of_discreteTopology (U := (transformedRowLattice matrix).toAddSubgroup)
  let : ProperSpace (transformedRowLattice matrix) := ProperSpace.of_isClosed closed
  exact ((isCompact_closedBall (0 : transformedRowLattice matrix) radius).finite_of_discrete).subset
    (by intro vector member; simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_lt member)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
