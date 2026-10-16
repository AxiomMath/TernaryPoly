module

public import TernaryPeriodPolynomials.SymmetricSpace.ChartsOpen

@[expose] public section

open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpaceCharts
open SymmetricSpacePositive

/-- The actual positive trace-one form space is globally homeomorphic to the explicit open
five-coordinate positivity domain. -/
def chartHomeomorph : Space ≃ₜ PositiveCoordinates where
  toFun S := ⟨extract S.val,extract_mem S⟩
  invFun x := ⟨reconstruct x.val,reconstruct_mem x.val x.property⟩
  left_inv S := by
    apply Subtype.ext
    exact reconstruct_extract S.val
      (Matrix.isHermitian_iff_isSymm.mp S.property.1.isHermitian) S.property.2
  right_inv x := by
    apply Subtype.ext
    exact extract_reconstruct x.val
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_extract.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_reconstruct.comp continuous_subtype_val

@[simp] theorem chartHomeomorph_apply (S : Space) :
    (chartHomeomorph S).val=extract S.val := rfl

@[simp] theorem chartHomeomorph_symm_apply (x : PositiveCoordinates) :
    (chartHomeomorph.symm x).val=reconstruct x.val := rfl

theorem positiveCoordinates_nonempty : positiveCoordinates.Nonempty := by
  obtain ⟨S,hS⟩ := traceOnePositive_nonempty
  exact ⟨extract S,extract_mem ⟨S,hS⟩⟩

/-- The affine coordinate model has exactly five real dimensions. -/
theorem finrank_coordinates : Module.finrank ℝ Coordinates=5 := by
  simp [Coordinates]

end TernaryPoly.SymmetricSpaceCharts
