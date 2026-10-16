module

public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesPositive

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpaceParabolicCoordinates
open SymmetricSpacePositive

theorem continuous_unipotent : Continuous (fun S : Space => unipotent S.val) := by
  apply continuous_pi
  intro i
  exact (continuous_subtype_val.matrix_elem (topIndex i) 2).div₀
    (continuous_subtype_val.matrix_elem 2 2) (fun S => ne_of_gt (height_pos S.val S.property.1))

theorem continuous_schur : Continuous (fun S : Space => schur S.val) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_subtype_val.matrix_elem (topIndex i) (topIndex j)).div₀
    (continuous_subtype_val.matrix_elem 2 2) (fun S => ne_of_gt (height_pos S.val S.property.1))).sub
    (((continuous_apply i).comp continuous_unipotent).mul
      ((continuous_apply j).comp continuous_unipotent))

/-- The actual inverse matrix is a polynomial in the unipotent and binary-form coordinates. -/
theorem continuous_assemble : Continuous (fun p : Vec2 × Mat2 => assemble p.1 p.2) := by
  have hv (i : Fin 2) : Continuous (fun p : Vec2 × Mat2 => p.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hB (i j : Fin 2) : Continuous (fun p : Vec2 × Mat2 => p.2 i j) :=
    continuous_snd.matrix_elem i j
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact (hB 0 0).add ((hv 0).mul (hv 0))
  · exact (hB 0 1).add ((hv 0).mul (hv 1))
  · exact hv 0
  · exact (hB 1 0).add ((hv 1).mul (hv 0))
  · exact (hB 1 1).add ((hv 1).mul (hv 1))
  · exact hv 1
  · exact hv 0
  · exact hv 1
  · exact continuous_const

theorem continuous_normalize_assemble :
    Continuous (fun p : Vec2 × PosDef2 => normalize (assemble p.1 p.2.val)) := by
  have hc : Continuous (fun p : Vec2 × PosDef2 => assemble p.1 p.2.val) :=
    continuous_assemble.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact (hc.matrix_trace.inv₀ (fun p =>
    ne_of_gt (assemble_positive p.1 p.2.val p.2.property).trace_pos)).smul hc

/-- Genuine plane-parabolic horospherical coordinates on the trace-one positive form space. -/
def horosphericalHomeomorph : Space ≃ₜ (Vec2 × PosDef2) where
  toFun S := (unipotent S.val,⟨schur S.val,schur_positive S.val S.property.1⟩)
  invFun p := ⟨normalize (assemble p.1 p.2.val),
    normalize_mem _ (assemble_positive p.1 p.2.val p.2.property)⟩
  left_inv S := by
    apply Subtype.ext
    exact normalize_assemble_coordinates S
  right_inv p := by
    apply Prod.ext
    · exact unipotent_normalize_assemble p.1 p.2.val p.2.property
    · apply Subtype.ext
      exact schur_normalize_assemble p.1 p.2.val p.2.property
  continuous_toFun := by
    exact continuous_unipotent.prodMk (Continuous.subtype_mk continuous_schur _)
  continuous_invFun := by
    exact Continuous.subtype_mk continuous_normalize_assemble _

@[simp] theorem horosphericalHomeomorph_fst (S : Space) :
    (horosphericalHomeomorph S).1=unipotent S.val := rfl

@[simp] theorem horosphericalHomeomorph_snd (S : Space) :
    (horosphericalHomeomorph S).2.val=schur S.val := rfl

@[simp] theorem horosphericalHomeomorph_symm (p : Vec2 × PosDef2) :
    (horosphericalHomeomorph.symm p).val=normalize (assemble p.1 p.2.val) := rfl

end TernaryPoly.SymmetricSpaceParabolicCoordinates
