module

public import TernaryPeriodPolynomials.SymmetricSpace.Line.BordificationGroup

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceLineBordification
open Matrix
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates
open SymmetricSpacePlaneBordification

@[simp] theorem lineParameters_A (g : LineGroup) :
    (lineParametersEquiv.symm g).A.val=topBlock (dualGL g.val) := by
  have h := congrArg (fun a : RealGL => topBlock a) (lineParametersEquiv_symm_matrix g)
  calc
    _=topBlock (toRealGL (lineParametersEquiv.symm g)) := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    _=_ := h

@[simp] theorem lineParameters_u (g : LineGroup) :
    (lineParametersEquiv.symm g).u=topVector (dualGL g.val) := by
  have h := congrArg (fun a : RealGL => topVector a) (lineParametersEquiv_symm_matrix g)
  calc
    _=topVector (toRealGL (lineParametersEquiv.symm g)) := by
      ext i; fin_cases i <;> rfl
    _=_ := h

@[simp] theorem lineParameters_d (g : LineGroup) :
    (lineParametersEquiv.symm g).d.val=(dualGL g.val).val 2 2 :=
  congrArg (fun a : RealGL => a.val 2 2) (lineParametersEquiv_symm_matrix g)

theorem continuous_topBlock : Continuous topBlock := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [topBlock]
  all_goals exact Units.continuous_val.matrix_elem _ _

theorem continuous_topVector : Continuous topVector := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [topVector]
  all_goals exact Units.continuous_val.matrix_elem _ _

theorem continuous_plane_matrix : Continuous (fun p : Parameters => (toRealGL p).val) := by
  have hA : Continuous (fun p : Parameters => p.A.val) := Units.continuous_val.comp continuous_A
  have hu : Continuous (fun p : Parameters => p.u) := continuous_u
  have hd : Continuous (fun p : Parameters => p.d.val) := Units.continuous_val.comp continuous_d
  change Continuous (fun p : Parameters => blockMatrix p.A.val p.u p.d.val)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact hA.matrix_elem 0 0
  · exact hA.matrix_elem 0 1
  · exact (continuous_apply 0).comp hu
  · exact hA.matrix_elem 1 0
  · exact hA.matrix_elem 1 1
  · exact (continuous_apply 1).comp hu
  · exact continuous_const
  · exact continuous_const
  · exact hd

theorem continuous_toRealGL : Continuous toRealGL := by
  apply Units.continuous_iff.mpr
  refine ⟨continuous_plane_matrix,?_⟩
  have h : Continuous (fun p : Parameters => (toRealGL p⁻¹).val) :=
    continuous_plane_matrix.comp continuous_inv
  simpa only [toRealGL_inv] using h

theorem continuous_lineParameters : Continuous lineParametersEquiv.symm := by
  have hg : Continuous (fun g : LineGroup => dualGL g.val) :=
    continuous_dualGL.comp continuous_subtype_val
  have ha : Continuous (fun g : LineGroup => (lineParametersEquiv.symm g).A.val) := by
    have h : Continuous (fun g : LineGroup => topBlock (dualGL g.val)) := continuous_topBlock.comp hg
    simpa only [lineParameters_A] using h
  have hai : Continuous (fun g : LineGroup => ((lineParametersEquiv.symm g).A⁻¹).val) := by
    have h : Continuous (fun g : LineGroup => (lineParametersEquiv.symm g⁻¹).A.val) := ha.comp continuous_inv
    have he (p : Parameters) : (p⁻¹).A=p.A⁻¹ := rfl
    simpa only [map_inv,he] using h
  have hu : Continuous (fun g : LineGroup => (lineParametersEquiv.symm g).u) := by
    have h : Continuous (fun g : LineGroup => topVector (dualGL g.val)) := continuous_topVector.comp hg
    simpa only [lineParameters_u] using h
  have hd : Continuous (fun g : LineGroup => (lineParametersEquiv.symm g).d.val) := by
    have h : Continuous (fun g : LineGroup => (dualGL g.val).val 2 2) :=
      (Units.continuous_val.comp hg).matrix_elem 2 2
    simpa only [lineParameters_d] using h
  change Continuous (fun g : LineGroup =>
    (⟨(lineParametersEquiv.symm g).A,(lineParametersEquiv.symm g).u,
      (lineParametersEquiv.symm g).d⟩ : Parameters))
  apply continuous_parameters_mk (Units.continuous_iff.mpr ⟨ha,hai⟩) hu
  apply Units.continuous_iff.mpr
  refine ⟨hd,?_⟩
  have h : Continuous (fun g : LineGroup => ((lineParametersEquiv.symm g).d.val)⁻¹) :=
    hd.inv₀ (fun g => (lineParametersEquiv.symm g).d.ne_zero)
  simpa using h

/-- The signed parameter topology agrees with the actual line subgroup's inherited real topology. -/
def lineParametersHomeomorph : Parameters ≃ₜ LineGroup where
  toEquiv := lineParametersEquiv.toEquiv
  continuous_toFun := (continuous_dualGL.comp continuous_toRealGL).subtype_mk _
  continuous_invFun := continuous_lineParameters

end TernaryPoly.SymmetricSpaceLineBordification
