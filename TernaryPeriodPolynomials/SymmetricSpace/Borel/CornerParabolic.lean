module

public import TernaryPeriodPolynomials.SymmetricSpace.Borel.CornerInclusions
public import TernaryPeriodPolynomials.SymmetricSpace.Plane.BordificationContinuousAction

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBorelCorner
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates
open SymmetricSpacePlaneBordification SymmetricSpaceLineBordification

/-- The full actual plane group maps to the full actual line group through the duality. -/
def planeToDualLine : PlaneGroup →* LineGroup where
  toFun g := ⟨dualGL g.val,by
    apply (dualGL_plane_iff_line (dualGL g.val)).mp
    simpa only [dualGL_involutive] using (mem_planeStabilizer_iff g.val).mp g.property⟩
  map_one' := by apply Subtype.ext; exact dualGLEquiv.map_one
  map_mul' g h := by apply Subtype.ext; exact dualGL_mul g.val h.val

def planeParametersHom : PlaneGroup →* Parameters :=
  lineParametersEquiv.symm.toMonoidHom.comp planeToDualLine

theorem planeParametersHom_matrix (g : PlaneGroup) : toRealGL (planeParametersHom g)=g.val := by
  change toRealGL (lineParametersEquiv.symm (planeToDualLine g))=g.val
  rw [lineParametersEquiv_symm_matrix]
  exact dualGL_involutive g.val

theorem planeParametersHom_borel (g : BorelGroup) :
    planeParametersHom (planeInclusion g)=planeParameterHom g := rfl

theorem continuous_planeParametersHom : Continuous planeParametersHom :=
  continuous_lineParameters.comp ((continuous_dualGL.comp continuous_subtype_val).subtype_mk _)

/-- The plane extension now acts by the full actual plane matrix subgroup. -/
def planeExtend (g : PlaneGroup) (p : PlaneBordification) : PlaneBordification :=
  SymmetricSpacePlaneBordification.extend (planeParametersHom g) p

theorem planeExtend_embedding (g : PlaneGroup) (S : Space) :
    planeExtend g (SymmetricSpacePlaneBordification.embedding S)=
      SymmetricSpacePlaneBordification.embedding (act g.val S) := by
  rw [planeExtend,SymmetricSpacePlaneBordification.extend_embedding,planeParametersHom_matrix]

theorem planeExtend_one (p : PlaneBordification) : planeExtend 1 p=p := by
  simp [planeExtend]

theorem planeExtend_mul (g h : PlaneGroup) (p : PlaneBordification) :
    planeExtend (g*h) p=planeExtend g (planeExtend h p) := by
  simp only [planeExtend,map_mul,SymmetricSpacePlaneBordification.extend_mul]

instance actualPlaneMulAction : MulAction PlaneGroup PlaneBordification where
  smul := planeExtend
  one_smul := planeExtend_one
  mul_smul := planeExtend_mul

theorem continuous_planeExtend_joint :
    Continuous (fun z : PlaneGroup × PlaneBordification => planeExtend z.1 z.2) :=
  SymmetricSpacePlaneBordification.continuous_extend_joint.comp
    ((continuous_planeParametersHom.comp continuous_fst).prodMk continuous_snd)

instance actualPlaneContinuousSMul : ContinuousSMul PlaneGroup PlaneBordification where
  continuous_smul := continuous_planeExtend_joint

theorem continuous_planeExtend (g : PlaneGroup) : Continuous (planeExtend g) :=
  SymmetricSpacePlaneBordification.continuous_extend (planeParametersHom g)

end TernaryPoly.SymmetricSpaceBorelCorner
