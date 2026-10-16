module

public import TernaryPeriodPolynomials.SymmetricSpace.Borel.CornerGroup

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBorelCorner
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates
open SymmetricSpacePlaneBordification SymmetricSpaceLineBordification

/-- Actual inclusion of the full flag stabilizer into the full plane stabilizer. -/
def planeInclusion : BorelGroup →* PlaneGroup where
  toFun g := ⟨g.val,g.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Actual inclusion of the full flag stabilizer into the full e0-line stabilizer. -/
def lineInclusion : BorelGroup →* LineGroup where
  toFun g := ⟨g.val,g.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem planeInclusion_val (g : BorelGroup) : (planeInclusion g).val=g.val := rfl
@[simp] theorem lineInclusion_val (g : BorelGroup) : (lineInclusion g).val=g.val := rfl

theorem continuous_planeInclusion : Continuous planeInclusion := continuous_subtype_val.subtype_mk _
theorem continuous_lineInclusion : Continuous lineInclusion := continuous_subtype_val.subtype_mk _

/-- Inverse transpose with the explicit reversal converts the plane inclusion to the actual line group. -/
def dualLineInclusion : BorelGroup →* LineGroup where
  toFun g := ⟨dualGL g.val,by
    apply (dualGL_plane_iff_line (dualGL g.val)).mp
    simpa only [dualGL_involutive] using (mem_planeStabilizer_iff g.val).mp g.property.1⟩
  map_one' := by apply Subtype.ext; exact dualGLEquiv.map_one
  map_mul' g h := by apply Subtype.ext; exact dualGL_mul g.val h.val

theorem continuous_dualLineInclusion : Continuous dualLineInclusion :=
  (continuous_dualGL.comp continuous_subtype_val).subtype_mk _

/-- The unique full signed plane parameters of the actual Borel inclusion. -/
def planeParameterHom : BorelGroup →* Parameters :=
  lineParametersEquiv.symm.toMonoidHom.comp dualLineInclusion

/-- The plane parameters reconstruct exactly the original real matrix, not a conjugate or quotient. -/
theorem planeParameterHom_matrix (g : BorelGroup) : toRealGL (planeParameterHom g)=g.val := by
  change toRealGL (lineParametersEquiv.symm (dualLineInclusion g))=g.val
  rw [lineParametersEquiv_symm_matrix]
  exact dualGL_involutive g.val

theorem planeParameterHom_inclusion (g : BorelGroup) :
    toRealGL (planeParameterHom g)=(planeInclusion g).val := planeParameterHom_matrix g

theorem continuous_planeParameterHom : Continuous planeParameterHom :=
  continuous_lineParameters.comp continuous_dualLineInclusion

end TernaryPoly.SymmetricSpaceBorelCorner
