module

public import TernaryPeriodPolynomials.SymmetricSpace.Borel.CornerAction
public import TernaryPeriodPolynomials.SymmetricSpace.Borel.CornerParabolic
public import TernaryPeriodPolynomials.SymmetricSpace.Line.BordificationOverlap

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBorelCorner
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates
open SymmetricSpaceFlagPlaneHomeomorph SymmetricSpaceLineBordification

/-- The actual corner action preserves the t1>0 plane-overlap domain. -/
def planeDomainAction (g : BorelGroup) (p : OverlapDomain) : OverlapDomain :=
  ⟨extend g p.val,(extend_pos1_iff g p.val).mpr p.property⟩

/-- The actual corner action preserves the t2>0 line-overlap domain. -/
def lineDomainAction (g : BorelGroup) (p : LineOverlapDomain) : LineOverlapDomain :=
  ⟨extend g p.val,(extend_pos2_iff g p.val).mpr p.property⟩

theorem continuous_planeDomainAction (g : BorelGroup) : Continuous (planeDomainAction g) :=
  ((continuous_extend g).comp continuous_subtype_val).subtype_mk _

theorem continuous_lineDomainAction (g : BorelGroup) : Continuous (lineDomainAction g) :=
  ((continuous_extend g).comp continuous_subtype_val).subtype_mk _

def planeDomainHomeomorph (g : BorelGroup) : OverlapDomain ≃ₜ OverlapDomain where
  toFun := planeDomainAction g
  invFun := planeDomainAction g⁻¹
  left_inv p := by apply Subtype.ext; exact (extendedHomeomorph g).left_inv p.val
  right_inv p := by apply Subtype.ext; exact (extendedHomeomorph g).right_inv p.val
  continuous_toFun := continuous_planeDomainAction g
  continuous_invFun := continuous_planeDomainAction g⁻¹

def lineDomainHomeomorph (g : BorelGroup) : LineOverlapDomain ≃ₜ LineOverlapDomain where
  toFun := lineDomainAction g
  invFun := lineDomainAction g⁻¹
  left_inv p := by apply Subtype.ext; exact (extendedHomeomorph g).left_inv p.val
  right_inv p := by apply Subtype.ext; exact (extendedHomeomorph g).right_inv p.val
  continuous_toFun := continuous_lineDomainAction g
  continuous_invFun := continuous_lineDomainAction g⁻¹

def planeInteriorPoint (S : Space) : OverlapDomain :=
  ⟨cornerEmbedding S,(cornerHomeomorph S).property.1⟩

def lineInteriorPoint (S : Space) : LineOverlapDomain :=
  ⟨cornerEmbedding S,(cornerHomeomorph S).property.2⟩

@[simp] theorem planeInteriorPoint_overlap (S : Space) :
    planeOverlapHomeomorph (planeInteriorPoint S)=SymmetricSpacePlaneBordification.embedding S :=
  planeOverlapHomeomorph_embedding S

@[simp] theorem lineInteriorPoint_overlap (S : Space) :
    lineOverlapHomeomorph (lineInteriorPoint S)=SymmetricSpaceLineBordification.embedding S :=
  lineOverlap_embedding S

theorem planeInteriorPoint_denseRange : DenseRange planeInteriorPoint := by
  have he : planeInteriorPoint=planeOverlapHomeomorph.symm ∘ SymmetricSpacePlaneBordification.embedding := by
    funext S
    apply planeOverlapHomeomorph.injective
    rw [planeInteriorPoint_overlap,Function.comp_apply,planeOverlapHomeomorph.apply_symm_apply]
  rw [he]
  exact planeOverlapHomeomorph.symm.surjective.denseRange.comp
    SymmetricSpacePlaneBordification.denseRange_embedding planeOverlapHomeomorph.symm.continuous

theorem lineInteriorPoint_denseRange : DenseRange lineInteriorPoint := by
  have he : lineInteriorPoint=lineOverlapHomeomorph.symm ∘ SymmetricSpaceLineBordification.embedding := by
    funext S
    apply lineOverlapHomeomorph.injective
    rw [lineInteriorPoint_overlap,Function.comp_apply,lineOverlapHomeomorph.apply_symm_apply]
  rw [he]
  exact lineOverlapHomeomorph.symm.surjective.denseRange.comp
    SymmetricSpaceLineBordification.denseRange_embedding lineOverlapHomeomorph.symm.continuous

@[simp] theorem planeDomainAction_interior (g : BorelGroup) (S : Space) :
    planeDomainAction g (planeInteriorPoint S)=planeInteriorPoint (act g.val S) := by
  apply Subtype.ext
  exact extend_embedding g S

@[simp] theorem lineDomainAction_interior (g : BorelGroup) (S : Space) :
    lineDomainAction g (lineInteriorPoint S)=lineInteriorPoint (act g.val S) := by
  apply Subtype.ext
  exact extend_embedding g S

/-- The entire plane overlap is equivariant for the actual inclusion of real matrix subgroups. -/
theorem planeOverlap_equivariant (g : BorelGroup) (p : OverlapDomain) :
    planeOverlapHomeomorph (planeDomainAction g p)=
      planeExtend (planeInclusion g) (planeOverlapHomeomorph p) := by
  have h : planeOverlapHomeomorph ∘ planeDomainAction g=
      planeExtend (planeInclusion g) ∘ planeOverlapHomeomorph :=
    planeInteriorPoint_denseRange.equalizer
      (planeOverlapHomeomorph.continuous.comp (continuous_planeDomainAction g))
      ((continuous_planeExtend (planeInclusion g)).comp planeOverlapHomeomorph.continuous) (by
        funext S
        simp only [Function.comp_apply,planeDomainAction_interior,planeInteriorPoint_overlap,
          planeExtend_embedding,planeInclusion_val])
  exact congrFun h p

/-- The same equality in the original full signed plane parameters, with the actual matrix unchanged. -/
theorem planeOverlap_equivariant_parameters (g : BorelGroup) (p : OverlapDomain) :
    planeOverlap (planeDomainAction g p)=
      SymmetricSpacePlaneBordification.extend (planeParameterHom g) (planeOverlap p) := by
  simpa only [planeOverlapHomeomorph_apply,planeExtend,planeParametersHom_borel] using
    planeOverlap_equivariant g p

/-- The entire line overlap is equivariant for the actual inclusion into the full e0-line subgroup. -/
theorem lineOverlap_equivariant (g : BorelGroup) (p : LineOverlapDomain) :
    lineOverlapHomeomorph (lineDomainAction g p)=
      SymmetricSpaceLineBordification.extend (lineInclusion g) (lineOverlapHomeomorph p) := by
  have h : lineOverlapHomeomorph ∘ lineDomainAction g=
      SymmetricSpaceLineBordification.extend (lineInclusion g) ∘ lineOverlapHomeomorph :=
    lineInteriorPoint_denseRange.equalizer
      (lineOverlapHomeomorph.continuous.comp (continuous_lineDomainAction g))
      ((SymmetricSpaceLineBordification.continuous_extend (lineInclusion g)).comp
        lineOverlapHomeomorph.continuous) (by
        funext S
        simp only [Function.comp_apply,lineDomainAction_interior,lineInteriorPoint_overlap,
          SymmetricSpaceLineBordification.extend_embedding,lineInclusion_val])
  exact congrFun h p

end TernaryPoly.SymmetricSpaceBorelCorner
