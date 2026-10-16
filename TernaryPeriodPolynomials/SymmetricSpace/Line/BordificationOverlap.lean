module

public import TernaryPeriodPolynomials.SymmetricSpace.Line.Bordification
public import TernaryPeriodPolynomials.SymmetricSpace.Line.BordificationFlagDuality
public import TernaryPeriodPolynomials.SymmetricSpace.Flag.PlaneHomeomorph

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceLineBordification
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates
open SymmetricSpaceFlagPlaneHomeomorph

/-- The complementary flag face, where the second root remains positive. -/
def lineOverlapDomain : Set Corner := {p | 0<p.2.2.val}
abbrev LineOverlapDomain := lineOverlapDomain

theorem lineOverlapDomain_open : IsOpen lineOverlapDomain :=
  isOpen_lt continuous_const
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))

/-- The corner duality exchanges the two actual overlap domains. -/
def lineDomainToPlane : LineOverlapDomain ≃ₜ OverlapDomain where
  toFun p := ⟨dualCorner p.val,p.property⟩
  invFun p := ⟨dualCorner p.val,p.property⟩
  left_inv p := by apply Subtype.ext; exact dualCorner_involutive p.val
  right_inv p := by apply Subtype.ext; exact dualCorner_involutive p.val
  continuous_toFun := (dualCornerHomeomorph.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (dualCornerHomeomorph.continuous.comp continuous_subtype_val).subtype_mk _

/-- The t2>0 flag face is homeomorphic to the entire actual e0-line partial bordification. -/
def lineOverlapHomeomorph : LineOverlapDomain ≃ₜ LineBordification :=
  lineDomainToPlane.trans planeOverlapHomeomorph

def lineOverlap (p : LineOverlapDomain) : LineBordification := lineOverlapHomeomorph p

theorem continuous_lineOverlap : Continuous lineOverlap := lineOverlapHomeomorph.continuous

@[simp] theorem lineOverlap_unipotent (p : LineOverlapDomain) :
    (lineOverlap p).1=![p.val.1 0*p.val.1 1-p.val.1 2,-p.val.1 0] := rfl

@[simp] theorem lineOverlap_shape (p : LineOverlapDomain) :
    (lineOverlap p).2.1.val=
      binaryNormalize !![(p.val.1 1)^2+(p.val.2.2.val^2)⁻¹,-p.val.1 1;-p.val.1 1,1] := by
  change binaryNormalize (shapeMatrix (-p.val.1 1) p.val.2.2.val)=_
  rw [shapeMatrix_formula,neg_sq]

@[simp] theorem lineOverlap_parameter (p : LineOverlapDomain) :
    (lineOverlap p).2.2.val=
      p.val.2.1.val/Real.sqrt ((p.val.1 1)^2+(p.val.2.2.val^2)⁻¹+1) := by
  change p.val.2.1.val/Real.sqrt (shapeTrace (-p.val.1 1) p.val.2.2.val)=_
  simp [shapeTrace]

/-- Both embeddings agree on the actual form space, not merely on formal coordinates. -/
theorem lineOverlap_embedding (S : Space) :
    lineOverlap ⟨cornerEmbedding S,(cornerHomeomorph S).property.2⟩=embedding S := by
  have he : lineDomainToPlane ⟨cornerEmbedding S,(cornerHomeomorph S).property.2⟩=
      ⟨cornerEmbedding (dualForm S),(cornerHomeomorph (dualForm S)).property.1⟩ := by
    apply Subtype.ext
    exact dualCorner_embedding S
  change planeOverlap (lineDomainToPlane ⟨cornerEmbedding S,(cornerHomeomorph S).property.2⟩)=_
  rw [he,planeOverlap_cornerEmbedding]
  rfl

theorem lineOverlap_boundary_iff (p : LineOverlapDomain) :
    lineOverlap p∈lineBoundary ↔ p.val.2.1.val=0 :=
  planeOverlap_boundary_iff (lineDomainToPlane p)

theorem lineOverlap_interior_iff (p : LineOverlapDomain) :
    lineOverlap p∈lineInterior ↔ 0<p.val.2.1.val :=
  planeOverlapHomeomorph_interior_iff (lineDomainToPlane p)

end TernaryPoly.SymmetricSpaceLineBordification
