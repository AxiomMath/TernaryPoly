module

public import TernaryPeriodPolynomials.SymmetricSpace.Line.BordificationGroupTopology
public import TernaryPeriodPolynomials.SymmetricSpace.Plane.BordificationContinuousAction

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceLineBordification
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates
open Topology

/-- The actual standard e0-line partial bordification, in dual plane coordinates. -/
abbrev LineBordification := SymmetricSpacePlaneBordification.PlaneBordification

def lineInterior : Set LineBordification := SymmetricSpacePlaneBordification.interior
def lineBoundary : Set LineBordification := SymmetricSpacePlaneBordification.boundary

/-- The original form space is identified with the positive locus through the explicit duality. -/
def lineInteriorHomeomorph : Space ≃ₜ lineInterior :=
  dualFormHomeomorph.trans SymmetricSpacePlaneBordification.spaceInteriorHomeomorph

def embedding (S : Space) : LineBordification := SymmetricSpacePlaneBordification.embedding (dualForm S)

@[simp] theorem embedding_unipotent (S : Space) :
    (embedding S).1=unipotent (dualForm S).val := rfl

@[simp] theorem embedding_shape (S : Space) :
    (embedding S).2.1.val=binaryNormalize (schur (dualForm S).val) := rfl

@[simp] theorem embedding_parameter (S : Space) :
    (embedding S).2.2.val=(Real.sqrt (schur (dualForm S).val).trace)⁻¹ := rfl

theorem embedding_range : Set.range embedding=lineInterior := by
  ext p
  constructor
  · rintro ⟨S,rfl⟩; exact (lineInteriorHomeomorph S).property
  · intro hp
    obtain ⟨S,hS⟩ := lineInteriorHomeomorph.surjective ⟨p,hp⟩
    exact ⟨S,congrArg Subtype.val hS⟩

theorem isOpen_lineInterior : IsOpen lineInterior := SymmetricSpacePlaneBordification.isOpen_interior

theorem isClosed_lineBoundary : IsClosed lineBoundary := SymmetricSpacePlaneBordification.isClosed_boundary

theorem dense_lineInterior : Dense lineInterior := SymmetricSpacePlaneBordification.dense_interior

theorem embedding_isOpenEmbedding : IsOpenEmbedding embedding :=
  isOpen_lineInterior.isOpenEmbedding_subtypeVal.comp lineInteriorHomeomorph.isOpenEmbedding

theorem denseRange_embedding : DenseRange embedding := by
  rw [DenseRange,embedding_range]
  exact dense_lineInterior

/-- The actual line boundary is the full unipotent vector times the binary symmetric space. -/
def boundaryHomeomorph : lineBoundary ≃ₜ (Vec2 × BinarySpace) :=
  SymmetricSpacePlaneBordification.boundaryHomeomorph

/-- The genuine e0-line subgroup acts using its uniquely determined signed plane parameters. -/
def extend (g : LineGroup) (p : LineBordification) : LineBordification :=
  SymmetricSpacePlaneBordification.extend (lineParametersEquiv.symm g) p

/-- Equivariance is for the original normalized matrix action of the actual line subgroup. -/
theorem extend_embedding (g : LineGroup) (S : Space) :
    extend g (embedding S)=embedding (act g.val S) := by
  change SymmetricSpacePlaneBordification.extend (lineParametersEquiv.symm g)
    (SymmetricSpacePlaneBordification.embedding (dualForm S))=
    SymmetricSpacePlaneBordification.embedding (dualForm (act g.val S))
  rw [SymmetricSpacePlaneBordification.extend_embedding,dualForm_act,lineParametersEquiv_symm_matrix]

@[simp] theorem extend_one (p : LineBordification) : extend 1 p=p := by
  simp only [extend,map_one,SymmetricSpacePlaneBordification.extend_one]

theorem extend_mul (g h : LineGroup) (p : LineBordification) :
    extend (g*h) p=extend g (extend h p) := by
  simp only [extend,map_mul,SymmetricSpacePlaneBordification.extend_mul]

instance lineMulAction : MulAction LineGroup LineBordification where
  smul := extend
  one_smul := extend_one
  mul_smul := extend_mul

theorem continuous_extend_joint : Continuous (fun z : LineGroup × LineBordification => extend z.1 z.2) :=
  SymmetricSpacePlaneBordification.continuous_extend_joint.comp
    ((continuous_lineParameters.comp continuous_fst).prodMk continuous_snd)

instance lineContinuousSMul : ContinuousSMul LineGroup LineBordification where
  continuous_smul := continuous_extend_joint

theorem continuous_extend (g : LineGroup) : Continuous (extend g) :=
  continuous_extend_joint.comp (continuous_const.prodMk continuous_id)

def extendedHomeomorph (g : LineGroup) : LineBordification ≃ₜ LineBordification where
  toFun := extend g
  invFun := extend g⁻¹
  left_inv p := by rw [←extend_mul,inv_mul_cancel,extend_one]
  right_inv p := by rw [←extend_mul,mul_inv_cancel,extend_one]
  continuous_toFun := continuous_extend g
  continuous_invFun := continuous_extend g⁻¹

theorem extend_interior_iff (g : LineGroup) (p : LineBordification) :
    extend g p∈lineInterior ↔ p∈lineInterior :=
  SymmetricSpacePlaneBordification.extend_interior_iff _ _

theorem extend_boundary_iff (g : LineGroup) (p : LineBordification) :
    extend g p∈lineBoundary ↔ p∈lineBoundary :=
  SymmetricSpacePlaneBordification.extend_boundary_iff _ _

def boundaryActionHomeomorph (g : LineGroup) : lineBoundary ≃ₜ lineBoundary :=
  SymmetricSpacePlaneBordification.boundaryActionHomeomorph (lineParametersEquiv.symm g)

/-- Both signs in GL2 and in the one-dimensional factor are retained by the actual group equivalence. -/
theorem extend_lineParameters (p : SymmetricSpacePlaneBordification.Parameters) (x : LineBordification) :
    extend (lineParametersEquiv p) x=SymmetricSpacePlaneBordification.extend p x := by
  simp [extend]

end TernaryPoly.SymmetricSpaceLineBordification
