module

public import TernaryPeriodPolynomials.SymmetricSpace.Borel.CornerOverlap

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRationalGluing
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates
open SymmetricSpaceFlagPlaneHomeomorph SymmetricSpaceLineBordification SymmetricSpaceBorelCorner
open Topology TopologicalSpace

/-- An actual local extension of normalized congruence, together with its interior and strata. -/
structure LocalExtension (r : RealGL) where
  domain : Opens Corner
  interior_mem : cornerInterior ⊆ domain
  homeomorph : domain ≃ₜ domain
  embedding_apply (S : Space) :
    (homeomorph ⟨cornerEmbedding S,interior_mem (cornerHomeomorph S).property⟩).val=
      cornerEmbedding (act r S)
  pos1_iff (p : domain) : 0<(homeomorph p).val.2.1.val ↔ 0<p.val.2.1.val
  pos2_iff (p : domain) : 0<(homeomorph p).val.2.2.val ↔ 0<p.val.2.2.val

/-- Every Borel element acts on the entire closed corner. -/
def borelModel (r : BorelGroup) : LocalExtension r.val where
  domain := ⊤
  interior_mem := fun _ _ => trivial
  homeomorph := ((Homeomorph.Set.univ Corner).trans (SymmetricSpaceBorelCorner.extendedHomeomorph r)).trans
    (Homeomorph.Set.univ Corner).symm
  embedding_apply S := SymmetricSpaceBorelCorner.extend_embedding r S
  pos1_iff p := extend_pos1_iff r p.val
  pos2_iff p := extend_pos2_iff r p.val

/-- The actual plane action, conjugated through the full flag-plane overlap homeomorphism. -/
def planeModelMap (r : PlaneGroup) : OverlapDomain ≃ₜ OverlapDomain :=
  (planeOverlapHomeomorph.trans
    (SymmetricSpacePlaneBordification.extendedHomeomorph (planeParametersHom r))).trans
      planeOverlapHomeomorph.symm

theorem planeModelMap_commute (r : PlaneGroup) (p : OverlapDomain) :
    planeOverlapHomeomorph (planeModelMap r p)=planeExtend r (planeOverlapHomeomorph p) := by
  exact planeOverlapHomeomorph.apply_symm_apply _

theorem planeModelMap_embedding (r : PlaneGroup) (S : Space) :
    (planeModelMap r ⟨cornerEmbedding S,(cornerHomeomorph S).property.1⟩).val=
      cornerEmbedding (act r.val S) := by
  have h : planeModelMap r ⟨cornerEmbedding S,(cornerHomeomorph S).property.1⟩=
      ⟨cornerEmbedding (act r.val S),(cornerHomeomorph (act r.val S)).property.1⟩ := by
    apply planeOverlapHomeomorph.injective
    rw [planeModelMap_commute,planeOverlapHomeomorph_embedding,planeExtend_embedding,
      planeOverlapHomeomorph_embedding]
  exact congrArg Subtype.val h

theorem planeModelMap_pos2 (r : PlaneGroup) (p : OverlapDomain) :
    0<(planeModelMap r p).val.2.2.val ↔ 0<p.val.2.2.val := by
  rw [←planeOverlapHomeomorph_interior_iff,planeModelMap_commute]
  exact (SymmetricSpacePlaneBordification.extend_interior_iff (planeParametersHom r)
    (planeOverlapHomeomorph p)).trans (planeOverlapHomeomorph_interior_iff p)

def planeModel (r : PlaneGroup) : LocalExtension r.val where
  domain := ⟨overlapDomain,overlapDomain_open⟩
  interior_mem := fun _ hp => hp.1
  homeomorph := planeModelMap r
  embedding_apply := planeModelMap_embedding r
  pos1_iff p := ⟨fun _ => p.property,fun _ => (planeModelMap r p).property⟩
  pos2_iff := planeModelMap_pos2 r

/-- The actual e0-line action, conjugated through the full flag-line overlap homeomorphism. -/
def lineModelMap (r : LineGroup) : LineOverlapDomain ≃ₜ LineOverlapDomain :=
  (lineOverlapHomeomorph.trans (SymmetricSpaceLineBordification.extendedHomeomorph r)).trans
    lineOverlapHomeomorph.symm

theorem lineModelMap_commute (r : LineGroup) (p : LineOverlapDomain) :
    lineOverlapHomeomorph (lineModelMap r p)=
      SymmetricSpaceLineBordification.extend r (lineOverlapHomeomorph p) := by
  exact lineOverlapHomeomorph.apply_symm_apply _

theorem lineModelMap_embedding (r : LineGroup) (S : Space) :
    (lineModelMap r ⟨cornerEmbedding S,(cornerHomeomorph S).property.2⟩).val=
      cornerEmbedding (act r.val S) := by
  have h : lineModelMap r ⟨cornerEmbedding S,(cornerHomeomorph S).property.2⟩=
      ⟨cornerEmbedding (act r.val S),(cornerHomeomorph (act r.val S)).property.2⟩ := by
    apply lineOverlapHomeomorph.injective
    rw [lineModelMap_commute]
    change SymmetricSpaceLineBordification.extend r
      (lineOverlap ⟨cornerEmbedding S,(cornerHomeomorph S).property.2⟩)=
      lineOverlap ⟨cornerEmbedding (act r.val S),(cornerHomeomorph (act r.val S)).property.2⟩
    rw [lineOverlap_embedding,SymmetricSpaceLineBordification.extend_embedding,lineOverlap_embedding]
  exact congrArg Subtype.val h

theorem lineModelMap_pos1 (r : LineGroup) (p : LineOverlapDomain) :
    0<(lineModelMap r p).val.2.1.val ↔ 0<p.val.2.1.val := by
  rw [←lineOverlap_interior_iff]
  change lineOverlapHomeomorph (lineModelMap r p)∈lineInterior ↔ _
  rw [lineModelMap_commute]
  exact (SymmetricSpaceLineBordification.extend_interior_iff r (lineOverlapHomeomorph p)).trans
    (lineOverlap_interior_iff p)

def lineModel (r : LineGroup) : LocalExtension r.val where
  domain := ⟨lineOverlapDomain,lineOverlapDomain_open⟩
  interior_mem := fun _ hp => hp.2
  homeomorph := lineModelMap r
  embedding_apply := lineModelMap_embedding r
  pos1_iff := lineModelMap_pos1 r
  pos2_iff p := ⟨fun _ => p.property,fun _ => (lineModelMap r p).property⟩

/-- Every real invertible matrix has its actual normalized action on the positive interior. -/
def interiorModel (r : RealGL) : LocalExtension r where
  domain := ⟨cornerInterior,cornerInterior_open⟩
  interior_mem := fun _ hp => hp
  homeomorph := (cornerHomeomorph.symm.trans (actionHomeomorph r)).trans cornerHomeomorph
  embedding_apply S := by
    change (cornerHomeomorph (act r (cornerHomeomorph.symm (cornerHomeomorph S)))).val=_
    rw [cornerHomeomorph.symm_apply_apply]
    rfl
  pos1_iff p := ⟨fun _ => p.property.1,
    fun _ => (cornerHomeomorph (act r (cornerHomeomorph.symm p))).property.1⟩
  pos2_iff p := ⟨fun _ => p.property.2,
    fun _ => (cornerHomeomorph (act r (cornerHomeomorph.symm p))).property.2⟩

end TernaryPoly.SymmetricSpaceRationalGluing
