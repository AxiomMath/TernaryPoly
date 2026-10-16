module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FacesRational

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaces
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
open SymmetricSpaceRationalGluing SymmetricSpaceBorelCorner SymmetricSpaceLineBordification
open Topology

/-- The actual transition preserves the zero first root and its intrinsic rational line. -/
theorem chart_line_compatible (g h : RationalGL) (p q : Corner)
    (he : chart g p=chart h q) (hp : p.2.1.val=0) :
    p.2.1.val=0 ∧ q.2.1.val=0 ∧ lineLabel g=lineLabel h := by
  obtain ⟨hd,ht⟩ := (chart_eq_iff g h p q).mp he
  change (transition (changeMatrix g h) ⟨p,hd⟩).val=q at ht
  have hr : changeMatrix g h∈lineStabilizer :=
    ((mem_domain_iff _ p).mp hd).1.resolve_left (by rw [hp]; exact lt_irrefl _)
  refine ⟨hp,?_,(lineLabel_eq_iff g h).mpr hr⟩
  rw [←ht]
  exact (transition_zero1_iff _ ⟨p,hd⟩).mpr hp

/-- The actual transition preserves the zero second root and its intrinsic rational plane. -/
theorem chart_plane_compatible (g h : RationalGL) (p q : Corner)
    (he : chart g p=chart h q) (hp : p.2.2.val=0) :
    p.2.2.val=0 ∧ q.2.2.val=0 ∧ planeLabel g=planeLabel h := by
  obtain ⟨hd,ht⟩ := (chart_eq_iff g h p q).mp he
  change (transition (changeMatrix g h) ⟨p,hd⟩).val=q at ht
  have hr : changeMatrix g h∈planeStabilizer :=
    ((mem_domain_iff _ p).mp hd).2.resolve_left (by rw [hp]; exact lt_irrefl _)
  refine ⟨hp,?_,(planeLabel_eq_iff g h).mpr hr⟩
  rw [←ht]
  exact (transition_zero2_iff _ ⟨p,hd⟩).mpr hp

/-- Intrinsic closed line-face subset of the actual gluing, indexed by an actual rational line. -/
def lineFace (L : Line) : Set Glued :=
  {x | ∃ g p,p.2.1.val=0 ∧ lineLabel g=L ∧ chart g p=x}

/-- Intrinsic closed plane-face subset, indexed by an actual rational plane. -/
def planeFace (P : Plane) : Set Glued :=
  {x | ∃ g p,p.2.2.val=0 ∧ planeLabel g=P ∧ chart g p=x}

/-- Exact coordinate preimage criterion for the actual line face. -/
theorem lineFace_chart_iff (L : Line) (g : RationalGL) (p : Corner) :
    chart g p∈lineFace L ↔ p.2.1.val=0 ∧ lineLabel g=L := by
  constructor
  · rintro ⟨h,q,hq,hL,he⟩
    obtain ⟨_,hp,hlabel⟩ := chart_line_compatible h g q p he hq
    exact ⟨hp,hlabel.symm.trans hL⟩
  · rintro ⟨hp,hL⟩
    exact ⟨g,p,hp,hL,rfl⟩

theorem planeFace_chart_iff (P : Plane) (g : RationalGL) (p : Corner) :
    chart g p∈planeFace P ↔ p.2.2.val=0 ∧ planeLabel g=P := by
  constructor
  · rintro ⟨h,q,hq,hP,he⟩
    obtain ⟨_,hp,hlabel⟩ := chart_plane_compatible h g q p he hq
    exact ⟨hp,hlabel.symm.trans hP⟩
  · rintro ⟨hp,hP⟩
    exact ⟨g,p,hp,hP,rfl⟩

theorem lineFace_unique {x : Glued} {L M : Line} (hL : x∈lineFace L) (hM : x∈lineFace M) : L=M := by
  obtain ⟨g,p,_,hg,rfl⟩ := hL
  exact hg.symm.trans ((lineFace_chart_iff M g p).mp hM).2

theorem planeFace_unique {x : Glued} {P Q : Plane} (hP : x∈planeFace P) (hQ : x∈planeFace Q) : P=Q := by
  obtain ⟨g,p,_,hg,rfl⟩ := hP
  exact hg.symm.trans ((planeFace_chart_iff Q g p).mp hQ).2

theorem chart_boundary_iff (g : RationalGL) (p : Corner) :
    chart g p∉Set.range SymmetricSpaceRationalGluing.embedding ↔ p.2.1.val=0 ∨ p.2.2.val=0 := by
  have h : chart g p∈Set.range SymmetricSpaceRationalGluing.embedding ↔ 0<p.2.1.val ∧ 0<p.2.2.val :=
    Set.ext_iff.mp (chart_preimage_embedding g) p
  rw [h,not_and_or,←halfLine_zero_iff_not_pos,←halfLine_zero_iff_not_pos]

/-- Every actual boundary point carries a rational line label or a rational plane label. -/
theorem boundary_iff_faces (x : Glued) : x∉Set.range SymmetricSpaceRationalGluing.embedding ↔
    (∃ L : Line,x∈lineFace L) ∨ (∃ P : Plane,x∈planeFace P) := by
  obtain ⟨g,p,rfl⟩ := chart_jointly_surjective x
  rw [chart_boundary_iff]
  constructor
  · rintro (h|h)
    · exact Or.inl ⟨lineLabel g,(lineFace_chart_iff _ _ _).mpr ⟨h,rfl⟩⟩
    · exact Or.inr ⟨planeLabel g,(planeFace_chart_iff _ _ _).mpr ⟨h,rfl⟩⟩
  · rintro (⟨L,hL⟩|⟨P,hP⟩)
    · exact Or.inl ((lineFace_chart_iff _ _ _).mp hL).1
    · exact Or.inr ((planeFace_chart_iff _ _ _).mp hP).1

/-- Simultaneous actual face labels are incident rational subspaces. -/
theorem face_labels_incident {x : Glued} {L : Line} {P : Plane}
    (hL : x∈lineFace L) (hP : x∈planeFace P) : incidence L P := by
  obtain ⟨g,p,_,hg,rfl⟩ := hL
  have hgp := ((planeFace_chart_iff P g p).mp hP).2
  rw [←hg,←hgp]
  exact labels_incident g

/-- Each actual labeled line-face is closed, by its exact chart preimages. -/
theorem lineFace_closed (L : Line) : IsClosed (lineFace L) := by
  apply isOpen_compl_iff.mp
  apply (glueData.isOpen_iff _).mpr
  intro g
  change IsOpen (chart g ⁻¹' (lineFace L)ᶜ)
  rw [Set.preimage_compl]
  by_cases hg : lineLabel g=L
  · have he : chart g ⁻¹' lineFace L={p : Corner | p.2.1.val=0} := by
      ext p
      exact (lineFace_chart_iff L g p).trans (and_iff_left hg)
    rw [he]
    exact (isClosed_eq (by fun_prop) continuous_const).isOpen_compl
  · have he : chart g ⁻¹' lineFace L=∅ := by
      ext p
      exact (lineFace_chart_iff L g p).trans (by simp only [hg,and_false,Set.mem_empty_iff_false])
    rw [he]
    simp

/-- Each actual labeled plane-face is closed. -/
theorem planeFace_closed (P : Plane) : IsClosed (planeFace P) := by
  apply isOpen_compl_iff.mp
  apply (glueData.isOpen_iff _).mpr
  intro g
  change IsOpen (chart g ⁻¹' (planeFace P)ᶜ)
  rw [Set.preimage_compl]
  by_cases hg : planeLabel g=P
  · have he : chart g ⁻¹' planeFace P={p : Corner | p.2.2.val=0} := by
      ext p
      exact (planeFace_chart_iff P g p).trans (and_iff_left hg)
    rw [he]
    exact (isClosed_eq (by fun_prop) continuous_const).isOpen_compl
  · have he : chart g ⁻¹' planeFace P=∅ := by
      ext p
      exact (planeFace_chart_iff P g p).trans (by simp only [hg,and_false,Set.mem_empty_iff_false])
    rw [he]
    simp

end TernaryPoly.SymmetricSpaceBoundaryFaces
