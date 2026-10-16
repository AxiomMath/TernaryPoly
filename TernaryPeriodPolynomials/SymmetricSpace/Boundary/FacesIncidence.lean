module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FacesLabels
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FacesFrames

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaces
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction SymmetricSpaceRationalGluing

/-- A literal full-flag zero-root point of the standard closed corner. -/
def origin : Corner := (0,⟨0,by norm_num [SymmetricSpaceFlagCoordinates.HalfLine]⟩,
  ⟨0,by norm_num [SymmetricSpaceFlagCoordinates.HalfLine]⟩)

def fullFlagPoint (g : RationalGL) : Glued := chart g origin

theorem fullFlagPoint_faces (g : RationalGL) :
    fullFlagPoint g∈lineFace (lineLabel g) ∩ planeFace (planeLabel g) :=
  ⟨(lineFace_chart_iff _ _ _).mpr ⟨rfl,rfl⟩,(planeFace_chart_iff _ _ _).mpr ⟨rfl,rfl⟩⟩

/-- Every actual rational incident pair occurs at a literal full-flag corner point. -/
theorem incident_fullFlagPoint (L : Line) (P : Plane) (hLP : incidence L P) :
    ∃ g : RationalGL,fullFlagPoint g∈lineFace L ∩ planeFace P := by
  obtain ⟨g,hL,hP⟩ := exists_frame_for_incident L P hLP
  exact ⟨g,by rw [←hL,←hP]; exact fullFlagPoint_faces g⟩

/-- Actual line-face/plane-face incidence is exactly strict containment of rational subspaces. -/
theorem face_inter_nonempty_iff (L : Line) (P : Plane) :
    (lineFace L ∩ planeFace P).Nonempty ↔ incidence L P := by
  constructor
  · rintro ⟨x,hL,hP⟩
    exact face_labels_incident hL hP
  · intro h
    obtain ⟨g,hg⟩ := incident_fullFlagPoint L P h
    exact ⟨fullFlagPoint g,hg⟩

theorem exists_incident_plane (L : Line) : ∃ P : Plane,incidence L P := by
  have htop : L.val≠⊤ := by
    intro h
    have hd := L.property.1
    rw [h] at hd
    norm_num at hd
  obtain ⟨v,hv⟩ := SetLike.exists_not_mem_of_ne_top L.val htop
  have hv0 : v≠0 := by intro h; exact hv (h ▸ L.val.zero_mem)
  let M : Line := ⟨Submodule.span ℚ {v},finrank_span_singleton hv0,trivial⟩
  have hLM : L≠M := by
    intro h
    apply hv
    rw [h]
    exact Submodule.subset_span (Set.mem_singleton v)
  let P := GoodIncidenceConnected.spanPlane (fun _ => True) L M hLM
  exact ⟨P,GoodIncidenceConnected.line_lt_plane (fun _ => True) le_sup_left⟩

theorem lineFace_nonempty (L : Line) : (lineFace L).Nonempty := by
  obtain ⟨P,hP⟩ := exists_incident_plane L
  obtain ⟨x,hL,_⟩ := (face_inter_nonempty_iff L P).mpr hP
  exact ⟨x,hL⟩

theorem planeFace_nonempty (P : Plane) : (planeFace P).Nonempty := by
  obtain ⟨L,hL⟩ := P.property.2
  obtain ⟨x,_,hP⟩ := (face_inter_nonempty_iff L P).mpr
    (GoodIncidenceConnected.line_lt_plane (fun _ => True) hL)
  exact ⟨x,hP⟩

theorem lineFace_injective : Function.Injective lineFace := by
  intro L M h
  obtain ⟨x,hx⟩ := lineFace_nonempty L
  exact lineFace_unique hx (h ▸ hx)

theorem planeFace_injective : Function.Injective planeFace := by
  intro P Q h
  obtain ⟨x,hx⟩ := planeFace_nonempty P
  exact planeFace_unique hx (h ▸ hx)

end TernaryPoly.SymmetricSpaceBoundaryFaces
