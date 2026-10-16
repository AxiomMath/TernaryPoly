module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Faces
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceModels
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces Topology

/-- The line stratum with every plane face removed, in the actual glued topology. -/
def openLineFace (L : Line) : Set Glued := {x | x ∈ lineFace L ∧ ∀ P, x ∉ planeFace P}

/-- The plane stratum with every line face removed. -/
def openPlaneFace (P : Plane) : Set Glued := {x | x ∈ planeFace P ∧ ∀ L, x ∉ lineFace L}

def lineLocus : Set Corner := {p | p.2.1.val = 0 ∧ 0 < p.2.2.val}
def planeLocus : Set Corner := {p | 0 < p.2.1.val ∧ p.2.2.val = 0}
def cornerLocus : Set Corner := {p | p.2.1.val = 0 ∧ p.2.2.val = 0}

/-- Exact line-stratum criterion: the other root is strictly positive. -/
theorem openLineFace_chart_iff (L : Line) (g : RationalGL) (p : Corner) :
    chart g p ∈ openLineFace L ↔ p ∈ lineLocus ∧ lineLabel g = L := by
  change (chart g p ∈ lineFace L ∧ ∀ P, chart g p ∉ planeFace P) ↔ _
  simp only [lineFace_chart_iff, planeFace_chart_iff]
  constructor
  · rintro ⟨⟨hz, hL⟩, hp⟩
    refine ⟨⟨hz, ?_⟩, hL⟩
    exact lt_of_le_of_ne p.2.2.property (Ne.symm (fun hz => hp (planeLabel g) ⟨hz, rfl⟩))
  · rintro ⟨⟨hz, hp⟩, hL⟩
    exact ⟨⟨hz, hL⟩, fun _ h => (ne_of_gt hp) h.1⟩

theorem openPlaneFace_chart_iff (P : Plane) (g : RationalGL) (p : Corner) :
    chart g p ∈ openPlaneFace P ↔ p ∈ planeLocus ∧ planeLabel g = P := by
  change (chart g p ∈ planeFace P ∧ ∀ L, chart g p ∉ lineFace L) ↔ _
  simp only [planeFace_chart_iff, lineFace_chart_iff]
  constructor
  · rintro ⟨⟨hz, hP⟩, hp⟩
    refine ⟨⟨?_, hz⟩, hP⟩
    exact lt_of_le_of_ne p.2.1.property (Ne.symm (fun hz => hp (lineLabel g) ⟨hz, rfl⟩))
  · rintro ⟨⟨hp, hz⟩, hP⟩
    exact ⟨⟨hz, hP⟩, fun _ h => (ne_of_gt hp) h.1⟩

/-- Any frame realizing the line covers its entire open stratum. -/
theorem openLineFace_subset_range (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    openLineFace L ⊆ Set.range (chart g) := by
  intro x hx
  obtain ⟨h, p, rfl⟩ := chart_jointly_surjective x
  obtain ⟨hp, hh⟩ := (openLineFace_chart_iff L h p).mp hx
  have hd : p ∈ overlap h g := (mem_domain_iff _ p).mpr
    ⟨Or.inr ((lineLabel_eq_iff h g).mp (hh.trans hg.symm)), Or.inl hp.2⟩
  exact ⟨(pairTransition h g ⟨p, hd⟩).val,
    ((chart_eq_iff h g _ _).mpr ⟨hd, rfl⟩).symm⟩

/-- Any frame realizing the plane covers its entire open stratum. -/
theorem openPlaneFace_subset_range (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    openPlaneFace P ⊆ Set.range (chart g) := by
  intro x hx
  obtain ⟨h, p, rfl⟩ := chart_jointly_surjective x
  obtain ⟨hp, hh⟩ := (openPlaneFace_chart_iff P h p).mp hx
  have hd : p ∈ overlap h g := (mem_domain_iff _ p).mpr
    ⟨Or.inl hp.1, Or.inr ((planeLabel_eq_iff h g).mp (hh.trans hg.symm))⟩
  exact ⟨(pairTransition h g ⟨p, hd⟩).val,
    ((chart_eq_iff h g _ _).mpr ⟨hd, rfl⟩).symm⟩

/-- A realizing full frame covers the entire incident corner intersection. -/
theorem flagFace_subset_range (L : Line) (P : Plane) (g : RationalGL)
    (hL : lineLabel g = L) (hP : planeLabel g = P) :
    lineFace L ∩ planeFace P ⊆ Set.range (chart g) := by
  intro x hx
  obtain ⟨h, p, rfl⟩ := chart_jointly_surjective x
  have hl := ((lineFace_chart_iff L h p).mp hx.1).2
  have hp := ((planeFace_chart_iff P h p).mp hx.2).2
  have hd : p ∈ overlap h g := (mem_domain_iff _ p).mpr
    ⟨Or.inr ((lineLabel_eq_iff h g).mp (hl.trans hL.symm)),
      Or.inr ((planeLabel_eq_iff h g).mp (hp.trans hP.symm))⟩
  exact ⟨(pairTransition h g ⟨p, hd⟩).val,
    ((chart_eq_iff h g _ _).mpr ⟨hd, rfl⟩).symm⟩

def lineLocusHomeomorph (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    lineLocus ≃ₜ openLineFace L :=
  (Homeomorph.setCongr (by
    ext p
    exact ((openLineFace_chart_iff L g p).trans (and_iff_left hg)).symm)).trans
      ((chart_isOpenEmbedding g).isEmbedding.homeomorphOfSubsetRange
        (openLineFace_subset_range L g hg))

def planeLocusHomeomorph (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    planeLocus ≃ₜ openPlaneFace P :=
  (Homeomorph.setCongr (by
    ext p
    exact ((openPlaneFace_chart_iff P g p).trans (and_iff_left hg)).symm)).trans
      ((chart_isOpenEmbedding g).isEmbedding.homeomorphOfSubsetRange
        (openPlaneFace_subset_range P g hg))

def cornerLocusHomeomorph (L : Line) (P : Plane) (g : RationalGL)
    (hL : lineLabel g = L) (hP : planeLabel g = P) :
    cornerLocus ≃ₜ ↥(lineFace L ∩ planeFace P) :=
  (Homeomorph.setCongr (by
    rw [flagFace_chart_preimage]
    ext p
    simp only [Set.mem_ofPred_eq, hL, hP, and_self, and_true]
    rfl)).trans
      ((chart_isOpenEmbedding g).isEmbedding.homeomorphOfSubsetRange
        (flagFace_subset_range L P g hL hP))

@[simp] theorem lineLocusHomeomorph_val (L : Line) (g : RationalGL)
    (hg : lineLabel g = L) (p : lineLocus) :
    (lineLocusHomeomorph L g hg p).val = chart g p.val := rfl

@[simp] theorem planeLocusHomeomorph_val (P : Plane) (g : RationalGL)
    (hg : planeLabel g = P) (p : planeLocus) :
    (planeLocusHomeomorph P g hg p).val = chart g p.val := rfl

@[simp] theorem cornerLocusHomeomorph_val (L : Line) (P : Plane) (g : RationalGL)
    (hL : lineLabel g = L) (hP : planeLabel g = P) (p : cornerLocus) :
    (cornerLocusHomeomorph L P g hL hP p).val = chart g p.val := rfl

end TernaryPoly.SymmetricSpaceBoundaryFaceModels
