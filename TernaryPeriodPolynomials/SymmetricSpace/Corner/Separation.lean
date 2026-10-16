module

public import TernaryPeriodPolynomials.SymmetricSpace.Corner.DegenerationClosure
public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingGlueData
public import TernaryPeriodPolynomials.Analysis.PartialGraphClosed
public import TernaryPeriodPolynomials.Topology.OpenGluing.GluingSeparation

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceCornerSeparation
open Topology SymmetricSpacePositive SymmetricSpaceFlagCoordinates
  SymmetricSpaceRationalGluing SymmetricSpaceCornerDegeneration SymmetricSpaceRationalAction

/-- The actual full partial transition graph, including both boundary faces and their corner. -/
def fullGraph (g : RealGL) : Set (Corner × Corner) :=
  PartialGraphClosed.graph (domain g) (fun p : domain g => (transition g p).val)

/-- The full continuous face extension is determined by the dense positive interior graph. -/
theorem closure_fullGraph (g : RealGL) :
    closure (fullGraph g) = closure (interiorTransitionGraph g) := by
  have h := PartialGraphClosed.closure_dense_graph (X := Corner) (Y := Corner) (domain g : Set Corner)
    (fun p : domain g => (transition g p).val)
    (continuous_subtype_val.comp (transition g).continuous)
    (liftInterior (domain g) (interior_subset_domain g))
    (denseRange_liftInterior (domain g) (interior_subset_domain g))
  have he : Set.range (fun S =>
      ((liftInterior (domain g) (interior_subset_domain g) S).val,
       (transition g (liftInterior (domain g) (interior_subset_domain g) S)).val)) =
      interiorTransitionGraph g := by
    ext p
    constructor
    · rintro ⟨S,rfl⟩
      refine ⟨S,rfl,?_⟩
      exact transition_interiorPoint g S
    · rintro ⟨S,hp,hq⟩
      refine ⟨S,?_⟩
      apply Prod.ext
      · exact hp.symm
      · exact (transition_interiorPoint g S).trans hq.symm
  rw [he] at h
  exact h.symm

/-- Every limit of full transitions stays in the genuine parabolic overlap domain. -/
theorem closure_fullGraph_domain (g : RealGL) {p : Corner × Corner}
    (hp : p ∈ closure (fullGraph g)) : p.1 ∈ domain g := by
  rw [closure_fullGraph] at hp
  have hc := closure_transition_subset_equations g hp
  rw [mem_domain_iff]
  constructor
  · by_cases h : 0 < p.1.2.1.val
    · exact Or.inl h
    · exact Or.inr (compatible_line_mem g hc (le_antisymm (le_of_not_gt h) p.1.2.1.property))
  · by_cases h : 0 < p.1.2.2.val
    · exact Or.inl h
    · exact Or.inr (compatible_plane_mem g hc (le_antisymm (le_of_not_gt h) p.1.2.2.property))

/-- Actual transition graphs are closed in the product of complete corner charts. -/
theorem isClosed_fullGraph (g : RealGL) : IsClosed (fullGraph g) :=
  PartialGraphClosed.isClosed_of_closure_domain (X := Corner) (Y := Corner) (domain g : Set Corner)
    (fun p : domain g => (transition g p).val)
    (continuous_subtype_val.comp (transition g).continuous)
    (fun _ hp => closure_fullGraph_domain g hp)

/-- The extended graph is precisely the closure of the actual interior graph. -/
theorem fullGraph_eq_closure_interior (g : RealGL) :
    fullGraph g = closure (interiorTransitionGraph g) := by
  rw [← closure_fullGraph,(isClosed_fullGraph g).closure_eq]

/-- The equality relation of each pair of actual rational corner charts is closed. -/
theorem isClosed_chart_relation (g h : RationalGL) :
    IsClosed {p : Corner × Corner | chart g p.1 = chart h p.2} := by
  have he : {p : Corner × Corner | chart g p.1 = chart h p.2} =
      fullGraph (changeMatrix g h) := by
    ext p
    rw [Set.mem_ofPred_eq,chart_eq_iff]
    rfl
  rw [he]
  exact isClosed_fullGraph _

/-- The actual rational corner gluing is Hausdorff. -/
instance : T2Space Glued := by
  apply (OpenGluingSeparation.t2Space_iff_closed_relations glueData).mpr
  intro g h
  have he : {p : glueData.U g × glueData.U h | glueData.Rel ⟨g,p.1⟩ ⟨h,p.2⟩} =
      {p : Corner × Corner | chart g p.1 = chart h p.2} := by
    ext p
    exact (glueData.ι_eq_iff_rel g h p.1 p.2).symm
  rw [he]
  exact isClosed_chart_relation g h

end TernaryPoly.SymmetricSpaceCornerSeparation
