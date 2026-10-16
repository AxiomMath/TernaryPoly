module

public import TernaryPeriodPolynomials.SymmetricSpace.Corner.DegenerationDetection
public import Mathlib.Topology.Separation.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceCornerDegeneration
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceLineBordification
open SymmetricSpaceBorelCorner

/-- The actual transition graph between two copies of the positive flag chart. -/
def interiorTransitionGraph (g : RealGL) : Set (Corner × Corner) :=
  {z | ∃ S : Space, z.1=cornerEmbedding S ∧ z.2=cornerEmbedding (act g S)}

def equationLocus (g : RealGL) : Set (Corner × Corner) := {z | Compatible g z.1 z.2}

/-- Both detector equations define a closed locus all the way to the root boundary. -/
theorem isClosed_equationLocus (g : RealGL) : IsClosed (equationLocus g) := by
  have hA := continuous_normalized_conjugate g continuous_A A_psd A_ne_zero
  have hD := continuous_normalized_conjugate (contragredient g) continuous_D D_psd D_ne_zero
  exact (isClosed_eq (continuous_A.comp continuous_snd) (hA.comp continuous_fst)).inter
    (isClosed_eq (continuous_D.comp continuous_snd) (hD.comp continuous_fst))

theorem interiorTransitionGraph_subset_equationLocus (g : RealGL) :
    interiorTransitionGraph g⊆equationLocus g := by
  rintro z ⟨S,hp,hq⟩
  change Compatible g z.1 z.2
  rw [hp,hq]
  constructor
  · rw [A_embedding,A_embedding]
    rfl
  · rw [D_embedding,D_embedding,inverseForm_act]
    rfl

/-- Limits of actual interior transitions satisfy the two literal normalized congruence equations. -/
theorem closure_transition_subset_equations (g : RealGL) :
    closure (interiorTransitionGraph g)⊆equationLocus g :=
  closure_minimal (interiorTransitionGraph_subset_equationLocus g) (isClosed_equationLocus g)

theorem closure_transition_zero_roots (g : RealGL) {p q : Corner}
    (h : (p,q)∈closure (interiorTransitionGraph g)) :
    (p.2.1.val=0 ↔ q.2.1.val=0) ∧ (p.2.2.val=0 ↔ q.2.2.val=0) := by
  have he : (p,q)∈equationLocus g := closure_transition_subset_equations g h
  have hc : Compatible g p q := he
  exact compatible_zero_roots g hc

theorem closure_transition_line (g : RealGL) {p q : Corner}
    (h : (p,q)∈closure (interiorTransitionGraph g)) (hp : p.2.1.val=0) :
    g∈lineStabilizer := compatible_line_mem g (closure_transition_subset_equations g h) hp

theorem closure_transition_plane (g : RealGL) {p q : Corner}
    (h : (p,q)∈closure (interiorTransitionGraph g)) (hp : p.2.2.val=0) :
    g∈planeStabilizer := compatible_plane_mem g (closure_transition_subset_equations g h) hp

theorem closure_transition_borel (g : RealGL) {p q : Corner}
    (h : (p,q)∈closure (interiorTransitionGraph g))
    (h1 : p.2.1.val=0) (h2 : p.2.2.val=0) : g∈borelStabilizer :=
  compatible_borel_mem g (closure_transition_subset_equations g h) h1 h2

end TernaryPoly.SymmetricSpaceCornerDegeneration
