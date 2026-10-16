module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingFrames
public import Mathlib.Topology.Gluing
public import TernaryPeriodPolynomials.Topology.OpenGluing.GluingSeparation

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRationalGluing
open SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
open TopologicalSpace Topology

/-- Actual open gluing data on all rational frames, with the four overlap cases. -/
def glueCore : TopCat.GlueData.MkCore where
  J := RationalGL
  U := fun _ => TopCat.of Corner
  V := overlap
  t g h := TopCat.ofHom ⟨pairTransition g h,(pairTransition g h).continuous⟩
  V_id := overlap_self
  t_id g := by funext p; exact pairTransition_self g p
  t_inter {g} {h} k p hp := pairTransition_inter g h k p hp
  cocycle := pairTransition_cocycle

/-- The genuine Mathlib gluing construction, with no assumed transition or cocycle laws. -/
def glueData : TopCat.GlueData := TopCat.GlueData.mk' glueCore

abbrev Glued := (glueData.toGlueData.glued : Type)

def chart (g : RationalGL) : Corner → Glued := glueData.toGlueData.ι g

theorem chart_isOpenEmbedding (g : RationalGL) : IsOpenEmbedding (chart g) :=
  glueData.ι_isOpenEmbedding g

theorem continuous_chart (g : RationalGL) : Continuous (chart g) := (chart_isOpenEmbedding g).continuous

theorem chart_injective (g : RationalGL) : Function.Injective (chart g) :=
  (chart_isOpenEmbedding g).injective

theorem chart_range_open (g : RationalGL) : IsOpen (Set.range (chart g)) :=
  (chart_isOpenEmbedding g).isOpen_range

theorem chart_jointly_surjective (x : Glued) : ∃ g p, chart g p=x := glueData.ι_jointly_surjective x

theorem chart_cover : (⋃ g : RationalGL,Set.range (chart g))=Set.univ := by
  ext x
  simp only [Set.mem_iUnion,Set.mem_range,Set.mem_univ,iff_true]
  exact chart_jointly_surjective x

theorem countable_chart_cover : (Set.range (fun g : RationalGL => Set.range (chart g))).Countable := by
  let : Countable RationalGL := rationalGL_countable
  exact Set.countable_range _

/-- Equality in the actual glued space is exactly the overlap/transition relation. -/
theorem chart_eq_iff (g h : RationalGL) (p q : Corner) :
    chart g p=chart h q ↔ ∃ hp : p∈overlap g h,(pairTransition g h ⟨p,hp⟩).val=q := by
  rw [show chart g p=chart h q ↔ glueData.Rel ⟨g,p⟩ ⟨h,q⟩ from
    glueData.ι_eq_iff_rel g h p q]
  change (∃ x : overlap g h,x.val=p ∧ (pairTransition g h x).val=q) ↔ _
  constructor
  · rintro ⟨⟨x,hx⟩,h,he⟩
    change x=p at h
    subst x
    exact ⟨hx,he⟩
  · rintro ⟨hp,he⟩
    exact ⟨⟨p,hp⟩,rfl,he⟩

theorem chart_transition (g h : RationalGL) (p : overlap g h) :
    chart g p.val=chart h (pairTransition g h p).val :=
  (chart_eq_iff g h _ _).mpr ⟨p.property,rfl⟩

/-- The source of a chart-image intersection is precisely the prescribed open overlap. -/
theorem chart_preimage_range (g h : RationalGL) :
    chart g ⁻¹' Set.range (chart h)=(overlap g h : Set Corner) := by
  ext p
  constructor
  · rintro ⟨q,hq⟩
    exact ((chart_eq_iff g h p q).mp hq.symm).choose
  · intro hp
    exact ⟨(pairTransition g h ⟨p,hp⟩).val,(chart_transition g h ⟨p,hp⟩).symm⟩

instance gluedSecondCountable : SecondCountableTopology Glued := by
  let : Countable RationalGL := rationalGL_countable
  let : Countable glueData.J := rationalGL_countable
  let : ∀ i, SecondCountableTopology (glueData.U i) := fun _ => inferInstanceAs (SecondCountableTopology Corner)
  exact TernaryPoly.OpenGluingSeparation.secondCountable glueData

end TernaryPoly.SymmetricSpaceRationalGluing
