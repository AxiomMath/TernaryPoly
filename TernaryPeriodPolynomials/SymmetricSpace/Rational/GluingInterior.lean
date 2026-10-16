module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingGlueData

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRationalGluing
open SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
open SymmetricSpaceRationalCharts Topology

/-- The actual positive-form space embeds through the identity rational frame. -/
def embedding (S : Space) : Glued := chart 1 (chartEmbedding 1 S)

/-- All rational charts give the very same point of the actual embedded symmetric space. -/
theorem chart_embedding (g : RationalGL) (S : Space) :
    chart g (chartEmbedding g S)=embedding S := by
  have h := chart_transition g 1 (chartPoint g 1 S)
  rw [pairTransition_chart] at h
  exact h

theorem embedding_isOpenEmbedding : IsOpenEmbedding embedding :=
  (chart_isOpenEmbedding 1).comp (chartEmbedding_isOpenEmbedding 1)

theorem continuous_embedding : Continuous embedding := embedding_isOpenEmbedding.continuous

theorem embedding_injective : Function.Injective embedding := embedding_isOpenEmbedding.injective

theorem embedding_range_open : IsOpen (Set.range embedding) := embedding_isOpenEmbedding.isOpen_range

/-- The preimage of the actual symmetric space in every corner is exactly its positive interior. -/
theorem chart_preimage_embedding (g : RationalGL) :
    chart g ⁻¹' Set.range embedding=cornerInterior := by
  ext p
  constructor
  · rintro ⟨S,hS⟩
    have he : chartEmbedding g S=p := chart_injective g ((chart_embedding g S).trans hS)
    exact he ▸ (chartHomeomorph g S).property
  · intro hp
    obtain ⟨S,hS⟩ := (chartEmbedding_range g).symm ▸ hp
    exact ⟨S,by rw [←hS,chart_embedding]⟩

/-- The actual symmetric space is dense in the complete rational corner gluing. -/
theorem embedding_denseRange : DenseRange embedding := by
  intro x
  obtain ⟨g,p,rfl⟩ := chart_jointly_surjective x
  apply map_mem_closure (continuous_chart g) (cornerInterior_dense p)
  intro q hq
  exact (show q ∈ chart g ⁻¹' Set.range embedding from (chart_preimage_embedding g).symm ▸ hq)

end TernaryPoly.SymmetricSpaceRationalGluing
