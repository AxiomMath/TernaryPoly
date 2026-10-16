module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ChartsBoundary

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryCharts
open Topology SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing
open scoped Manifold

/-- The entire image of an actual rational chart has explicit product collar coordinates. -/
def collarHomeomorph (g : RationalGL) : ProductModel ≃ₜ Set.range (chart g) :=
  cornerProductHomeomorph.symm.trans (chart_isOpenEmbedding g).isEmbedding.toHomeomorph

def collar (g : RationalGL) (p : ProductModel) : Glued := (collarHomeomorph g p).val

@[simp] theorem collar_eq (g : RationalGL) (p : ProductModel) :
    collar g p=chart g (cornerProductHomeomorph.symm p) := rfl

theorem collar_isOpenEmbedding (g : RationalGL) : IsOpenEmbedding (collar g) :=
  (chart_isOpenEmbedding g).comp cornerProductHomeomorph.symm.isOpenEmbedding

@[simp] theorem collar_range (g : RationalGL) : Set.range (collar g)=Set.range (chart g) := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact (collarHomeomorph g p).property
  · intro hx
    exact ⟨(collarHomeomorph g).symm ⟨x,hx⟩,
      congrArg Subtype.val ((collarHomeomorph g).apply_symm_apply ⟨x,hx⟩)⟩

/-- Radius zero in the local collar is exactly the actual manifold boundary. -/
theorem collar_zero_iff (g : RationalGL) (p : ProductModel) :
    collar g p∈(𝓡∂ 5).boundary Glued ↔ p.2.val=0 := by
  have h := Set.ext_iff.mp (chart_preimage_boundary g) (cornerProductHomeomorph.symm p)
  change collar g p∈(𝓡∂ 5).boundary Glued ↔
    (cornerProductHomeomorph.symm p).2.1.val=0 ∨
    (cornerProductHomeomorph.symm p).2.2.val=0 at h
  rw [←cornerProduct_zero,Homeomorph.apply_symm_apply] at h
  exact h

/-- Every positive collar radius lies in the actual embedded symmetric space. -/
theorem collar_positive_iff (g : RationalGL) (p : ProductModel) :
    collar g p∈Set.range embedding ↔ 0<p.2.val := by
  have h := Set.ext_iff.mp (chart_preimage_embedding g) (cornerProductHomeomorph.symm p)
  change collar g p∈Set.range embedding ↔ _ at h
  rw [←cornerProduct_positive,Homeomorph.apply_symm_apply] at h
  exact h

/-- The zero-radius slice of the chart collar. -/
def boundarySlice (g : RationalGL) (v : BoundaryCoordinates) : Glued :=
  collar g (v,⟨0,le_rfl⟩)

theorem boundarySlice_isEmbedding (g : RationalGL) : IsEmbedding (boundarySlice g) :=
  (collar_isOpenEmbedding g).isEmbedding.comp (isEmbedding_prodMkLeft (⟨0,le_rfl⟩ : HalfLine))

/-- The collar's boundary slice parametrizes exactly the boundary points in that chart. -/
theorem boundarySlice_range (g : RationalGL) :
    Set.range (boundarySlice g)=Set.range (chart g) ∩ (𝓡∂ 5).boundary Glued := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨(collarHomeomorph g (v,⟨0,le_rfl⟩)).property,
      (collar_zero_iff g (v,⟨0,le_rfl⟩)).mpr rfl⟩
  · rintro ⟨hc,hb⟩
    obtain ⟨p,hp⟩ := (Set.ext_iff.mp (collar_range g) x).mpr hc
    have hz : p.2.val=0 := (collar_zero_iff g p).mp (hp.symm ▸ hb)
    have he : (p.1,(⟨0,le_rfl⟩ : HalfLine))=p := by
      apply Prod.ext
      · rfl
      · exact Subtype.ext hz.symm
    refine ⟨p.1,?_⟩
    change collar g (p.1,⟨0,le_rfl⟩)=x
    rw [he,hp]

/-- Every boundary point has a real four-dimensional slice and a nonnegative collar radius. -/
theorem exists_local_collar (x : Glued) (hx : x∈(𝓡∂ 5).boundary Glued) :
    ∃ g : RationalGL, ∃ v : BoundaryCoordinates, boundarySlice g v=x := by
  obtain ⟨g,p,hp⟩ := chart_jointly_surjective x
  have h : x∈Set.range (boundarySlice g) :=
    (Set.ext_iff.mp (boundarySlice_range g) x).mpr ⟨⟨p,hp⟩,hx⟩
  obtain ⟨v,hv⟩ := h
  exact ⟨g,v,hv⟩

end TernaryPoly.SymmetricSpaceBoundaryCharts
