module

public import TernaryPeriodPolynomials.Building.Primitive.LineHeight
public import TernaryPeriodPolynomials.Building.OrientedChain.ListChains

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientHeightFiltration
open ModThreeGoodAction AugmentedFrameComplex PrimitiveLineHeight OrientedListChains

local instance : DecidableEq RationalLine := fun _ _ => Classical.propDecidable _

/-- The actual ambient full subcomplex on primitive lines of height at most `N`. -/
def bounded (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) :
    PreAbstractSimplicialComplex RationalLine where
  faces := {s | s ∈ ambient ∧ ∀ L ∈ s, height F L ≤ N}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(ambient.isRelLowerSet_faces hs.1).1,?_⟩
    intro t hts ht
    exact ⟨(ambient.isRelLowerSet_faces hs.1).2 hts ht,fun L hL => hs.2 L (hts hL)⟩

theorem bounded_le_ambient (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) :
    bounded F N ≤ ambient := fun _ h => h.1

theorem bounded_mono (F : IntegralVector →ₗ[ℤ] ℤ) {M N : ℕ} (hMN : M ≤ N) :
    bounded F M ≤ bounded F N := fun _ h => ⟨h.1,fun L hL => (h.2 L hL).trans hMN⟩

theorem allowed_bounded_iff (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (l : List RationalLine) :
    Allowed (bounded F N) l ↔ Allowed ambient l ∧ ∀ L ∈ l, height F L ≤ N := by
  classical
  constructor
  · rintro (rfl | hl)
    · exact ⟨Or.inl rfl,by simp⟩
    · exact ⟨Or.inr hl.1,fun L hL => hl.2 L (List.mem_toFinset.mpr hL)⟩
  · rintro ⟨hl,hheight⟩
    rcases hl with rfl | hl
    · exact Or.inl rfl
    · exact Or.inr ⟨hl,fun L hL => hheight L (List.mem_toFinset.mp hL)⟩

/-- A reduced triangle has full rational rank or lies strictly below the current height. -/
def ReducedTriangle (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (l : List RationalLine) : Prop :=
  Module.finrank ℚ (faceSpan l.toFinset) = 3 ∨ ∀ L ∈ l, height F L < N

/-- The finite span of literal bounded reduced triangles. -/
def reducedTriangles (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) : Submodule ℚ (Chain RationalLine) :=
  Submodule.span ℚ {c | ∃ l : List RationalLine,
    l.length = 3 ∧ Allowed (bounded F N) l ∧ ReducedTriangle F N l ∧ simplex l = c}

theorem simplex_mem_reducedTriangles (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (l : List RationalLine) (hlen : l.length = 3) (hl : Allowed (bounded F N) l)
    (hr : ReducedTriangle F N l) : simplex l ∈ reducedTriangles F N :=
  Submodule.subset_span ⟨l,hlen,hl,hr,rfl⟩

theorem reducedTriangles_le_chains (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) :
    reducedTriangles F N ≤ chains (bounded F N) 3 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hlen,hl,_,rfl⟩
  change simplex l ∈ chains (bounded F N) 3
  simpa only [hlen] using simplex_mem_chains (bounded F N) l hl

/-- Every finite face spans at most the three-dimensional rational ambient space. -/
theorem faceSpan_finrank_le_three (s : Finset RationalLine) :
    Module.finrank ℚ (faceSpan s) ≤ 3 := by
  have h := Submodule.finrank_le (faceSpan s)
  simpa [ModThreeGoodAction.Space] using h

end TernaryPoly.AmbientHeightFiltration
