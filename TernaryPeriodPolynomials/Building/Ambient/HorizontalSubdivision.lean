module

public import TernaryPeriodPolynomials.Building.Ambient.HorizontalGeometry
public import TernaryPeriodPolynomials.Building.Ambient.EdgeRetraction
public import TernaryPeriodPolynomials.Building.Ambient.HeightFiltration

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientHorizontalSubdivision
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces
open GoodIntegralNormalization PrimitiveLineHeight IntegralFrameHeightReduction
open AmbientHorizontalGeometry AmbientDependentTriangles AmbientHeightFiltration
open OrientedListChains

local instance : DecidableEq RationalLine := fun _ _ => Classical.propDecidable _

private theorem toFinset_instance_eq (l : List RationalLine) :
    @List.toFinset RationalLine (fun a b => Subtype.instDecidableEq a b) l = l.toFinset := by
  ext x
  simp only [List.mem_toFinset]

/-- The same literal vertex is used for every triangle incident to an ordered edge. -/
def edgeDifference (F : IntegralVector →ₗ[ℤ] ℤ) (U V : RationalLine) : RationalLine :=
  if h : rationalVector (nonnegativeRepresentative F U - nonnegativeRepresentative F V) ≠ 0 then
    vectorLine (rationalVector (nonnegativeRepresentative F U - nonnegativeRepresentative F V)) h
  else U

/-- Install the chosen primitive representatives on every line of an actual integral basis. -/
theorem nonnegative_basis (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) :
    ∃ h : IntegralGL, ∀ j : Fin 3,
      h.val.col j = nonnegativeRepresentative F (augmentedLine g j.castSucc) := by
  apply AmbientEdgeRetraction.exists_basis_columns g
    (fun j => nonnegativeRepresentative F (augmentedLine g j.castSucc))
  · exact fun j => nonnegativeRepresentative_primitive F _
  · exact fun j => nonnegativeRepresentative_span F _

/-- Exact endpoint alignment identifies the universal difference with the frame construction. -/
theorem edgeDifference_eq (F : IntegralVector →ₗ[ℤ] ℤ) (U V : RationalLine)
    (g : IntegralGL) (h0 : g.val.col 0 = nonnegativeRepresentative F U)
    (h1 : g.val.col 1 = nonnegativeRepresentative F V) :
    edgeDifference F U V = differenceLine g := by
  have hv : nonnegativeRepresentative F U - nonnegativeRepresentative F V = differenceVector g := by
    rw [differenceVector,h0,h1]
  have hn := AmbientIndependentTriple.rationalVector_ne_zero_of_primitive (differenceVector_primitive g)
  apply Subtype.ext
  simp only [edgeDifference,hv,dite_eq_left hn]
  exact (differenceLine_val g).symm

/-- A genuine high horizontal edge has one common height-zero difference vertex. -/
theorem edgeDifference_height_zero (F : IntegralVector →ₗ[ℤ] ℤ) (U V : RationalLine)
    (hne : U ≠ V) (hf : {U,V} ∈ ambient) (hh : height F U = height F V) :
    height F (edgeDifference F U V) = 0 := by
  obtain ⟨g,hg0,hg1⟩ := BadEdgeNormalForm.ordered_ambient_edge U V hne (by
    convert hf using 1
    ext x
    simp)
  obtain ⟨h,hs⟩ := nonnegative_basis F g
  have h0 : h.val.col 0 = nonnegativeRepresentative F U := by
    have he := hs 0
    change h.val.col 0 = nonnegativeRepresentative F (augmentedLine g 0) at he
    rwa [hg0] at he
  have h1 : h.val.col 1 = nonnegativeRepresentative F V := by
    have he := hs 1
    change h.val.col 1 = nonnegativeRepresentative F (augmentedLine g 1) at he
    rwa [hg1] at he
  rw [edgeDifference_eq F U V h h0 h1]
  apply difference_height_zero
  rw [h0,h1,nonnegativeRepresentative_value,nonnegativeRepresentative_value,hh]

/-- An ordered full-rank actual ambient triangle admits aligned primitive columns. -/
theorem independent_aligned_basis (F : IntegralVector →ₗ[ℤ] ℤ) (U V W : RationalLine)
    (hf : [U,V,W].toFinset ∈ ambient)
    (hd : Module.finrank ℚ (faceSpan [U,V,W].toFinset) = 3) :
    ∃ g : IntegralGL,
      g.val.col 0 = nonnegativeRepresentative F U ∧
      g.val.col 1 = nonnegativeRepresentative F V ∧
      augmentedLine g 0 = U ∧ augmentedLine g 1 = V ∧ augmentedLine g 2 = W := by
  classical
  let L : Fin 3 → RationalLine := ![U,V,W]
  have he : @Finset.image (Fin 3) RationalLine (fun a b => Subtype.instDecidableEq a b)
      L Finset.univ = [U,V,W].toFinset := by
    ext x
    simp [L,Fin.exists_fin_succ,eq_comm]
  obtain ⟨g,hg⟩ := AmbientIndependentTriple.exists_integralGL_of_finrank_eq_three L
    (by rw [he]; exact hf) (by rw [he]; exact hd)
  obtain ⟨h,hs⟩ := nonnegative_basis F g
  have hcol (j : Fin 3) : h.val.col j = nonnegativeRepresentative F (L j) := by
    rw [hs,hg]
  have hline (j : Fin 3) : augmentedLine h j.castSucc = L j := by
    apply Subtype.ext
    rw [columnLine_span,hcol]
    exact nonnegativeRepresentative_span F (L j)
  exact ⟨h,hcol 0,hcol 1,hline 0,hline 1,hline 2⟩

/-- Coning an incident independent triangle to the common difference gives an actual tetrahedron. -/
theorem incident_geometry (F : IntegralVector →ₗ[ℤ] ℤ) (U V W : RationalLine)
    (hf : [U,V,W].toFinset ∈ ambient)
    (hd : Module.finrank ℚ (faceSpan [U,V,W].toFinset) = 3) :
    [edgeDifference F U V,U,V,W].toFinset ∈ ambient ∧
      Module.finrank ℚ (faceSpan [edgeDifference F U V,U,W].toFinset) = 3 ∧
      Module.finrank ℚ (faceSpan [edgeDifference F U V,V,W].toFinset) = 3 := by
  classical
  obtain ⟨g,h0,h1,g0,g1,g2⟩ := independent_aligned_basis F U V W hf hd
  rw [edgeDifference_eq F U V g h0 h1,← g0,← g1,← g2]
  refine ⟨?_,?_,?_⟩
  · convert horizontal_tetrahedron g using 1
    ext x
    simp
  · obtain ⟨⟨h,hh0,hh1,hh2⟩,_⟩ := horizontal_replacement_bases g
    rw [← hh0,← hh1,← hh2]
    apply Nat.le_antisymm (faceSpan_finrank_le_three _)
    have hb := basis_face_finrank_ge h
    rwa [toFinset_instance_eq] at hb
  · obtain ⟨_,⟨h,hh0,hh1,hh2⟩⟩ := horizontal_replacement_bases g
    rw [← hh0,← hh1,← hh2]
    apply Nat.le_antisymm (faceSpan_finrank_le_three _)
    have hb := basis_face_finrank_ge h
    rwa [toFinset_instance_eq] at hb

/-- The common difference provides the exact local input for finite high-edge elimination. -/
theorem horizontal_input (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hN : 0 < N)
    (U V : RationalLine) (hne : U ≠ V) (hf : {U,V} ∈ ambient)
    (hU : height F U = N) (hV : height F V = N) :
    ∃ D : RationalLine, height F D < N ∧ ∀ W : RationalLine,
      [U,V,W].Nodup → Allowed (bounded F N) [U,V,W] →
      Module.finrank ℚ (faceSpan [U,V,W].toFinset) = 3 →
      Allowed (bounded F N) [D,U,V,W] ∧
      Module.finrank ℚ (faceSpan [D,U,W].toFinset) = 3 ∧
      Module.finrank ℚ (faceSpan [D,V,W].toFinset) = 3 := by
  classical
  have hD := edgeDifference_height_zero F U V hne hf (hU.trans hV.symm)
  refine ⟨edgeDifference F U V,by omega,?_⟩
  intro W _ hW hd
  obtain ⟨hface,hheight⟩ := (allowed_bounded_iff F N [U,V,W]).mp hW
  have hface' : [U,V,W].toFinset ∈ ambient := hface.resolve_left (by simp)
  obtain ⟨hcone,hleft,hright⟩ := incident_geometry F U V W hface' hd
  refine ⟨(allowed_bounded_iff F N _).mpr ⟨Or.inr hcone,?_⟩,hleft,hright⟩
  intro L hL
  rcases List.mem_cons.mp hL with rfl | hL
  · omega
  · exact hheight L hL

end TernaryPoly.AmbientHorizontalSubdivision
