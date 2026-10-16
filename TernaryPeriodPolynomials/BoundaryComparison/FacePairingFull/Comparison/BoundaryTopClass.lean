module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Faces
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyComplete
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionGeometry
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Incidence
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Orientation
public import TernaryPeriodPolynomials.Topology.TopHomology.ConnectedManifold

@[expose] public section


/-!
# D1: the top homology of the arithmetic boundary `∂M` is spanned by its fundamental class

`BoundaryBase = ∂M` is connected: the upstairs boundary is the union of the closed rational line and
plane faces (`boundary_eq_face_union`), each contractible
(`actual_boundary_face_contractibility`), two of which meet exactly when the line lies in the plane
(`face_inter_nonempty_iff`), and the incidence graph is connected (`OrdinaryIncidence.connected`); `∂M` is
the image of this connected set under the quotient map. With the general theorem
`TopHomology.chains_top_homology_eq_smul`, every class of `H₄(∂M; ℚ)` is a rational multiple of
`boundaryFundamentalClass` (`boundary_top_homology_eq_smul`), so `dim H₄(∂M; ℚ) ≤ 1`.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPoly TernaryPoly.OrdinaryIncidence TernaryPoly.SymmetricSpaceBoundaryFaces
  TernaryPoly.SymmetricSpaceBoundaryFaceTopology TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceBordifiedQuotient TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularBoundaryRestriction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

/-- The faces indexed by the vertices of the incidence graph. -/
def vertexFace : Vertex → Set Glued
  | Sum.inl L => lineFace L
  | Sum.inr P => planeFace P

theorem vertexFace_preconnected (v : Vertex) : IsPreconnected (vertexFace v) := by
  cases v with
  | inl L =>
    have hc := actual_boundary_face_contractibility.1 L
    have : PreconnectedSpace (lineFace L) := inferInstance
    exact isPreconnected_iff_preconnectedSpace.mpr this
  | inr P =>
    have hc := actual_boundary_face_contractibility.2.1 P
    have : PreconnectedSpace (planeFace P) := inferInstance
    exact isPreconnected_iff_preconnectedSpace.mpr this

theorem upstairsBoundary_eq_iUnion : upstairsBoundary = ⋃ v : Vertex, vertexFace v := by
  ext x
  have h := Set.ext_iff.mp boundary_eq_face_union x
  simp only [upstairsBoundary, Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion] at h ⊢
  rw [h]
  constructor
  · rintro (⟨L, hL⟩ | ⟨P, hP⟩)
    · exact ⟨Sum.inl L, hL⟩
    · exact ⟨Sum.inr P, hP⟩
  · rintro ⟨v, hv⟩
    cases v with
    | inl L => exact Or.inl ⟨L, hv⟩
    | inr P => exact Or.inr ⟨P, hv⟩

theorem upstairsBoundary_preconnected : IsPreconnected upstairsBoundary := by
  rw [upstairsBoundary_eq_iUnion]
  refine IsPreconnected.iUnion_of_reflTransGen vertexFace_preconnected ?_
  intro u v
  have hr := connected.preconnected u v
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  refine Relation.ReflTransGen.mono (fun a b hab => ?_) u v hr
  cases a with
  | inl L =>
    cases b with
    | inl L' => exact hab.elim
    | inr P => exact (face_inter_nonempty_iff L P).mpr hab
  | inr P =>
    cases b with
    | inl L =>
      have := (face_inter_nonempty_iff L P).mpr hab
      rw [Set.inter_comm] at this
      exact this
    | inr P' => exact hab.elim


theorem boundary_preconnected_space : PreconnectedSpace BoundaryBase := by
  have hsurj : boundary principalSix = projection principalSix '' upstairsBoundary := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
      exact ⟨x, (boundary_iff x).mpr hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact (boundary_iff x).mp hx
  have h : IsPreconnected (boundary principalSix) := by
    rw [hsurj]
    exact upstairsBoundary_preconnected.image _ (projection_continuous principalSix).continuousOn
  exact isPreconnected_iff_preconnectedSpace.mp h


open TernaryPoly.SymmetricSpaceBoundaryManifold TernaryPoly.SymmetricSpaceBoundaryOrientation
  TernaryPoly.ContractibleSingularHomology in
/-- **`dim H₄(∂M; ℚ) ≤ 1`:** every top class of the arithmetic boundary is a rational multiple of the
boundary fundamental class. -/
theorem boundary_top_homology_eq_smul (c : (chains BoundaryBase).homology 4) :
    ∃ q : ℚ, c = q • boundaryFundamentalClass := by
  have := boundary_preconnected_space
  obtain ⟨q, hq⟩ := TopHomology.chains_top_homology_eq_smul (n := 2) boundaryEuclidean
    boundaryOrientation c
  exact ⟨q, by rw [hq, boundaryFundamentalClass_eq_ordinary]⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
