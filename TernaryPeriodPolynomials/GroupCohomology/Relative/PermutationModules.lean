module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.PermutationIndices

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativePermutationModules
open OrdinaryIncidence OrdinaryIncidenceChains OrdinaryRelativeGraph
open RelativePermutationQuotient RelativePermutationIndices
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The finite direct sum of the bad-line and bad-plane permutation modules. -/
abbrev VertexModule := (BadLine →₀ ℚ) × (BadPlane →₀ ℚ)
/-- The finite direct sum of bad-bad and bad-Good flag permutation modules. -/
abbrev EdgeModule := (BB →₀ ℚ) × (BG →₀ ℚ)

/-- Explicit coordinates for the actual relative vertex quotient. -/
def vertexEquiv : R₀ ≃ₗ[ℚ] VertexModule :=
  (quotientEquiv goodVertex VertexGood goodVertex_range).trans
    ((Finsupp.domLCongr vertexSplit).trans (Finsupp.sumFinsuppLEquivProdFinsupp ℚ))
/-- Explicit coordinates for the actual relative edge quotient. -/
def edgeEquiv : R₁ ≃ₗ[ℚ] EdgeModule :=
  (quotientEquiv goodEdge EdgeGood goodEdge_range).trans
    ((Finsupp.domLCongr edgeSplit).trans (Finsupp.sumFinsuppLEquivProdFinsupp ℚ))

theorem vertexEquiv_mk (c : VertexChains) :
    vertexEquiv (Submodule.Quotient.mk c) = Finsupp.sumFinsuppLEquivProdFinsupp ℚ
      (Finsupp.domLCongr (R := ℚ) vertexSplit (project VertexGood c)) := rfl
theorem edgeEquiv_mk (c : EdgeChains) :
    edgeEquiv (Submodule.Quotient.mk c) = Finsupp.sumFinsuppLEquivProdFinsupp ℚ
      (Finsupp.domLCongr (R := ℚ) edgeSplit (project EdgeGood c)) := rfl

theorem vertexEquiv_single_good (v : Vertex) (h : VertexGood v) (q : ℚ) :
    vertexEquiv (Submodule.Quotient.mk (Finsupp.single v q)) = 0 := by
  rw [vertexEquiv_mk,project_single,dite_eq_left h,map_zero,map_zero]
theorem edgeEquiv_single_good (e : Edge) (h : EdgeGood e) (q : ℚ) :
    edgeEquiv (Submodule.Quotient.mk (Finsupp.single e q)) = 0 := by
  rw [edgeEquiv_mk,project_single,dite_eq_left h,map_zero,map_zero]

theorem vertexEquiv_single_badLine (L : BadLine) (q : ℚ) :
    vertexEquiv (Submodule.Quotient.mk (Finsupp.single (.inl L.val) q)) =
      (Finsupp.single L q,0) := by
  rw [vertexEquiv_mk,project_single,dite_eq_right (show ¬VertexGood (.inl L.val) from L.property),Finsupp.domLCongr_single]
  exact split_single_inl L q

theorem vertexEquiv_single_badPlane (P : BadPlane) (q : ℚ) :
    vertexEquiv (Submodule.Quotient.mk (Finsupp.single (.inr P.val) q)) =
      (0,Finsupp.single P q) := by
  rw [vertexEquiv_mk,project_single,dite_eq_right (show ¬VertexGood (.inr P.val) from P.property),Finsupp.domLCongr_single]
  exact split_single_inr P q

theorem edgeEquiv_single_bb (e : BB) (q : ℚ) :
    edgeEquiv (Submodule.Quotient.mk (Finsupp.single e.val q)) = (Finsupp.single e q,0) := by
  rw [edgeEquiv_mk,project_single,dite_eq_right (show ¬EdgeGood e.val from e.property.1),Finsupp.domLCongr_single]
  simp only [edgeSplit,Equiv.coe_fn_mk,dite_eq_right e.property.2,split_single_inl]

theorem edgeEquiv_single_bg (e : BG) (q : ℚ) :
    edgeEquiv (Submodule.Quotient.mk (Finsupp.single e.val q)) = (0,Finsupp.single e q) := by
  rw [edgeEquiv_mk,project_single,dite_eq_right (show ¬EdgeGood e.val from e.property.1),Finsupp.domLCongr_single]
  simp only [edgeSplit,Equiv.coe_fn_mk,dite_eq_left e.property.2,split_single_inr]

/-- These are the literal independent permutations of the two complementary index types. -/
def vertexLinear (g : GoodBuilding.K) : VertexModule ≃ₗ[ℚ] VertexModule :=
  (Finsupp.domLCongr (badLineAction g)).prodCongr (Finsupp.domLCongr (badPlaneAction g))
def edgeLinear (g : GoodBuilding.K) : EdgeModule ≃ₗ[ℚ] EdgeModule :=
  (Finsupp.domLCongr (bbAction g)).prodCongr (Finsupp.domLCongr (bgAction g))

/-- Actual relative vertex quotient action becomes the displayed bad-line/bad-plane permutations. -/
theorem vertexEquiv_equivariant (g : GoodBuilding.K) (x : R₀) :
    vertexEquiv (OrdinaryRelativeGraphAction.vertexAction g x) = vertexLinear g (vertexEquiv x) := by
  refine Submodule.Quotient.induction_on goodVertices x ?_
  intro c
  rw [OrdinaryRelativeGraphAction.vertexAction_mk,vertexEquiv_mk,vertexEquiv_mk]
  change Finsupp.sumFinsuppLEquivProdFinsupp ℚ
    (Finsupp.domLCongr (R := ℚ) vertexSplit
      (project VertexGood (Finsupp.domLCongr (R := ℚ) (OrdinaryIncidence.vertexAction g) c))) = _
  rw [project_natural VertexGood _ (VertexGood_action g),
    reindex_natural vertexSplit _ _ (vertexSplit_natural g),split_natural]
  rfl

/-- Actual relative edge quotient action becomes the displayed BB/BG flag permutations. -/
theorem edgeEquiv_equivariant (g : GoodBuilding.K) (x : R₁) :
    edgeEquiv (OrdinaryRelativeGraphAction.edgeAction g x) = edgeLinear g (edgeEquiv x) := by
  refine Submodule.Quotient.induction_on goodEdges x ?_
  intro c
  rw [OrdinaryRelativeGraphAction.edgeAction_mk,edgeEquiv_mk,edgeEquiv_mk]
  change Finsupp.sumFinsuppLEquivProdFinsupp ℚ
    (Finsupp.domLCongr (R := ℚ) edgeSplit
      (project EdgeGood (Finsupp.domLCongr (R := ℚ) (OrdinaryIncidenceChains.edgeAction g) c))) = _
  rw [project_natural EdgeGood _ (EdgeGood_action g),
    reindex_natural edgeSplit _ _ (edgeSplit_natural g),split_natural]
  rfl

/-- The bad-vertex permutation maps form a genuine representation of the original K. -/
def vertexRepresentation : Representation ℚ GoodBuilding.K VertexModule where
  toFun g := (vertexLinear g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro c
    obtain ⟨x,rfl⟩ := vertexEquiv.surjective c
    change vertexLinear 1 (vertexEquiv x) = vertexEquiv x
    rw [← vertexEquiv_equivariant,map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    obtain ⟨x,rfl⟩ := vertexEquiv.surjective c
    change vertexLinear (g*h) (vertexEquiv x) = vertexLinear g (vertexLinear h (vertexEquiv x))
    rw [← vertexEquiv_equivariant,← vertexEquiv_equivariant,← vertexEquiv_equivariant,map_mul]
    rfl

/-- The two relative flag permutation maps likewise form a genuine K representation. -/
def edgeRepresentation : Representation ℚ GoodBuilding.K EdgeModule where
  toFun g := (edgeLinear g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro c
    obtain ⟨x,rfl⟩ := edgeEquiv.surjective c
    change edgeLinear 1 (edgeEquiv x) = edgeEquiv x
    rw [← edgeEquiv_equivariant,map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    obtain ⟨x,rfl⟩ := edgeEquiv.surjective c
    change edgeLinear (g*h) (edgeEquiv x) = edgeLinear g (edgeLinear h (edgeEquiv x))
    rw [← edgeEquiv_equivariant,← edgeEquiv_equivariant,← edgeEquiv_equivariant,map_mul]
    rfl

/-- The actual relative modules are the four asserted permutation modules, equivariantly. -/
theorem permutation_module_identification :
    (∀ g x, vertexEquiv (OrdinaryRelativeGraphAction.vertexAction g x) = vertexRepresentation g (vertexEquiv x)) ∧
    (∀ g x, edgeEquiv (OrdinaryRelativeGraphAction.edgeAction g x) = edgeRepresentation g (edgeEquiv x)) :=
  ⟨vertexEquiv_equivariant,edgeEquiv_equivariant⟩

end TernaryPoly.RelativePermutationModules
