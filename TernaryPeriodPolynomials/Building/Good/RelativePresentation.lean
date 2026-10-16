module

public import TernaryPeriodPolynomials.Building.Good.RelativePresentationEvaluation

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodRelativePresentation
open ModThreeGoodAction AugmentedFrameComplex GoodRelativeChains
open GoodRelativePresentationFrames GoodRelativePresentationEvaluation
open ReferenceCoefficientMatrices OrientedListChains

abbrev ReferenceQuotient := GoodOrbitRelations.FreeOrbit ⧸ GoodOrbitRelations.relations

/-- Further quotient orientation classes by the actual norm relations. -/
def orientationToReference : OrientationQuotient →ₗ[ℚ] ReferenceQuotient :=
  orientations.liftQ GoodOrbitRelations.relations.mkQ (by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr (orientations_le_relations hx))

@[simp] theorem orientationToReference_deltaClass (g : K) :
    orientationToReference (deltaClass g) = GoodOrbitRelations.relations.mkQ (GoodOrbitRelations.delta g) := rfl

/-- Evaluate genuine oriented chains in the quotient by all exact reference relations. -/
def fullEvaluator : Chain RationalLine →ₗ[ℚ] ReferenceQuotient :=
  orientationToReference.comp evaluator

@[simp] theorem fullEvaluator_triangle (g : K) :
    fullEvaluator (triangle g).val = GoodOrbitRelations.relations.mkQ (GoodOrbitRelations.delta g) := by
  change orientationToReference (evaluator (triangle g).val) = _
  rw [evaluator_triangle,orientationToReference_deltaClass]

theorem fullEvaluator_proper_chain {c : Chain RationalLine} (hc : c ∈ chains properGood 3) :
    fullEvaluator c = 0 := by
  change orientationToReference (evaluator c) = 0
  rw [evaluator_proper_chain hc,map_zero]

def fullGoodEvaluator : GoodTwo →ₗ[ℚ] ReferenceQuotient := fullEvaluator.comp GoodTwo.subtype

@[simp] theorem fullGoodEvaluator_triangle (g : K) :
    fullGoodEvaluator (triangle g) = GoodOrbitRelations.relations.mkQ (GoodOrbitRelations.delta g) :=
  fullEvaluator_triangle g

@[simp] theorem fullGoodEvaluator_proper (p : ProperTwo) : fullGoodEvaluator (properInclusion p) = 0 :=
  fullEvaluator_proper_chain p.property

/-- The reference norm is the evaluator of the actual tetrahedron boundary. -/
theorem fullEvaluator_tetrahedron_boundary (g : K) :
    fullEvaluator (boundary (simplex (tetrahedronList g.val))) = 0 := by
  have hn : GoodOrbitRelations.relations.mkQ (GoodOrbitRelations.normRelation g) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span (Or.inl (Or.inl ⟨g,rfl⟩))
  have he := congrArg fullGoodEvaluator (triangle_norm_boundary g)
  simp only [map_add,fullGoodEvaluator_triangle,fullGoodEvaluator_proper,add_zero] at he
  have hn' : GoodOrbitRelations.relations.mkQ (GoodOrbitRelations.delta g) +
      GoodOrbitRelations.relations.mkQ (GoodOrbitRelations.delta (g*aK)) +
      GoodOrbitRelations.relations.mkQ (GoodOrbitRelations.delta (g*aK^2)) = 0 := by
    simpa only [GoodOrbitRelations.normRelation,map_add] using hn
  rw [hn'] at he
  exact he.symm

/-- Every actual Good tetrahedron boundary vanishes, including all orders and degeneracies. -/
theorem fullEvaluator_good_four_boundary (l : List RationalLine) (hlen : l.length = 4)
    (hl : Allowed good l) : fullEvaluator (boundary (simplex l)) = 0 := by
  let : DecidableEq RationalLine := Classical.decEq _
  by_cases hn : l.Nodup
  · have hf : l.toFinset ∈ good := by
      rcases hl with rfl | hl
      · simp at hlen
      · exact hl
    obtain ⟨g,hg⟩ := good_tetrahedron_perm l hlen hn hf
    obtain ⟨q,hq⟩ := OrientedSimplexPermutation.simplex_perm_smul hg
    rw [hq,map_smul,map_smul,fullEvaluator_tetrahedron_boundary,smul_zero]
  · rw [simplex_eq_zero_of_not_nodup l hn,map_zero,map_zero]

/-- Finite actual Good degree-three chains have zero boundary evaluator. -/
theorem fullEvaluator_good_boundary {c : Chain RationalLine} (hc : c ∈ chains good 4) :
    fullEvaluator (boundary c) = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    exact fullEvaluator_good_four_boundary l hlen hl
  | zero => rw [map_zero,map_zero]
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => simp only [map_smul,ih,smul_zero]

/-- Both actual proper chains and actual tetrahedron boundaries lie in the evaluator kernel. -/
theorem nullSubmodule_le_ker : nullSubmodule ≤ LinearMap.ker fullGoodEvaluator := by
  apply sup_le
  · rintro x ⟨p,rfl⟩
    exact fullGoodEvaluator_proper p
  · rintro x ⟨c,rfl⟩
    exact fullEvaluator_good_boundary c.property

/-- The inverse presentation map uses the actual relative Good chain quotient. -/
def presentationInverse : RelativeBoundaryTwo →ₗ[ℚ] ReferenceQuotient :=
  nullSubmodule.liftQ fullGoodEvaluator nullSubmodule_le_ker

@[simp] theorem presentationInverse_quotientMap (x : GoodTwo) :
    presentationInverse (quotientMap x) = fullEvaluator x.val := rfl

/-- The constructed inverse recovers the literal free-module quotient on every finite frame combination. -/
theorem presentationInverse_orbitMap :
    presentationInverse.comp GoodRelativeChains.orbitMap = GoodOrbitRelations.relations.mkQ := by
  apply Finsupp.lhom_ext
  intro g q
  have h : Finsupp.single g q = q • GoodOrbitRelations.delta g := by simp [GoodOrbitRelations.delta]
  rw [h,map_smul,map_smul]
  change q • presentationInverse (GoodRelativeChains.orbitMap (GoodOrbitRelations.delta g)) = _
  rw [GoodRelativeChains.orbitMap_delta,presentationInverse_quotientMap,fullEvaluator_triangle]

/-- Exact completeness of the three reference relations for the actual relative Good chains. -/
theorem orbitMap_ker : LinearMap.ker GoodRelativeChains.orbitMap = GoodOrbitRelations.relations := by
  apply le_antisymm
  · intro x hx
    have he := LinearMap.congr_fun presentationInverse_orbitMap x
    have hx' : GoodRelativeChains.orbitMap x = 0 := hx
    change presentationInverse (GoodRelativeChains.orbitMap x) = GoodOrbitRelations.relations.mkQ x at he
    rw [hx',map_zero] at he
    exact (Submodule.Quotient.mk_eq_zero _).mp he.symm
  · exact GoodRelativeChains.relations_le_ker

end TernaryPoly.GoodRelativePresentation
