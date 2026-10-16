module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityGluing

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory Limits TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap RationalLocalOrientation
open EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))

/-- The open-set property quantifies over every charted structure on the literal subtype,
so that iterated restrictions can use their own canonical orientations. -/
def OpenDuality (s : Set B) : Prop :=
  ∀ (cs : ChartedSpace H s), letI := cs; Duality (restrictedProjection p s) V n e

omit [ChartedSpace H B] in
/-- The open-set duality property holds for the empty subset. -/
theorem openDuality_empty : OpenDuality p V n e ∅ := by
  intro cs
  let := cs
  exact duality_empty (restrictedProjection p ∅) V n e

/-- A contained open's complete duality transports to the literal iterated restriction. -/
theorem openDuality_nested (A D : Set B) (hA : IsOpen A) (hAD : A ⊆ D)
    [ChartedSpace H (Subtype.val ⁻¹' A : Set D)]
    (hd : OpenDuality p V n e A) : Duality (nestedProjection p A D) V n e := by
  let : ChartedSpace H A := inferInstanceAs (ChartedSpace H (⟨A,hA⟩ : Opens B))
  exact duality_homeomorph (restrictedProjection p A) V n e (nestedProjection p A D) e
    (nestedSubsetCoverHomeomorph p A D hAD).symm (hd inferInstance)

/-- Actual binary cap gluing applies to arbitrary ambient opens through the proved
nested-covering homeomorphisms, with no assumed orientation comparison. -/
theorem openDuality_union (A D : Set B) (hA : IsOpen A) (hD : IsOpen D)
    (hdA : OpenDuality p V n e A) (hdD : OpenDuality p V n e D)
    (hdI : OpenDuality p V n e (A ∩ D)) : OpenDuality p V n e (A ∪ D) := by
  intro cs
  let := cs
  let S := A ∪ D
  let U : Opens (TopCat.of S) := ⟨Subtype.val ⁻¹' A,hA.preimage continuous_subtype_val⟩
  let W : Opens (TopCat.of S) := ⟨Subtype.val ⁻¹' D,hD.preimage continuous_subtype_val⟩
  let : ChartedSpace H (Subtype.val ⁻¹' A : Set S) := TopologicalSpace.Opens.instChartedSpace U
  let : ChartedSpace H (Subtype.val ⁻¹' D : Set S) := TopologicalSpace.Opens.instChartedSpace W
  let : ChartedSpace H (Subtype.val ⁻¹' (A ∩ D) : Set S) :=
    TopologicalSpace.Opens.instChartedSpace (U ⊓ W)
  have hUW : U ⊔ W = ⊤ := by
    ext x
    exact ⟨fun _ => Set.mem_univ x,fun _ => x.property⟩
  let : LocallyCompactSpace H := e.isClosedEmbedding.locallyCompactSpace
  let : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace H S
  apply duality_twoOpen (restrictedProjection p S) V n e U W hUW
  · exact openDuality_nested p V n e A S hA Set.subset_union_left hdA
  · exact openDuality_nested p V n e D S hD Set.subset_union_right hdD
  · exact openDuality_nested p V n e (A ∩ D) S (hA.inter hD)
      (Set.inter_subset_left.trans Set.subset_union_left) hdI

/-- The actual open-set duality property passes to an increasing union. -/
theorem openDuality_iUnion (A : ℕ → Set B) (hA : ∀ i, IsOpen (A i)) (hm : Monotone A)
    (hd : ∀ i, OpenDuality p V n e (A i)) : OpenDuality p V n e (⋃ i, A i) := by
  intro cs
  let := cs
  let S := ⋃ i, A i
  let U : ℕ → Opens (TopCat.of S) := fun i =>
    ⟨Subtype.val ⁻¹' A i,(hA i).preimage continuous_subtype_val⟩
  let : ∀ i, ChartedSpace H (Subtype.val ⁻¹' A i : Set S) :=
    fun i => TopologicalSpace.Opens.instChartedSpace (U i)
  have hU : Monotone U := fun _ _ hij _ hx => hm hij hx
  have hcover : (⋃ i, (U i : Set (TopCat.of S))) = Set.univ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp x.property
      exact Set.mem_iUnion.mpr ⟨i,hi⟩
  apply duality_increasing (restrictedProjection p S) V n e U hU hcover
  intro i
  exact openDuality_nested p V n e (A i) S (hA i) (Set.subset_iUnion A i) (hd i)

/-- The proved whole-base restriction adapter recovers actual ambient duality. -/
theorem duality_of_openDuality_univ (hd : OpenDuality p V n e Set.univ) : Duality p V n e := by
  let : ChartedSpace H (Set.univ : Set B) := inferInstanceAs (ChartedSpace H (⊤ : Opens B))
  exact duality_homeomorph (restrictedProjection p Set.univ) V n e p e
    (univCoverHomeomorph p) (hd inferInstance)

end TernaryPoly.SingularLocalCompactDuality
