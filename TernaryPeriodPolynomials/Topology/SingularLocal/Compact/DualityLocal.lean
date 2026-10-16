module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityEuclidean
public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.CompactCap
public import TernaryPeriodPolynomials.Topology.Covering.EuclideanCharts

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory Limits TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap SingularLocalConstant RationalLocalOrientation
open EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))

/-- A genuine continuous section transfers the full actual constant-coefficient duality
property to the literal local system of an arbitrary rational representation. -/
theorem duality_section (s : B ⟶ E) (hs : s ≫ p = 𝟙 B)
    (hd : Duality (𝟙 B) (constantRep (ModuleCat.of ℚ V)) n e) : Duality p V n e := by
  constructor
  · intro o a b hab
    have := hd.1 o a b hab
    exact SingularLocalSection.section_compactCap_isIso p s hs V n e o a b hab
  · intro a ha
    exact (hd.2 a ha).of_iso (SingularLocalSection.compactCohomologyIso p s hs V a)

omit [ChartedSpace H B] in
/-- Every open subset inside one genuine Euclidean covering chart has actual local-coefficient
compact-cap duality and upper-degree compact-cohomology vanishing. -/
theorem openDuality_in_chart (U : Opens B) (h : U ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (s : CoveringEuclideanCharts.Section p U) (D : Set B) (hD : IsOpen D) (hDU : D ⊆ U) :
    OpenDuality p V n e D := by
  intro cs
  let := cs
  let A : Set U := Subtype.val ⁻¹' D
  have hA : IsOpen A := hD.preimage continuous_subtype_val
  let t := h '' A
  have ht : IsOpen t := h.isOpenMap A hA
  let hd : D ≃ₜ t := (nestedSubsetCoverHomeomorph (G := G) p D U hDU).base.symm.trans (h.image A)
  let sd := CoveringEuclideanCharts.Section.restrict p s (⟨D,hD⟩ : Opens B) hDU
  exact duality_section (restrictedProjection p D) V n e sd.map sd.right_inv
    (duality_homeomorphicEuclideanOpen (ModuleCat.of ℚ V) n e t ht hd)

end TernaryPoly.SingularLocalCompactDuality
