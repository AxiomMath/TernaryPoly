module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Representatives

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory Limits HomologicalComplex
open SingularLocalCoefficient SingularLocalHomology SingularLocalSupport SingularLocalCompactCap
open FreeActionLinearization CoveringSingularOrbits RationalLocalOrientation
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsEmpty B]

/-- Actual geometric local cochains on an empty base form the zero cochain complex. -/
theorem empty_localCochains_isZero : IsZero (localCochains p hp.out V) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change c = 0
  funext σ
  exact False.elim (isEmptyElim (atVertex σ) : False)

/-- Actual local chains on an empty base form the zero chain complex. -/
theorem empty_localChains_isZero : IsZero (coveringLocalChains p V) := by
  let : IsCancelSMul G E := hp.out.isCancelSMul
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change c = 0
  apply DFinsupp.ext
  intro σ
  exact False.elim (isEmptyElim (atVertex σ) : False)

/-- Every actual fixed-support cochain complex on an empty base vanishes. -/
theorem empty_supportCochains_isZero (K : Set B) : IsZero (supportCochains p V K) :=
  IsZero.of_mono (supportInclusion p V K) (empty_localCochains_isZero p V)

/-- Every actual fixed-support cohomology group on an empty base vanishes. -/
theorem empty_supportCohomology_isZero (K : Set B) (a : ℕ) :
    IsZero ((supportCochains p V K).homology a) :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) a).map_isZero (empty_supportCochains_isZero p V K)

/-- Actual compact-support cohomology on an empty base vanishes in every degree. -/
theorem empty_compactCohomology_isZero (a : ℕ) : IsZero (compactCohomology p V a) := by
  have hz (x : compactCohomology p V a) : x = 0 := by
    obtain ⟨K,c,rfl⟩ := compactClass_exists_rep p V a x
    have hc : c = 0 := (ModuleCat.subsingleton_of_isZero (empty_supportCohomology_isZero p V K a)).elim _ _
    rw [hc,map_zero]
  let : Subsingleton (compactCohomology p V a) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Every actual local homology group on an empty base vanishes. -/
theorem empty_localHomology_isZero (b : ℕ) : IsZero ((coveringLocalChains p V).homology b) :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) b).map_isZero (empty_localChains_isZero p V)

/-- The literal compact cap map on an empty oriented manifold is an isomorphism. -/
theorem empty_compactCap_isIso {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
    (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
    (a b : ℕ) (hab : a+b = n+2) : IsIso (compactCapMap p V n e o a b hab) :=
  (empty_compactCohomology_isZero p V a).isIso (empty_localHomology_isZero p V b) _

end TernaryPoly.SingularLocalCompactDuality
