module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.CoveringChart

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory Set HomologicalComplex SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold

/-- Real Hom cochains carry an actual chain isomorphism contravariantly to a cochain isomorphism. -/
def realHomIso {K L : ChainComplex (ModuleCat ℝ) ℕ} (e : K ≅ L) (F : ModuleCat ℝ) :
    realHomComplex L F ≅ realHomComplex K F where
  hom := realHomPullback e.hom F
  inv := realHomPullback e.inv F
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change L.X n →ₗ[ℝ] F at φ
    apply LinearMap.ext
    intro c
    have h := congrArg (fun f : L ⟶ L => f.f n c) e.inv_hom_id
    exact congrArg (fun x => φ x) h
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change K.X n →ₗ[ℝ] F at φ
    apply LinearMap.ext
    intro c
    have h := congrArg (fun f : K ⟶ K => f.f n c) e.hom_inv_id
    exact congrArg (fun x => φ x) h

/-- The literal homeomorphism from an actual smaller quotient chart to its coordinate domain. -/
def quotientChartHomeomorph (S : Space) {V : Set Coordinates}
    (hVt : V ⊆ (quotientChart S).target) : chartOpen S V ≃ₜ V where
  toFun q := ⟨quotientChart S q, q.property.2⟩
  invFun x := ⟨(quotientChart S).symm x,
    (quotientChart S).map_target (hVt x.property), by
      change quotientChart S ((quotientChart S).symm x.val) ∈ V
      rw [(quotientChart S).right_inv (hVt x.property)]
      exact x.property⟩
  left_inv q := Subtype.ext ((quotientChart S).left_inv q.property.1)
  right_inv x := Subtype.ext ((quotientChart S).right_inv (hVt x.property))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (quotientChart S).continuousOn_toFun.comp_continuous continuous_subtype_val
      (fun q => q.property.1)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (quotientChart S).continuousOn_invFun.comp_continuous continuous_subtype_val
      (fun x => hVt x.property)

/-- Actual singular cochains on the coordinate chart and the underlying arithmetic quotient
open are isomorphic through the real chain map of their literal chart homeomorphism. -/
def quotientChartSingularIso (S : Space) {V : Set Coordinates}
    (hVt : V ⊆ (quotientChart S).target) (F : ModuleCat.{0} ℝ) :
    realSingularCochains (TopCat.of V) F ≅ realSingularCochains (TopCat.of (chartOpen S V)) F :=
  realHomIso
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)).mapIso
      (TopCat.isoOfHomeo (quotientChartHomeomorph S hVt))) F

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The local comparison on the actual arithmetic quotient open, with coefficient coordinates
specified by its genuine covering sheet. This is a local trivialization, not a global assertion
that the deck coefficient local system is constant. -/
def quotientLocalComparison (ρ : Representation ℝ DeckGroup F) (S : Space)
    {V : Set Coordinates} (hV : IsOpen V) (hVt : V ⊆ (quotientChart S).target)
    (hc : Convex ℝ V) (hne : V.Nonempty) (n : ℕ) :
    (coveringComplex ρ (chartOpen_isOpen S hV)).homology n ≅
      (realSingularCochains (TopCat.of (chartOpen S V)) (ModuleCat.of ℝ F)).homology n :=
  coveringLocalComparison ρ S hV hVt hc hne n ≪≫
    (homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n).mapIso
      (quotientChartSingularIso S hVt (ModuleCat.of ℝ F))

/-- Every point of every quotient open has a genuine convex lifting neighborhood carrying
the proved real de Rham/singular comparison in all degrees. -/
theorem quotientLocalComparison_exists (ρ : Representation ℝ DeckGroup F)
    {U : Set OrbitSpace} (hU : IsOpen U) {q : OrbitSpace} (hq : q ∈ U) :
    ∃ S : Space, ∃ r : ℝ, 0 < r ∧
      ∃ _hball : Metric.ball (quotientChart S q) r ⊆ (quotientChart S).target,
        q ∈ chartOpen S (Metric.ball (quotientChart S q) r) ∧
        chartOpen S (Metric.ball (quotientChart S q) r) ⊆ U ∧
        ∀ n : ℕ, Nonempty
          ((coveringComplex ρ (chartOpen_isOpen S
            (V := Metric.ball (quotientChart S q) r) Metric.isOpen_ball)).homology n ≅
            (realSingularCochains (TopCat.of (chartOpen S (Metric.ball (quotientChart S q) r)))
              (ModuleCat.of ℝ F)).homology n) := by
  obtain ⟨S, hqS⟩ := quotientCharts_cover q
  have hx : quotientChart S q ∈ chartDomain S U :=
    ⟨(quotientChart S).map_source hqS, by
      simpa only [mem_preimage, (quotientChart S).left_inv hqS] using hq⟩
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (chartDomain_isOpen S hU) _ hx
  have hbt : Metric.ball (quotientChart S q) r ⊆ (quotientChart S).target :=
    fun x hx => (hb hx).1
  refine ⟨S, r, hr, hbt, ⟨hqS, Metric.mem_ball_self hr⟩,
    chartOpen_subset_of_chartDomain S hb, fun n => ?_⟩
  exact ⟨quotientLocalComparison ρ S Metric.isOpen_ball hbt (convex_ball _ _)
    ⟨quotientChart S q, Metric.mem_ball_self hr⟩ n⟩

end TernaryPoly.SmoothSingularComparison
