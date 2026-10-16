module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Opposite TopologicalSpace Set HomologicalComplex
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts SymmetricSpacePositive
open scoped Topology
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- Every actual quotient neighborhood contains a genuine convex-ball covering frame. -/
theorem exists_convex_frame_neighborhood {U : Set OrbitSpace} (hU : IsOpen U)
    {q : OrbitSpace} (hq : q ∈ U) :
    ∃ S : Space, ∃ r : ℝ, 0 < r ∧
      ∃ _hball : Metric.ball (quotientChart S q) r ⊆ (quotientChart S).target,
        q ∈ chartOpen S (Metric.ball (quotientChart S q) r) ∧
        chartOpen S (Metric.ball (quotientChart S q) r) ⊆ U := by
  obtain ⟨S, hqS⟩ := quotientCharts_cover q
  have hx : quotientChart S q ∈ chartDomain S U :=
    ⟨(quotientChart S).map_source hqS, by
      simpa only [mem_preimage, (quotientChart S).left_inv hqS] using hq⟩
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (chartDomain_isOpen S hU) _ hx
  exact ⟨S, r, hr, fun x hx => (hb hx).1, ⟨hqS, Metric.mem_ball_self hr⟩,
    chartOpen_subset_of_chartDomain S hb⟩

/-- The actual singular coefficient augmentation is a quasi-isomorphism on sufficiently small
true quotient neighborhoods, proved through the explicit genuine covering frame. -/
theorem coveringSingularAugmentation_local_quasiIso {U : Set OrbitSpace} (hU : IsOpen U)
    {q : OrbitSpace} (hq : q ∈ U) :
    ∃ V : Opens (TopCat.of OrbitSpace), q ∈ V ∧ (V : Set OrbitSpace) ⊆ U ∧
      QuasiIso (coveringSingularAugmentation ρ (V : Set OrbitSpace)) := by
  obtain ⟨S, r, hr, hball, hqV, hVU⟩ := exists_convex_frame_neighborhood hU hq
  have : ContractibleSpace (Metric.ball (quotientChart S q) r) :=
    (convex_ball _ _).contractibleSpace ⟨_, Metric.mem_ball_self hr⟩
  exact ⟨⟨chartOpen S (Metric.ball (quotientChart S q) r), chartOpen_isOpen S Metric.isOpen_ball⟩,
    hqV, hVU, coveringSingularAugmentation_quasiIso ρ (chartSingularFrame S hball)⟩

/-- The actual augmented singular resolution controls positive-degree exactness. -/
theorem coveringCochains_exactAt_of_augmentation {U : Set OrbitSpace}
    [QuasiIso (coveringSingularAugmentation ρ U)] (n : ℕ) : (coveringCochains ρ U).ExactAt (n+1) := by
  apply (quasiIsoAt_iff_exactAt (coveringSingularAugmentation ρ U) (n+1) ?_).mp inferInstance
  apply (exactAt_iff_isZero_homology _ _).mpr
  exact isZero_single_obj_homology _ _ _ _ (Nat.succ_ne_zero n)

/-- Every actual closed singular cochain of positive degree has a genuine primitive after
restriction to a sufficiently small quotient neighborhood. -/
theorem singular_local_lifting {U : Set OrbitSpace} (hU : IsOpen U) {q : OrbitSpace} (hq : q ∈ U)
    (n : ℕ) (w : (coveringCochains ρ U).X (n+1))
    (hw : (coveringCochains ρ U).d (n+1) ((n+1)+1) w = 0) :
    ∃ V : Opens (TopCat.of OrbitSpace), q ∈ V ∧ ∃ hVU : (V : Set OrbitSpace) ⊆ U,
      ∃ z : (coveringCochains ρ (V : Set OrbitSpace)).X n,
        (coveringCochains ρ (V : Set OrbitSpace)).d n (n+1) z =
          (coveringCochainRestriction ρ hVU).f (n+1) w := by
  obtain ⟨V, hqV, hVU, hQI⟩ := coveringSingularAugmentation_local_quasiIso ρ hU hq
  have : QuasiIso (coveringSingularAugmentation ρ (V : Set OrbitSpace)) := hQI
  have he := coveringCochains_exactAt_of_augmentation ρ (U := V) n
  rw [exactAt_iff' _ n (n+1) ((n+1)+1) (by simp) (by simp)] at he
  have hc := congrArg (fun m => m.hom w) ((coveringCochainRestriction ρ hVU).comm (n+1) ((n+1)+1))
  change (coveringCochains ρ (V : Set OrbitSpace)).d (n+1) ((n+1)+1)
    ((coveringCochainRestriction ρ hVU).f (n+1) w) =
    (coveringCochainRestriction ρ hVU).f ((n+1)+1) ((coveringCochains ρ U).d (n+1) ((n+1)+1) w) at hc
  have hz := hc.trans ((congrArg ((coveringCochainRestriction ρ hVU).f ((n+1)+1)) hw).trans (map_zero _))
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp he _ hz
  exact ⟨V, hqV, hVU, z, hz⟩

end TernaryPoly.SmoothSingularGlobal
