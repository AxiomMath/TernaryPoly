module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.TQ
public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.C5

@[expose] public section


/-!
# Proposition C.5 (the graph step) from the paper-route `Γ(6)` theorem

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.
Paper: Proposition C.5 (`ar:prop:graph`).

`paper_graph_route` has exactly the type of `line_constant_term_comparison`.  The `Γ(6)` constant-term map `TΓ` is the one of
`GammaNStokes.LevelChange.propC5_gammaN_printed_paperRoute` (canonical face pairings and the literal Stokes lemma, with the
canonical line map from `EichlerShimuraInj.classicalLine`), transported to the `K†` strata by the dictionaries
`phiPlane`/`phiLine`.  Both its existence clause (the Eisenstein classes with zero flags, used for the line lift by averaging
and Shapiro) and its uniqueness clause (the graph clause) are used; the default `propC5_gammaN_printed`, `exists_TQ` and
`line_constant_term_comparison` are not.  The lemmas of `KDaggerComparison.TQ` that depend on the default existence clause are re-proved here
with the existence clause as an explicit hypothesis `PrintedExistence TΓ` (discharged by the paper-route theorem).

* `constant_terms_of_printed`, `exists_line_lift_of`, `exists_lineMap_of`, `exists_T_ext_of`, `TQ_exists_clause_of`: parametrized versions.
* `paper_graph_aux`: the combined statement (both `line_constant_term_comparison` clauses, the seed property of `TΓ` and the transport characterization).
* `paperGraphMap`, `paperGraphMap_exists`, `paperGraphMap_unique`, `paperGraphMap_transport`, `paper_graph_route`.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.KDaggerComparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

/-- The existence clause of the printed `Γ(N)` Proposition C.5 for a map `TΓ`: every `ξ'` is the plane boundary of a class with
zero flags whose line boundary is `TΓ ξ'`. -/
def PrintedExistence {N n : ℕ} [NeZero N] (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n) : Prop :=
  ∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
    planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧
      lineCuspSumEmbedding N n (TΓ ξ) = lineBoundary N n c

section Param

variable {N : ℕ} [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) {n : ℕ}

include h3 hN in
/-- `KDaggerComparison.constant_terms_of_gammaN` with the existence clause of the `Γ(N)` theorem as a hypothesis. -/
theorem constant_terms_of_printed (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n)
    (hex : PrintedExistence TΓ) (ξ : StratumH2 n trivialCharacter .plane)
    (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      (globalCoordinates n trivialCharacter c).1 = ξ ∧
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 := by
  obtain ⟨ξ', hξ'⟩ := phiPlane_mem_range N h3 hN n ξ hξ
  obtain ⟨c', hz, hp, -⟩ := hex ξ'
  have hrep : ∀ i : PlaneFaces N,
      resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_le_self (levelPrincipal N) (planeFlagAt (planeFaceRepr i))) (classPrincipal N h3 n hN c') =
      resPrincipal N (planeFlagAt (planeFaceRepr i)) (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
          (planeFlagAt (planeFaceRepr i)) ξ) := by
    intro i
    apply (planeH2Equiv N h3 (planeFaceRepr i) n trivialCharacter hN).injective
    calc planeH2Equiv N h3 (planeFaceRepr i) n trivialCharacter hN
          (resH2 (rationalCoefficientComponent n trivialCharacter)
            (fixedPointLevel_le_self (levelPrincipal N) (planeFlagAt (planeFaceRepr i))) (classPrincipal N h3 n hN c'))
        = resAtC N (planeFaceRepr i) n c' := planeH2Equiv_res_classPrincipal N (planeFaceRepr i) n h3 hN c'
      _ = rPlane N n (planeFaceRepr i) c' :=
          (congrArg (fun f => f c') (rPlane_eq_resAtC N n (planeFaceRepr i))).symm
      _ = planeBoundary N n c' i := (planeBoundary_apply N n c' i).symm
      _ = planeCuspSumEmbedding N n ξ' i := by rw [hp]
      _ = phiPlane N h3 hN n ξ i := by rw [hξ']
      _ = phiPlaneAt N h3 hN n (planeFaceRepr i) ξ := phiPlane_apply N h3 hN n ξ i
      _ = _ := rfl
  have hy := res_eq_of_reps h3 ξ (classPrincipal N h3 n hN c') hrep
  obtain ⟨c, hc⟩ : ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c = classK N h3 hN n c' :=
    Submodule.Quotient.mk_surjective _ _
  refine ⟨c, ?_, ?_⟩
  · rw [← sub_eq_zero]
    refine (eq_zero_iff_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) _).mpr fun F => ?_
    refine (map_sub (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F) _ _).trans
      (sub_eq_zero.mpr ?_)
    refine res_level_injective (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)
      (levelPrincipal_le N) (levelPrincipal_norm N) F ?_
    have e := planeCoordinate_component N n h3 hN c' c hc F
    have e' : resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F
          (globalCoordinates n trivialCharacter c).1) =
        resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_level F) (classK N h3 hN n c')) :=
      congrArg _ e
    exact e'.trans (res_classK_plane h3 hN c' ξ hy F)
  · have hpli : PlaneLocallyInner N h3 hN n c' := by
      refine (planeLocallyInner_iff_cusps N n h3 hN c').mpr fun h => ?_
      have hm := ((zeroFlags_iff_mixed N n hN c').mp hz).2 h
      have hm' : resAtC N h n c' ∈ faceCuspidalInH2 N h n := by
        have := LinearMap.congr_fun (rPlane_eq_resAtC N n h) c'
        exact this ▸ hm
      rwa [faceCuspidalInH2_eq_locallyInner] at hm'
    have he : ∀ e : Edges, resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_le_level e)
        (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 := by
      intro e
      rw [hc]
      exact classK_edge_vanishing N h3 hN n c' hpli e
    exact innerBoundary_of_edgeVanishing n trivialCharacter .line c he

include h3 hN in
/-- `KDaggerComparison.exists_line_lift` with the existence clause as a hypothesis. -/
theorem exists_line_lift_of (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n)
    (hG : GraphMapGamma N n TΓ) (hex : PrintedExistence TΓ)
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ)
    (ξ' : PlaneCuspSum N n) (hξ' : planeCuspSumEmbedding N n ξ' = phiPlane N h3 hN n ξ) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      (globalCoordinates n trivialCharacter c).1 = ξ ∧
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 ∧
      phiLine N h3 hN n (globalCoordinates n trivialCharacter c).2 = lineCuspSumEmbedding N n (TΓ ξ') := by
  obtain ⟨c, hc1, hc2⟩ := constant_terms_of_printed h3 hN TΓ hex ξ hξ
  have hin : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 := by
    rw [hc1]; exact hξ
  obtain ⟨ξ'', e1, e2⟩ := identification_of_class N h3 hN n TΓ hG c hin
  rw [hc1] at e1
  have e3 : ξ'' = ξ' := planeCuspSumEmbedding_injective N n (e1.trans hξ'.symm)
  exact ⟨c, hc1, hc2, by rw [← e2, e3]⟩

include h3 hN in
/-- `KDaggerComparison.exists_lineMap` with the existence clause as a hypothesis. -/
theorem exists_lineMap_of (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n)
    (hG : GraphMapGamma N n TΓ) (hex : PrintedExistence TΓ)
    (Ψ : (FacePairingFull.innerClasses n .plane) →ₗ[ℂ] PlaneCuspSum N n)
    (hΨ : ∀ ξ : (FacePairingFull.innerClasses n .plane),
      planeCuspSumEmbedding N n (Ψ ξ) = phiPlane N h3 hN n ξ.1) :
    ∃ L : (FacePairingFull.innerClasses n .plane) →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      ∀ ξ : (FacePairingFull.innerClasses n .plane),
        phiLine N h3 hN n (L ξ) = lineCuspSumEmbedding N n (TΓ (Ψ ξ)) := by
  have hΛ' : ∀ ξ : (FacePairingFull.innerClasses n .plane), ∃ y : StratumH2 n trivialCharacter .line,
      phiLine N h3 hN n y = lineCuspSumEmbedding N n (TΓ (Ψ ξ)) := fun ξ =>
    (exists_line_lift_of h3 hN TΓ hG hex ξ.1 ξ.2 (Ψ ξ) (hΨ ξ)).elim
      fun c hc => ⟨(globalCoordinates n trivialCharacter c).2, hc.2.2⟩
  let Lm : (FacePairingFull.innerClasses n .plane) →ₗ[ℂ] LinearMap.range (phiLine N h3 hN n) :=
    LinearMap.codRestrict _ ((lineCuspSumEmbedding N n).comp (TΓ.comp Ψ)) hΛ'
  let Eq2 := LinearEquiv.ofInjective (phiLine N h3 hN n) (phiLine_injective N h3 hN n)
  refine ⟨Eq2.symm.toLinearMap.comp Lm, fun ξ => ?_⟩
  have := Eq2.apply_symm_apply (Lm ξ)
  exact congrArg Subtype.val this

include h3 hN in
/-- `KDaggerComparison.exists_T_ext` with the existence clause as a hypothesis. -/
theorem exists_T_ext_of (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n)
    (hG : GraphMapGamma N n TΓ) (hex : PrintedExistence TΓ) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      ∀ ξ, InnerBoundary n trivialCharacter .plane ξ → ∀ ξ' : PlaneCuspSum N n,
        planeCuspSumEmbedding N n ξ' = phiPlane N h3 hN n ξ →
        phiLine N h3 hN n (T ξ) = lineCuspSumEmbedding N n (TΓ ξ') := by
  obtain ⟨Ψ, hΨ⟩ := exists_planeSection N h3 hN n
  obtain ⟨L, hL⟩ := exists_lineMap_of h3 hN TΓ hG hex Ψ hΨ
  obtain ⟨T, hTξ⟩ := exists_extend_of_sub (FacePairingFull.innerClasses n .plane) L
  refine ⟨T, fun ξ hξ ξ' hξ' => ?_⟩
  have e3 : ξ' = Ψ ⟨ξ, hξ⟩ := planeCuspSumEmbedding_injective N n (hξ'.trans (hΨ ⟨ξ, hξ⟩).symm)
  rw [e3]
  exact (congrArg (phiLine N h3 hN n) (hTξ ⟨ξ, hξ⟩)).trans (hL ⟨ξ, hξ⟩)

include h3 hN in
/-- `KDaggerComparison.TQ_exists_clause` with the existence clause as a hypothesis. -/
theorem TQ_exists_clause_of (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n)
    (hG : GraphMapGamma N n TΓ) (hex : PrintedExistence TΓ)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ → ∀ ξ' : PlaneCuspSum N n,
        planeCuspSumEmbedding N n ξ' = phiPlane N h3 hN n ξ →
        phiLine N h3 hN n (T ξ) = lineCuspSumEmbedding N n (TΓ ξ'))
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    InnerBoundary n trivialCharacter .line (T ξ) ∧
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ) := by
  obtain ⟨ξ', hξ'⟩ := phiPlane_mem_range N h3 hN n ξ hξ
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_line_lift_of h3 hN TΓ hG hex ξ hξ ξ' hξ'
  have e : (globalCoordinates n trivialCharacter c).2 = T ξ :=
    phiLine_injective N h3 hN n (hc3.trans (hT ξ hξ ξ' hξ').symm)
  exact ⟨e ▸ hc2, c, Prod.ext hc1 e⟩

end Param

/-- **The combined graph specification at `Γ(6)`.**  `T` has both clauses of `line_constant_term_comparison`, and there is a `Γ(6)` constant-term map `TΓ` with the
printed seed property and the `Γ(6)` graph clause such that `Φ_line (T ξ) = TΓ ξ'` whenever `ξ'` is the `Γ(6)` plane boundary of the inner class `ξ`. -/
def PaperGraphSpec (n : ℕ) (hn : 4 ≤ n)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line) : Prop :=
  (∃ TΓ : PlaneCuspSum 6 n →ₗ[ℂ] LineCuspSum 6 n,
    (∀ (f : TwTuple 6 n) (ξ : PlaneCuspSum 6 n), planeCuspSumEmbedding 6 n ξ = seedBoundary 6 n f →
      lineCuspSumEmbedding 6 n (TΓ ξ) = lineBoundary 6 n (classCG 6 n hn f)) ∧
    GraphMapGamma 6 n TΓ ∧
    ∀ ξ, InnerBoundary n trivialCharacter .plane ξ → ∀ ξ' : PlaneCuspSum 6 n,
      planeCuspSumEmbedding 6 n ξ' = phiPlane 6 (by norm_num) (by norm_num) n ξ →
      phiLine 6 (by norm_num) (by norm_num) n (T ξ) = lineCuspSumEmbedding 6 n (TΓ ξ')) ∧
  (∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
    InnerBoundary n trivialCharacter .line (T ξ) ∧
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ)) ∧
  ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
    InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 →
    InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 →
    (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1

/-- Existence of a map with `PaperGraphSpec`, from the paper-route `Γ(6)` theorem. -/
theorem paper_graph_aux (n : ℕ) (hn : 4 ≤ n) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      PaperGraphSpec n hn T := by
  obtain ⟨TΓ, h1, hex, h3'⟩ :=
    GammaNStokes.LevelChange.propC5_gammaN_printed_paperRoute (N := 6) (n := n) (by norm_num) hn
  have hG : GraphMapGamma 6 n TΓ := fun c hc ξP ξQ e1 e2 => h3' c hc ξP ξQ e1 e2
  have hex' : PrintedExistence TΓ := hex
  obtain ⟨T, hT⟩ := exists_T_ext_of (N := 6) (by norm_num) (by norm_num) TΓ hG hex'
  have hex2 := TQ_exists_clause_of (N := 6) (by norm_num) (by norm_num) TΓ hG hex' T hT
  exact ⟨T, ⟨TΓ, h1, hG, hT⟩, hex2,
    fun c hin _ => graph_clause_of_gammaN 6 (by norm_num) (by norm_num) n TΓ hG T
      (fun ξ hξ => (hex2 ξ hξ).2) c hin⟩

/-- The graph map of Proposition C.5: the transport `Φ_line⁻¹ ∘ TΓ ∘ Φ_plane` of the `Γ(6)` paper-route constant term, extended linearly. -/
def paperGraphMap (n : ℕ) (hn : 4 ≤ n) :
    StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line :=
  Classical.choose (paper_graph_aux n hn)

theorem paperGraphMap_spec (n : ℕ) (hn : 4 ≤ n) : PaperGraphSpec n hn (paperGraphMap n hn) :=
  Classical.choose_spec (paper_graph_aux n hn)

/-- Existence clause of Proposition C.5 for `paperGraphMap`. -/
theorem paperGraphMap_exists (n : ℕ) (hn : 4 ≤ n) :
    ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      InnerBoundary n trivialCharacter .line (paperGraphMap n hn ξ) ∧
        ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
          globalCoordinates n trivialCharacter c = (ξ, paperGraphMap n hn ξ) :=
  (paperGraphMap_spec n hn).2.1

/-- Uniqueness (graph) clause of Proposition C.5 for `paperGraphMap`. -/
theorem paperGraphMap_unique (n : ℕ) (hn : 4 ≤ n) :
    ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 →
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 →
      (globalCoordinates n trivialCharacter c).2 =
        paperGraphMap n hn (globalCoordinates n trivialCharacter c).1 :=
  (paperGraphMap_spec n hn).2.2

/-- Transport characterization: `paperGraphMap` is the `phiPlane`/`phiLine` transport of a `Γ(6)` constant-term map `TΓ` with the printed
seed property and the `Γ(6)` graph clause (the paper-route theorem's). -/
theorem paperGraphMap_transport (n : ℕ) (hn : 4 ≤ n) :
    ∃ TΓ : PlaneCuspSum 6 n →ₗ[ℂ] LineCuspSum 6 n,
      (∀ (f : TwTuple 6 n) (ξ : PlaneCuspSum 6 n), planeCuspSumEmbedding 6 n ξ = seedBoundary 6 n f →
        lineCuspSumEmbedding 6 n (TΓ ξ) = lineBoundary 6 n (classCG 6 n hn f)) ∧
      GraphMapGamma 6 n TΓ ∧
      ∀ ξ, InnerBoundary n trivialCharacter .plane ξ → ∀ ξ' : PlaneCuspSum 6 n,
        planeCuspSumEmbedding 6 n ξ' = phiPlane 6 (by norm_num) (by norm_num) n ξ →
        phiLine 6 (by norm_num) (by norm_num) n (paperGraphMap n hn ξ) =
          lineCuspSumEmbedding 6 n (TΓ ξ') :=
  (paperGraphMap_spec n hn).1

/-- **Proposition C.5** (the type of `line_constant_term_comparison`), from the paper-route `Γ(6)` theorem and the actual `phiPlane`/`phiLine` dictionaries. -/
theorem paper_graph_route (n : ℕ) (hn : 4 ≤ n) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      (∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
        InnerBoundary n trivialCharacter .line (T ξ) ∧
          ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
            globalCoordinates n trivialCharacter c = (ξ, T ξ)) ∧
      ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 →
        InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 →
        (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1 :=
  ⟨paperGraphMap n hn, paperGraphMap_exists n hn, paperGraphMap_unique n hn⟩

end TernaryPeriodPolynomials.Argument.BoundaryComparison
