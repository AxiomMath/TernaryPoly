module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Existence
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Converse
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm

@[expose] public section


/-!
# `K†` comparison, CMP-C5 with `T := T_Q`

`exists_TQ`: with `TΓ` the printed constant term of `propC5_gammaN_printed`, there is a linear `T : StratumH2 plane → StratumH2 line`, the transport
`T_Q = Φ_line⁻¹ ∘ TΓ ∘ Φ_plane` of `TΓ` extended linearly off the inner classes, with both clauses of the `line_constant_term_comparison` and the characterisation
`Φ_line (T ξ) = TΓ ξ'` for every `ξ'` with `Φ_plane ξ = ξ'`.  Existence uses `constant_terms_of_gammaN`; the graph clause uses `graph_clause_of_gammaN`.
Thus the existential `T` of `line_constant_term_comparison` is identified: any `T` with the existence clause agrees with `T_Q` on the inner classes (`identification`).

Formalized by Claude Sonnet 5.5.
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

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

section TQ

theorem exists_extend_of_sub {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (p : Submodule ℂ V) (L : p →ₗ[ℂ] W) : ∃ T : V →ₗ[ℂ] W, ∀ x : p, T x = L x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend L
  exact ⟨g, fun x => LinearMap.congr_fun hg x⟩

open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

theorem phiLine_injective : Function.Injective (phiLine N h3 hN n) := by
  rw [injective_iff_map_eq_zero]
  exact fun ξ h => eq_zero_of_phiLine_eq_zero N h3 hN n ξ h

include h3 hN in
/-- **A line lift.**  For every `InnerBoundary` plane class `ξ` and `ξ' ∈ 𝒞_P(E)` with the `Γ(N)` plane boundary of `ξ` there is a global `K†`-cocycle with
plane coordinate `ξ`, `InnerBoundary` line coordinate, and `Γ(N)` line boundary `TΓ ξ'`. -/
theorem exists_line_lift (hn : 4 ≤ n) (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n) (hG : GraphMapGamma N n TΓ)
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ)
    (ξ' : PlaneCuspSum N n) (hξ' : planeCuspSumEmbedding N n ξ' = phiPlane N h3 hN n ξ) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      (globalCoordinates n trivialCharacter c).1 = ξ ∧
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 ∧
      phiLine N h3 hN n (globalCoordinates n trivialCharacter c).2 = lineCuspSumEmbedding N n (TΓ ξ') := by
  obtain ⟨c, hc1, hc2⟩ := constant_terms_of_gammaN (N := N) (n := n) h3 hN hn ξ hξ
  have hin : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 := by
    rw [hc1]; exact hξ
  obtain ⟨ξ'', e1, e2⟩ := identification_of_class N h3 hN n TΓ hG c hin
  rw [hc1] at e1
  have e3 : ξ'' = ξ' := planeCuspSumEmbedding_injective N n (e1.trans hξ'.symm)
  exact ⟨c, hc1, hc2, by rw [← e2, e3]⟩

include h3 hN in
/-- The transport of the inner plane classes to `𝒞_P(E)` is a linear map. -/
theorem exists_planeSection : ∃ Ψ : (FacePairingFull.innerClasses n .plane) →ₗ[ℂ] PlaneCuspSum N n,
    ∀ ξ : (FacePairingFull.innerClasses n .plane), planeCuspSumEmbedding N n (Ψ ξ) = phiPlane N h3 hN n ξ.1 := by
  have hinj := planeCuspSumEmbedding_injective N n
  let Eq' := LinearEquiv.ofInjective (planeCuspSumEmbedding N n) hinj
  let Pm : (FacePairingFull.innerClasses n .plane) →ₗ[ℂ] LinearMap.range (planeCuspSumEmbedding N n) :=
    LinearMap.codRestrict _ ((phiPlane N h3 hN n).comp (FacePairingFull.innerClasses n .plane).subtype)
      (fun ξ => phiPlane_mem_range N h3 hN n ξ.1 ξ.2)
  refine ⟨Eq'.symm.toLinearMap.comp Pm, fun ξ => ?_⟩
  have := Eq'.apply_symm_apply (Pm ξ)
  exact congrArg Subtype.val this

include h3 hN in
/-- The map `ξ ↦ (line coordinate of the lift)` is linear on the inner plane classes. -/
theorem exists_lineMap (hn : 4 ≤ n) (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n) (hG : GraphMapGamma N n TΓ)
    (Ψ : (FacePairingFull.innerClasses n .plane) →ₗ[ℂ] PlaneCuspSum N n)
    (hΨ : ∀ ξ : (FacePairingFull.innerClasses n .plane),
      planeCuspSumEmbedding N n (Ψ ξ) = phiPlane N h3 hN n ξ.1) :
    ∃ L : (FacePairingFull.innerClasses n .plane) →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      ∀ ξ : (FacePairingFull.innerClasses n .plane),
        phiLine N h3 hN n (L ξ) = lineCuspSumEmbedding N n (TΓ (Ψ ξ)) := by
  have hΛ' : ∀ ξ : (FacePairingFull.innerClasses n .plane), ∃ y : StratumH2 n trivialCharacter .line,
      phiLine N h3 hN n y = lineCuspSumEmbedding N n (TΓ (Ψ ξ)) := fun ξ =>
    (exists_line_lift N h3 hN n hn TΓ hG ξ.1 ξ.2 (Ψ ξ) (hΨ ξ)).elim
      fun c hc => ⟨(globalCoordinates n trivialCharacter c).2, hc.2.2⟩
  let Lm : (FacePairingFull.innerClasses n .plane) →ₗ[ℂ] LinearMap.range (phiLine N h3 hN n) :=
    LinearMap.codRestrict _ ((lineCuspSumEmbedding N n).comp (TΓ.comp Ψ)) hΛ'
  let Eq2 := LinearEquiv.ofInjective (phiLine N h3 hN n) (phiLine_injective N h3 hN n)
  refine ⟨Eq2.symm.toLinearMap.comp Lm, fun ξ => ?_⟩
  have := Eq2.apply_symm_apply (Lm ξ)
  exact congrArg Subtype.val this

include h3 hN in
/-- **`T_Q` as a linear map.**  For a map `TΓ` with the `Γ(N)` graph clause there is a linear `T : StratumH2 plane → StratumH2 line` whose
`Γ(N)` line boundary on an inner class `ξ` is `TΓ ξ'` for every `ξ'` with the `Γ(N)` plane boundary of `ξ`. -/
theorem exists_T_ext (hn : 4 ≤ n) (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n) (hG : GraphMapGamma N n TΓ) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      ∀ ξ, InnerBoundary n trivialCharacter .plane ξ → ∀ ξ' : PlaneCuspSum N n,
        planeCuspSumEmbedding N n ξ' = phiPlane N h3 hN n ξ →
        phiLine N h3 hN n (T ξ) = lineCuspSumEmbedding N n (TΓ ξ') := by
  obtain ⟨Ψ, hΨ⟩ := exists_planeSection N h3 hN n
  obtain ⟨L, hL⟩ := exists_lineMap N h3 hN n hn TΓ hG Ψ hΨ
  obtain ⟨T, hTξ⟩ := exists_extend_of_sub (FacePairingFull.innerClasses n .plane) L
  refine ⟨T, fun ξ hξ ξ' hξ' => ?_⟩
  have e3 : ξ' = Ψ ⟨ξ, hξ⟩ := planeCuspSumEmbedding_injective N n (hξ'.trans (hΨ ⟨ξ, hξ⟩).symm)
  rw [e3]
  exact (congrArg (phiLine N h3 hN n) (hTξ ⟨ξ, hξ⟩)).trans (hL ⟨ξ, hξ⟩)

include h3 hN in
/-- The existence clause for `T_Q`. -/
theorem TQ_exists_clause (hn : 4 ≤ n) (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n) (hG : GraphMapGamma N n TΓ)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ → ∀ ξ' : PlaneCuspSum N n,
        planeCuspSumEmbedding N n ξ' = phiPlane N h3 hN n ξ →
        phiLine N h3 hN n (T ξ) = lineCuspSumEmbedding N n (TΓ ξ'))
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    InnerBoundary n trivialCharacter .line (T ξ) ∧
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ) := by
  obtain ⟨ξ', hξ'⟩ := phiPlane_mem_range N h3 hN n ξ hξ
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_line_lift N h3 hN n hn TΓ hG ξ hξ ξ' hξ'
  have e : (globalCoordinates n trivialCharacter c).2 = T ξ :=
    phiLine_injective N h3 hN n (hc3.trans (hT ξ hξ ξ' hξ').symm)
  exact ⟨e ▸ hc2, c, Prod.ext hc1 e⟩

include h3 hN in
/-- **CMP-C5 with `T := T_Q`.**  Let `TΓ` be the printed constant term of the literal `Γ(N)` Proposition C.5.  There is a linear map
`T : StratumH2 plane → StratumH2 line` (the transport `T_Q = Φ_line⁻¹ ∘ TΓ ∘ Φ_plane` of `TΓ`, extended linearly off the inner classes) such that
`T` has both clauses of the `line_constant_term_comparison`, and, characteristically, for every `InnerBoundary` plane class `ξ` and every `ξ' ∈ 𝒞_P(E)`
with the `Γ(N)` plane boundary of `ξ`, the `Γ(N)` line boundary of `T ξ` is `TΓ ξ'`.  By the injectivity of the line dictionary, any other
`T` with the existence clause agrees with `T_Q` on the inner classes (`identification`). -/
theorem exists_TQ (hn : 4 ≤ n) :
    ∃ TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n,
      (∀ (f : TwTuple N n) (ξ : PlaneCuspSum N n), planeCuspSumEmbedding N n ξ = seedBoundary N n f →
        lineCuspSumEmbedding N n (TΓ ξ) = lineBoundary N n (classCG N n hn f)) ∧
      GraphMapGamma N n TΓ ∧
      ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
        (∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
          InnerBoundary n trivialCharacter .line (T ξ) ∧
            ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
              globalCoordinates n trivialCharacter c = (ξ, T ξ)) ∧
        (∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
          InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 →
          InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 →
          (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1) ∧
        ∀ ξ, InnerBoundary n trivialCharacter .plane ξ → ∀ ξ' : PlaneCuspSum N n,
          planeCuspSumEmbedding N n ξ' = phiPlane N h3 hN n ξ →
          phiLine N h3 hN n (T ξ) = lineCuspSumEmbedding N n (TΓ ξ') := by
  obtain ⟨TΓ, h1, -, h3'⟩ := propC5_gammaN_printed (N := N) (n := n) hN hn
  have hG : GraphMapGamma N n TΓ := fun c hc ξP ξQ e1 e2 => h3' c hc ξP ξQ e1 e2
  obtain ⟨T, hT⟩ := exists_T_ext N h3 hN n hn TΓ hG
  have hex := TQ_exists_clause N h3 hN n hn TΓ hG T hT
  exact ⟨TΓ, h1, hG, T, hex,
    fun c hin _ => graph_clause_of_gammaN N h3 hN n TΓ hG T (fun ξ hξ => (hex ξ hξ).2) c hin, hT⟩

end TQ
end TernaryPeriodPolynomials.Argument.KDaggerComparison
