module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Inner
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Injective
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.PropC5Printed

@[expose] public section


/-!
# `K†` comparison, CMP-C5: the `line_constant_term_comparison` is the transport of the literal `Γ(N)` Proposition C.5

`identification_of_class`, `identification`: the line coordinate of a global `K†`-cocycle with `InnerBoundary` plane coordinate is the transport
of `TΓ` applied to the transport of its plane coordinate (`TΓ` any map with the `Γ(N)` graph clause `GraphMapGamma`).
`line_coordinate_eq_of_plane_eq`, `graph_clause_of_gammaN`: the uniqueness clause of `line_constant_term_comparison` follows from the `Γ(N)` graph clause.
`prop_C_5_comparison`: the packaged statement with `TΓ` the printed constant term of `propC5_gammaN_printed`.

What is NOT proved here: the existence clause (i) of `line_constant_term_comparison` from the `Γ(N)` statement (averaging over `K†/Γ(N)`); it is the model theorem.

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

section Transport

/-- The graph clause of Proposition C.5 at `Γ(N)` for a map `TΓ`: every global class with zero flag restrictions and mixed
cuspidal face restrictions `(ξ_P, ξ_Q)` has `ξ_Q = TΓ ξ_P`. -/
def GraphMapGamma (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n) : Prop :=
  ∀ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c →
    ∀ (ξP : PlaneCuspSum N n) (ξQ : LineCuspSum N n),
      planeCuspSumEmbedding N n ξP = planeBoundary N n c →
      lineCuspSumEmbedding N n ξQ = lineBoundary N n c → ξQ = TΓ ξP

/-- **CMP-C5 (identification, class form).**  For every global `K†`-cocycle whose plane coordinate is `InnerBoundary`, the `Γ(N)`
plane boundary of its plane coordinate is the image of some `ξ' ∈ 𝒞_P(E)`, and the `Γ(N)` line boundary of its line coordinate is the
image of `TΓ ξ'`. -/
theorem identification_of_class (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n) (hTΓ : GraphMapGamma N n TΓ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hin : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1) :
    ∃ ξ' : PlaneCuspSum N n,
      planeCuspSumEmbedding N n ξ' = phiPlane N h3 hN n (globalCoordinates n trivialCharacter c).1 ∧
      lineCuspSumEmbedding N n (TΓ ξ') = phiLine N h3 hN n (globalCoordinates n trivialCharacter c).2 := by
  have hz := zeroFlags_litAll_of_inner N h3 hN n c hin
  have hm := (zeroFlags_iff_mixed N n hN _).mp hz
  obtain ⟨⟨ξP, hP⟩, ⟨ξQ, hQ⟩⟩ := exists_coordinates N n _ hm
  refine ⟨ξP, hP.trans (phiPlane_globalCoordinates N h3 hN n c).symm, ?_⟩
  rw [← hTΓ _ hz ξP ξQ hP hQ]
  exact hQ.trans (phiLine_globalCoordinates N h3 hN n c).symm

/-- **CMP-C5 (identification).**  If `T` is any map with the existence clause of the `line_constant_term_comparison` (every inner plane class is the
plane coordinate of a global `K†`-cocycle with line coordinate `T ξ`), then `T` is the transport of the `Γ(N)` constant term
`TΓ` through the face dictionaries: for every inner `ξ` there is `ξ' ∈ 𝒞_P(E)` with `ξ'` the `Γ(N)` plane boundary of `ξ` and
`TΓ ξ'` the `Γ(N)` line boundary of `T ξ`. -/
theorem identification (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n) (hTΓ : GraphMapGamma N n TΓ)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ))
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ ξ' : PlaneCuspSum N n, planeCuspSumEmbedding N n ξ' = phiPlane N h3 hN n ξ ∧
      lineCuspSumEmbedding N n (TΓ ξ') = phiLine N h3 hN n (T ξ) := by
  obtain ⟨c, hc⟩ := hT ξ hξ
  have hin : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 := by
    rw [hc]; exact hξ
  have := identification_of_class N h3 hN n TΓ hTΓ c hin
  rw [hc] at this
  exact this

end Transport
section Uniqueness

include h3 hN in
/-- **The uniqueness clause of `line_constant_term_comparison` from the `Γ(N)` statement.**  Two global `K†`-cocycles with `InnerBoundary` plane coordinates
and equal plane coordinates have equal line coordinates. -/
theorem line_coordinate_eq_of_plane_eq (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n) (hTΓ : GraphMapGamma N n TΓ)
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hin : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1)
    (hin' : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c').1)
    (hP : (globalCoordinates n trivialCharacter c).1 = (globalCoordinates n trivialCharacter c').1) :
    (globalCoordinates n trivialCharacter c).2 = (globalCoordinates n trivialCharacter c').2 := by
  have hz := zeroFlags_litAll_of_inner N h3 hN n c hin
  have hz' := zeroFlags_litAll_of_inner N h3 hN n c' hin'
  obtain ⟨⟨ξP, hP1⟩, ⟨ξQ, hQ1⟩⟩ := exists_coordinates N n _ ((zeroFlags_iff_mixed N n hN _).mp hz)
  obtain ⟨⟨ξP', hP2⟩, ⟨ξQ', hQ2⟩⟩ := exists_coordinates N n _ ((zeroFlags_iff_mixed N n hN _).mp hz')
  have e1 : planeCuspSumEmbedding N n ξP = planeCuspSumEmbedding N n ξP' := by
    rw [hP1, hP2, ← phiPlane_globalCoordinates N h3 hN n c, ← phiPlane_globalCoordinates N h3 hN n c', hP]
  have e2 : ξP = ξP' := planeCuspSumEmbedding_injective N n e1
  have e3 : ξQ = ξQ' := by
    rw [hTΓ _ hz ξP ξQ hP1 hQ1, hTΓ _ hz' ξP' ξQ' hP2 hQ2, e2]
  have e4 : phiLine N h3 hN n (globalCoordinates n trivialCharacter c).2 =
      phiLine N h3 hN n (globalCoordinates n trivialCharacter c').2 := by
    rw [phiLine_globalCoordinates N h3 hN n c, phiLine_globalCoordinates N h3 hN n c', ← hQ1, ← hQ2, e3]
  have e5 : (globalCoordinates n trivialCharacter c).2 - (globalCoordinates n trivialCharacter c').2 = 0 :=
    eq_zero_of_phiLine_eq_zero N h3 hN n _ (by rw [map_sub, e4, sub_self])
  exact sub_eq_zero.mp e5

include h3 hN in
/-- **Graph clause (ii) of `line_constant_term_comparison` from the `Γ(N)` statement.**  If `T` has the existence clause (i), then every global cocycle with
`InnerBoundary` plane coordinate has line coordinate `T` of its plane coordinate. -/
theorem graph_clause_of_gammaN (TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n) (hTΓ : GraphMapGamma N n TΓ)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ))
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hin : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1) :
    (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1 := by
  obtain ⟨c₀, hc₀⟩ := hT _ hin
  have hin₀ : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c₀).1 := by
    rw [hc₀]; exact hin
  have := line_coordinate_eq_of_plane_eq N h3 hN n TΓ hTΓ c c₀ hin hin₀ (by rw [hc₀])
  rw [this, hc₀]

end Uniqueness

section Final

open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

include h3 hN in
/-- **CMP-C5.**  Let `TΓ` be the printed constant term of the literal `Γ(N)` Proposition C.5 (`propC5_gammaN_printed`). For every map `T`
with the existence clause (i) of the `line_constant_term_comparison` (every `InnerBoundary` plane class is the plane coordinate of a global `K†`-cocycle with
line coordinate `T ξ`):
* the graph clause (ii) of `line_constant_term_comparison` holds for `T` (it follows from the literal `Γ(N)` clause and the injectivity of the line dictionary);
* `T` is the transport of `TΓ`: for every inner `ξ` there is `ξ' ∈ 𝒞_P(E)` with `ξ'` equal to the `Γ(N)` plane boundary of `ξ` and
  `TΓ ξ'` equal to the `Γ(N)` line boundary of `T ξ`. -/
theorem prop_C_5_comparison (hn : 4 ≤ n) :
    ∃ TΓ : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n,
      (∀ (f : TwTuple N n) (ξ : PlaneCuspSum N n), planeCuspSumEmbedding N n ξ = seedBoundary N n f →
        lineCuspSumEmbedding N n (TΓ ξ) = lineBoundary N n (classCG N n hn f)) ∧
      GraphMapGamma N n TΓ ∧
      ∀ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
        (∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
          ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
            globalCoordinates n trivialCharacter c = (ξ, T ξ)) →
        (∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
          InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 →
          (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1) ∧
        ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
          ∃ ξ' : PlaneCuspSum N n, planeCuspSumEmbedding N n ξ' = phiPlane N h3 hN n ξ ∧
            lineCuspSumEmbedding N n (TΓ ξ') = phiLine N h3 hN n (T ξ) := by
  obtain ⟨TΓ, h1, -, h3'⟩ := propC5_gammaN_printed (N := N) (n := n) hN hn
  have hG : GraphMapGamma N n TΓ := fun c hc ξP ξQ e1 e2 => h3' c hc ξP ξQ e1 e2
  exact ⟨TΓ, h1, hG, fun T hT =>
    ⟨fun c hin => graph_clause_of_gammaN N h3 hN n TΓ hG T hT c hin,
      fun ξ hξ => identification N h3 hN n TΓ hG T hT ξ hξ⟩⟩

end Final
end TernaryPeriodPolynomials.Argument.KDaggerComparison
