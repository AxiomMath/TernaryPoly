module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.Assembly
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.PlanePeriodExact
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Period.MemberRealized
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.Covers
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtPlanePeriodVector
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Dimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SturmBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main

@[expose] public section


/-!
# `GoodPlanePeriodsRealized`: every parabolic class is realized by the automorphic plane span

Good-plane analogue of `Automorphic.DirectFinal.periodsRealized_of`
(`Period.MemberRealized.memberRealized` + `Constituent.modelCoversForms`), using
`PlanePeriodExact.goodPlaneEdge_sourceCoordinate_eq_period` in place of the line-side exact-value
identity.

The good-plane Levi has the same level (three) as the bad line, so `levelPeriodMap (n+1) (-1)` is
the same map on both sides; `levelPeriodMap_injective_goodPlane` (unconditional in `n`) identifies
its range with the parabolic subspace for every `n`. For `n < 3` that subspace is already `⊥`
(`S (n+1)` is `0`-dimensional there), so the realization is vacuous; for `n ≥ 3`,
`Constituent.modelCoversForms` decomposes every cusp form into pieces individually realized by
`plane_memberRealized`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.LevelThree.GoodPlaneConj
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot (qcls qcls_eq_zero_iff qcls_add qcls_smul)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity
  (levelPlus levelPeriodMap levelPeriodMap_apply)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
  (S periodCocycle form_holo)
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspLevel cuspRes CuspH2)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag goodPlaneFrame)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.LevelThreeSource
open TernaryPeriodPolynomials.EvenLevelThree
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Automorphic.Contracts (wtOf)
open TernaryPeriodPolynomials.Automorphic.Period.MemberRealized (classicalToWeight)
open TernaryPeriodPolynomials.Automorphic.Constituent (modelCoversForms)
open TernaryPeriodPolynomials.MultiplicityOne (LevelThreeCusp)
open TernaryPeriodPolynomials.LevelThreeInjective.Main (levelPeriodMap_injective_goodPlane)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodDimension
  (finrank_cuspForm_eq' levelPeriodMap_range_eq_parabolic_of_injective)
open TernaryPeriodPolynomials.LevelThree.SturmBound (cuspForm_finiteDimensional)
open Module (finrank)

noncomputable section


namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan

variable {n : ℕ}

/-- For `n < 3` the classical cusp-form space `S (n+1)` is `0`-dimensional, so the parabolic
subspace of `levelRep (n+1) (-1)` is already `⊥`: the realization goal is vacuous. -/
theorem small_n_vacuous (hn : 0 < n) (hn3 : n < 3) :
    ∀ y ∈ parabolicH1 (levelRep (n + 1) (-1)) (upper 1) (lower 1),
      ∃ ξ' ∈ automorphicPlaneSpan n,
        goodPlaneEdge hn (cuspRes n trivialCharacter .plane true ξ') = y := by
  have hfd : FiniteDimensional ℂ (S (n + 1)) := cuspForm_finiteDimensional _
  have hrank : finrank ℂ (S (n + 1)) = 0 := by
    have h := finrank_cuspForm_eq' (m := n + 1)
    omega
  have hall : ∀ x : S (n + 1), x = 0 := finrank_zero_iff_forall_zero.mp hrank
  have hinj : Function.Injective (levelPeriodMap (n + 1) (-1)) :=
    fun a b _ => (hall a).trans (hall b).symm
  have hrange := levelPeriodMap_range_eq_parabolic_of_injective (Nat.succ_pos n) hinj
  intro y hy
  rw [← hrange] at hy
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [← hx, hall x]
  simp

/-- **The plane analogue of `Period.MemberRealized.memberRealized`.** For a single classical
level-three weight vector `w` of `M.cusp`, its scalar-weighted cusp form is realized: there is a
plane source class in `automorphicPlaneSpan n` whose good-plane edge is `-` the level-period-map
value of that form. -/
theorem plane_memberRealized (hn : 0 < n) (M : CohomologicalCuspData n)
    (w : levelThreeClassicalVectorsWt M.cusp (wtOf n)) :
    ∃ g : S (n + 1),
      (⇑g : UpperHalfPlane → ℂ) = cuspScalarWeightedLinearWt M.cusp (wtOf n) 1 w.1 ∧
        ∃ ξ' ∈ automorphicPlaneSpan n,
          goodPlaneEdge hn (cuspRes n trivialCharacter .plane true ξ') =
            - levelPeriodMap (n + 1) (-1) g := by
  by_cases hw : w = 0
  · have h0 : w.1 = 0 := congrArg Subtype.val hw
    exact ⟨0, by simp [h0], 0, Submodule.zero_mem _, by simp⟩
  · have hσ : LevelThreeCusp M.cusp := levelThreeCusp_of_weightVector (classicalToWeight M.cusp n w)
      (fun h => hw (Subtype.ext (by simpa [classicalToWeight] using congrArg Subtype.val h)))
    have negative : wtOf n < 0 := by show -((n : ℤ) + 3) < 0; omega
    have weight : -(wtOf n) = ((n + 1 : ℕ) : ℤ) + 2 := by
      show -(-((n : ℤ) + 3)) = ((n + 1 : ℕ) : ℤ) + 2
      push_cast; omega
    obtain ⟨g, hg⟩ := l3p_exists_S_cast (n + 1) weight
      (levelThreeFormWt M.cusp (wtOf n) negative w.1 w.2)
    have hf : (g : UpperHalfPlane → ℂ) = cuspScalarWeightedLinearWt M.cusp (wtOf n) 1 w.1 :=
      hg.trans (levelThreeForm_coeWt M.cusp (wtOf n) negative w.1 w.2)
    let stages := TernaryPeriodPolynomials.AnalyticClasses.continuousStages M.inducingData
    let I := l3FamilyInputWt M.inducingData hσ (-((n : ℤ) + 3)) rfl (classicalToWeight M.cusp n w)
    have hα : L3PlanePeriodFormula (lteDataWt I stages) ⇑g := fun A =>
      l3pp_alpha_one_eq_formulaWt I stages hf (form_holo g) A
    have hsrc : goodPlaneSource M.inducingData (lteDataWt I stages) ∈
        sourceCocycles M.inducingData .plane :=
      goodPlaneSource_isSourceCocycle_of_trivial M.inducingData (lteDataWt I stages) rfl
    refine ⟨g, hf,
      sourceClass M.inducingData .plane ⟨goodPlaneSource M.inducingData (lteDataWt I stages), hsrc⟩,
      ?_, ?_⟩
    · exact Submodule.subset_span ⟨M, by
        rw [← sourceClass_range M.inducingData .plane]; exact LinearMap.mem_range_self _ _⟩
    · exact goodPlaneEdge_sourceCoordinate_eq_period hn M (lteDataWt I stages) g hα

/-- List-induction assembly of `plane_memberRealized` across a `modelCoversForms` decomposition. -/
private theorem plane_key (hn : 0 < n)
    (l : List (Σ D : CohomologicalCuspData n, levelThreeClassicalVectorsWt D.cusp (wtOf n))) :
    ∃ g : S (n + 1), (⇑g : UpperHalfPlane → ℂ) =
        (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (wtOf n) 1 p.2.1).sum ∧
      ∃ ξ' ∈ automorphicPlaneSpan n,
        goodPlaneEdge hn (cuspRes n trivialCharacter .plane true ξ') =
          - levelPeriodMap (n + 1) (-1) g := by
  induction l with
  | nil => exact ⟨0, by simp, 0, Submodule.zero_mem _, by simp⟩
  | cons p l ih =>
    obtain ⟨g, hg, ξ'₀, hξ'₀mem, hξ'₀⟩ := ih
    obtain ⟨f, hf, ξ'₁, hξ'₁mem, hξ'₁⟩ := plane_memberRealized hn p.1 p.2
    refine ⟨f + g, ?_, ξ'₁ + ξ'₀, Submodule.add_mem _ hξ'₁mem hξ'₀mem, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      rw [← hg, ← hf]
      rfl
    · simp only [map_add]
      rw [hξ'₀, hξ'₁]
      abel

/-- For `n ≥ 3`, `modelCoversForms` decomposes every cusp form into realized pieces, so every
parabolic class (via the unconditional range identification) is realized. -/
theorem large_n_realized (hn : 0 < n) (hn3 : 3 ≤ n) :
    ∀ y ∈ parabolicH1 (levelRep (n + 1) (-1)) (upper 1) (lower 1),
      ∃ ξ' ∈ automorphicPlaneSpan n,
        goodPlaneEdge hn (cuspRes n trivialCharacter .plane true ξ') = y := by
  intro y hy
  have hrange := levelPeriodMap_range_eq_parabolic_of_injective (Nat.succ_pos n)
    (levelPeriodMap_injective_goodPlane n)
  rw [← hrange] at hy
  obtain ⟨f, hf⟩ := hy
  obtain ⟨l, hl⟩ := modelCoversForms n hn3 f
  obtain ⟨g, hg, ξ', hξ'mem, hedge⟩ := plane_key hn l
  have hgf : g = f := DFunLike.coe_injective (hg.trans hl.symm)
  refine ⟨-ξ', Submodule.neg_mem _ hξ'mem, ?_⟩
  simp only [map_neg]
  rw [hedge, hgf, neg_neg]
  exact hf

theorem goodPlanePeriodsRealized (n : ℕ) (hn : 0 < n) : GoodPlanePeriodsRealized n hn := by
  by_cases hn3 : 3 ≤ n
  · exact large_n_realized hn hn3
  · exact small_n_vacuous hn (by omega)

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
