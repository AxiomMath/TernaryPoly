module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NSeedSurj
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CellOrbit
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.ZeroFlagsPlane
public import TernaryPeriodPolynomials.EisensteinSeries.Class.BridgeK

@[expose] public section


/-!
# The plane constant terms of the classical series at level `Γ(N)` (unconditional) and `eisensteinP`

Formalized by Claude Sonnet 5.5.

* `CuspValues`: the exact restrictions of the series at every cusp to every plane cusp (membership in the seed span, vanishing for different orbits, the seed class for the same cusp);
* `cuspValues`: they hold for `3 ≤ N`, `4 ≤ n`, from the `resAtC_value_none/pos/neg` (`EisensteinClass/BridgeK`) and the cell combinatorics (`CellOrbit`);
* **`classicalPlane_of_values`**, **`classicalPlaneConstantTerms`**: `ClassicalPlaneConstantTerms` (`r_B = 0` via `zeroFlags_of_plane_mixed`, `r_P ℰ_P(ξ) = ξ` at every plane face);
* **`eisensteinP_gammaN`**: the `eisensteinP` obligation, unconditional (a linear section of the seed map; the canonical `T` and the printed identification remain separate obligations).
-/

open scoped MatrixGroups DirectSum
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **The restrictions of the series to the plane cusps, as complex classes of `faceRep N h n`** (the values to be delivered by S6's complex bridge
`resAtC ∘ complexify = complexifyAt ∘ resTo` and `cuspSeedAt ↦ faceSeedKerClass`):
* `mem`: the restriction of the series at the cusp `h'` (seed `b`) to the plane cusp `h` lies in the seed span of `h` (this is `SeriesRestrictionInSeedSpan` for every `f`);
* `none`: it is zero if the cusps are in different `Γ(N)`-orbits (no cell);
* `self_hol`, `self_conj`: the restriction of the series at the cusp `h` to the same cusp is exactly the seed class. -/
structure CuspValues (hn : 4 ≤ n) : Prop where
  mem : ∀ (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h h' : SL(3, ℤ)) (b : Bool),
    resAtC N h n (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g h' b hn)) ∈ faceSeedSpan N h n
  none : ∀ (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h h' : SL(3, ℤ)) (b : Bool),
    (∀ c : Ck N (h' * h⁻¹), ¬ IsCellK N (h' * h⁻¹) c) →
      resAtC N h n (EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g h' b hn)) = 0
  self_hol : ∀ (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ)),
    resAtC N h n (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g h false hn)) = (faceSeedKerClass N h n g).1
  self_conj : ∀ (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ)),
    resAtC N h n (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g h true hn)) = (faceSeedConjKerClass N h n g).1

open scoped Classical in
/-- **`ClassicalPlaneConstantTerms` from the cusp values**: `r_B = 0` and `r_P ℰ_P(ξ) = ξ` for the summed classical series. -/
theorem classicalPlane_of_values (hN : 3 ≤ N) (hn : 4 ≤ n) (hv : CuspValues N n hn) :
    ClassicalPlaneConstantTerms N n hn := by
  intro f
  have hsum : ∀ h : SL(3, ℤ), rPlane N n h (classCG N n hn f) =
      ∑ x : PlaneFaces N, ∑ b : Bool, resAtC N h n (EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b) (planeFaceRepr x) b hn)) := by
    intro h
    have e : rPlane N n h = resAtC N h n := by
      unfold rPlane resAtC twoCohomologyRestriction
      rfl
    rw [e]
    unfold classCG
    exact (map_sum (resAtC N h n) _ _).trans (Finset.sum_congr rfl fun x _ => map_sum (resAtC N h n) _ _)
  refine ⟨?_, ?_⟩
  · refine zeroFlags_of_plane_mixed N n hN _ fun h => ?_
    rw [hsum]
    refine Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun b _ => ?_
    exact faceSeedSpan_le_cuspidalInH2 N h n (hv.mem _ _ _ _)
  · apply DFinsupp.ext
    intro i
    rw [planeBoundary_apply, hsum, seedBoundary_apply, Finset.sum_eq_single i]
    · rw [Fintype.sum_bool, hv.self_conj, hv.self_hol, add_comm]
    · intro x _ hxi
      refine Finset.sum_eq_zero fun b _ => ?_
      exact hv.none _ _ _ _ (no_cell_of_ne N hxi)
    · simp

/-- **The cusp values hold (unconditionally for `3 ≤ N`, `4 ≤ n`)**, from S6's exact values `resAtC_value_none/pos/neg` and the cell combinatorics of `CellOrbit`. -/
theorem cuspValues (hN : 3 ≤ N) (hn : 4 ≤ n) : CuspValues N n hn where
  mem g h h' b := resAtC_eisensteinAtClass_mem_faceSeedSpan N n h g hn h' b hN
  none g h h' b hnone := resAtC_value_none (f := g) (hn := hn) b hN hnone
  self_hol g h := by
    obtain ⟨c₀, hc, h22, hsl⟩ := cell_self N hN n g h
    have := resAtC_value_pos (f := g) (hn := hn) (b := false) hN hc h22
    rw [ite_eq_right (by simp), hsl] at this
    exact this
  self_conj g h := by
    obtain ⟨c₀, hc, h22, hsl⟩ := cell_self N hN n g h
    have := resAtC_value_pos (f := g) (hn := hn) (b := true) hN hc h22
    rw [ite_eq_left rfl, hsl] at this
    exact this

/-- **`ClassicalPlaneConstantTerms` (unconditional)**: `r_B ℰ_P(ξ) = 0` and `r_P ℰ_P(ξ) = ξ` at every plane face of `Γ(N)`, `3 ≤ N`, `4 ≤ n`. -/
theorem classicalPlaneConstantTerms (hN : 3 ≤ N) (hn : 4 ≤ n) : ClassicalPlaneConstantTerms N n hn :=
  classicalPlane_of_values N n hN hn (cuspValues N n hN hn)

/-- **S1's `eisensteinP`, unconditional** (`3 ≤ N`, `4 ≤ n`): one linear `T : 𝒞_P(E) → 𝒞_Q(E)` and for each `ξ` a global class of `Γ(N)` with zero flag restrictions,
plane coordinate `ξ` and line coordinate `Tξ` (built from a linear section of the seed map; not the canonical, section-independent `T`). -/
theorem eisensteinP_gammaN (hN : 3 ≤ N) (hn : 4 ≤ n) :
    ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n,
      ∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
        planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧
          lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c :=
  eisensteinP_of_planeConstantTerms N n hN hn (classicalPlaneConstantTerms N n hN hn)

end TernaryPeriodPolynomials.Argument.FormClassK
