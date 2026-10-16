module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.CompleteDictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.CompleteTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Inner
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Converse
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm

@[expose] public section


/-!
# `K†` comparison, completeness of the face dictionary, line side

The line analogues of `CompleteDictionary`: `LineQInvariants`, `range_phiLine`, `phiLineEquiv`, `innerBoundary_iff_phiLine_mem_range`,
`phiLineInnerEquiv`, `vanishesOnGood_iff_phiLineAt`, `vanishesOnGood_iff_phiLine`.

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

section Line

open scoped Classical

/-- Reading a family of classes over all rational lines at the chosen representatives of the faces of `Γ(N)`. -/
def lineReps : FaceFamily N n .line →ₗ[ℂ] LineFaceH2 N n :=
  ∑ i : LineFaces N, (DirectSum.lof ℂ (LineFaces N)
    (fun i => groupCohomology.H2 (lineFaceRep N i.rep n)) i).comp
      ((lineH2Equiv N h3 i.rep n trivialCharacter hN).toLinearMap ∘ₗ LinearMap.proj (lineFlagAt i.rep))

theorem lineReps_apply (w : FaceFamily N n .line) (i : LineFaces N) :
    lineReps N h3 hN n w i =
      lineH2Equiv N h3 i.rep n trivialCharacter hN (w (lineFlagAt i.rep)) := by
  simp only [lineReps, LinearMap.sum_apply, LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [DFinsupp.finsetSum_apply]
  simp [DirectSum.of_apply]

theorem phiLine_eq_comp : phiLine N h3 hN n = lineReps N h3 hN n ∘ₗ stratumFamily N n .line := by
  apply LinearMap.ext
  intro ξ
  ext1 i
  rw [phiLine_apply, LinearMap.comp_apply, lineReps_apply]
  rfl

/-- **The `K†`-invariant line vectors** of `⨁_{faces of Γ(N)} H²(Γ(N) ∩ face, E_n)`: those that extend to a `K†`-invariant family over
all rational lines. -/
def LineQInvariants : Submodule ℂ (LineFaceH2 N n) :=
  (qFamilies N n .line).map (lineReps N h3 hN n)

theorem mem_lineQInvariants_iff (v : LineFaceH2 N n) :
    v ∈ LineQInvariants N h3 hN n ↔ ∃ w ∈ qFamilies N n .line, ∀ i : LineFaces N,
      lineH2Equiv N h3 i.rep n trivialCharacter hN (w (lineFlagAt i.rep)) = v i := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, fun i => (lineReps_apply N h3 hN n w i).symm⟩
  · rintro ⟨w, hw, h⟩
    refine ⟨w, hw, ?_⟩
    ext1 i
    rw [lineReps_apply, h]

/-- **Completeness of the line dictionary (CMP-2).**  The image of `phiLine` is exactly the `K†`-invariant vectors. -/
theorem range_phiLine : LinearMap.range (phiLine N h3 hN n) = LineQInvariants N h3 hN n := by
  rw [phiLine_eq_comp, LinearMap.range_comp, range_stratumFamily]
  rfl

theorem phiLine_injective : Function.Injective (phiLine N h3 hN n) := by
  rw [injective_iff_map_eq_zero]
  exact fun ξ h => eq_zero_of_phiLine_eq_zero N h3 hN n ξ h

/-- **The line face dictionary is a linear isomorphism onto the `K†`-invariant line vectors.** -/
def phiLineEquiv : StratumH2 n trivialCharacter .line ≃ₗ[ℂ] LineQInvariants N h3 hN n :=
  (LinearEquiv.ofInjective (phiLine N h3 hN n) (phiLine_injective N h3 hN n)).trans
    (LinearEquiv.ofEq _ _ (range_phiLine N h3 hN n))

theorem phiLineEquiv_apply (ξ : StratumH2 n trivialCharacter .line) :
    ((phiLineEquiv N h3 hN n ξ : LineQInvariants N h3 hN n) : LineFaceH2 N n) = phiLine N h3 hN n ξ := rfl

/-- **Inner classes = mixed cuspidal vectors (converse of `phiLine_mem_range`).** -/
theorem innerBoundary_of_phiLine_mem_range (ξ : StratumH2 n trivialCharacter .line)
    (h : phiLine N h3 hN n ξ ∈ LinearMap.range (lineCuspSumEmbedding N n)) :
    InnerBoundary n trivialCharacter .line ξ := by
  refine (innerBoundary_iff_locallyInner ξ).mpr fun F => ?_
  obtain ⟨i, γ, hγ, hF⟩ := exists_lineFace_translate N F
  have hmem : Matrix.SpecialLinearGroup.mapGL ℚ γ ∈ rationalLevel :=
    levelPrincipal_le N (mapGL_mem_levelPrincipal N h3 hγ)
  have hi : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (lineFlagAt i.rep) ξ ∈ locallyInnerClasses n trivialCharacter .line (lineFlagAt i.rep) := by
    refine (locallyInnerClasses_lineFlag_iff N h3 i.rep n trivialCharacter hN _).mpr ?_
    have := (mem_range_lineCuspSumEmbedding N n _).mp h i
    rwa [phiLine_apply] at this
  have e := stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
    ⟨_, hmem⟩ (lineFlagAt i.rep) F hF.symm ξ
  rw [← e]
  exact stabilizerTransportH2_mem_locallyInner n trivialCharacter .line ⟨_, hmem⟩ _ _ hF.symm _ hi

theorem innerBoundary_iff_phiLine_mem_range (ξ : StratumH2 n trivialCharacter .line) :
    InnerBoundary n trivialCharacter .line ξ ↔
      phiLine N h3 hN n ξ ∈ LinearMap.range (lineCuspSumEmbedding N n) :=
  ⟨phiLine_mem_range N h3 hN n ξ, innerBoundary_of_phiLine_mem_range N h3 hN n ξ⟩

/-- **The inner line classes are isomorphic to the `K†`-invariant mixed cuspidal vectors `𝒞_Q(E)^{K†}`.** -/
def phiLineInnerEquiv : FacePairingFull.innerClasses n .line ≃ₗ[ℂ]
    ↥(LineQInvariants N h3 hN n ⊓ LinearMap.range (lineCuspSumEmbedding N n)) :=
  (Submodule.equivMapOfInjective (phiLine N h3 hN n) (phiLine_injective N h3 hN n)
    (FacePairingFull.innerClasses n .line)).trans
    (LinearEquiv.ofEq _ _ (by
      ext v
      constructor
      · rintro ⟨ξ, hξ, rfl⟩
        exact ⟨(range_phiLine N h3 hN n).le ⟨ξ, rfl⟩, phiLine_mem_range N h3 hN n ξ hξ⟩
      · rintro ⟨hv, hc⟩
        obtain ⟨ξ, rfl⟩ := (range_phiLine N h3 hN n).ge hv
        exact ⟨ξ, innerBoundary_of_phiLine_mem_range N h3 hN n ξ hc, rfl⟩))

/-- **`VanishesOnGood` at every integral change of basis** (line side). -/
theorem vanishesOnGood_iff_phiLineAt (ξ : StratumH2 n trivialCharacter .line) :
    VanishesOnGood n trivialCharacter .line ξ ↔
      ∀ h : SL(3, ℤ), GoodFlag .line (lineFlagAt h) → phiLineAt N h3 hN n h ξ = 0 := by
  rw [vanishesOnGood_iff_fixedPointH2]
  constructor
  · intro hv h hg
    have := hv _ hg
    change lineH2Equiv N h3 h n trivialCharacter hN
      (resPrincipal N (lineFlagAt h) (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (lineFlagAt h) ξ)) = 0
    rw [this, LinearMap.map_zero, LinearEquiv.map_zero]
  · intro hv F hF
    obtain ⟨h, rfl⟩ := lineFlagAt_surjective F
    exact fixedPointH2_eq_zero_of_res N n ξ _
      ((lineH2Equiv N h3 h n trivialCharacter hN).map_eq_zero_iff.mp (hv h hF))

/-- **`VanishesOnGood` ⟺ zero restriction at every good face of `Γ(N)`** (line side). -/
theorem vanishesOnGood_iff_phiLine (ξ : StratumH2 n trivialCharacter .line) :
    VanishesOnGood n trivialCharacter .line ξ ↔
      ∀ i : LineFaces N, GoodFlag .line (lineFlagAt i.rep) → phiLine N h3 hN n ξ i = 0 := by
  rw [vanishesOnGood_iff_fixedPointH2]
  constructor
  · intro hv i hg
    rw [phiLine_apply]
    have := hv _ hg
    change lineH2Equiv N h3 i.rep n trivialCharacter hN
      (resPrincipal N (lineFlagAt i.rep) (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
          (lineFlagAt i.rep) ξ)) = 0
    rw [this, LinearMap.map_zero, LinearEquiv.map_zero]
  · intro hv F hF
    obtain ⟨i, γ, hγ, hFγ⟩ := exists_lineFace_translate N F
    have hmem : Matrix.SpecialLinearGroup.mapGL ℚ γ ∈ rationalLevel :=
      levelPrincipal_le N (mapGL_mem_levelPrincipal N h3 hγ)
    have hg : GoodFlag .line (lineFlagAt i.rep) := by
      rw [hFγ] at hF
      exact (goodFlag_rationalLevel_smul_iff .line ⟨_, hmem⟩ _).mp hF
    have h1 := hv i hg
    rw [phiLine_apply] at h1
    have h2 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (lineFlagAt i.rep) ξ = 0 :=
      fixedPointH2_eq_zero_of_res N n ξ _
        ((lineH2Equiv N h3 i.rep n trivialCharacter hN).map_eq_zero_iff.mp h1)
    exact fixedPointH2_eq_zero_of_orbit N h3 n ξ _ F γ hγ hFγ h2

end Line

end TernaryPeriodPolynomials.Argument.KDaggerComparison
