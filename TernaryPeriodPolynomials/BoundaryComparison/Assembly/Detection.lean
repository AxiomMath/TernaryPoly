module

public import TernaryPeriodPolynomials.BoundaryComparison.ClassicalFaces.Certificate
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.ClusterDetection

@[expose] public section


/-!
# Detection through the classical faces: per-datum and Hecke-character cluster

`perDatumDetection_classical` and `cluster_zero_classical` are the copies of `perDatumDetectionMS`
(`Entry/PerDatumMS.lean`) and `cluster_zero` (`ManuscriptC6/ClusterDetection.lean`) in which the good-line
nonvanishing is `cuspRes_line_true_image_ne_zero_certified` (which uses the R3 certificate
`paper_entry_at_classical_faces` at `N = 6`, `ClassicalFaces/Certificate.lean`, hence R2's `paper_finite_entry`).
`cluster_zero_classical` takes an arbitrary uniqueness map `T₀` (R1's graph map in the final assembly).  Neither uses `badPlaneEntryIdentity`, `cuspRes_line_true_image_ne_zero` or `Targets.PropC5`.  The helper
lemmas `exists_package_of_nonzero`, `exists_smul_of_vanishesOnGood`, `scalar_eq_zero_of_image_vanishes`,
`exists_smul_plane`, `localJoint_congr`, `pairChar` are reused unchanged.

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.LocalInterface
open TernaryPeriodPolynomials.Spectral.LocalLevelOne
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConsumersStd
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
open TernaryPeriodPolynomials.Argument.BadPlaneInjectivity (IsUniquenessMap)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

/-- **Per-datum detection through the classical faces.**  The copy of `perDatumDetectionMS` whose good-line
nonvanishing is `cuspRes_line_true_image_ne_zero_certified` (through the R3 certificate
`paper_entry_at_classical_faces`). -/
theorem perDatumDetection_classical (n : ℕ) (hn : 0 < n) (D : CohomologicalCuspData n)
    (T : boundarySummand D.inducingData .plane →ₗ[ℂ] boundarySummand D.inducingData .line)
    (hT : RealizesStandardConv D.inducingData T) (ξ : boundarySummand D.inducingData .plane)
    (hplane : VanishesOnGood n D.inducingData.chi .plane ξ.val)
    (hline : VanishesOnGood n D.inducingData.chi .line (T ξ).val) : ξ = 0 := by
  by_contra hξ
  have hobtain1 := exists_package_of_nonzero n hn D ξ hξ hplane
  obtain ⟨hodd, ⟨P⟩⟩ := hobtain1
  have hTζ := cuspRes_line_true_image_ne_zero_certified n D hodd P.S P.I P.halfWeight_eq P.vector_eq T hT
  have hζgood : cuspRes n D.inducingData.chi .plane true (SphericalEntryData.badPlaneClass P.S P.I).val = 0 :=
    cuspRes_plane_true_badPlane D.inducingData _
      (planeSource_isSourceCocycle D.inducingData _ P.S.hχ) (SphericalEntryData.badPlane_isSourceCocycle P.S P.I)
  exact detection_of_witness n D (by have := P.S.large; omega) T ξ hξ hplane hline
    (SphericalEntryData.badPlaneClass P.S P.I) hTζ hζgood

/-- **Detection on a character cluster, through the classical faces.**  The copy of `cluster_zero` whose good-line
nonvanishing is `cuspRes_line_true_image_ne_zero_certified`; `T₀` is an arbitrary uniqueness map (R1's graph map in
the final assembly). -/
theorem cluster_zero_classical (n : ℕ) (hn : 4 ≤ n)
    (hecke : BoundaryHecke n trivialCharacter) (hhecke : ActualBoundaryHecke n trivialCharacter hecke)
    (hhol : ∀ D : CohomologicalCuspData n, PlaneEisensteinConvergent D.inducingData)
    (T₀ : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT₀ : IsUniquenessMap n trivialCharacter T₀)
    (C : Finset (CohomologicalCuspData n)) (f : CohomologicalCuspData n → StratumH2 n trivialCharacter .plane)
    (hf : ∀ D ∈ C, f D ∈ boundarySummand D.inducingData .plane)
    (same : ∀ D ∈ C, ∀ D' ∈ C, pairChar hecke hhecke D = pairChar hecke hhecke D')
    (hplane : VanishesOnGood n trivialCharacter .plane (∑ D ∈ C, f D))
    (hline : VanishesOnGood n trivialCharacter .line (T₀ (∑ D ∈ C, f D))) : ∑ D ∈ C, f D = 0 := by
  classical
  by_contra hξ
  set ξ := ∑ D ∈ C, f D with hξdef
  have hξgood : cuspRes n trivialCharacter .plane true ξ = 0 :=
    vanishesOnGood_fixedPointH2 hplane (cuspFlag .plane true) ((cuspFlag_good_iff .plane true).mpr rfl)
  have hξbad : cuspRes n trivialCharacter .plane false ξ ≠ 0 := fun h =>
    hξ ((eq_zero_iff_cuspRes .plane ξ).mpr ⟨hξgood, h⟩)
  obtain ⟨D₁, hD₁, hD₁ne⟩ : ∃ D ∈ C, cuspRes n trivialCharacter .plane false (f D) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hξbad
    rw [hξdef, map_sum]
    exact Finset.sum_eq_zero hall
  have hsph : SphericalCusp D₁.cusp := by
    by_contra hns
    exact hD₁ne (TernaryPeriodPolynomials.Separation.cuspRes_plane_false_eq_zero_of_not_spherical
      D₁.inducingData hns (hf D₁ hD₁))
  have hodd := TernaryPeriodPolynomials.LevelOneCohomologicalParity.level_one_cohomological_parity
    n (by omega) D₁.inducingData rfl hsph
  have hobtain3 := exists_sphericalEntryPackage D₁.inducingData hodd rfl hsph
  obtain ⟨P⟩ := hobtain3
  have hT := standardFromT0Std_realizesStandardConv D₁ hn (hhol D₁) T₀ hT₀
  have hTζ := cuspRes_line_true_image_ne_zero_certified n D₁ hodd P.S P.I P.halfWeight_eq P.vector_eq _ hT
  have hζgood : cuspRes n trivialCharacter .plane true (SphericalEntryData.badPlaneClass P.S P.I).val = 0 :=
    cuspRes_plane_true_badPlane D₁.inducingData _
      (TernaryPeriodPolynomials.SourceConstruction.planeSource_isSourceCocycle D₁.inducingData _ P.S.hχ) (SphericalEntryData.badPlane_isSourceCocycle P.S P.I)
  have hξK : cuspRes n trivialCharacter .plane false ξ ∈ localJoint n trivialCharacter
      (TernaryPeriodPolynomials.Spectral.pairCharacter D₁.inducingData hecke hhecke) .plane false := by
    rw [hξdef, map_sum]
    refine Submodule.sum_mem _ (fun D hD => ?_)
    have h1 := cuspRes_mem_localJoint_of_mem D.inducingData hecke hhecke .plane false (hf D hD)
    have h2 : localJoint n trivialCharacter
        (TernaryPeriodPolynomials.Spectral.pairCharacter D.inducingData hecke hhecke) .plane false =
        localJoint n trivialCharacter
          (TernaryPeriodPolynomials.Spectral.pairCharacter D₁.inducingData hecke hhecke) .plane false := by
      apply localJoint_congr
      intro t ht
      exact congrFun (same D hD D₁ hD₁) ⟨t, ht⟩
    rw [h2] at h1
    exact h1
  have hlg : cuspRes n trivialCharacter .line true (T₀ ξ) = 0 :=
    vanishesOnGood_fixedPointH2 hline (cuspFlag .line true) ((cuspFlag_good_iff .line true).mpr rfl)
  exact hξ (eq_zero_of_witness n hn D₁ hecke hhecke T₀ ξ hξgood hξK hlg
    (SphericalEntryData.badPlaneClass P.S P.I) hζgood hTζ)

end TernaryPeriodPolynomials.Argument.BoundaryComparison
