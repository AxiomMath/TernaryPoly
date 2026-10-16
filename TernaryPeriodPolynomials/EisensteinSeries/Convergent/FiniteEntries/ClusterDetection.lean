module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.PerDatumMS
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.HeckeCluster
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.sStd.StandardFromT0
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge

@[expose] public section


/-!
# Detection on a Hecke-character cluster (paper route, without isotypical projectors)

`cluster_zero`: let `C` be a finite family of data with a common away-three pair character, `f D` a plane class of
`boundarySummand D`, `ξ_C = ∑_{D ∈ C} f D`.  If `ξ_C` vanishes on the good plane and `T₀ ξ_C` on the good line, then
`ξ_C = 0`.  Proof: the coordinates of all `f D` at the bad-plane cusp lie in the local joint eigenspace of the common
character, of dimension at most one (`identityPlane_localUnique`); a nonzero `ξ_C` has a nonzero coordinate there, so some
`f D₁` does, hence `D₁.cusp` is spherical (`cuspRes_plane_false_eq_zero_of_not_spherical`); the entry package of `D₁` gives
the bad-plane section `ζ` whose image has nonzero good-line coordinate (`cuspRes_line_true_image_ne_zero`); then
`ξ_C = c ζ` and `T₀ ξ_C = c T₀ ζ` vanishes at the good line only for `c = 0`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.LocalInterface
open TernaryPeriodPolynomials.Spectral.LocalLevelOne
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConsumersStd
open TernaryPeriodPolynomials.Argument.BadPlaneInjectivity (IsUniquenessMap)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries

/-- The local joint eigenspace depends on the character only through its away-three values. -/
theorem localJoint_congr {n : ℕ} (χ : RankOneCharacter) (c c' : HeckeCorrespondence → ℂ) (side : Side) (good : Bool)
    (h : ∀ t, AwayThree t → c t = c' t) : localJoint n χ c side good = localJoint n χ c' side good := by
  unfold localJoint
  congr 1
  funext t
  rw [h t.1 t.2]

/-- The away-three pair character of a datum, as a function on the away-three correspondences. -/
def pairChar {n : ℕ} (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (D : CohomologicalCuspData n) :
    {t : HeckeCorrespondence // AwayThree t} → ℂ :=
  fun t => TernaryPeriodPolynomials.Spectral.pairCharacter D.inducingData hecke hhecke t.1

/-- **Multiplicity one at the bad-plane cusp for a character cluster.** -/
theorem exists_smul_plane (n : ℕ) (D₁ : CohomologicalCuspData n) (h3n : 3 ≤ n)
    (hecke : BoundaryHecke n trivialCharacter) (hhecke : ActualBoundaryHecke n trivialCharacter hecke)
    (ξ ζ : StratumH2 n trivialCharacter .plane)
    (hζ : ζ ∈ boundarySummand D₁.inducingData .plane)
    (hξK : cuspRes n trivialCharacter .plane false ξ ∈ localJoint n trivialCharacter
      (TernaryPeriodPolynomials.Spectral.pairCharacter D₁.inducingData hecke hhecke) .plane false)
    (hξgood : cuspRes n trivialCharacter .plane true ξ = 0)
    (hζgood : cuspRes n trivialCharacter .plane true ζ = 0)
    (hζbad : cuspRes n trivialCharacter .plane false ζ ≠ 0) : ∃ c : ℂ, ξ = c • ζ := by
  classical
  have hne : associatePair D₁.inducingData ≠ ⊥ := by
    intro hbot
    have hmem : ((ζ, 0) : BoundaryCoordinates n D₁.inducingData.chi) ∈ associatePair D₁.inducingData :=
      ⟨hζ, Submodule.zero_mem _⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hζbad (by rw [show ζ = 0 from congrArg Prod.fst hmem, map_zero])
  have hunique := identityPlane_localUnique D₁ hecke hhecke h3n hne
  have := cuspH2_finiteDimensional (n := n) D₁.inducingData.chi .plane false
  let K := localJoint n D₁.inducingData.chi (TernaryPeriodPolynomials.Spectral.pairCharacter
    D₁.inducingData hecke hhecke) .plane false
  have hζK : cuspRes n D₁.inducingData.chi .plane false ζ ∈ K :=
    cuspRes_mem_localJoint_of_mem D₁.inducingData hecke hhecke .plane false hζ
  have hne1 : (⟨_, hζK⟩ : K) ≠ 0 := fun h => hζbad (congrArg Subtype.val h)
  have hrank : Module.finrank ℂ K = 1 :=
    le_antisymm hunique (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne1⟩)
  have hobtain1 := (finrank_eq_one_iff_of_nonzero' _ hne1).mp hrank ⟨_, hξK⟩
  obtain ⟨c, hc⟩ := hobtain1
  have hcξ : cuspRes n D₁.inducingData.chi .plane false ξ =
      c • cuspRes n D₁.inducingData.chi .plane false ζ := (congrArg Subtype.val hc).symm
  refine ⟨c, ?_⟩
  have hz : ξ - c • ζ = 0 := by
    rw [eq_zero_iff_cuspRes]
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_smul, hξgood, hζgood, smul_zero, sub_zero]
    · rw [map_sub, map_smul, hcξ, sub_self]
  exact sub_eq_zero.mp hz

/-- The last step of the detection on a character cluster: a class `ξ` of the common local joint eigenspace vanishing on
the good plane, together with a witness `ζ` of the summand of `D₁` vanishing on the good plane and with nonvanishing
good-line image, vanishes as soon as its image vanishes on the good line. -/
theorem eq_zero_of_witness (n : ℕ) (hn : 4 ≤ n) (D₁ : CohomologicalCuspData n)
    (hecke : BoundaryHecke n trivialCharacter) (hhecke : ActualBoundaryHecke n trivialCharacter hecke)
    (T₀ : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (ξ : StratumH2 n trivialCharacter .plane)
    (hξgood : cuspRes n trivialCharacter .plane true ξ = 0)
    (hξK : cuspRes n trivialCharacter .plane false ξ ∈ localJoint n trivialCharacter
      (TernaryPeriodPolynomials.Spectral.pairCharacter D₁.inducingData hecke hhecke) .plane false)
    (hlg : cuspRes n trivialCharacter .line true (T₀ ξ) = 0)
    (ζ : boundarySummand D₁.inducingData .plane)
    (hζgood : cuspRes n trivialCharacter .plane true ζ.val = 0)
    (hTζ : cuspRes n trivialCharacter .line true (T₀ ζ.val) ≠ 0) : ξ = 0 := by
  have hζbad : cuspRes n trivialCharacter .plane false ζ.val ≠ 0 := by
    intro h0
    apply hTζ
    have : ζ.val = 0 := (eq_zero_iff_cuspRes .plane ζ.val).mpr ⟨hζgood, h0⟩
    rw [this, map_zero]
    exact map_zero _
  have hobtain3 := exists_smul_plane n D₁ (by omega) hecke hhecke ξ ζ.val ζ.property hξK hξgood hζgood hζbad
  obtain ⟨c, hc⟩ := hobtain3
  have hTξ : T₀ ξ = c • T₀ ζ.val := by rw [hc, map_smul]
  rw [hTξ, map_smul] at hlg
  have hc0 : c = 0 := (smul_eq_zero.mp hlg).resolve_right hTζ
  rw [hc, hc0, zero_smul]

/-- **Detection on a character cluster.** -/
theorem cluster_zero (n : ℕ) (hn : 4 ≤ n)
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
  have hobtain2 := exists_sphericalEntryPackage D₁.inducingData hodd rfl hsph
  obtain ⟨P⟩ := hobtain2
  have hT := standardFromT0Std_realizesStandardConv D₁ hn (hhol D₁) T₀ hT₀
  have hTζ := cuspRes_line_true_image_ne_zero n D₁.inducingData hodd rfl P.S P.I P.halfWeight_eq P.vector_eq _ hT
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

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
