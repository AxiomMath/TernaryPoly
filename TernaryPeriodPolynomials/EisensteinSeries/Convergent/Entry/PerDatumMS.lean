module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CuspResProj
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SupportSphericity
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelOneParity

@[expose] public section



/-!
# Per-datum detection along the paper route (Appendix C.6, odd case)

`perDatumDetectionMS`: for a paper datum `D` and any map `T` realizing the standard operator, a plane class
`ξ ∈ boundarySummand D` vanishing at the good plane whose image vanishes at the good line is zero.

Proof (the paper's, via the explicit entry): a nonzero such `ξ` has a bad-plane representative, hence `D.cusp`
has a spherical vector and `n` is odd (`bad_plane_support_sphericity`, `level_one_cohomological_parity`); N2's entry
package gives the Eichler input `I` and the bad-plane section `ζ = [badPlaneWeight · planeSource D (planeLevi I)]` of the
summand. The Shapiro coordinates of `ζ` are `(0 at the good plane)` and, by the class-level entry identity
(`classLevel_paper`), `T ζ` has the good-line coordinate `−printedScalar` times that of the line source of `I`, which is
nonzero (`lineSource_cuspRes_ne_zero_of_eichler`).  The local joint eigenspace of the pair character at the bad-plane
cusp has dimension at most one (`identityPlane_localUnique`), so `ξ = c ζ`, and the good-line coordinate of `T ξ`
vanishes only for `c = 0`.  This replaces `StandardConv.sphericalGoodCuspDetectionConvergent` (a modified port of the
original detection) by the explicit entry computation.

Formalized by Claude Sonnet 5.5.
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

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- `c • x = 0` over `ℂ` (proved for an arbitrary module so that the instance problem is not
re-solved on the concrete cohomology space). -/
private theorem complex_smul_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] {c : ℂ} {x : V}
    (h : c • x = 0) : c = 0 ∨ x = 0 :=
  smul_eq_zero.mp h


namespace SphericalEntryData

variable {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) (I : EichlerInput D.cusp n)

include S in
/-- The bad-plane section of the Eichler plane source, as a class of the plane summand. -/
def badPlaneClass : boundarySummand D .plane :=
  SourceQuotient.sourceToSummand D .plane
    ⟨fun y g => badPlaneWeight g • planeSource D (planeLevi I) y g, badPlane_isSourceCocycle S I⟩

theorem badPlaneClass_val :
    (badPlaneClass S I).val = SourceSpace.sourceClass D .plane
      ⟨fun y g => badPlaneWeight g • planeSource D (planeLevi I) y g, badPlane_isSourceCocycle S I⟩ := rfl

end SphericalEntryData

/-- **The good-line coordinate of the image of the bad-plane section is nonzero** (the entry identity). -/
theorem cuspRes_line_true_image_ne_zero (n : ℕ) (D : InducingData n) (hodd : Odd n)
    (hχ : D.chi = trivialCharacter) (S : SphericalEntryData D) (I : EichlerInput D.cusp n)
    (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T) :
    cuspRes n D.chi .line true (T (SphericalEntryData.badPlaneClass S I)).val ≠ 0 := by
  have hpaper := classLevel_paper n D S I hw hv T hT
  unfold PaperEntry at hpaper
  obtain ⟨hprinted, hSigP, hEq, hNeg⟩ := hpaper
  have hls0 : IsSourceCocycle D .line (lineSource D (SphericalEntryData.lineLevi I)) :=
    lineSource_isSourceCocycle D _ S.hχ
  have hline_ne := lineSource_cuspRes_ne_zero_of_eichler D hχ I hodd hls0
  have h1 := ((cuspRes_goodComponent .line _).symm.trans
    (congrArg (cuspRes n D.chi .line true) hEq)).trans
    (LinearMap.map_smul (cuspRes n D.chi .line true) S.printedScalar _)
  have h2 := (congrArg (cuspRes n D.chi .line true) hNeg).trans
    (LinearMap.map_neg (cuspRes n D.chi .line true) _)
  have h3 : cuspRes n D.chi .line true
      (SourceSpace.sourceClass D .line
        ⟨fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g,
          SphericalEntryData.goodLine_isSourceCocycle S I⟩) ≠ 0 := by
    rw [cuspRes_line_true_goodLine D _ hls0]
    exact hline_ne
  intro hz
  have h5 := h1.symm.trans hz
  have h6 := (congrArg (fun z => S.printedScalar • z) h2).symm.trans h5
  rw [smul_neg, neg_eq_zero] at h6
  exact h3 ((complex_smul_eq_zero h6).resolve_left S.printedScalar_ne_zero)

/-- **Multiplicity one at the bad-plane cusp** (`identityPlane_localUnique`): a plane class of the summand vanishing at
the good plane is a multiple of any class `ζ` of the summand that vanishes at the good plane and not at the bad one. -/
theorem exists_smul_of_vanishesOnGood (n : ℕ) (D : CohomologicalCuspData n) (h3n : 3 ≤ n)
    (ξ ζ : boundarySummand D.inducingData .plane)
    (hξ : VanishesOnGood n D.inducingData.chi .plane ξ.val)
    (hζgood : cuspRes n D.inducingData.chi .plane true ζ.val = 0)
    (hζbad : cuspRes n D.inducingData.chi .plane false ζ.val ≠ 0) : ∃ c : ℂ, ξ = c • ζ := by
  classical
  have hobtain1 := TernaryPeriodPolynomials.BoundaryHeckeDescent.boundary_hecke_descent n trivialCharacter
  obtain ⟨hecke, hhecke⟩ := hobtain1
  have hne : associatePair D.inducingData ≠ ⊥ := by
    intro hbot
    have hmem : ((ζ.val, 0) : BoundaryCoordinates n D.inducingData.chi) ∈ associatePair D.inducingData :=
      ⟨ζ.property, Submodule.zero_mem _⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hζbad (by rw [show ζ.val = 0 from congrArg Prod.fst hmem, map_zero])
  have hunique := identityPlane_localUnique D hecke hhecke h3n hne
  have := cuspH2_finiteDimensional (n := n) D.inducingData.chi .plane false
  let K := localJoint n D.inducingData.chi (TernaryPeriodPolynomials.Spectral.pairCharacter
    D.inducingData hecke hhecke) .plane false
  have hζK : cuspRes n D.inducingData.chi .plane false ζ.val ∈ K :=
    cuspRes_mem_localJoint_of_mem D.inducingData hecke hhecke .plane false ζ.property
  have hξK : cuspRes n D.inducingData.chi .plane false ξ.val ∈ K :=
    cuspRes_mem_localJoint_of_mem D.inducingData hecke hhecke .plane false ξ.property
  have hne1 : (⟨_, hζK⟩ : K) ≠ 0 := fun h => hζbad (congrArg Subtype.val h)
  have hrank : Module.finrank ℂ K = 1 :=
    le_antisymm hunique (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne1⟩)
  have hobtain2 := (finrank_eq_one_iff_of_nonzero' _ hne1).mp hrank ⟨_, hξK⟩
  obtain ⟨c, hc⟩ := hobtain2
  have hcξ : cuspRes n D.inducingData.chi .plane false ξ.val =
      c • cuspRes n D.inducingData.chi .plane false ζ.val := (congrArg Subtype.val hc).symm
  have hξgood : cuspRes n D.inducingData.chi .plane true ξ.val = 0 :=
    vanishesOnGood_fixedPointH2 hξ (cuspFlag .plane true) ((cuspFlag_good_iff .plane true).mpr rfl)
  refine ⟨c, Subtype.ext ?_⟩
  have hz : ξ.val - c • ζ.val = 0 := by
    rw [eq_zero_iff_cuspRes]
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_smul, hξgood, hζgood, smul_zero, sub_zero]
    · rw [map_sub, map_smul, hcξ, sub_self]
  exact sub_eq_zero.mp hz

/-- A nonzero plane class of the summand with a bad-plane representative gives an odd degree and an entry package. -/
theorem exists_package_of_nonzero (n : ℕ) (hn : 0 < n) (D : CohomologicalCuspData n)
    (ξ : boundarySummand D.inducingData .plane) (hξ : ξ ≠ 0)
    (hplane : VanishesOnGood n D.inducingData.chi .plane ξ.val) :
    Odd n ∧ Nonempty (SphericalEntryPackage D.inducingData) := by
  have hχ : D.inducingData.chi = trivialCharacter := rfl
  have hrep := TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.bad_plane_same_constituent_representative
    n hn D.inducingData hχ ξ hplane
  have hsph := TernaryPeriodPolynomials.BadPlaneSupportSphericity.bad_plane_support_sphericity
    n hn D.inducingData hχ ξ hξ hrep
  have hodd := TernaryPeriodPolynomials.LevelOneCohomologicalParity.level_one_cohomological_parity
    n hn D.inducingData hχ hsph
  exact ⟨hodd, exists_sphericalEntryPackage D.inducingData hodd hχ hsph⟩

/-- The scalar step: if `ξ = c ζ` and `T ξ` vanishes at the good line while `T ζ` does not, then `c = 0`. -/
theorem scalar_eq_zero_of_image_vanishes (n : ℕ) (D : CohomologicalCuspData n)
    (T : boundarySummand D.inducingData .plane →ₗ[ℂ] boundarySummand D.inducingData .line)
    (ξ ζ : boundarySummand D.inducingData .plane) (c : ℂ) (hξζ : ξ = c • ζ)
    (hline : VanishesOnGood n D.inducingData.chi .line (T ξ).val)
    (hTζ : cuspRes n D.inducingData.chi .line true (T ζ).val ≠ 0) : c = 0 := by
  have hTξ : T ξ = c • T ζ := (congrArg T hξζ).trans (map_smul T c ζ)
  have hTξv : (T ξ).val = c • (T ζ).val := congrArg Subtype.val hTξ
  have hTξc : cuspRes n D.inducingData.chi .line true (T ξ).val =
      c • cuspRes n D.inducingData.chi .line true (T ζ).val := by
    exact (congrArg (cuspRes n D.inducingData.chi .line true) hTξv).trans
      ((cuspRes n D.inducingData.chi .line true).map_smul c (T ζ).val)
  have hlg : cuspRes n D.inducingData.chi .line true (T ξ).val = 0 :=
    vanishesOnGood_fixedPointH2 hline (cuspFlag .line true) ((cuspFlag_good_iff .line true).mpr rfl)
  exact (complex_smul_eq_zero (hTξc.symm.trans hlg)).resolve_right hTζ

/-- The detection argument once a witness `ζ` of the summand, vanishing at the good plane, whose
image does not vanish at the good line, is given. -/
theorem detection_of_witness (n : ℕ) (D : CohomologicalCuspData n) (h3n : 3 ≤ n)
    (T : boundarySummand D.inducingData .plane →ₗ[ℂ] boundarySummand D.inducingData .line)
    (ξ : boundarySummand D.inducingData .plane) (hξ : ¬ ξ = 0)
    (hplane : VanishesOnGood n D.inducingData.chi .plane ξ.val)
    (hline : VanishesOnGood n D.inducingData.chi .line (T ξ).val)
    (ζ : boundarySummand D.inducingData .plane)
    (hTζ : cuspRes n D.inducingData.chi .line true (T ζ).val ≠ 0)
    (hζgood : cuspRes n D.inducingData.chi .plane true ζ.val = 0) : False := by
  have hζbad : cuspRes n D.inducingData.chi .plane false ζ.val ≠ 0 := by
    intro h0
    apply hTζ
    have : ζ = 0 := Subtype.ext ((eq_zero_iff_cuspRes .plane ζ.val).mpr ⟨hζgood, h0⟩)
    exact (congrArg (fun z : boundarySummand D.inducingData .line =>
      cuspRes n D.inducingData.chi .line true z.val) ((congrArg T this).trans (map_zero T))).trans
      (LinearMap.map_zero _)
  have hobtain4 := exists_smul_of_vanishesOnGood n D h3n ξ ζ hplane hζgood hζbad
  obtain ⟨c, hξζ⟩ := hobtain4
  have hc0 : c = 0 := scalar_eq_zero_of_image_vanishes n D T ξ ζ c hξζ hline hTζ
  apply hξ
  rw [hξζ, hc0]
  exact zero_smul ℂ ζ

/-- **Per-datum detection along the paper route.** -/
theorem perDatumDetectionMS (n : ℕ) (hn : 0 < n) (D : CohomologicalCuspData n)
    (T : boundarySummand D.inducingData .plane →ₗ[ℂ] boundarySummand D.inducingData .line)
    (hT : RealizesStandardConv D.inducingData T) (ξ : boundarySummand D.inducingData .plane)
    (hplane : VanishesOnGood n D.inducingData.chi .plane ξ.val)
    (hline : VanishesOnGood n D.inducingData.chi .line (T ξ).val) : ξ = 0 := by
  by_contra hξ
  have hobtain3 := exists_package_of_nonzero n hn D ξ hξ hplane
  obtain ⟨hodd, ⟨P⟩⟩ := hobtain3
  have hTζ := cuspRes_line_true_image_ne_zero n D.inducingData hodd rfl P.S P.I P.halfWeight_eq P.vector_eq T hT
  have hζgood : cuspRes n D.inducingData.chi .plane true (SphericalEntryData.badPlaneClass P.S P.I).val = 0 :=
    cuspRes_plane_true_badPlane D.inducingData _
      (planeSource_isSourceCocycle D.inducingData _ P.S.hχ) (SphericalEntryData.badPlane_isSourceCocycle P.S P.I)
  exact detection_of_witness n D (by have := P.S.large; omega) T ξ hξ hplane hline
    (SphericalEntryData.badPlaneClass P.S P.I) hTζ hζgood

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
