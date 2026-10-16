module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageForms
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageCF
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NSeedSurj
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.GoodFlagTransport
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Weight

@[expose] public section


/-!
# CMP-8 (3): the passage from level one to the `Γ(N)`-level `seedBoundary`

`phiPlane_badPlaneClass`: for the entry datum, the vector `phiPlane (a_pl)` over the plane faces of `Γ(N)` of the bad-plane section `a_pl = badPlaneClass S I` equals
`seedBoundary N n (entryTuple f1)`, where `f1` is the classical level-one form of the Eichler vector (its function is the scalar function of the vector) and
`entryTuple f1 i false = K_i • f1|Γ₂(N)`, `entryTuple f1 i true = conj(K_i (-1)^{n+1}) • f1*|Γ₂(N)` at the bad faces, `0` at the good faces,
`K_i = (-1)^n (n+1)/2` (`entryCoeff`; `c_F(g_i) = 1`, `cF_faceArg`).  Ingredients: `badPlaneClass_cOmega` (the class of `badPlaneWeight · planeSource` is that of `badPlaneWeight · cOmega`),
`phiPlaneAt_good` (zero at the good faces), `phiPlaneAt_bad_face_forms` (the bad faces).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.AnalyticClasses TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.GammaNFacesFull
  TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

/-- The entry section `a_pl` is the class of the weighted plane integral cochain `badPlaneWeight · cOmega`. -/
theorem badPlaneClass_cOmega (M : CohomologicalCuspData n) (I : EichlerInput M.cusp n)
    (S : SphericalEntryData M.inducingData) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) :
    ∃ hPP : IsSourceCocycle M.inducingData .plane (fun y g => badPlaneWeight g • cOmega n M.inducingData S.F y g),
      ((SphericalEntryData.badPlaneClass S I).val : StratumH2 n M.inducingData.chi .plane) =
        SourceSpace.sourceClass M.inducingData .plane ⟨_, hPP⟩ := by
  have hE := SphericalEntryData.planeLevi_alpha (S := S) (I := I) hw hv
  have holo := SphericalEntryData.holomorphic_F (S := S) (I := I) hw hv
  have hc : ∀ g : RealGL3, componentCharacter M.inducingData.chi g = 1 :=
    componentCharacter_eq_one_of_integral M.inducingData.chi S.hχ
  have hRa : IsSourceCocycle M.inducingData .plane (fun y g => cOmega n M.inducingData S.F y g) :=
    cOmega_isSourceCocycle M.inducingData S.F holo (SphericalEntryData.planeLevi I) hE hc S.hχ
      (continuousStages M.inducingData) S.halfWeight S.vector
      (fixed_of_spherical M.inducingData.cusp S.vector S.spherical) rfl
  have hPP : IsSourceCocycle M.inducingData .plane (fun y g => badPlaneWeight g • cOmega n M.inducingData S.F y g) :=
    isSourceCocycle_smul_weight M.inducingData badPlaneWeight_planeWeight _ hRa
  refine ⟨hPP, ?_⟩
  have e := sourceToSummand_cOmega_eq_planeSource_weight M.inducingData S.F holo (SphericalEntryData.planeLevi I) hE hc
    S.hχ badPlaneWeight_planeWeight hPP
  exact (congrArg Subtype.val e).symm

omit [NeZero N] in
/-- **The coordinate of a class vanishing on the good planes is zero at a good face.** -/
theorem phiPlaneAt_good (h : SL(3, ℤ)) (hgood : GoodFlag .plane (planeFlagAt h))
    (a : StratumH2 n trivialCharacter .plane) (ha : VanishesOnGood n trivialCharacter .plane a) :
    phiPlaneAt N h3 hN n h a = 0 := by
  have h0 := (vanishesOnGood_iff_fixedPointH2 a).mp ha (planeFlagAt h) hgood
  unfold phiPlaneAt
  change (planeH2Equiv N h3 h n trivialCharacter hN)
    (resPrincipal N (planeFlagAt h) (rationalCoefficientComponent n trivialCharacter)
      (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (planeFlagAt h) a)) = 0
  rw [h0, LinearMap.map_zero, LinearEquiv.map_zero]

section Final

open TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.FormSeedBridge
  TernaryPeriodPolynomials.Argument.CuspidalSpan UpperHalfPlane
open scoped Classical

/-- The scalar `K_i` of the face `i`: `0` at the good faces, the constant `(-1)^n (n+1)/2` at the bad faces. -/
def entryCoeff (i : PlaneFaces N) : ℂ :=
  if GoodFlag .plane (planeFlagAt (planeFaceRepr i)) then 0 else ((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹)

/-- **The tuple of cusp forms of `Γ₂(N)` attached to the entry section:** on the bad faces `K_i • f` (holomorphic seed) and
`conj(K_i (-1)^{n+1}) • f*` (antiholomorphic seed), `0` on the good faces. -/
def entryTuple (f1 : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ) :=
  fun i b => if b then (starRingEnd ℂ (entryCoeff N n i * (-1) ^ (n + 1))) • levelN N (fStar f1)
    else entryCoeff N n i • levelN N f1

/-- **CMP-8 (3): the passage from level one to the `Γ(N)`-level `seedBoundary`.**  For the entry datum (`M`, Eichler input `I`, spherical datum `S` of the same weight and vector), the classical
level-one form `f1` of the Eichler vector satisfies `phiPlane (a_pl) = seedBoundary (entryTuple f1)`: the `Γ(N)`-plane-boundary vector of the entry section `a_pl` (S3's `phiPlane`) is the vector of
classical seed classes of `K_i f` and `K_i (-1)^{n+1} f*` at the bad faces and `0` at the good faces. -/
theorem phiPlane_badPlaneClass (M : CohomologicalCuspData n) (I : EichlerInput M.cusp n)
    (S : SphericalEntryData M.inducingData) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) :
    ∃ f1 : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ),
      (f1 : ℍ → ℂ) = cuspScalarWeightedLinear M.cusp I.halfWeight 1 I.vector ∧
      phiPlane N h3 hN n (SphericalEntryData.badPlaneClass S I).val = seedBoundary N n (entryTuple N n f1) := by
  obtain ⟨f0, hform⟩ := EichlerInput.exists_classicalForm I M.cohomological
  have hhw : -2 * I.halfWeight = ((n + 3 : ℕ) : ℤ) := by
    have := I.weight
    push_cast
    omega
  obtain ⟨f1, hf1⟩ := TernaryPeriodPolynomials.Oldform.exists_cuspForm_cast hhw f0
  refine ⟨f1, hf1.trans hform, ?_⟩
  obtain ⟨hPP, hcl⟩ := badPlaneClass_cOmega n M I S hw hv
  have hv0 : VanishesOnGood n trivialCharacter .plane (SphericalEntryData.badPlaneClass S I).val :=
    GoodPlaneSpan.vanishesOnGood_of_cuspRes_good_eq_zero _ (by
      rw [SphericalEntryData.badPlaneClass_val]
      exact cuspRes_plane_true_badPlane M.inducingData _ (planeSource_isSourceCocycle M.inducingData _ S.hχ)
        (SphericalEntryData.badPlane_isSourceCocycle S I))
  ext1 i
  rw [phiPlane_apply, seedBoundary_apply N n]
  by_cases hg : GoodFlag .plane (planeFlagAt (planeFaceRepr i))
  · rw [phiPlaneAt_good N h3 hN n _ hg _ hv0]
    have h0 : entryCoeff N n i = 0 := ite_eq_left hg
    have e1 : entryTuple N n f1 i false = 0 := by simp [entryTuple, h0]
    have e2 : entryTuple N n f1 i true = 0 := by simp [entryTuple, h0]
    rw [e1, e2]
    have z1 : faceSeedKerClass N (planeFaceRepr i) n (0 : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) = 0 := by
      simpa using faceSeedKerClass_smul N n (planeFaceRepr i) 0 (0 : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    have z2 : faceSeedConjKerClass N (planeFaceRepr i) n (0 : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) = 0 := by
      simpa using faceSeedConjKerClass_smul N n (planeFaceRepr i) 0 (0 : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    rw [z1, z2]
    simp
  · rw [hcl, phiPlaneAt_bad_face_forms N h3 hN n M I S hw hv hPP f0 hform f1 hf1 _ hg]
    have h0 : entryCoeff N n i = ((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) := ite_eq_right hg
    have e1 : entryTuple N n f1 i false = entryCoeff N n i • levelN N f1 := by simp [entryTuple]
    have e2 : entryTuple N n f1 i true =
        (starRingEnd ℂ (entryCoeff N n i * (-1) ^ (n + 1))) • levelN N (fStar f1) := by simp [entryTuple]
    rw [e1, e2, faceSeedKerClass_smul, faceSeedConjKerClass_smul, h0, cF_faceArg M.inducingData S.hχ, mul_one]
    simp only [Submodule.coe_smul, Complex.conj_conj]

end Final

end TernaryPeriodPolynomials.Argument.KDaggerComparison
