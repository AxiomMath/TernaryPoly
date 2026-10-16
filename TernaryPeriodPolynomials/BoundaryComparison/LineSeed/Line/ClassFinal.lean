module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.ClassIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.LineSeedEdge

@[expose] public section


/-!
# The good-line coordinate restricted to `Λ₁⁺` is the line seed class (LS15c)

For odd `n`, the entry section `a_li = goodLineClass S I` of an Eichler input `I` has good-line coordinate `X` (the Shapiro coordinate at the reference good line, equal to every
transported `cuspRes`, `KDaggerComparison.transport_cuspRes_line`).  Its restriction to `Λ₁⁺` (`linePlusRes`) is `(n+1)/2` times the complexified de Rham class of the reflection-invariant
line seed `σ_f + (-1)ⁿ \overline{σ_{f^*}}` of the level-one cusp form `f` of `I` (`lineSeedIdentity`, mirror of `SeedC3S4c.ClassIdentity.seed_class_identity`): the Hochschild-Serre edge of
`Λ₁⁺` is injective and both sides have the same edge, `-3(n+1)` times the restriction of the pivot-swap `[dlCocycleOf n ψ_f]` (`goodLine_edge`, `edge_lineReflRel`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.LineCoordinates (Λ₁)
open TernaryPeriodPolynomials.Argument.KDaggerComparison (goodLineClass goodLine_edge transport_cuspRes_line)
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.LineSeed (reflSeedInv)
open TernaryPeriodPolynomials.Argument.SeedC3S4c (fStar)
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension (restriction restriction_apply restriction_intertwines)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

local notation "Lvl1" => TernaryPeriodPolynomials.Argument.SeedC3S4c.Lvl1

section

variable {n : ℕ}

/-- Restriction `H²(Λ₁, ρ_n) → H²(Λ₁⁺, ρ_n)`: the comparison with group cohomology followed by the restriction along `Λ₁⁺ ⊆ Λ₁`. -/
abbrev linePlusRes (n : ℕ) : H2 Λ₁ (ρn n) →ₗ[ℂ] groupCohomology.H2 (linePlusRep n) :=
  (twoCohomologyRestriction Lam1Plus.subtype (goodLineCoefficientRep n)).comp (toH2L n)

theorem linePlusRes_relClass (c : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n)) :
    twoCohomologyRestriction Lam1Plus.subtype (goodLineCoefficientRep n)
        (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n) c).val =
      (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n) (linePlusRestrictS n c)).val := by
  rw [relativeTwoCocycleClass_apply, relativeTwoCocycleClass_apply, twoCohomologyRestriction_apply]
  rfl

/-- The `Λ₁⁺`-edge of the restriction of a class of `KL` is the `SL₂(ℤ)`-restriction of its edge. -/
theorem linePlusEdge_resH2 (hn : 0 < n) (x : H2 Λ₁ (ρn n)) (hx : x ∈ KL n) :
    ∃ y : (twoCohomologyRestriction linePlusExtensionS.inl (linePlusRep n)).ker,
      y.val = linePlusRes n x ∧
        (linePlusLeviCohomologyIso n hn).hom (linePlusEdgeS n y) =
          restriction (n + 1) 0 0 (edgeK n hn ⟨x, hx⟩) := by
  obtain ⟨c, hc⟩ := relativeTwoCocycleClass_surjective goodLineRadicalInclusion
    goodLineRadicalInclusion_injective (goodLineCoefficientRep n) ⟨toH2L n x, hx⟩
  refine ⟨relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n) (linePlusRestrictS n c), ?_, ?_⟩
  · rw [← linePlusRes_relClass, hc]
    rfl
  · rw [linePlusEdge_restrict]
    congr 1
    change _ = goodLineBinaryEdge n hn ⟨toH2L n x, hx⟩
    rw [hc]

section Edge

variable (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2)

include hw in
/-- **The edge of the reflection-invariant line seed**: `-6` times the `SL₂(ℤ)`-restriction of the class of the pivot-swap `dlCocycleOf n ψ_f`. -/
theorem edge_lineReflRel (hodd : Odd n) (hn : 0 < n) :
    (linePlusLeviCohomologyIso n hn).hom (linePlusEdgeS n
        (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n) (lineReflRel f))) =
      (-6 : ℂ) • restriction (n + 1) 0 0
        (groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) (dlCocycleOf n (psiF f hw hodd))) := by
  unfold lineReflRel
  rw [map_add, map_smul, map_add, map_smul, map_add, map_smul, lineSeedEdge hn f, lineConjSeedEdge hn (fStar f)]
  exact edgeComb_class f hw hodd hn

include hw in
/-- **A class of the kernel with the right edge is the complexified de Rham class of the reflection-invariant line seed.** -/
theorem eq_seed_of_edge_line (hodd : Odd n) (hn : 0 < n)
    (y : (twoCohomologyRestriction linePlusExtensionS.inl (linePlusRep n)).ker)
    (hy : (linePlusLeviCohomologyIso n hn).hom (linePlusEdgeS n y) =
      ((-3 : ℂ) * ((n + 1 : ℕ) : ℂ)) • restriction (n + 1) 0 0
        (groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) (dlCocycleOf n (psiF f hw hodd)))) :
    y.val = (((n : ℂ) + 1) / 2) • lineComplexify n
      (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty linePlusData.action
        (linePlusData.rhoR n) (reflSeedInv linePlusData linePlus_hΛ f 1)) := by
  rw [lineComplexify_reflSeed, ← Submodule.coe_smul]
  congr 1
  apply linePlusEdgeS_injective n
  apply (linePlusLeviCohomologyIso n hn).toLinearEquiv.injective
  change (linePlusLeviCohomologyIso n hn).hom (linePlusEdgeS n y) =
    (linePlusLeviCohomologyIso n hn).hom (linePlusEdgeS n ((((n : ℂ) + 1) / 2) •
      relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n) (lineReflRel f)))
  rw [hy, map_smul, map_smul, edge_lineReflRel f hw hodd hn, smul_smul]
  congr 1
  push_cast
  ring

end Edge


section Identity

theorem classicalBinaryCocycle_congr' {w w' : ℤ} (hw : w = w')
    (f : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range w)
    (f' : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range w')
    (hfun : (f : UpperHalfPlane → ℂ) = f') (d : ℕ) (we : w = (d : ℤ) + 2) (we' : w' = (d : ℤ) + 2)
    (τ : ℤ) : classicalBinaryCocycle f d we τ = classicalBinaryCocycle f' d we' τ := by
  subst hw
  obtain rfl : f = f' := DFunLike.coe_injective hfun
  rfl

theorem cuspForm_cast_coe' {Λ : Subgroup (GL (Fin 2) ℝ)} {w w' : ℤ} (h : w = w')
    (g : CuspForm Λ w) : ((h ▸ g : CuspForm Λ w') : UpperHalfPlane → ℂ) = g := by
  subst h
  rfl

/-- **The good-line coordinate of the entry section, restricted to `Λ₁⁺`, is the line seed class** (mirror of `SeedC3S4c.seed_class_identity`; line half of the classical-seeds comparison).
For odd `n` and an Eichler input `I`, the restriction to `Λ₁⁺` of the good-line coordinate `X` of the entry section `a_li` (the Shapiro coordinate at the reference good line, equal to every
transported `cuspRes`, `transport_cuspRes_line`) is `(n+1)/2` times the complexified de Rham class of the reflection-invariant line seed `σ_f + (-1)ⁿ \overline{σ_{f^*}}` of the level-one
cusp form `f` of `I`.  (The factor is `(n+1)/2`: `-3(n+1)` is the library edge, `-6` the edge of the seed class.) -/
theorem lineSeedIdentity {n : ℕ} (hn : Odd n) (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n) :
    ∃ f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ),
      (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I ∧
      linePlusRes n (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
          (QuotientGroup.mk rationalGoodLine : Flags .line) (goodLineClass S I).val) =
        (((n : ℂ) + 1) / 2) • lineComplexify n
          (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty linePlusData.action
            (linePlusData.rhoR n) (reflSeedInv linePlusData linePlus_hΛ f 1)) := by
  have hW : -2 * I.halfWeight = ((n + 3 : ℕ) : ℤ) := by
    have := classicalFormOfEichlerInput_weight_eq I
    push_cast at this ⊢
    omega
  have hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
  obtain ⟨f, hfun⟩ : ∃ f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ),
      (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I :=
    ⟨hW ▸ classicalFormOfEichlerInput I, cuspForm_cast_coe' hW _⟩
  refine ⟨f, hfun, ?_⟩
  obtain ⟨γ, hγ⟩ := lineTransporter
  obtain ⟨h, hedge⟩ := goodLine_edge hn M S I γ hγ
  rw [← transport_cuspRes_line γ hγ]
  obtain ⟨y, hy1, hy2⟩ := linePlusEdge_resH2 hn.pos _ h
  have hc : classicalBinaryCocycle (classicalFormOfEichlerInput I) (n + 1)
      (classicalFormOfEichlerInput_weight_eq I) 0 = classicalBinaryCocycle f (n + 1) hw 0 :=
    classicalBinaryCocycle_congr' hW.symm.symm _ _ hfun.symm _ _ _ _
  have hψ : eichlerClassicalCocycle I hn = psiF f hw hn := by
    unfold eichlerClassicalCocycle psiF classicalArithmeticCocycle
    rw [hc]
  rw [← hy1]
  refine eq_seed_of_edge_line f hw hn hn.pos y ?_
  rw [hy2, hedge, hψ, map_smul]

end Identity

end

end TernaryPeriodPolynomials.Argument.LineSeed
