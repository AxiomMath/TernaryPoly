module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.BadLineSummand
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Linear
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Inputs

@[expose] public section


/-!
# The level-three source construction at the bad line (trivial character, odd degree)

Given the injectivity of the parity-projected level-three period map, the explicit Eichler family
`w ↦ l3FamilyData … w` of the level-three weight vectors of weight `-(n + 3)` gives a linear map
`w ↦ lineSource3 D (E w)` into the source cocycles of the line whose bad-line Shapiro coordinate is
injective (`exists_badLine_sourceMap_of_period`), i.e. `LevelThreeSourceConstruction D .line false`
(`levelThreeSourceConstruction_badLine_of_period`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThreeSource
  (levelThreeWeightVectors sourceWeight LevelThreeSourceConstruction)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel binaryArithmeticRepresentation)

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

/-- **A linear family of Levi data gives a linear family of line sources with injective bad-line
coordinate** as soon as the vanishing of the Levi period class forces the parameter to vanish. -/
theorem exists_badLine_sourceMap_of_family {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D : InducingData n) (hchi : D.chi = trivialCharacter) (pos : 0 < n)
    (E : W → LineLeviCocycleData3 D.cusp n)
    (hsrc : ∀ w : W, IsSourceCocycle D .line (lineSource3 D (E w)))
    (hadd : ∀ w w' h x, (E (w + w')).α h x = (E w).α h x + (E w').α h x)
    (hsmul : ∀ (c : ℂ) (w : W) h x, (E (c • w)).α h x = c • (E w).α h x)
    (hper : ∀ w : W, (∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • (E w).α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        binaryArithmeticRepresentation n A w₀ - w₀) → w = 0) :
    ∃ Φ : W →ₗ[ℂ] sourceCocycles D .line,
      Function.Injective (sourceCoordinate D .line false ∘ₗ Φ) := by
  refine ⟨{ toFun := fun w => ⟨lineSource3 D (E w), hsrc w⟩,
            map_add' := fun w w' => Subtype.ext (lineSource3_add D _ _ _ (hadd w w')),
            map_smul' := fun c w => Subtype.ext (lineSource3_smul D _ _ c (hsmul c w)) }, ?_⟩
  refine lineSource3_badLine_coordinate_injective D hchi pos E hsrc _ ?_ hper
  intro w
  rfl

/-- **A linear map from the level-three weight vectors into the line source cocycles with injective
bad-line coordinate**, given the injectivity of the parity-projected level-three period map. -/
theorem exists_badLine_sourceMap_of_period (D : InducingData n)
    (hchi : D.chi = trivialCharacter) (hodd : Odd n)
    (hper : Function.Injective (levelPeriodMap (n + 1) 0)) :
    ∃ Φ : levelThreeWeightVectors D.cusp (sourceWeight n) →ₗ[ℂ] sourceCocycles D .line,
      Function.Injective (sourceCoordinate D .line false ∘ₗ Φ) := by
  by_cases hex : ∃ w₀ : levelThreeWeightVectors D.cusp (sourceWeight n), w₀ ≠ 0
  · obtain ⟨w₀, hw₀⟩ := hex
    obtain ⟨k, hk⟩ := hodd
    have hn : (n : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
    have hhalf : 2 * (-((k : ℤ) + 2)) = -((n : ℤ) + 3) := by omega
    have hσ : MultiplicityOne.LevelThreeCusp D.cusp :=
      levelThreeCusp_of_weightVector w₀ hw₀
    have pos : 0 < n := by omega
    have hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
      intro u
      rw [hchi]
      rfl
    exact exists_badLine_sourceMap_of_family D hchi pos
      (l3FamilyData D hσ (-((k : ℤ) + 2)) hhalf (AnalyticClasses.continuousStages D))
      (fun v => lineSource3_isSourceCocycle D _ hχ)
      (fun w w' h x => congrFun (congrFun
        (l3FamilyData_α_add D hσ (-((k : ℤ) + 2)) hhalf (AnalyticClasses.continuousStages D)
          w w') h) x)
      (fun c w h x => congrFun (congrFun
        (l3FamilyData_α_smul D hσ (-((k : ℤ) + 2)) hhalf (AnalyticClasses.continuousStages D)
          c w) h) x)
      (fun v hv => l3Family_coboundary_imp_zero D hσ (-((k : ℤ) + 2)) hhalf hper v hv)
  · refine ⟨0, fun a b _ => ?_⟩
    push Not at hex
    rw [hex a, hex b]

/-- **The level-three source construction at the bad line** (trivial character, odd degree), given the
injectivity of the parity-projected level-three period map. -/
theorem levelThreeSourceConstruction_badLine_of_period (D : InducingData n) (hodd : Odd n)
    (hper : Function.Injective (levelPeriodMap (n + 1) 0)) :
    LevelThreeSourceConstruction D .line false := fun hchi _ =>
  exists_badLine_sourceMap_of_period D hchi hodd hper

end TernaryPeriodPolynomials.SourceConstruction

end
