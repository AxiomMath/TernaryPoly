module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Injective
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Parity
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SturmBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.LowerBound

@[expose] public section


/-!
# Dimension consequences of the level-three period map

* `finrank_cuspForm_le_core`: Bol injectivity (`levelThreePeriodMap_injective`) embeds
  `S_{m+2}(Γ₁(3))` into the parabolic cohomology of `Γ₁(3)`, so
  `dim S_{m+2}(Γ₁(3)) ≤ 2 (⌊(m+2)/3⌋ - 1)`.
* `levelPeriodMap_range_eq_parabolic`: **Eichler–Shimura for `Γ₁'(3)`, conditional on injectivity of
  the parity-projected map.** If `levelPeriodMap m e` is injective and
  `⌊(m+2)/3⌋ - 1 ≤ dim S_{m+2}`, its image is exactly the parabolic cohomology
  `H¹_par(Γ₁'(3), Sym^m ⊗ det^e)`, because the latter has dimension `⌊(m+2)/3⌋ - 1`
  (`ExactLevel.finrank_level_parabolicH1_eq`).
* `levelPeriodMap_range_eq_parabolic_of_injective`: the same with the dimension hypothesis
  discharged by `LevelThreeLowerBound.finrank_cuspForm_eq` (`dim S_k(Γ₁(3)) = ⌊k/3⌋ - 1`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Module
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParabolic
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodInjective

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodDimension

variable (m : ℕ) (e : ℤ)

/-- **The period map embeds cusp forms into parabolic cohomology (Bol).** -/
theorem finrank_cuspForm_le_core (hm : 0 < m) [FiniteDimensional ℂ (S m)] :
    finrank ℂ (S m) + 2 ≤ 2 * ((m + 2) / 3) := by
  have := ParabolicBounds.core_H1_finiteDimensional (m := m) (0 : ℤ)
  let g : S m →ₗ[ℂ] parabolicH1 (coreRep m (0 : ℤ)) coreT coreL :=
    (levelThreePeriodMap m (0 : ℤ)).codRestrict _ (levelThreePeriodMap_mem_parabolic m (0 : ℤ))
  have hinj : Function.Injective g := by
    intro f₁ f₂ h
    exact levelThreePeriodMap_injective m (0 : ℤ) hm (congrArg Subtype.val h)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hexact := Existence.finrank_core_parabolicH1_sym_eq (m := m) (0 : ℤ) hm
  change finrank ℂ (parabolicH1 (coreRep m (0 : ℤ)) coreT coreL) + 2 = _ at hexact
  omega

variable {m e}

/-- **`dim S_{m+2}(Γ₁(3)) = ⌊(m+2)/3⌋ - 1`** (Sturm bound and the explicit cusp forms). -/
theorem finrank_cuspForm_eq' : finrank ℂ (S m) = (m + 2) / 3 - 1 := by
  have h : finrank ℂ (S m) = ((((m : ℤ) + 2) / 3 - 1).toNat : ℕ) :=
    LevelThreeLowerBound.finrank_cuspForm_eq ((m : ℤ) + 2)
  rw [h]
  omega

/-- **Eichler–Shimura for `Γ₁'(3)`, conditional on injectivity of the parity-projected map.** -/
theorem levelPeriodMap_range_eq_parabolic (hm : 0 < m) [FiniteDimensional ℂ (S m)]
    (hinj : Function.Injective (levelPeriodMap m e))
    (hdim : (m + 2) / 3 - 1 ≤ finrank ℂ (S m)) :
    LinearMap.range (levelPeriodMap m e) = parabolicH1 (levelRep m e) (upper 1) (lower 1) := by
  have := ParabolicBounds.level_H1_finiteDimensional (m := m) e hm
  have hle : LinearMap.range (levelPeriodMap m e) ≤
      parabolicH1 (levelRep m e) (upper 1) (lower 1) := by
    rintro _ ⟨f, rfl⟩
    exact levelPeriodMap_mem_parabolic m e f
  have hexact := ExactLevel.finrank_level_parabolicH1_eq (m := m) e hm
  have hrange : finrank ℂ (LinearMap.range (levelPeriodMap m e)) = finrank ℂ (S m) :=
    LinearMap.finrank_range_of_inj hinj
  apply Submodule.eq_of_le_of_finrank_le hle
  omega

/-- **Eichler–Shimura for `Γ₁'(3)`, conditional only on injectivity of the parity-projected map**:
the dimension hypothesis is discharged by `finrank_cuspForm_eq'`. -/
theorem levelPeriodMap_range_eq_parabolic_of_injective (hm : 0 < m)
    (hinj : Function.Injective (levelPeriodMap m e)) :
    LinearMap.range (levelPeriodMap m e) = parabolicH1 (levelRep m e) (upper 1) (lower 1) := by
  have hfd : FiniteDimensional ℂ (S m) := SturmBound.cuspForm_finiteDimensional ((m : ℤ) + 2)
  exact @levelPeriodMap_range_eq_parabolic m e hm hfd hinj
    (le_of_eq (finrank_cuspForm_eq' (m := m)).symm)

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodDimension
