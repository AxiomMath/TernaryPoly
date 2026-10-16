module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationLineType

@[expose] public section


/-!
# A nonzero pair forces a level-three vector

If `associatePair D ≠ ⊥`, some source cocycle has a nonzero Shapiro coordinate at one of the four
cusps (`exists_sourceCoordinate_ne_zero`), and the value of the induced section at the cusp frame
is a nonzero vector of `D.cusp` fixed by the Levi level of the cusp: `GL₂(ℤ̂)` at the two level-one
cusps, `{k : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` at the good plane and the bad line. Hence `D.cusp` is
spherical or has a nonzero vector in `levelThreeValues` (`spherical_or_levelThree`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.MultiplicityOne

variable {n : ℕ}

/-- The line Levi element `diag(1, k)` of a level-three `k` lies in the finite level. -/
theorem lineLevi_mem_finiteLevel_of_planeLeviLevel (k : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (hk : PlaneLeviLevel k) :
    GeneralLinearGroup.map integralEmbedding (lineLevi 1 k) ∈ finiteLevel := by
  refine Subgroup.mem_map.mpr ⟨lineLevi 1 k, ?_, rfl⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction (lineLevi 1 k)).val = lastRow
  rw [CuspOrbits.lastRow_vecMul]
  have h10 : integralReduction (k.val 1 0) = 0 := hk.1
  have h11 : integralReduction (k.val 1 1) = 1 := hk.2
  funext j
  rw [GeneralLinearGroup.map_apply, lineLevi_val]
  fin_cases j <;> simp [lastRow, h10, h11]

theorem exists_levelThreeValues_of_badLineLevelVector (σ : CuspidalRepresentation)
    (h : BadLineLevelVector σ) : ∃ v : σ.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues σ := by
  obtain ⟨v, hv, hfix⟩ := h
  exact ⟨v, hv, fun k hk => hfix k (lineLevi_mem_finiteLevel_of_planeLeviLevel k hk)⟩

/-- **A nonzero pair forces a spherical or a level-three vector.** -/
theorem spherical_or_levelThree (D : InducingData n) (hne : associatePair D ≠ ⊥) :
    SphericalCusp D.cusp ∨ ∃ v : D.cusp.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues D.cusp := by
  obtain ⟨side, good, c, hc⟩ := exists_sourceCoordinate_ne_zero D hne
  cases side with
  | plane =>
    have hci : coordinateImage D .plane good ≠ ⊥ :=
      (coordinateImage_ne_bot_iff D .plane good).mpr ⟨c, hc⟩
    have hpl := planeLevelVector_of_coordinateImage_ne_bot D good hci
    cases good with
    | false => exact Or.inl ((planeLevelVector_false_iff _).mp hpl)
    | true => exact Or.inr ((planeLevelVector_true_iff _).mp hpl)
  | line =>
    have hll := lineLocalType_of_sourceCoordinate_ne_zero D good c hc
    cases good with
    | false => exact Or.inr (exists_levelThreeValues_of_badLineLevelVector _ hll)
    | true => exact Or.inl hll

/-- A non-spherical cuspidal datum with a nonzero pair has a nonzero level-three vector. -/
theorem exists_levelThree_of_not_spherical (D : InducingData n) (hne : associatePair D ≠ ⊥)
    (hns : ¬ SphericalCusp D.cusp) :
    ∃ v : D.cusp.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues D.cusp :=
  (spherical_or_levelThree D hne).resolve_left hns

end TernaryPeriodPolynomials.MultiplicityOne
