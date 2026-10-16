module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.TransferBack
public import TernaryPeriodPolynomials.BoundaryComparison.BadPlaneInjectivity.TEliminate
public import TernaryPeriodPolynomials.BoundaryComparison.PlaneLineComparison.Coordinates

@[expose] public section


/-!
# K†-level transfer of a normal-subgroup class: flag restrictions and the line coordinate

Formalized by Claude Sonnet 5.5.

For a normal finite-index subgroup `M` of the level group `Γ = rationalLevel` and a class `x ∈ H²(M, ρ)`:

* `trToLevel`: the transfer (corestriction) `H²(M, ρ) → H²(Γ, ρ)`;
* `faceRestriction_trToLevel_eq_zero`: if `x` restricts to zero on `M ∩ Γ_z` for every point `z` of a
  `GL₃(ℚ)`-set `X`, then `tr x` restricts to zero on `Γ_z` for every `z`;
* `innerBoundary_plane_of_edgeVanishing`: if a global cocycle's class restricts to zero on the stabilizer of
  every complete flag, its plane coordinate is `InnerBoundary`;
* `lineCoordinate_eq_of_edgeVanishing`: for any uniqueness map `T₀` (`line_constant_term_comparison`), such a cocycle has
  line coordinate `T₀ (plane coordinate)`.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

section Transfer

theorem fixedPointLevel_le_self {X : Type} [MulAction RationalGL3 X] (L : Subgroup RationalGL3) (z : X) :
    fixedPointLevel L z ≤ L := inf_le_left

theorem fixedPointLevel_le_level {X : Type} [MulAction RationalGL3 X] (z : X) :
    fixedPointLevel rationalLevel z ≤ rationalLevel := inf_le_left

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
  (M : Subgroup RationalGL3) (hM : M ≤ rationalLevel)
  (hMnorm : ∀ g ∈ rationalLevel, ∀ m ∈ M, g⁻¹ * m * g ∈ M) [M.IsFiniteRelIndex rationalLevel]

/-- The finite quotient `Γ / M`. -/
instance levelQuotFintype : Fintype (↥rationalLevel ⧸ M.subgroupOf rationalLevel) := by
  have hfin : (M.subgroupOf rationalLevel).FiniteIndex := inferInstance
  exact Subgroup.fintypeQuotientOfFiniteIndex

include hM hMnorm in
/-- **The transfer (corestriction) `H²(M, ρ) → H²(Γ, ρ)`** to the level group. -/
def trToLevel : H2 M ρ →ₗ[ℂ] H2 rationalLevel ρ :=
  @trH2 _ _ _ _ _ ρ M rationalLevel (levelQuotFintype M) hM hMnorm

include hM hMnorm in
/-- **Restriction of the transfer to a point stabilizer.**  If `x ∈ H²(M, ρ)` restricts to zero on
`M ∩ Γ_z` for every point `z` of a `GL₃(ℚ)`-set `X`, then `tr x` restricts to zero on `Γ_z`. -/
theorem faceRestriction_trToLevel_eq_zero {X : Type} [MulAction RationalGL3 X] (x : H2 M ρ)
    (hx : ∀ z : X, resH2 ρ (fixedPointLevel_le_self M z) x = 0) (y : X) :
    resH2 ρ (fixedPointLevel_le_level y) (trToLevel ρ M hM hMnorm x) = 0 := by
  let _ := levelQuotFintype M
  apply res_level_injective ρ M hM hMnorm y
  rw [map_zero]
  have hc : resH2 ρ (fixedPointLevel_mono_level M hM y)
      (resH2 ρ (fixedPointLevel_le_level y) (trToLevel ρ M hM hMnorm x)) =
      resH2 ρ (fixedPointLevel_le_self M y) (resH2 ρ hM (trToLevel ρ M hM hMnorm x)) := by
    rw [resH2_comp, resH2_comp]
  rw [hc]
  change resH2 ρ _ (resH2 ρ hM (trH2 ρ hM hMnorm x)) = 0
  rw [resH2_trH2, map_smul, map_sum]
  refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun q _ => ?_)
  refine res_act_zero ρ (fixedPointLevel_le_self M y)
    (fixedPointLevel_le_self M ((Quotient.out q : rationalLevel).val⁻¹ • y))
    (hMnorm _ (Quotient.out q).2) ?_ x (hx _)
  intro n hn
  refine ⟨hMnorm _ (Quotient.out q).2 n hn.1, ?_⟩
  apply MulAction.mem_stabilizer_iff.mpr
  have h2 : n • y = y := MulAction.mem_stabilizer_iff.mp hn.2
  rw [mul_smul, mul_smul, smul_inv_smul, h2]

end Transfer

section Coordinates

open TernaryPeriodPolynomials.Argument.BadPlaneInjectivity

/-- **A global class whose restriction to the stabilizer of every complete flag vanishes has
`InnerBoundary` coordinates** (on either side): the class of the pulled-back cocycle at a flag `F` is the
restriction of the class to `Γ_F`, and its restriction to each `Γ_e`, `e` over `F`, is the restriction of
the class to `Γ_e`. -/
theorem innerBoundary_of_edgeVanishing (n : ℕ) (χ : RankOneCharacter) (side : Side)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (h : ∀ e : Edges, resH2 (rationalCoefficientComponent n χ) (fixedPointLevel_le_level e)
      (classOf rationalLevel (rationalCoefficientComponent n χ) c) = 0) :
    InnerBoundary n χ side
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side)
        (restrictionCocycle n χ side c)) := by
  rw [innerBoundary_iff_locallyInner]
  intro flag
  rw [locallyInnerClasses_eq]
  simp only [locallyInnerAt, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]
  intro e he
  have h1 : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) flag
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side)
        (restrictionCocycle n χ side c)) =
      resH2 (rationalCoefficientComponent n χ) (fixedPointLevel_le_level flag)
        (classOf rationalLevel (rationalCoefficientComponent n χ) c) := rfl
  rw [h1, resH2_comp]
  exact h e

/-- **Line coordinate of a class with vanishing flag restrictions** (`line_constant_term_comparison`, uniqueness clause): if
the global class of `c` restricts to zero on the stabilizer of every complete flag, then for every
uniqueness map `T₀` (e.g. the canonical one of `line_constant_term_comparison`) the line coordinate is `T₀` applied to the plane
coordinate. -/
theorem lineCoordinate_eq_of_edgeVanishing (n : ℕ)
    (T₀ : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT₀ : IsUniquenessMap n trivialCharacter T₀)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (h : ∀ e : Edges, resH2 (rationalCoefficientComponent n trivialCharacter)
      (fixedPointLevel_le_level e)
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0) :
    (globalCoordinates n trivialCharacter c).2 = T₀ (globalCoordinates n trivialCharacter c).1 :=
  hT₀ c (innerBoundary_of_edgeVanishing n trivialCharacter .plane c h)
    (innerBoundary_of_edgeVanishing n trivialCharacter .line c h)

end Coordinates

end TernaryPeriodPolynomials.Argument.FormClassK
