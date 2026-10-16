module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.IntegralFlags
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.ArithmeticCohomology

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryFiniteness.FiniteFlagOrbits

noncomputable section

instance arithmeticLevel_finiteIndex : arithmeticLevel.FiniteIndex := by
  let : Finite (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)) :=
    Finite.of_injective Units.val Units.val_injective
  apply Subgroup.finiteIndex_of_le (H := reductionThree.ker)
  intro matrix membership
  change reductionThree matrix ∈ rowStabilizer
  change reductionThree matrix = 1 at membership
  rw [membership]
  exact rowStabilizer.one_mem

def fromIntegralQuotient (side : Side) : IntegralGL3 ⧸ arithmeticLevel → ArithmeticCohomology.flagOrbits side :=
  Quotient.map (fun matrix => (QuotientGroup.mk (IntegralFlags.rational matrix⁻¹) : Flags side)) (by
    intro left right related
    have membership : left⁻¹ * right ∈ arithmeticLevel := QuotientGroup.leftRel_apply.mp related
    let levelElement : arithmeticLevel := ⟨(left⁻¹ * right)⁻¹, arithmeticLevel.inv_mem membership⟩
    have rational_mem : rationalInclusion levelElement ∈ rationalLevel := ⟨levelElement, rfl⟩
    apply (MulAction.orbitRel rationalLevel (Flags side)).symm
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨rationalInclusion levelElement, rational_mem⟩, ?_⟩
    change (QuotientGroup.mk (rationalInclusion levelElement * IntegralFlags.rational left⁻¹) : Flags side) =
      QuotientGroup.mk (IntegralFlags.rational right⁻¹)
    congr 1
    change IntegralFlags.rational ((left⁻¹ * right)⁻¹) * IntegralFlags.rational left⁻¹ = _
    rw [← map_mul]
    simp)

theorem fromIntegralQuotient_surjective (side : Side) : Function.Surjective (fromIntegralQuotient side) := by
  intro orbit
  induction orbit using Quotient.inductionOn with
  | _ flag =>
    obtain ⟨matrix, representative⟩ := IntegralFlags.integral_representative side flag
    refine ⟨QuotientGroup.mk matrix⁻¹, ?_⟩
    change Quotient.mk _ (QuotientGroup.mk (IntegralFlags.rational (matrix⁻¹)⁻¹)) = Quotient.mk _ flag
    rw [inv_inv, representative]

instance flagOrbits_finite (side : Side) : Finite (ArithmeticCohomology.flagOrbits side) :=
  Finite.of_surjective (fromIntegralQuotient side) (fromIntegralQuotient_surjective side)

theorem boundary_finiteDimensional_of_stabilizers (degree : ℕ) (character : RankOneCharacter)
    [∀ (side : Side) (orbit : ArithmeticCohomology.flagOrbits side),
      FiniteDimensional ℂ (groupCohomology.H2
        (ArithmeticCohomology.stabilizerRepresentation degree character side orbit))] :
    FiniteDimensional ℂ (BoundaryCoordinates degree character) :=
  ArithmeticCohomology.boundary_finiteDimensional degree character

end

end TernaryPeriodPolynomials.BoundaryFiniteness.FiniteFlagOrbits
