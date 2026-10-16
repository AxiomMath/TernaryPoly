module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.FiniteFlagOrbits

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryFiniteness.ArithmeticStabilizers

noncomputable section

def integralParabolic (side : Side) : Subgroup IntegralGL3 := (parabolic side).comap IntegralFlags.rational

def conjugateLevel (representative : IntegralGL3) : Subgroup IntegralGL3 :=
  arithmeticLevel.comap (MulAut.conj representative).toMonoidHom

def localLevel (side : Side) (representative : IntegralGL3) : Subgroup (integralParabolic side) :=
  (conjugateLevel representative).subgroupOf (integralParabolic side)

instance localLevel_finiteIndex (side : Side) (representative : IntegralGL3) :
    (localLevel side representative).FiniteIndex := by
  let : Finite (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)) :=
    Finite.of_injective Units.val Units.val_injective
  let reduction := reductionThree.comp
    ((MulAut.conj representative).toMonoidHom.comp (integralParabolic side).subtype)
  apply Subgroup.finiteIndex_of_le (H := reduction.ker)
  intro matrix membership
  change reductionThree (representative * matrix.val * representative⁻¹) = 1 at membership
  change reductionThree (representative * matrix.val * representative⁻¹) ∈ rowStabilizer
  rw [membership]
  exact rowStabilizer.one_mem

theorem rational_injective : Function.Injective IntegralFlags.rational := by
  intro left right equality
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  apply Int.cast_injective (α := ℚ)
  exact congrArg (fun matrix : RationalGL3 => matrix.val row column) equality

def toStabilizer (side : Side) (representative : IntegralGL3) :
    localLevel side representative →*
      MulAction.stabilizer rationalLevel (QuotientGroup.mk (IntegralFlags.rational representative) : Flags side) where
  toFun matrix :=
    ⟨⟨IntegralFlags.rational (representative * matrix.val.val * representative⁻¹),
      ⟨⟨representative * matrix.val.val * representative⁻¹, matrix.property⟩, rfl⟩⟩, by
      change (QuotientGroup.mk
        (IntegralFlags.rational (representative * matrix.val.val * representative⁻¹) *
          IntegralFlags.rational representative) : Flags side) = _
      apply QuotientGroup.eq.mpr
      have parabolic_mem : IntegralFlags.rational matrix.val.val ∈ parabolic side := matrix.val.property
      simpa only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
        mul_inv_cancel_right, inv_mul_cancel, mul_one] using (parabolic side).inv_mem parabolic_mem⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change IntegralFlags.rational (representative * 1 * representative⁻¹) = 1
    simp
  map_mul' left right := by
    apply Subtype.ext
    apply Subtype.ext
    change IntegralFlags.rational (representative * (left.val.val * right.val.val) * representative⁻¹) =
      IntegralFlags.rational (representative * left.val.val * representative⁻¹) *
        IntegralFlags.rational (representative * right.val.val * representative⁻¹)
    rw [← map_mul]
    congr 1
    simp only [mul_assoc, inv_mul_cancel_left]

theorem toStabilizer_injective (side : Side) (representative : IntegralGL3) :
    Function.Injective (toStabilizer side representative) := by
  intro left right equality
  have matrices := rational_injective (congrArg (fun element => element.val.val) equality)
  have integral_equality : representative * left.val.val * representative⁻¹ =
      representative * right.val.val * representative⁻¹ := matrices
  apply Subtype.ext
  apply Subtype.ext
  exact mul_left_cancel (mul_right_cancel integral_equality)

theorem toStabilizer_surjective (side : Side) (representative : IntegralGL3) :
    Function.Surjective (toStabilizer side representative) := by
  intro element
  obtain ⟨integral, equality⟩ := element.val.property
  have stabilizes : (QuotientGroup.mk (element.val.val * IntegralFlags.rational representative) : Flags side) =
      QuotientGroup.mk (IntegralFlags.rational representative) := element.property
  have parabolic_mem : IntegralFlags.rational (representative⁻¹ * integral.val * representative) ∈ parabolic side := by
    have membership := QuotientGroup.eq.mp stabilizes.symm
    change (IntegralFlags.rational representative)⁻¹ *
      (element.val.val * IntegralFlags.rational representative) ∈ parabolic side at membership
    have rational_equality : IntegralFlags.rational integral.val = element.val.val := equality
    simpa only [map_mul, map_inv, rational_equality, mul_assoc] using membership
  let localElement : localLevel side representative :=
    ⟨⟨representative⁻¹ * integral.val * representative, parabolic_mem⟩, by
      change representative * (representative⁻¹ * integral.val * representative) * representative⁻¹ ∈ arithmeticLevel
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using integral.property⟩
  refine ⟨localElement, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change IntegralFlags.rational
    (representative * (representative⁻¹ * integral.val * representative) * representative⁻¹) = element.val.val
  have rational_equality : IntegralFlags.rational integral.val = element.val.val := equality
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using rational_equality

def stabilizerEquiv (side : Side) (representative : IntegralGL3) :
    localLevel side representative ≃*
      MulAction.stabilizer rationalLevel (QuotientGroup.mk (IntegralFlags.rational representative) : Flags side) :=
  MulEquiv.ofBijective (toStabilizer side representative)
    ⟨toStabilizer_injective side representative, toStabilizer_surjective side representative⟩

def orbitRepresentative (side : Side) (orbit : ArithmeticCohomology.flagOrbits side) : IntegralGL3 :=
  Classical.choose (IntegralFlags.integral_representative side orbit.out)

theorem orbitRepresentative_spec (side : Side) (orbit : ArithmeticCohomology.flagOrbits side) :
    QuotientGroup.mk (IntegralFlags.rational (orbitRepresentative side orbit)) = orbit.out :=
  Classical.choose_spec (IntegralFlags.integral_representative side orbit.out)

def orbitStabilizerEquiv (side : Side) (orbit : ArithmeticCohomology.flagOrbits side) :
    localLevel side (orbitRepresentative side orbit) ≃* ArithmeticCohomology.flagStabilizer side orbit :=
  (stabilizerEquiv side (orbitRepresentative side orbit)).trans
    (MulEquiv.subgroupCongr (congrArg (MulAction.stabilizer rationalLevel) (orbitRepresentative_spec side orbit)))

def localRepresentation (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (orbit : ArithmeticCohomology.flagOrbits side) : Rep ℂ (localLevel side (orbitRepresentative side orbit)) :=
  Rep.of ((ArithmeticCohomology.stabilizerRepresentation degree character side orbit).ρ.comp
    (orbitStabilizerEquiv side orbit).toMonoidHom)

instance localRepresentation_finiteDimensional (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (orbit : ArithmeticCohomology.flagOrbits side) :
    FiniteDimensional ℂ (localRepresentation degree character side orbit) :=
  ArithmeticCohomology.homogeneous_finiteDimensional 3 degree

def localCohomologyEquiv (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (orbit : ArithmeticCohomology.flagOrbits side) :
    groupCohomology.H2 (localRepresentation degree character side orbit) ≃ₗ[ℂ]
      groupCohomology.H2 (ArithmeticCohomology.stabilizerRepresentation degree character side orbit) :=
  (groupCohomology.mapIso (orbitStabilizerEquiv side orbit) (LinearEquiv.refl ℂ _)
    (fun _ => rfl) 2).toLinearEquiv

end

end TernaryPeriodPolynomials.BoundaryFiniteness.ArithmeticStabilizers
