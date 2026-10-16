module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearFlagRepresentatives
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.PlaneDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

theorem integerSpecialLinearRationalHom_real (matrix : SpecialLinearGroup (Fin 3) ℤ) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (integerSpecialLinearRationalHom matrix) =
      SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) matrix) := by
  change GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix)) = _
  rw [integerGL3_map_map, specialLinear_toGL_map]

theorem rational_real_inPlane_iff (matrix : RationalGL3) :
    InPlaneParabolic (GeneralLinearGroup.map (algebraMap ℚ ℝ) matrix) ↔ InPlaneParabolic matrix := by
  constructor
  · rintro ⟨first, second⟩
    constructor
    · change (matrix.val 2 0 : ℝ) = 0 at first
      exact_mod_cast first
    · change (matrix.val 2 1 : ℝ) = 0 at second
      exact_mod_cast second
  · exact inPlane_map (algebraMap ℚ ℝ) matrix

theorem principal_flag_stabilizer_iff (representative : SpecialLinearGroup (Fin 3) ℤ)
    (element : principalRealSpecialLinear) :
    element ∈ MulAction.stabilizer principalRealSpecialLinear
      (QuotientGroup.mk (integerSpecialLinearRationalHom representative) : Flags .plane) ↔
      InPlaneParabolic (SpecialLinearGroup.toGL
        ((SpecialLinearGroup.map (Int.castRingHom ℝ) representative)⁻¹ * element.val *
          SpecialLinearGroup.map (Int.castRingHom ℝ) representative)) := by
  change (QuotientGroup.mk (principalRealRationalHom element * integerSpecialLinearRationalHom representative) :
    Flags .plane) = QuotientGroup.mk (integerSpecialLinearRationalHom representative) ↔ _
  rw [eq_comm, QuotientGroup.eq]
  change InPlaneParabolic ((integerSpecialLinearRationalHom representative)⁻¹ *
    (principalRealRationalHom element * integerSpecialLinearRationalHom representative)) ↔ _
  rw [← rational_real_inPlane_iff]
  simp only [map_mul, map_inv, principalRealRationalHom_real, integerSpecialLinearRationalHom_real, mul_assoc]

theorem principalIntegerSpecialLinear_conjugate (representative : SpecialLinearGroup (Fin 3) ℤ)
    (element : principalIntegerSpecialLinear) :
    representative * element.val * representative⁻¹ ∈ principalIntegerSpecialLinear := by
  change integerSpecialLinearReduction (representative * element.val * representative⁻¹) = 1
  rw [map_mul, map_mul, map_inv, show integerSpecialLinearReduction element.val = 1 from element.property,
    mul_one, mul_inv_cancel]

theorem principalRealSpecialLinear_integer_conjugate (representative : SpecialLinearGroup (Fin 3) ℤ)
    (element : principalRealSpecialLinear) :
    SpecialLinearGroup.map (Int.castRingHom ℝ) representative * element.val *
      (SpecialLinearGroup.map (Int.castRingHom ℝ) representative)⁻¹ ∈ principalRealSpecialLinear := by
  obtain ⟨integer, principal, represents⟩ := element.property
  refine ⟨representative * integer * representative⁻¹,
    principalIntegerSpecialLinear_conjugate representative ⟨integer, principal⟩, ?_⟩
  simp only [map_mul, map_inv, represents]

noncomputable def principalFlagStabilizerEquiv (representative : SpecialLinearGroup (Fin 3) ℤ) :
    MulAction.stabilizer principalRealSpecialLinear
      (QuotientGroup.mk (integerSpecialLinearRationalHom representative) : Flags .plane) ≃*
        principalRealPlaneParabolic where
  toFun element := ⟨(SpecialLinearGroup.map (Int.castRingHom ℝ) representative)⁻¹ * element.val.val *
    SpecialLinearGroup.map (Int.castRingHom ℝ) representative,
    by
      refine ⟨?_, (principal_flag_stabilizer_iff representative element.val).mp element.property⟩
      change (SpecialLinearGroup.map (Int.castRingHom ℝ) representative)⁻¹ * element.val.val *
        SpecialLinearGroup.map (Int.castRingHom ℝ) representative ∈ principalRealSpecialLinear
      simpa only [map_inv, inv_inv] using principalRealSpecialLinear_integer_conjugate representative⁻¹ element.val⟩
  invFun element := ⟨⟨SpecialLinearGroup.map (Int.castRingHom ℝ) representative * element.val *
    (SpecialLinearGroup.map (Int.castRingHom ℝ) representative)⁻¹,
    principalRealSpecialLinear_integer_conjugate representative ⟨element.val, element.property.1⟩⟩,
    by
      apply (principal_flag_stabilizer_iff representative _).mpr
      have cancellation : (SpecialLinearGroup.map (Int.castRingHom ℝ) representative)⁻¹ *
          (SpecialLinearGroup.map (Int.castRingHom ℝ) representative * element.val *
            (SpecialLinearGroup.map (Int.castRingHom ℝ) representative)⁻¹) *
          SpecialLinearGroup.map (Int.castRingHom ℝ) representative = element.val := by group
      change InPlaneParabolic (SpecialLinearGroup.toGL (_ * (_ * element.val * _) * _))
      rw [cancellation]
      exact element.property.2⟩
  left_inv element := by
    apply Subtype.ext
    apply Subtype.ext
    change _ * (_⁻¹ * element.val.val * _) * _⁻¹ = element.val.val
    group
  right_inv element := by
    apply Subtype.ext
    change _⁻¹ * (_ * element.val * _⁻¹) * _ = element.val
    group
  map_mul' first second := by
    apply Subtype.ext
    change _⁻¹ * (first.val.val * second.val.val) * _ =
      (_⁻¹ * first.val.val * _) * (_⁻¹ * second.val.val * _)
    group

theorem principalFlagStabilizerEquiv_val (representative : SpecialLinearGroup (Fin 3) ℤ)
    (element : MulAction.stabilizer principalRealSpecialLinear
      (QuotientGroup.mk (integerSpecialLinearRationalHom representative) : Flags .plane)) :
    (principalFlagStabilizerEquiv representative element).val =
      (SpecialLinearGroup.map (Int.castRingHom ℝ) representative)⁻¹ * element.val.val *
        SpecialLinearGroup.map (Int.castRingHom ℝ) representative := rfl

theorem principalFlagRepresentativeDomain_isFundamental (representative : SpecialLinearGroup (Fin 3) ℤ) :
    IsFundamentalDomain (MulAction.stabilizer principalRealSpecialLinear
      (QuotientGroup.mk (integerSpecialLinearRationalHom representative) : Flags .plane))
      ((fun matrix : RealSL3 => SpecialLinearGroup.map (Int.castRingHom ℝ) representative * matrix) ''
        principalPlaneDomain) realSpecialLinearHaar := by
  apply principalPlaneDomain_isFundamental.image_of_equiv
    (Equiv.mulLeft (SpecialLinearGroup.map (Int.castRingHom ℝ) representative))
    (measurePreserving_mul_left realSpecialLinearHaar
      (SpecialLinearGroup.map (Int.castRingHom ℝ) representative)⁻¹).quasiMeasurePreserving
    (principalFlagStabilizerEquiv representative).toEquiv
  intro element matrix
  change SpecialLinearGroup.map (Int.castRingHom ℝ) representative *
    ((principalFlagStabilizerEquiv representative element).val * matrix) = element.val.val *
      (SpecialLinearGroup.map (Int.castRingHom ℝ) representative * matrix)
  rw [principalFlagStabilizerEquiv_val]
  group

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
