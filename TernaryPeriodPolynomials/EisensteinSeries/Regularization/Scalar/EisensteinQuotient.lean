module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.EisensteinAutomorphy
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.PrincipalQuotient
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.QuotientPieces
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Reduced.PieceScalarBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter MeasureTheory
open scoped Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)

theorem normalizedScalarEisensteinSum_principal_slice_invariant
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (integral : GL3 IntegralAdeles) (principal : principalRealSpecialLinear) (matrix : RealSL3) :
    normalizedScalarEisensteinSum degree family parameter (realSpecialIntegralSlice integral (principal.val * matrix)) =
      normalizedScalarEisensteinSum degree family parameter (realSpecialIntegralSlice integral matrix) := by
  obtain ⟨integer, integer_principal, represents⟩ := principal.property
  have identity : realSpecialIntegralSlice integral (principal.val * matrix) =
      atInfinity (SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) integer)) *
        realSpecialIntegralSlice integral matrix := by
    rw [← represents]
    simp only [realSpecialIntegralSlice, map_mul, atInfinity_mul, mul_assoc]
  rw [identity]
  apply normalizedScalarEisensteinSum_principal_integer_translation flat parameter
    ⟨integer, integer_principal⟩ _ integral
  simp only [realSpecialIntegralSlice, map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul]

noncomputable def normalizedScalarEisensteinPrincipalQuotient
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (integral : GL3 IntegralAdeles) : PrincipalQuotient → ℂ :=
  Quotient.lift (fun matrix => normalizedScalarEisensteinSum degree family parameter (realSpecialIntegralSlice integral matrix))
    (by
      intro first second relation
      obtain ⟨principal, equality⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp relation)
      change principal.val * second = first at equality
      rw [← equality]
      exact normalizedScalarEisensteinSum_principal_slice_invariant flat parameter integral principal second)

theorem normalizedScalarEisensteinPrincipalQuotient_mk
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (integral : GL3 IntegralAdeles) (matrix : RealSL3) :
    normalizedScalarEisensteinPrincipalQuotient flat parameter integral (Quotient.mk'' matrix) =
      normalizedScalarEisensteinSum degree family parameter (realSpecialIntegralSlice integral matrix) := rfl

theorem normalizedScalarEisensteinPrincipalQuotient_measurable
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (large : 3 / 2 < parameter.re)
    (integral : GL3 IntegralAdeles) : Measurable (normalizedScalarEisensteinPrincipalQuotient flat parameter integral) := by
  apply measurable_from_quotient.mpr
  exact (normalized_scalar_sum_continuous flat parameter large (realSpecialIntegralSlice_continuous integral)).measurable

theorem normalizedScalarEisensteinPrincipalQuotient_residue_limit
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (point : PrincipalQuotient) :
    Tendsto (fun displacement : ℝ => (displacement : ℂ) *
      normalizedScalarEisensteinPrincipalQuotient flat ((3 : ℂ) / 2 + (displacement : ℂ)) integral point)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral point)) := by
  induction point using Quotient.inductionOn with
  | h matrix => exact normalizedBoundaryResidue_tendsto flat continuation_spec (realSpecialIntegralSlice integral matrix)

theorem integer_inverse_slice_identity (integer : SpecialLinearGroup (Fin 3) ℤ)
    (integral : GL3 IntegralAdeles) (matrix : RealSL3) :
    rationalGroup (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL integer)) *
      realSpecialIntegralSlice integral ((SpecialLinearGroup.map (Int.castRingHom ℝ) integer)⁻¹ * matrix) =
      realSpecialIntegralSlice (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles)
        (SpecialLinearGroup.toGL integer) * integral) matrix := by
  rw [integerGL3_adelic_factor]
  apply adelicGroup_eq_of_components
  · simp only [realSpecialIntegralSlice, map_mul, realGroup_atInfinity, realGroup_atFinite, mul_one,
      specialLinear_toGL_map, map_inv, mul_inv_cancel_left]
  · simp only [realSpecialIntegralSlice, map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul,
      integerGL3_map_map]

theorem normalizedScalarEisensteinSum_integer_inverse_slice
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (integer : SpecialLinearGroup (Fin 3) ℤ)
    (integral : GL3 IntegralAdeles) (matrix : RealSL3) :
    normalizedScalarEisensteinSum degree family parameter
      (realSpecialIntegralSlice integral ((SpecialLinearGroup.map (Int.castRingHom ℝ) integer)⁻¹ * matrix)) =
      normalizedScalarEisensteinSum degree family parameter
        (realSpecialIntegralSlice (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles)
          (SpecialLinearGroup.toGL integer) * integral) matrix) := by
  rw [← integer_inverse_slice_identity, normalizedScalarEisensteinSum_rational flat]

theorem normalizedScalarEisensteinPrincipalQuotient_piece_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n, ∀ integral : GL3 IntegralAdeles,
        displacement * ‖normalizedScalarEisensteinPrincipalQuotient flat
          ((3 : ℂ) / 2 + (displacement : ℂ)) integral point‖ ≤ (2 : ℝ) ^ (4 * m + 8 * n) * bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalized_scalar_reduced_piece_boundary_bound flat
  refine ⟨bound, nonnegative, ?_⟩
  filter_upwards [bounded] with displacement bound_at
  intro residue m n point member integral
  obtain ⟨representative, representative_member, rfl⟩ := member
  obtain ⟨reduced, reduced_member, rfl⟩ := representative_member
  rw [normalizedScalarEisensteinPrincipalQuotient_mk]
  change displacement * ‖normalizedScalarEisensteinSum degree family ((3 : ℂ) / 2 + (displacement : ℂ))
    (realSpecialIntegralSlice integral
      ((SpecialLinearGroup.map (Int.castRingHom ℝ) (integerSpecialLinearReductionRepresentative residue))⁻¹ * reduced))‖ ≤ _
  rw [normalizedScalarEisensteinSum_integer_inverse_slice flat]
  exact bound_at m n reduced reduced_member _

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
