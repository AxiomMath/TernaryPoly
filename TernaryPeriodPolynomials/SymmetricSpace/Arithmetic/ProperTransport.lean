module

public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.SymmetricSpaceArithmeticProper
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperBounds

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceArithmeticProper
open Matrix SymmetricSpacePositive

/-- The quadratic value of an actual integral row is the corresponding congruence diagonal. -/
theorem row_quadratic (g : IntegralGL) (S : Space) (i : Fin 3) :
    quadratic S.val ((realIntegral g).val i) = conjugate (realIntegral g) S.val i i := by
  change ((realIntegral g).val i) ⬝ᵥ (S.val*ᵥ((realIntegral g).val i)) =
    ((realIntegral g).val*S.val*(realIntegral g).val.conjTranspose) i i
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,Matrix.mulVec,dotProduct]

/-- Trace normalization bounds each row's positive quadratic value by the explicit scale. -/
theorem row_quadratic_le_scale (g : IntegralGL) (S : Space) (i : Fin 3) :
    quadratic S.val ((realIntegral g).val i) ≤ scale g S := by
  rw [row_quadratic,conjugate_eq_scale_smul]
  change scale g S*(act (realIntegral g) S).val i i ≤ scale g S
  exact (mul_le_mul_of_nonneg_left (diagonal_le_one (act (realIntegral g) S) i)
    (le_of_lt (scale_pos g S))).trans_eq (mul_one _)

/-- The determinant identity bounds the positive normalization scalar uniformly on compact
source and target sets, rather than assuming the normalized transporter is an isometry. -/
theorem compact_scale_bound (C D : Set Space) (hC : IsCompact C) (hD : IsCompact D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : IntegralGL) (S : Space),
      S ∈ C → act (realIntegral g) S ∈ D → scale g S ≤ K := by
  obtain ⟨M,hM⟩ := compact_det_upper C hC
  obtain ⟨δ,hδ,hδD⟩ := compact_det_lower D hD
  refine ⟨max 1 (M/δ),lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro g S hS hT
  have hcube : scale g S^3*δ ≤ M := calc
    _ ≤ scale g S^3*(act (realIntegral g) S).val.det :=
      mul_le_mul_of_nonneg_left (hδD _ hT) (le_of_lt (pow_pos (scale_pos g S) 3))
    _ = S.val.det := (normalized_determinant g S).symm
    _ ≤ M := hM S hS
  by_cases hr : scale g S ≤ 1
  · exact hr.trans (le_max_left _ _)
  · exact (le_self_pow₀ (le_of_not_ge hr) (by decide : (3 : ℕ) ≠ 0)).trans
      (((le_div_iff₀ hδ).mpr hcube).trans (le_max_right _ _))

/-- Every compact transporter for the literal normalized integral action has a uniform bound
on all nine real matrix entries. -/
theorem compact_transporter_entry_bound (C D : Set Space) (hC : IsCompact C) (hD : IsCompact D) :
    ∃ R : ℝ, ∀ (g : IntegralGL), (∃ S ∈ C, act (realIntegral g) S ∈ D) →
      ∀ i j, |(g.val i j : ℝ)| ≤ R := by
  obtain ⟨ε,hε,hεC⟩ := compact_uniform_coercivity C hC
  obtain ⟨K,_hK,hKCD⟩ := compact_scale_bound C D hC hD
  refine ⟨max 1 (K/ε),?_⟩
  intro g hg i j
  obtain ⟨S,hS,hT⟩ := hg
  have hsq : ε*‖(realIntegral g).val i‖^2 ≤ K :=
    (hεC S hS ((realIntegral g).val i)).trans
      ((row_quadratic_le_scale g S i).trans (hKCD g S hS hT))
  have hnorm : ‖(realIntegral g).val i‖ ≤ max 1 (K/ε) := by
    by_cases hr : ‖(realIntegral g).val i‖ ≤ 1
    · exact hr.trans (le_max_left _ _)
    · have hsq' : ‖(realIntegral g).val i‖^2 ≤ K/ε :=
        (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hsq)
      exact (le_self_pow₀ (le_of_not_ge hr) (by decide : (2 : ℕ) ≠ 0)).trans
        (hsq'.trans (le_max_right _ _))
  have hcoord := (norm_le_pi_norm ((realIntegral g).val i) j).trans hnorm
  exact hcoord

end TernaryPoly.SymmetricSpaceArithmeticProper
