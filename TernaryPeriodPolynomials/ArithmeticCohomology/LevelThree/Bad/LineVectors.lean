module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineTransitions

@[expose] public section


/-!
# Integral vector identities for the radical cosets at the bad line

For `A ∈ Γ₁'(3)`, `r ∈ ℤ²` and a radical index `d ∈ (ℤ/p)²` put
`d' = crep(d A)`, `w_d = -q(d A) A⁻¹`, `d₂ = crep(d - r)`, `z_d = -q(d - r)`,
`z'_d = -q(d' - r A)`, `d'' = crep(d' - r A)`. This file proves the integral identities that make the
radical contributions to the edge cocycle of `T c` telescope:

* `wB_zP`: `w_d + z'_d A⁻¹ = z_d + w_{d₂}`;
* `L1`: `d + εp w_d = d' A⁻¹`;
* `L2`: `d' A⁻¹ + εp z'_d A⁻¹ = r + d'' A⁻¹`;
* `sum_zP`: `∑_d z'_d = εp (r A)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineVectors

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets
open GoodLineCosets (cvec crep cq ivmul_sub ivmul_add ivmul_smul ivmul_neg ivmul_injective
  eps_smul_cq eps_smul_injective cvec_crep crep_add_eps crep_levi_bijective
  crep_shift_bijective)

variable (p : Nat.Primes) (A : binaryArithmeticLevel)

/-- `d' = crep (d A)`. -/
abbrev dA (d : Fin p.val × Fin p.val) : Fin p.val × Fin p.val :=
  crep p (ivmul (cvec p d) A.val.val)

/-- `w_d = -q(d A) A⁻¹`. -/
abbrev wB (d : Fin p.val × Fin p.val) : ℤ × ℤ :=
  -ivmul (cq p (ivmul (cvec p d) A.val.val)) (A.val⁻¹ : GL (Fin 2) ℤ).val

/-- `z_d = -q(d - r)`. -/
abbrev zS (r : ℤ × ℤ) (d : Fin p.val × Fin p.val) : ℤ × ℤ := -cq p (cvec p d - r)

/-- `d₂ = crep (d - r)`. -/
abbrev dS (r : ℤ × ℤ) (d : Fin p.val × Fin p.val) : Fin p.val × Fin p.val :=
  crep p (cvec p d - r)

/-- `z'_d = -q(d' - r A)`. -/
abbrev zP (r : ℤ × ℤ) (d : Fin p.val × Fin p.val) : ℤ × ℤ :=
  -cq p (cvec p (dA p A d) - ivmul r A.val.val)

/-- `d'' = crep (d' - r A)`. -/
abbrev dA2 (r : ℤ × ℤ) (d : Fin p.val × Fin p.val) : Fin p.val × Fin p.val :=
  crep p (cvec p (dA p A d) - ivmul r A.val.val)

theorem epsP_mul_self : epsP p * epsP p = (p.val : ℤ) * p.val := by
  unfold epsP
  split_ifs <;> ring

theorem wB_zP (r : ℤ × ℤ) (d : Fin p.val × Fin p.val) :
    wB p A d + ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val =
      zS p r d + wB p A (dS p r d) := by
  apply ivmul_injective A.val
  apply eps_smul_injective p
  have e1 : epsP p • ivmul (wB p A d) A.val.val =
      -(ivmul (cvec p d) A.val.val - cvec p (dA p A d)) := by
    simp only [wB, dA, ivmul_neg, ivmul_cancel_inv, smul_neg, eps_smul_cq]
  have e2 : epsP p • ivmul (ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val) A.val.val =
      -((cvec p (dA p A d) - ivmul r A.val.val) -
        cvec p (dA2 p A r d)) := by
    simp only [zP, dA2, dA, ivmul_cancel_inv, smul_neg, eps_smul_cq]
  have e3 : epsP p • ivmul (zS p r d) A.val.val =
      -(ivmul (cvec p d) A.val.val - ivmul r A.val.val - ivmul (cvec p (dS p r d)) A.val.val) := by
    simp only [zS, dS, ivmul_neg, smul_neg, ← ivmul_smul, eps_smul_cq, ivmul_sub]
  have e4 : epsP p • ivmul (wB p A (dS p r d)) A.val.val =
      -(ivmul (cvec p (dS p r d)) A.val.val -
        cvec p (crep p (ivmul (cvec p (dS p r d)) A.val.val))) := by
    simp only [wB, ivmul_neg, ivmul_cancel_inv, smul_neg, eps_smul_cq]
  have h1 : cvec p (dA p A d) - ivmul r A.val.val =
      (ivmul (cvec p d) A.val.val - ivmul r A.val.val) +
        epsP p • (-cq p (ivmul (cvec p d) A.val.val)) := by
    unfold dA
    rw [cvec_crep]
    module
  have h2 : ivmul (cvec p (dS p r d)) A.val.val =
      (ivmul (cvec p d) A.val.val - ivmul r A.val.val) +
        epsP p • (-ivmul (cq p (cvec p d - r)) A.val.val) := by
    simp only [dS]
    rw [cvec_crep, ivmul_sub, ivmul_smul, ivmul_sub]
    module
  have hcr : crep p (cvec p (dA p A d) - ivmul r A.val.val) =
      crep p (ivmul (cvec p (dS p r d)) A.val.val) := by
    rw [h1, h2, crep_add_eps, crep_add_eps]
  rw [ivmul_add, ivmul_add, smul_add, smul_add, e1, e2, e3, e4]
  simp only [dA2]
  rw [hcr]
  module

theorem L1 (d : Fin p.val × Fin p.val) :
    cvec p d + epsP p • wB p A d = ivmul (cvec p (dA p A d)) (A.val⁻¹ : GL (Fin 2) ℤ).val := by
  simp only [wB, dA]
  rw [cvec_crep, ivmul_sub, ivmul_smul, ivmul_inv_cancel]
  module

theorem eps_zP (r : ℤ × ℤ) (d : Fin p.val × Fin p.val) :
    epsP p • zP p A r d =
      cvec p (dA2 p A r d) - (cvec p (dA p A d) - ivmul r A.val.val) := by
  simp only [zP, dA2]
  rw [smul_neg, eps_smul_cq]
  abel

theorem L2 (r : ℤ × ℤ) (d : Fin p.val × Fin p.val) :
    ivmul (cvec p (dA p A d)) (A.val⁻¹ : GL (Fin 2) ℤ).val +
        epsP p • ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val =
      r + ivmul (cvec p (dA2 p A r d)) (A.val⁻¹ : GL (Fin 2) ℤ).val := by
  rw [← ivmul_smul, eps_zP, ivmul_sub, ivmul_sub, ivmul_inv_cancel]
  abel

theorem sum_zP (r : ℤ × ℤ) :
    ∑ d : Fin p.val × Fin p.val, zP p A r d = epsP p • ivmul r A.val.val := by
  apply eps_smul_injective p
  have hz : ∀ d : Fin p.val × Fin p.val, epsP p • zP p A r d =
      (cvec p (dA2 p A r d) - cvec p (dA p A d)) + ivmul r A.val.val := by
    intro d
    rw [eps_zP]
    abel
  have hsum : epsP p • ∑ d : Fin p.val × Fin p.val, zP p A r d =
      ∑ d : Fin p.val × Fin p.val,
        ((cvec p (dA2 p A r d) - cvec p (dA p A d)) + ivmul r A.val.val) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun d _ => hz d)
  have b1 : ∑ d : Fin p.val × Fin p.val, cvec p (dA p A d) =
      ∑ e : Fin p.val × Fin p.val, cvec p e :=
    (crep_levi_bijective p A.val).sum_comp (fun e => cvec p e)
  have b2 : ∑ d : Fin p.val × Fin p.val, cvec p (dA2 p A r d) =
      ∑ e : Fin p.val × Fin p.val, cvec p e :=
    ((crep_shift_bijective p (ivmul r A.val.val)).comp
      (crep_levi_bijective p A.val)).sum_comp (fun e => cvec p e)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, b1, b2, sub_self, zero_add,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hsum
  rw [hsum, smul_smul, epsP_mul_self, ← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_mul]

end TernaryPeriodPolynomials.LevelThree.BadLineVectors
