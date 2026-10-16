module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LinePairs

@[expose] public section


/-!
# The radical contributions to the edge of the Hecke image

Let `c` be a relative cocycle of the bad-line stabilizer and `A ∈ Γ₁'(3)`. Suppose the mixed cochain
`E = edge c A` is a *linear cocycle plus a coboundary*,
`E v = ℓ v + (ρ(Ux v) S₀ - S₀)`, where `ℓ` is additive and `ρ(R(w, εp, 1)) ℓ(v) = (εp)⁻¹ ℓ(v)` (this is
the case for the pair cocycles of `BadLinePairs`: the radical acts trivially on the image of the
binary embedding and the scalar `diag(εp,1,1)` acts by `(εp)⁻¹`). Then the radical terms of
`edge_heckeTwo'`, which come from the `p²` cosets `τ_d = R(d, εp, 1)`, add up to `E` itself
modulo a radical coboundary (`rad_pair`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineRadical

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets BadLineTransitions BadLineVectors BadLineEdge
open GoodLineCosets (cvec ivmul_add ivmul_smul crep_levi_bijective crep_shift_bijective
  epsP_ne_zero')

variable (p : Nat.Primes) (A : binaryArithmeticLevel)

/-- `G_e = R(e A⁻¹, εp, 1)`. -/
def Gm (e : Fin p.val × Fin p.val) : RationalGL3 :=
  R (icast (ivmul (cvec p e) (A.val⁻¹ : GL (Fin 2) ℤ).val)) (epsU p) 1

/-- `τ_d · Ux w_d = G_{d'}`. -/
theorem T1 (d : Fin p.val × Fin p.val) :
    sRad p d * ((Ux (wB p A d) : ΛB) : RationalGL3) = Gm p A (dA p A d) := by
  rw [sRad, Ux, Mel_val, Gm, R_mul]
  refine R_congr ?_ ?_ ?_
  · rw [inv_one, Units.val_one, vmul_one, epsU_val, icast_smul_int, ← icast_add]
    exact congrArg icast (L1 p A d)
  · simp
  · simp

/-- `G_{d'} · Ux v_d = Ux r · G_{d''}`. -/
theorem T2 (r : ℤ × ℤ) (d : Fin p.val × Fin p.val) :
    Gm p A (dA p A d) * ((Ux (ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val) : ΛB) :
      RationalGL3) = ((Ux r : ΛB) : RationalGL3) * Gm p A (dA2 p A r d) := by
  rw [Gm, Gm, Ux, Ux, Mel_val, Mel_val, R_mul, R_mul]
  refine R_congr ?_ ?_ ?_
  · simp only [map_one, inv_one, Units.val_one, vmul_one, one_smul]
    rw [epsU_val, icast_smul_int, ← icast_add, ← icast_add]
    exact congrArg icast (L2 p A r d)
  · simp
  · simp

/-- `ivmul` as an additive homomorphism. -/
def ivmulH (M : Matrix (Fin 2) (Fin 2) ℤ) : (ℤ × ℤ) →+ (ℤ × ℤ) :=
  AddMonoidHom.mk' (fun b => ivmul b M) (fun x y => ivmul_add x y M)

theorem sum_ivmul {ι : Type*} (s : Finset ι) (f : ι → ℤ × ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    ∑ i ∈ s, ivmul (f i) M = ivmul (∑ i ∈ s, f i) M :=
  (map_sum (ivmulH M) f s).symm

theorem sum_vd (r : ℤ × ℤ) :
    ∑ d : Fin p.val × Fin p.val, ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val =
      epsP p • r := by
  rw [sum_ivmul, sum_zP, ivmul_smul, ivmul_inv_cancel]

section Radical

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
  (c : groupCohomology.cocycles₂ (Aρ ρ)) (ℓ : (ℤ × ℤ) →+ Aρ ρ)
  (hℓ : ∀ (w : ℚ × ℚ) (v : ℤ × ℤ), R1 ρ (R w (epsU p) 1) (ℓ v) = ((epsP p : ℂ))⁻¹ • ℓ v)
  (S₀ : Aρ ρ)
  (hE : ∀ v : ℤ × ℤ, edgeB ρ c A v = ℓ v + (R1 ρ (Ux v) S₀ - S₀))

include hℓ hE in
/-- **The radical terms reproduce the edge cocycle up to a coboundary.** -/
theorem rad_pair :
    ∃ S : Aρ ρ, ∀ r : ℤ × ℤ,
      (∑ d : Fin p.val × Fin p.val, R1 ρ (sRad p d) ((Aρ ρ).ρ (Ux (wB p A d))
            (edgeB ρ c A (ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val))) +
        (R1 ρ (Ux r) (∑ d : Fin p.val × Fin p.val, phiB p ρ c A d) -
          ∑ d : Fin p.val × Fin p.val, phiB p ρ c A d)) =
        edgeB ρ c A r + (R1 ρ (Ux r) S - S) := by
  have hne : (epsP p : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (epsP_ne_zero' p)
  refine ⟨(∑ e : Fin p.val × Fin p.val, R1 ρ (Gm p A e) S₀) +
    (∑ d : Fin p.val × Fin p.val, phiB p ρ c A d) - S₀, fun r => ?_⟩
  have hG : ∀ (e : Fin p.val × Fin p.val) (v : ℤ × ℤ),
      R1 ρ (Gm p A e) (ℓ v) = ((epsP p : ℂ))⁻¹ • ℓ v := fun e v => hℓ _ v
  have step : ∀ d : Fin p.val × Fin p.val,
      R1 ρ (sRad p d) ((Aρ ρ).ρ (Ux (wB p A d))
          (edgeB ρ c A (ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val))) =
        ((epsP p : ℂ))⁻¹ • ℓ (ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val) +
          (R1 ρ (Ux r) (R1 ρ (Gm p A (dA2 p A r d)) S₀) - R1 ρ (Gm p A (dA p A d)) S₀) := by
    intro d
    have hc : ∀ v : Aρ ρ, R1 ρ (sRad p d) ((Aρ ρ).ρ (Ux (wB p A d)) v) =
        R1 ρ (Gm p A (dA p A d)) v := by
      intro v
      change R1 ρ (sRad p d) (R1 ρ (Ux (wB p A d)) v) = _
      rw [R1_mul, T1]
    have e1 : R1 ρ (Gm p A (dA p A d)) (R1 ρ (Ux (ivmul (zP p A r d)
        (A.val⁻¹ : GL (Fin 2) ℤ).val)) S₀) =
        R1 ρ (Ux r) (R1 ρ (Gm p A (dA2 p A r d)) S₀) :=
      (R1_mul ρ _ _ _).trans ((congrArg (fun g => R1 ρ g S₀) (T2 p A r d)).trans
        (R1_mul ρ _ _ _).symm)
    rw [hc, hE, map_add, map_sub, hG, e1]
  have hsum : ∑ d : Fin p.val × Fin p.val, ((epsP p : ℂ))⁻¹ •
      ℓ (ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val) = ℓ r := by
    rw [← Finset.smul_sum, ← map_sum, sum_vd, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  have b1 : ∑ d : Fin p.val × Fin p.val, R1 ρ (Gm p A (dA p A d)) S₀ =
      ∑ e : Fin p.val × Fin p.val, R1 ρ (Gm p A e) S₀ :=
    (crep_levi_bijective p A.val).sum_comp (fun e => R1 ρ (Gm p A e) S₀)
  have b2 : ∑ d : Fin p.val × Fin p.val, R1 ρ (Gm p A (dA2 p A r d)) S₀ =
      ∑ e : Fin p.val × Fin p.val, R1 ρ (Gm p A e) S₀ :=
    ((crep_shift_bijective p (ivmul r A.val.val)).comp
      (crep_levi_bijective p A.val)).sum_comp (fun e => R1 ρ (Gm p A e) S₀)
  rw [Finset.sum_congr rfl (fun d _ => step d), Finset.sum_add_distrib, hsum,
    Finset.sum_sub_distrib, ← map_sum, b1, b2, hE r]
  simp only [map_add, map_sub]
  abel

end Radical

end TernaryPeriodPolynomials.LevelThree.BadLineRadical
