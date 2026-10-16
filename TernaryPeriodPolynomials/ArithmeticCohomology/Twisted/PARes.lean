module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Levi
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneLocalOp

@[expose] public section


/-!
# Restriction to the plane `X₂ = 0` for the sign-twisted coefficient system

For `χ(-1_∞) = -1` the twisted coefficient action is the trivial-character action multiplied by the
sign of the determinant.  Restricting to the plane `X₂ = 0` therefore turns the action of
`P(x, B, d)` into `sgn(det B · d) · d⁻¹ · A_B`, with `A_B` the binary action of twist `-1`
(`restrict_PT`).  Since a binary action of twist `0` is `det B` times the one of twist `-1`
(`AbinT_eq`), every Levi term of the identity-plane Hecke computation becomes a twist-`0` binary
operator: on `GL₂(ℤ)` the sign `det m = ±1` cancels the factor `det m⁻¹`, on `B_j` (of determinant
`p > 0`) the factor `p` of the corestriction cancels `p⁻¹`, and only the representative
`σ₀ = diag(1, 1, εp)` keeps the sign `sgnP p`.

All lemmas about the Hecke image of a relative two-cocycle are stated for an arbitrary family of
linear coordinates `l μ` with `res (ζ_μ(y)) = Lam (l μ) y`, so that they do not depend on how the
edge cocycle of the relative class is packaged.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.Twisted

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets IdentityPlaneTransitions IdentityPlaneEdge
  IdentityPlaneCoordinate

variable (n : ℕ)

/-- The rational coefficient representation of a rank-one character. -/
abbrev ρT (χ : RankOneCharacter) : Representation ℂ RationalGL3 (HomogeneousPoly n) :=
  rationalCoefficientComponent n χ

/-- The binary action `A_B` in degree `n` with twist `0`. -/
abbrev AbinT (B : GL (Fin 2) ℚ) : Module.End ℂ (Binary.HomogeneousPoly n) :=
  Binary.homogeneousAction n 0 (cx2 B)

theorem det_cx2 (B : GL (Fin 2) ℚ) :
    ((GeneralLinearGroup.det (cx2 B) : ℂˣ) : ℂ) = ((B.val.det : ℚ) : ℂ) := by
  have h : (B.val.map (algebraMap ℚ ℂ)).det = algebraMap ℚ ℂ B.val.det :=
    (RingHom.map_det _ _).symm
  rw [GeneralLinearGroup.val_det_apply]
  exact h.trans (eq_ratCast _ _)

/-- Twist `0` is `det` times twist `-1`. -/
theorem AbinT_eq (B : GL (Fin 2) ℚ) :
    AbinT n B = ((B.val.det : ℚ) : ℂ) • Abin n B := by
  have h := homogeneousAction_succ_twist n (-1) (cx2 B)
  rw [neg_add_cancel, det_cx2] at h
  exact h

theorem AbinT_mul (g h : GL (Fin 2) ℚ) (v : Binary.HomogeneousPoly n) :
    AbinT n g (AbinT n h v) = AbinT n (g * h) v := by
  simp only [AbinT, map_mul, Module.End.mul_apply]

theorem AbinT_one (v : Binary.HomogeneousPoly n) : AbinT n 1 v = v := by
  simp only [AbinT, map_one, Module.End.one_apply]

/-! ### Determinants and signs -/

theorem det_integralEmbed (m : GL (Fin 2) ℤ) :
    (integralEmbed m).val.det = ((m.val.det : ℤ) : ℚ) := by
  rw [integralEmbed_val]
  exact (RingHom.map_det (Int.castRingHom ℚ) m.val).symm

theorem det_int_cases (m : GL (Fin 2) ℤ) : m.val.det = 1 ∨ m.val.det = -1 := by
  have hv : ((GeneralLinearGroup.det m : ℤˣ) : ℤ) = m.val.det := GeneralLinearGroup.val_det_apply m
  rcases Int.units_eq_one_or (GeneralLinearGroup.det m) with hd | hd
  · left
    rw [hd] at hv
    simpa using hv.symm
  · right
    rw [hd] at hv
    simpa using hv.symm

theorem sign_det_integralEmbed (m : GL (Fin 2) ℤ) :
    (if 0 < (integralEmbed m).val.det * ((1 : ℚˣ) : ℚ) then (1 : ℂ) else -1) =
      (((integralEmbed m).val.det : ℚ) : ℂ) := by
  rw [det_integralEmbed, Units.val_one, mul_one]
  rcases det_int_cases m with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- The determinant sign of an integral plane element is its integral determinant. -/
theorem detSign_Pint {χ : RankOneCharacter} (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) :
    detSign χ (Pint b m) = (((integralEmbed m).val.det : ℚ) : ℂ) := by
  rw [detSign_odd hχ]
  have hdet : (Pint b m).val.det = (integralEmbed m).val.det * ((1 : ℚˣ) : ℚ) := det_P _ _ _
  rw [hdet]
  exact sign_det_integralEmbed m

variable (p : Nat.Primes)

/-- The determinant sign of `σ₀ = diag(1, 1, εp)` is `sgnP p`. -/
theorem detSign_sigma {χ : RankOneCharacter} (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    detSign χ (sExpl p none) = ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) := by
  rw [detSign_odd hχ]
  have hdet : (sExpl p none).val.det = ((epsP p : ℤ) : ℚ) := by
    have h : (sExpl p none).val.det = (1 : GL (Fin 2) ℚ).val.det * ((epsU p : ℚˣ) : ℚ) :=
      det_P _ _ _
    rw [h, epsU_val]
    simp
  rw [hdet]
  have hp : (0 : ℚ) < (p.val : ℚ) := by exact_mod_cast p.property.pos
  have hp' : ¬ (p.val : ℚ) < 0 := not_lt.mpr hp.le
  by_cases h : (p.val : ℤ) % 3 = 1
  · simp [IdentityPlaneLocalOp.sgnP, epsP, h, hp]
  · simp [IdentityPlaneLocalOp.sgnP, epsP, h, hp']

/-- The determinant sign of `s_{k,r}` is positive. -/
theorem detSign_sExpl_some (χ : RankOneCharacter) (k : Option (Fin p.val)) (r : Fin p.val) :
    detSign χ (sExpl p (some (k, r))) = 1 := by
  apply detSign_of_pos
  change 0 < (P (icast (wint p k r)) (BGL p k) 1).val.det
  rw [det_P, BGL_val, Bmat_det, Units.val_one, mul_one]
  exact_mod_cast p.property.pos

/-! ### Restricted coefficient action -/

/-- **Restriction of the twisted coefficient action of `P(x, B, d)`.** -/
theorem restrict_PT (χ : RankOneCharacter) (x : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ)
    (v : HomogeneousPoly n) :
    res n (ρT n χ (P x B d) v) =
      detSign χ (P x B d) • (((d : ℚ) : ℂ)⁻¹ • Abin n B (res n v)) := by
  rw [ρT, rho_apply_eq_detSign_smul, map_smul, restrict_P]

theorem res_PintT {χ : RankOneCharacter} (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (v : HomogeneousPoly n) :
    res n (ρT n χ (Pint b m) v) = AbinT n (integralEmbed m) (res n v) := by
  rw [ρT, rho_apply_eq_detSign_smul, map_smul, res_Pint, AbinT_eq, detSign_Pint hχ,
    LinearMap.smul_apply]

theorem res_sigmaT {χ : RankOneCharacter} (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (v : HomogeneousPoly n) :
    res n (ρT n χ (sExpl p none) v) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • (((epsP p : ℚ) : ℂ)⁻¹ • res n v) := by
  rw [ρT, rho_apply_eq_detSign_smul, map_smul, res_sigma, detSign_sigma p hχ]

theorem res_sExplT (χ : RankOneCharacter) (k : Option (Fin p.val)) (r : Fin p.val)
    (v : HomogeneousPoly n) :
    res n (ρT n χ (sExpl p (some (k, r))) v) =
      ((p.val : ℚ) : ℂ)⁻¹ • AbinT n (BGL p k) (res n v) := by
  have hp : ((p.val : ℚ) : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [ρT, rho_apply_eq_detSign_smul, map_smul, res_sExpl, detSign_sExpl_some, one_smul,
    AbinT_eq, BGL_val, Bmat_det, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hp, one_smul]

/-! ### Restricted values of the three edge terms -/

section Edge

variable (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
  (ξ : ℤ × ℤ → Aρ (ρT n χ)) (l : Fin 2 → Binary.HomogeneousPoly n)
  (hξ : ∀ y : ℤ × ℤ, res n (ξ y) = Lam l (icast y))

include hχ

include hξ in
theorem res_term_sigmaT (b : ℤ × ℤ) :
    res n (R (ρT n χ) (sExpl p none) (ξ (epsP p • b))) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • Lam l (icast b) := by
  have hne : (((epsP p : ℤ) : ℚ) : ℂ) ≠ 0 := by exact_mod_cast epsP_ne_zero p
  refine (res_sigmaT n p hχ _).trans ?_
  rw [hξ, ← icast_smul_int, Lam_smul, smul_smul (((epsP p : ℤ) : ℚ) : ℂ)⁻¹, inv_mul_cancel₀ hne,
    one_smul]

theorem res_term_coboundaryT (b : ℤ × ℤ) (v : Aρ (ρT n χ)) :
    res n (R (ρT n χ) (Pint b 1) v - v) = 0 := by
  have h : res n (R (ρT n χ) (Pint b 1) v - v) =
      res n (ρT n χ (Pint b 1) v) - res n v :=
    map_sub (res n) (ρT n χ (Pint b 1) v) (v : HomogeneousPoly n)
  rw [h]
  exact sub_eq_zero.mpr ((res_PintT n hχ b 1 v).trans (by rw [map_one, AbinT_one]))

include hξ in
theorem res_conjT (ν : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    res n (conjFun (ρT n χ) ν ξ y) =
      AbinT n (integralEmbed ν) (Lam l (bmul ((integralEmbed ν)⁻¹ : GL (Fin 2) ℚ).val (icast y))) := by
  unfold conjFun
  refine (res_PintT n hχ 0 ν _).trans ?_
  rw [hξ, icast_imul, integralEmbed_inv]

include hξ in
theorem res_kappaT (k : Option (Fin p.val)) (ν : GL (Fin 2) ℤ) (x : ℤ × ℤ) :
    res n (kappaFun p (ρT n χ) k (conjFun (ρT n χ) ν ξ) x) =
      AbinT n (BGL p k) (AbinT n (integralEmbed ν) (Lam l
        (bmul ((integralEmbed ν)⁻¹ : GL (Fin 2) ℚ).val
          (bmul ((BGL p k)⁻¹ : GL (Fin 2) ℚ).val (icast x))))) := by
  have hp : ((p.val : ℚ) : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  unfold kappaFun
  have hsum := map_sum (res n) (fun r : Fin p.val => (R (ρT n χ) (sExpl p (some (k, r)))
    (conjFun (ρT n χ) ν ξ (-quotVec p k (wint p k r - x))) : HomogeneousPoly n)) Finset.univ
  refine hsum.trans ?_
  have hterm : ∀ r : Fin p.val, res n (R (ρT n χ) (sExpl p (some (k, r)))
      (conjFun (ρT n χ) ν ξ (-quotVec p k (wint p k r - x)))) =
      ((p.val : ℚ) : ℂ)⁻¹ • AbinT n (BGL p k) (AbinT n (integralEmbed ν) (Lam l
        (bmul ((integralEmbed ν)⁻¹ : GL (Fin 2) ℚ).val (-icast (quotVec p k (wint p k r - x)))))) := by
    intro r
    refine (res_sExplT n p χ k r _).trans ?_
    rw [res_conjT n χ hχ ξ l hξ, icast_neg]
  refine (Finset.sum_congr rfl (fun r _ => hterm r)).trans ?_
  rw [← Finset.smul_sum, ← map_sum, ← map_sum, ← Lam_sum, ← bmul_sum, Finset.sum_neg_distrib,
    sum_quot, neg_neg, bmul_smul, Lam_smul, map_smul, map_smul, smul_smul, inv_mul_cancel₀ hp,
    one_smul]

include hξ in
theorem res_term_kappaT (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (b : ℤ × ℤ) :
    res n (R (ρT n χ) (Pint 0 m) (kappaFun p (ρT n χ) (arithmeticNext p m j)
        (conjFun (ρT n χ) (arithmeticDelta p m j)⁻¹ ξ) (imul (m⁻¹ : GL (Fin 2) ℤ).val b))) =
      AbinT n (BGL p j) (Lam l (bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast b))) := by
  refine (res_PintT n hχ 0 m _).trans ?_
  rw [res_kappaT n p χ hχ ξ l hξ, AbinT_mul, AbinT_mul, integral_relation, icast_imul,
    integralEmbed_inv, ← bmul_mul, ← bmul_mul, ← Units.val_mul, ← Units.val_mul]
  congr 4
  rw [← integral_relation p m j]
  simp only [_root_.mul_inv_rev, mul_assoc, map_inv, inv_inv]

end Edge

/-! ### The restricted edge of the Hecke image -/

/-- The restriction on the carrier of the coefficient representation of `Λ₀`. -/
abbrev resAT (χ : RankOneCharacter) : Aρ (ρT n χ) →ₗ[ℂ] Binary.HomogeneousPoly n := res n

section Hecke

variable (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
  (c : groupCohomology.cocycles₂ (Aρ (ρT n χ))) (hrel : ∀ a b : ℤ × ℤ, c (Uel a, Uel b) = 0)
  (l : GL (Fin 2) ℤ → Fin 2 → Binary.HomogeneousPoly n)
  (hl : ∀ (μ : GL (Fin 2) ℤ) (y : ℤ × ℤ), res n (edgeFun (ρT n χ) c μ y) = Lam (l μ) (icast y))

include hχ hrel hl

/-- **The restricted edge of the twisted Hecke image.** If the edge cocycle of `c` restricts to the
linear function `Lam (l μ)`, then the restricted edge cocycle of the local Hecke image is
`sgnP p · Lam (l m) + ∑_j A_{B_j} Lam (l μ_j) (B_j⁻¹ ·)`, with `A_{B_j}` of twist `0`. -/
theorem res_edge_heckeT (m : GL (Fin 2) ℤ) (b : ℤ × ℤ) :
    resAT n χ (edgeFun (ρT n χ) (heckeTwo p (ρT n χ) c) m b) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • Lam (l m) (icast b) +
        ∑ j : Option (Fin p.val), AbinT n (BGL p j)
          (Lam (l (arithmeticDelta p m j)) (bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast b))) := by
  rw [edge_heckeTwo p (ρT n χ) c hrel m b]
  rw [map_add, map_add, map_sum]
  have h0 : resAT n χ (R (ρT n χ) (sExpl p none) (edgeFun (ρT n χ) c m (epsP p • b))) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • Lam (l m) (icast b) :=
    res_term_sigmaT n p χ hχ (edgeFun (ρT n χ) c m) (l m) (hl m) b
  have h1 : ∀ j : Option (Fin p.val), resAT n χ (R (ρT n χ) (Pint 0 m)
      (kappaFun p (ρT n χ) (arithmeticNext p m j)
        (conjFun (ρT n χ) (arithmeticDelta p m j)⁻¹ (edgeFun (ρT n χ) c (arithmeticDelta p m j)))
        (imul (m⁻¹ : GL (Fin 2) ℤ).val b))) =
      AbinT n (BGL p j)
        (Lam (l (arithmeticDelta p m j)) (bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast b))) :=
    fun j => res_term_kappaT n p χ hχ (edgeFun (ρT n χ) c (arithmeticDelta p m j))
      (l (arithmeticDelta p m j)) (hl _) m j b
  refine (congrArg₂ (· + ·) (congrArg₂ (· + ·) h0 (Finset.sum_congr rfl (fun j _ => h1 j)))
    (res_term_coboundaryT n χ hχ b _)).trans ?_
  exact add_zero _

/-- **The restricted generator values of the twisted Hecke image.** -/
theorem lam_heckeT (m : GL (Fin 2) ℤ) (k : Fin 2) :
    res n (edgeFun (ρT n χ) (heckeTwo p (ρT n χ) c) m (if k = 0 then (1, 0) else (0, 1))) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • l m k + ∑ j : Option (Fin p.val),
        AbinT n (BGL p j)
          ((((BGL p j)⁻¹ : GL (Fin 2) ℚ).val 0 k : ℂ) • l (arithmeticDelta p m j) 0 +
            (((BGL p j)⁻¹ : GL (Fin 2) ℚ).val 1 k : ℂ) • l (arithmeticDelta p m j) 1) := by
  refine (res_edge_heckeT n p χ hχ c hrel l hl m _).trans ?_
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl (fun j _ => by rw [Lam_bmul_e]))
  have hk : Lam (l m) (icast (if k = 0 then (1, 0) else (0, 1))) = l m k := by
    fin_cases k
    · exact Lam_e0 _
    · exact Lam_e1 _
  rw [hk]

end Hecke

end TernaryPeriodPolynomials.Twisted
