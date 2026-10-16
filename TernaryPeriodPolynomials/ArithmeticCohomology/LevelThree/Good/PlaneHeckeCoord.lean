module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneHeckeEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge2
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCoordinate

@[expose] public section


/-!
# The binary coordinate of the good-plane edge under the local Hecke operator

Restriction to the plane `X₂ = 0` turns the coefficient action of `P(x, B, d)` into `d⁻¹ · A_B`
(`IdentityPlaneCoordinate.restrict_P`), so the binary coordinate of a radical cocycle only sees the
linear function `y ↦ res ζ(y)`. Combined with the edge formula `GoodPlaneHeckeEdge.edge_heckeTwo`
this gives the exact cocycle-level identity for the Hecke image in the `κ`-twisted coordinates
(`edgeVal_hecke`):

`E(T c)(m) = E(c)(m) + p ∑_j A_{B_j} E(c)(δ_j)`,

where `B_j = p κ(α_j)⁻¹` (`GoodPlaneCosets.BG_inv_eq`), `α_j m = δ_j α_{k_j}`, and `A_B` is
`Sym^{n+1} ⊗ det⁻¹` evaluated at `B`. This is the good-plane analogue of the second half of
`IdentityPlaneCoordinate`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneHeckeCoord

open TernaryPeriodPolynomials.Spectral
open PlaneCoordinates
open IdentityPlaneCosets (icast icast_neg icast_sub icast_add icast_smul_int bmul_injective imul
  epsP epsP_ne_zero)
open IdentityPlaneCoordinate (ρn cx2 Abin res genRes Lam Lam_sum Lam_smul Lam_bmul_e Lam_e0 Lam_e1
  res_cocycle bmul_sum Abin_mul Abin_one restrict_P action_coord)
open GoodPlaneCosetData GoodPlaneFrame GoodPlaneModel GoodPlaneCosets GoodPlaneTransitions
open GoodPlaneHeckeEdge (R Aρ edgeFun conjFun kappaFun heckeTwo inl_eq splitting_eq act_unit_one
  edge_heckeTwo heckeTwo_relative)
open GoodPlaneEdge (jc_val splitRadicalInput_apply)
open GoodPlaneEdge2 (edgeVal)
open LevelThreeCosets (levelNext levelDelta)

variable (n : ℕ)

/-- The relative two-cocycles of the good-plane stabilizer. -/
abbrev Rel := relativeTwoCocycles goodPlaneExtension.inl (coefRep n)

/-! ### The sum of the quotient vectors -/

section SumQuot

variable (p : Nat.Primes)

/-- `∑_r q_r(x) = -p B_k⁻¹ x`. -/
theorem sum_quot (k : Option (Fin p.val)) (x : ℤ × ℤ) :
    ∑ r : Fin p.val, icast (quotVec p k (wint p k r - x)) =
      -((p.val : ℚ) • bmul ((BG p k)⁻¹ : GL (Fin 2) ℚ).val (icast x)) := by
  apply bmul_injective (BG p k)
  rw [bmul_sum, bmul_neg, bmul_smul, bmul_cancel_inv]
  have h : ∀ r : Fin p.val, bmul (BG p k).val (icast (quotVec p k (wint p k r - x))) =
      icast (wint p k r) - icast x - icast (wint p k (repIdx p k (wint p k r - x))) := by
    intro r
    have := rep_spec' p k (wint p k r - x)
    rw [icast_sub] at this
    rw [this]
    abel
  simp only [h, Finset.sum_sub_distrib]
  have hb := (radical_bijective p x k).sum_comp (fun r => icast (wint p k r))
  rw [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℚ]
  abel

end SumQuot

/-! ### The edge cocycle in Sol's coordinates -/

theorem edgeFun_eq (c : Rel n) (m : binaryArithmeticLevel) (y : ℤ × ℤ) :
    edgeFun (ρn n) c.val m y =
      splitEdgeCycle goodPlaneSplitting (coefRep n) (m, 1) c (Multiplicative.ofAdd y) := by
  rw [splitEdgeCycle_apply, splitRadicalInput_apply, inl_eq, inl_eq, splitting_eq, edgeFun]
  simp only [toAdd_ofAdd, act_unit_one]

/-- The restricted generator values of the edge at `μ`. -/
abbrev lam (c : Rel n) (μ : binaryArithmeticLevel) : Fin 2 → Binary.HomogeneousPoly n :=
  genRes n (splitEdgeCycle goodPlaneSplitting (coefRep n) (μ, 1) c)

theorem res_edgeFun (c : Rel n) (m : binaryArithmeticLevel) (y : ℤ × ℤ) :
    res n (edgeFun (ρn n) c.val m y) = Lam (lam n c m) (icast y) := by
  rw [edgeFun_eq]
  exact res_cocycle n _ y

/-! ### Restricted values of the three edge terms -/

theorem res_PK (b : ℤ × ℤ) (m : binaryArithmeticLevel) (v : HomogeneousPoly n) :
    res n (ρn n (PK b m) v) = Abin n (Em m) (res n v) := by
  rw [PK, restrict_P, Units.val_one, Rat.cast_one, inv_one, one_smul]

section Restricted

variable (p : Nat.Primes)

theorem res_sigma (v : HomogeneousPoly n) :
    res n (ρn n (sExpl p none) v) = ((epsP p : ℚ) : ℂ)⁻¹ • res n v := by
  rw [sExpl, restrict_P, Abin_one]
  rfl

theorem res_sExpl (k : Option (Fin p.val)) (r : Fin p.val) (v : HomogeneousPoly n) :
    res n (ρn n (sExpl p (some (k, r))) v) = Abin n (BG p k) (res n v) := by
  rw [sExpl, restrict_P, Units.val_one, Rat.cast_one, inv_one, one_smul]

variable (c : Rel n)

theorem res_term_sigma (m : binaryArithmeticLevel) (b : ℤ × ℤ) :
    res n (R (ρn n) (sExpl p none) (edgeFun (ρn n) c.val m (epsP p • b))) =
      Lam (lam n c m) (icast b) := by
  have h := res_sigma n p (edgeFun (ρn n) c.val m (epsP p • b))
  refine h.trans ?_
  rw [res_edgeFun, ← icast_smul_int, Lam_smul, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast epsP_ne_zero p

theorem res_term_coboundary (b : ℤ × ℤ) (v : Aρ (ρn n)) :
    res n (R (ρn n) (PK b 1) v - v) = 0 := by
  have h : res n (R (ρn n) (PK b 1) v - v) = res n (ρn n (PK b 1) v) - res n v :=
    map_sub (res n) (ρn n (PK b 1) v) (v : HomogeneousPoly n)
  rw [h]
  exact sub_eq_zero.mpr ((res_PK n b 1 v).trans (by rw [map_one, Abin_one]))

theorem res_conj (ν μ : binaryArithmeticLevel) (y : ℤ × ℤ) :
    res n (conjFun (ρn n) ν (edgeFun (ρn n) c.val μ) y) =
      Abin n (Em ν) (Lam (lam n c μ) (bmul ((Em ν)⁻¹ : GL (Fin 2) ℚ).val (icast y))) := by
  unfold conjFun
  refine (res_PK n 0 ν _).trans ?_
  rw [res_edgeFun, bmul_Em_inv]

theorem res_kappa (k : Option (Fin p.val)) (ν μ : binaryArithmeticLevel) (x : ℤ × ℤ) :
    res n (kappaFun p (ρn n) k (conjFun (ρn n) ν (edgeFun (ρn n) c.val μ)) x) =
      ((p.val : ℚ) : ℂ) • Abin n (BG p k) (Abin n (Em ν) (Lam (lam n c μ)
        (bmul ((Em ν)⁻¹ : GL (Fin 2) ℚ).val
          (bmul ((BG p k)⁻¹ : GL (Fin 2) ℚ).val (icast x))))) := by
  unfold kappaFun
  have hsum := map_sum (res n)
    (fun r : Fin p.val => (R (ρn n) (sExpl p (some (k, r)))
      (conjFun (ρn n) ν (edgeFun (ρn n) c.val μ) (-quotVec p k (wint p k r - x))) :
        HomogeneousPoly n)) Finset.univ
  refine hsum.trans ?_
  have hterm : ∀ r : Fin p.val, res n (R (ρn n) (sExpl p (some (k, r)))
      (conjFun (ρn n) ν (edgeFun (ρn n) c.val μ) (-quotVec p k (wint p k r - x)))) =
      Abin n (BG p k) (Abin n (Em ν) (Lam (lam n c μ)
        (bmul ((Em ν)⁻¹ : GL (Fin 2) ℚ).val (-icast (quotVec p k (wint p k r - x)))))) := by
    intro r
    refine (res_sExpl n p k r _).trans ?_
    rw [res_conj, icast_neg]
  refine (Finset.sum_congr rfl (fun r _ => hterm r)).trans ?_
  rw [← map_sum, ← map_sum, ← Lam_sum, ← bmul_sum, Finset.sum_neg_distrib, sum_quot, neg_neg,
    bmul_smul, Lam_smul, map_smul, map_smul]

end Restricted

section Kappa

variable (p : Nat.Primes) (hp3 : p.val ≠ 3) (c : Rel n)

theorem integral_relation (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    Em m * BG p (levelNext p hp3 m j) * Em (levelDelta p hp3 m j)⁻¹ = BG p j := by
  rw [Em_inv, ← BG_mul_delta p hp3, mul_inv_cancel_right]

theorem inv_relation (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    (Em (levelDelta p hp3 m j)⁻¹)⁻¹ * (BG p (levelNext p hp3 m j))⁻¹ * (Em m)⁻¹ =
      (BG p j)⁻¹ := by
  rw [← integral_relation p hp3 m j]
  group

theorem res_term_kappa (m : binaryArithmeticLevel) (j : Option (Fin p.val)) (b : ℤ × ℤ) :
    res n (R (ρn n) (PK 0 m) (kappaFun p (ρn n) (levelNext p hp3 m j)
        (conjFun (ρn n) (levelDelta p hp3 m j)⁻¹ (edgeFun (ρn n) c.val (levelDelta p hp3 m j)))
        (imul (kap m⁻¹).val b))) =
      ((p.val : ℚ) : ℂ) • Abin n (BG p j) (Lam (lam n c (levelDelta p hp3 m j))
        (bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val (icast b))) := by
  refine (res_PK n 0 m _).trans ?_
  rw [res_kappa, map_smul, Abin_mul, Abin_mul, integral_relation p hp3, ← bmul_Em_inv,
    ← bmul_mul, ← bmul_mul, ← Units.val_mul, ← Units.val_mul, inv_relation p hp3]

end Kappa

/-! ### The restricted edge of the Hecke image -/

/-- The restriction on the carrier of the coefficient representation of `ΛG`. -/
abbrev resA : Aρ (ρn n) →ₗ[ℂ] Binary.HomogeneousPoly n := res n

theorem rel_UK (c : Rel n) (a b : ℤ × ℤ) : c.val (UK a, UK b) = 0 := by
  have h := c.2 (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
  rwa [inl_eq, inl_eq] at h

section HeckeRestricted

variable (p : Nat.Primes) (hp3 : p.val ≠ 3) (c : Rel n)

theorem res_edge_hecke (m : binaryArithmeticLevel) (b : ℤ × ℤ) :
    resA n (edgeFun (ρn n) (heckeTwo p hp3 (ρn n) c.val) m b) =
      Lam (lam n c m) (icast b) + ∑ j : Option (Fin p.val), ((p.val : ℚ) : ℂ) •
        Abin n (BG p j) (Lam (lam n c (levelDelta p hp3 m j))
          (bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val (icast b))) := by
  rw [edge_heckeTwo p hp3 (ρn n) c.val (rel_UK n c) m b, map_add, map_add, map_sum]
  have h0 : resA n (R (ρn n) (sExpl p none) (edgeFun (ρn n) c.val m (epsP p • b))) =
      Lam (lam n c m) (icast b) := res_term_sigma n p c m b
  refine (congrArg₂ (· + ·) (congrArg₂ (· + ·) h0
    (Finset.sum_congr rfl (fun j _ => res_term_kappa n p hp3 c m j b)))
      (res_term_coboundary n b _)).trans ?_
  exact add_zero _

end HeckeRestricted

/-! ### The Hecke image as a relative cocycle -/

section Headline

variable {n : ℕ} (p : Nat.Primes) (hp3 : p.val ≠ 3) (c : Rel n)

/-- The Hecke image as a relative cocycle. -/
def heckeRel : Rel n :=
  ⟨heckeTwo p hp3 (ρn n) c.val, by
    intro u v
    rw [inl_eq, inl_eq]
    exact heckeTwo_relative p hp3 (ρn n) c.val (rel_UK n c) _ _⟩

theorem heckeRel_val : (heckeRel p hp3 c).val = heckeTwo p hp3 (ρn n) c.val := rfl

theorem lam_generator (μ : binaryArithmeticLevel) (k : Fin 2) :
    lam n c μ k = res n (edgeFun (ρn n) c.val μ (if k = 0 then (1, 0) else (0, 1))) := by
  rw [edgeFun_eq]
  unfold lam genRes radicalLatticeGenerator radicalLatticeFirst radicalLatticeSecond
  split_ifs <;> rfl

/-- **The restricted generator values of the Hecke image.** -/
theorem lam_hecke (m : binaryArithmeticLevel) (k : Fin 2) :
    lam n (heckeRel p hp3 c) m k = lam n c m k + ∑ j : Option (Fin p.val), ((p.val : ℚ) : ℂ) •
      Abin n (BG p j) ((((BG p j)⁻¹ : GL (Fin 2) ℚ).val 0 k : ℂ) •
          lam n c (levelDelta p hp3 m j) 0 +
        (((BG p j)⁻¹ : GL (Fin 2) ℚ).val 1 k : ℂ) • lam n c (levelDelta p hp3 m j) 1) := by
  rw [lam_generator]
  refine (res_edge_hecke n p hp3 c m _).trans ?_
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl (fun j _ => by rw [Lam_bmul_e]))
  fin_cases k
  · exact Lam_e0 _
  · exact Lam_e1 _

/-! ### The binary coordinate -/

theorem edgeVal_val (μ : binaryArithmeticLevel) :
    (edgeVal c (μ, 1)).val =
      (n + 1 : ℂ)⁻¹ • (X 0 * (lam n c μ 0).val + X 1 * (lam n c μ 1).val) :=
  jc_val n (splitEdgeCycle goodPlaneSplitting (coefRep n) (μ, 1) c)

/-- The underlying polynomial of a binary coefficient. -/
abbrev polyVal : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] Binary.Poly :=
  (Binary.HomogeneousPoly (n + 1)).subtype

/-- **Cocycle-level Hecke formula for the good-plane binary edge.** For a relative two-cocycle
`c`, the binary edge cocycle of its local Hecke image is
`E(Tc)(m) = E(c)(m) + p ∑_j A_{B_j} E(c)(δ_j)`, where `B_j = p κ(α_j)⁻¹` and
`α_j m = δ_j α_{k_j}`. -/
theorem edgeVal_hecke (m : binaryArithmeticLevel) :
    edgeVal (heckeRel p hp3 c) (m, 1) = edgeVal c (m, 1) + ((p.val : ℚ) : ℂ) •
      ∑ j : Option (Fin p.val), Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) (BG p j))
        (edgeVal c (levelDelta p hp3 m j, 1)) := by
  apply (show Function.Injective (polyVal (n := n)) from Subtype.val_injective)
  rw [map_add, map_smul, map_sum]
  change (edgeVal (heckeRel p hp3 c) (m, 1)).val = (edgeVal c (m, 1)).val +
    ((p.val : ℚ) : ℂ) • ∑ j : Option (Fin p.val),
      Binary.action (-1) (cx2 (BG p j)) (edgeVal c (levelDelta p hp3 m j, 1)).val
  rw [edgeVal_val, edgeVal_val, lam_hecke, lam_hecke]
  simp only [edgeVal_val, ← action_coord]
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, mul_add, Finset.mul_sum,
    smul_add, Finset.smul_sum, mul_smul_comm, smul_smul, Finset.sum_add_distrib]
  simp only [mul_comm ((n : ℂ) + 1)⁻¹ _]
  abel

end Headline

end TernaryPeriodPolynomials.LevelThree.GoodPlaneHeckeCoord
