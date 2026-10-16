module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHeckeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalEdgeFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.RadicalBinaryEquivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CentralAction

@[expose] public section


/-!
# The binary coordinate of the identity-plane edge under the local Hecke operator

Restriction to the plane `X₂ = 0` turns the coefficient action of `P(x, B, d)` into
`d⁻¹ · A_B` (`restrict_P`), so the binary coordinate of a radical cocycle only sees the linear
function `y ↦ res ζ(y)`. Combined with the edge formula `IdentityPlaneEdge.edge_heckeTwo`, this gives
the exact cocycle-level identity for the Hecke image.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets IdentityPlaneTransitions IdentityPlaneEdge

variable (n : ℕ)

/-- The rational coefficient representation with trivial character. -/
abbrev ρn : Representation ℂ RationalGL3 (HomogeneousPoly n) :=
  rationalCoefficientComponent n trivialCharacter

/-- Complexification of rational binary matrices. -/
abbrev cx2 : GL (Fin 2) ℚ →* Binary.GL2 := GeneralLinearGroup.map (algebraMap ℚ ℂ)

/-- The binary action `A_B` in degree `n` with twist `-1`. -/
abbrev Abin (B : GL (Fin 2) ℚ) : Module.End ℂ (Binary.HomogeneousPoly n) :=
  Binary.homogeneousAction n (-1) (cx2 B)

/-- The restriction to the plane `X₂ = 0`. -/
abbrev res : HomogeneousPoly n →ₗ[ℂ] Binary.HomogeneousPoly n := binaryHomogeneousRestrict n

theorem rho_coe (g : RationalGL3) (v : HomogeneousPoly n) :
    (ρn n g v).val = action (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) g) v.val := by
  change (1 : ℂ) • action (-1)
    (GeneralLinearGroup.map (algebraMap ℝ ℂ) (GeneralLinearGroup.map (algebraMap ℚ ℝ) g)) v.val = _
  rw [one_smul]
  congr 2

theorem restrict_substitute_P (x : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) (f : Poly) :
    binaryPolynomialRestrict (substitute (GeneralLinearGroup.map (algebraMap ℚ ℂ) (P x B d)).val f) =
      Binary.substitute (cx2 B).val (binaryPolynomialRestrict f) := by
  have equality : binaryPolynomialRestrict.comp
      (substitute (GeneralLinearGroup.map (algebraMap ℚ ℂ) (P x B d)).val) =
      (Binary.substitute (cx2 B).val).comp binaryPolynomialRestrict := by
    apply MvPolynomial.algHom_ext
    intro coordinate
    fin_cases coordinate <;>
      simp [AlgHom.comp_apply, substitute_X, linearForm, binaryPolynomialRestrict, Binary.substitute_X,
        Binary.linearForm, Fin.sum_univ_three, Fin.sum_univ_two, P_val]
  exact congrArg (fun hom : Poly →ₐ[ℂ] Binary.Poly => hom f) equality

theorem det_P (x : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    (P x B d).val.det = B.val.det * d := by
  rw [P_val, Matrix.det_fin_three, Matrix.det_fin_two]
  simp
  ring

/-- **Restriction of the coefficient action of `P(x, B, d)`.** -/
theorem restrict_P (x : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) (v : HomogeneousPoly n) :
    res n (ρn n (P x B d) v) = ((d : ℚ) : ℂ)⁻¹ • Abin n B (res n v) := by
  apply Subtype.ext
  rw [binaryHomogeneousRestrict_apply, rho_coe, action_apply, map_smul, ← map_inv, P_inv,
    restrict_substitute_P]
  change _ = ((d : ℚ) : ℂ)⁻¹ • Binary.action (-1) (cx2 B) (binaryPolynomialRestrict v.val)
  rw [Binary.action_apply, ← map_inv, smul_smul]
  congr 1
  change ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℂ) (P x B d)) : ℂˣ) : ℂ) ^ (-1 : ℤ) =
    ((d : ℚ) : ℂ)⁻¹ * ((GeneralLinearGroup.det (cx2 B) : ℂˣ) : ℂ) ^ (-1 : ℤ)
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
  change ((P x B d).val.map (algebraMap ℚ ℂ)).det ^ (-1 : ℤ) =
    ((d : ℚ) : ℂ)⁻¹ * (B.val.map (algebraMap ℚ ℂ)).det ^ (-1 : ℤ)
  have h1 : ((P x B d).val.map (algebraMap ℚ ℂ)).det = algebraMap ℚ ℂ (P x B d).val.det :=
    (RingHom.map_det _ _).symm
  have h2 : (B.val.map (algebraMap ℚ ℂ)).det = algebraMap ℚ ℂ B.val.det := (RingHom.map_det _ _).symm
  rw [h1, h2, det_P]
  simp only [_root_.zpow_neg_one, map_mul, mul_inv, eq_ratCast]
  ring

/-! ### Linear functions of the radical coordinate -/

section Lam

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- `Lam l y = y₁ l₀ + y₂ l₁` for a rational vector `y`. -/
def Lam (l : Fin 2 → W) (y : ℚ × ℚ) : W := ((y.1 : ℂ)) • l 0 + ((y.2 : ℂ)) • l 1

theorem Lam_add (l : Fin 2 → W) (y z : ℚ × ℚ) : Lam l (y + z) = Lam l y + Lam l z := by
  simp only [Lam, Prod.fst_add, Prod.snd_add, Rat.cast_add, add_smul]
  abel

theorem Lam_zero (l : Fin 2 → W) : Lam l 0 = 0 := by simp [Lam]

theorem Lam_neg (l : Fin 2 → W) (y : ℚ × ℚ) : Lam l (-y) = -Lam l y := by
  simp only [Lam, Prod.fst_neg, Prod.snd_neg, Rat.cast_neg, neg_smul]
  abel

theorem Lam_sub (l : Fin 2 → W) (y z : ℚ × ℚ) : Lam l (y - z) = Lam l y - Lam l z := by
  rw [sub_eq_add_neg, Lam_add, Lam_neg, ← sub_eq_add_neg]

theorem Lam_smul (l : Fin 2 → W) (q : ℚ) (y : ℚ × ℚ) : Lam l (q • y) = (q : ℂ) • Lam l y := by
  simp only [Lam, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Rat.cast_mul, smul_add, smul_smul]

theorem Lam_sum {ι : Type*} (s : Finset ι) (l : Fin 2 → W) (y : ι → ℚ × ℚ) :
    Lam l (∑ i ∈ s, y i) = ∑ i ∈ s, Lam l (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lam_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Lam_add, ih]

theorem Lam_bmul (l : Fin 2 → W) (B : Matrix (Fin 2) (Fin 2) ℚ) (y : ℚ × ℚ) :
    Lam l (bmul B y) = Lam (fun k => ((B 0 k : ℚ) : ℂ) • l 0 + ((B 1 k : ℚ) : ℂ) • l 1) y := by
  simp only [Lam, bmul, Rat.cast_add, Rat.cast_mul, add_smul, smul_add, smul_smul]
  module

theorem map_Lam {W' : Type*} [AddCommGroup W'] [Module ℂ W'] (f : W →ₗ[ℂ] W') (l : Fin 2 → W)
    (y : ℚ × ℚ) : f (Lam l y) = Lam (fun k => f (l k)) y := by
  simp only [Lam, map_add, map_smul]

end Lam

/-! ### Restricted values of upper radical cocycles -/

/-- The restricted generator values `res ξ(e_k)`. -/
def genRes (ξ : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) : Fin 2 → Binary.HomogeneousPoly n :=
  fun k => res n (ξ (radicalLatticeGenerator k))

/-- **Restricted values of a radical cocycle are linear.** -/
theorem res_cocycle (ξ : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) (y : ℤ × ℤ) :
    res n (ξ (Multiplicative.ofAdd y)) = Lam (genRes n ξ) (icast y) := by
  let g : ℤ × ℤ →+ Binary.HomogeneousPoly n :=
    AddMonoidHom.mk' (fun y => res n (ξ (Multiplicative.ofAdd y))) (by
      intro a b
      have h := (groupCohomology.mem_cocycles₁_iff ξ).mp ξ.2 (Multiplicative.ofAdd a)
        (Multiplicative.ofAdd b)
      change res n (ξ (Multiplicative.ofAdd a * Multiplicative.ofAdd b)) = _
      have e := binaryHomogeneousRestrict_upperLattice n (Multiplicative.ofAdd a) (ξ (Multiplicative.ofAdd b))
      rw [h]
      exact (map_add (res n) (_ : HomogeneousPoly n) _).trans (by rw [e, add_comm]))
  have hy : y = y.1 • ((1, 0) : ℤ × ℤ) + y.2 • ((0, 1) : ℤ × ℤ) := by
    ext <;> simp
  change g y = _
  rw [hy, map_add, map_zsmul, map_zsmul]
  simp only [Lam, icast, genRes, radicalLatticeGenerator, radicalLatticeFirst, radicalLatticeSecond]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one, mul_zero,
    add_zero, zero_add, ite_eq_left, Fin.isValue, one_ne_zero, ite_false]
  rw [← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ]
  simp [g]

/-! ### The sum of the quotient vectors -/

theorem bmul_sum {ι : Type*} (s : Finset ι) (B : Matrix (Fin 2) (Fin 2) ℚ) (y : ι → ℚ × ℚ) :
    bmul B (∑ i ∈ s, y i) = ∑ i ∈ s, bmul B (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bmul_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bmul_add, ih]

variable (p : Nat.Primes)

/-- `∑_r q_r(x) = -p B_k⁻¹ x`. -/
theorem sum_quot (k : Option (Fin p.val)) (x : ℤ × ℤ) :
    ∑ r : Fin p.val, icast (quotVec p k (wint p k r - x)) =
      -((p.val : ℚ) • bmul ((BGL p k)⁻¹ : GL (Fin 2) ℚ).val (icast x)) := by
  apply bmul_injective (BGL p k)
  rw [bmul_sum, bmul_neg, bmul_smul, bmul_cancel_inv]
  have h : ∀ r : Fin p.val, bmul (BGL p k).val (icast (quotVec p k (wint p k r - x))) =
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

/-! ### The edge cocycle in Sol's coordinates -/

/-- The relative two-cocycles of the identity-plane stabilizer. -/
abbrev Rel := relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n)

theorem edgeFun_eq (c : Rel n) (m : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    edgeFun (ρn n) c.val m y = identityPlaneRadicalEdgeCycle n c m (Multiplicative.ofAdd y) := by
  rw [identityPlaneSplitEdgeCycle_apply, inl_eq, inl_eq, splitting_eq]
  rfl

theorem res_edgeFun (c : Rel n) (m : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    res n (edgeFun (ρn n) c.val m y) =
      Lam (genRes n (identityPlaneRadicalEdgeCycle n c m)) (icast y) := by
  rw [edgeFun_eq]
  exact res_cocycle n _ y

/-! ### Restricted values of the three edge terms -/

theorem Abin_mul (g h : GL (Fin 2) ℚ) (v : Binary.HomogeneousPoly n) :
    Abin n g (Abin n h v) = Abin n (g * h) v := by
  simp only [Abin, map_mul, Module.End.mul_apply]

theorem Abin_one (v : Binary.HomogeneousPoly n) : Abin n 1 v = v := by
  simp only [Abin, map_one, Module.End.one_apply]

theorem res_Pint (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (v : HomogeneousPoly n) :
    res n (ρn n (Pint b m) v) = Abin n (integralEmbed m) (res n v) := by
  rw [Pint, restrict_P, Units.val_one, Rat.cast_one, inv_one, one_smul]
  rfl

theorem res_sigma (v : HomogeneousPoly n) :
    res n (ρn n (sExpl p none) v) = ((epsP p : ℚ) : ℂ)⁻¹ • res n v := by
  rw [sExpl, restrict_P, Abin_one]
  rfl

theorem res_sExpl (k : Option (Fin p.val)) (r : Fin p.val) (v : HomogeneousPoly n) :
    res n (ρn n (sExpl p (some (k, r))) v) = Abin n (BGL p k) (res n v) := by
  rw [sExpl, restrict_P, Units.val_one, Rat.cast_one, inv_one, one_smul]

variable (c : Rel n)

/-- The restricted generator values of the edge at `μ`. -/
abbrev lam (μ : GL (Fin 2) ℤ) : Fin 2 → Binary.HomogeneousPoly n :=
  genRes n (identityPlaneRadicalEdgeCycle n c μ)

theorem res_term_sigma (m : GL (Fin 2) ℤ) (b : ℤ × ℤ) :
    res n (R (ρn n) (sExpl p none) (edgeFun (ρn n) c.val m (epsP p • b))) =
      Lam (lam n c m) (icast b) := by
  have h := res_sigma n p (edgeFun (ρn n) c.val m (epsP p • b))
  refine h.trans ?_
  rw [res_edgeFun, ← icast_smul_int, Lam_smul, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast epsP_ne_zero p

theorem res_term_coboundary (b : ℤ × ℤ) (v : Aρ (ρn n)) :
    res n (R (ρn n) (Pint b 1) v - v) = 0 := by
  have h : res n (R (ρn n) (Pint b 1) v - v) = res n (ρn n (Pint b 1) v) - res n v :=
    map_sub (res n) (ρn n (Pint b 1) v) (v : HomogeneousPoly n)
  rw [h]
  exact sub_eq_zero.mpr ((res_Pint n b 1 v).trans (by rw [map_one, Abin_one]))

theorem res_conj (ν μ : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    res n (conjFun (ρn n) ν (edgeFun (ρn n) c.val μ) y) =
      Abin n (integralEmbed ν) (Lam (lam n c μ) (bmul ((integralEmbed ν)⁻¹ : GL (Fin 2) ℚ).val (icast y))) := by
  unfold conjFun
  refine (res_Pint n 0 ν _).trans ?_
  rw [res_edgeFun, icast_imul, integralEmbed_inv]

theorem res_kappa (k : Option (Fin p.val)) (ν μ : GL (Fin 2) ℤ) (x : ℤ × ℤ) :
    res n (kappaFun p (ρn n) k (conjFun (ρn n) ν (edgeFun (ρn n) c.val μ)) x) =
      ((p.val : ℚ) : ℂ) • Abin n (BGL p k) (Abin n (integralEmbed ν) (Lam (lam n c μ)
        (bmul ((integralEmbed ν)⁻¹ : GL (Fin 2) ℚ).val
          (bmul ((BGL p k)⁻¹ : GL (Fin 2) ℚ).val (icast x))))) := by
  unfold kappaFun
  have hsum := map_sum (res n) (fun r : Fin p.val => (R (ρn n) (sExpl p (some (k, r)))
    (conjFun (ρn n) ν (edgeFun (ρn n) c.val μ) (-quotVec p k (wint p k r - x))) : HomogeneousPoly n))
    Finset.univ
  refine hsum.trans ?_
  have hterm : ∀ r : Fin p.val, res n (R (ρn n) (sExpl p (some (k, r)))
      (conjFun (ρn n) ν (edgeFun (ρn n) c.val μ) (-quotVec p k (wint p k r - x)))) =
      Abin n (BGL p k) (Abin n (integralEmbed ν) (Lam (lam n c μ)
        (bmul ((integralEmbed ν)⁻¹ : GL (Fin 2) ℚ).val (-icast (quotVec p k (wint p k r - x)))))) := by
    intro r
    refine (res_sExpl n p k r _).trans ?_
    rw [res_conj, icast_neg]
  refine (Finset.sum_congr rfl (fun r _ => hterm r)).trans ?_
  rw [← map_sum, ← map_sum, ← Lam_sum, ← bmul_sum, Finset.sum_neg_distrib, sum_quot, neg_neg,
    bmul_smul, Lam_smul, map_smul, map_smul]

theorem integral_relation (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    integralEmbed m * BGL p (arithmeticNext p m j) * integralEmbed (arithmeticDelta p m j)⁻¹ = BGL p j := by
  rw [integralEmbed_inv, ← BGL_mul_delta, mul_inv_cancel_right]

theorem res_term_kappa (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (b : ℤ × ℤ) :
    res n (R (ρn n) (Pint 0 m) (kappaFun p (ρn n) (arithmeticNext p m j)
        (conjFun (ρn n) (arithmeticDelta p m j)⁻¹ (edgeFun (ρn n) c.val (arithmeticDelta p m j)))
        (imul (m⁻¹ : GL (Fin 2) ℤ).val b))) =
      ((p.val : ℚ) : ℂ) • Abin n (BGL p j) (Lam (lam n c (arithmeticDelta p m j))
        (bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast b))) := by
  refine (res_Pint n 0 m _).trans ?_
  rw [res_kappa, map_smul, Abin_mul, Abin_mul, integral_relation, icast_imul, integralEmbed_inv,
    ← bmul_mul, ← bmul_mul, ← Units.val_mul, ← Units.val_mul]
  congr 4
  rw [← integral_relation p m j]
  simp only [_root_.mul_inv_rev, mul_assoc, map_inv, inv_inv]

/-! ### The restricted edge of the Hecke image -/

/-- The restriction on the carrier of the coefficient representation of `Λ₀`. -/
abbrev resA : Aρ (ρn n) →ₗ[ℂ] Binary.HomogeneousPoly n := res n

theorem rel_Uel (a b : ℤ × ℤ) : c.val (Uel a, Uel b) = 0 := by
  have h := c.2 (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
  rwa [inl_eq, inl_eq] at h

theorem res_edge_hecke (m : GL (Fin 2) ℤ) (b : ℤ × ℤ) :
    resA n (edgeFun (ρn n) (heckeTwo p (ρn n) c.val) m b) =
      Lam (lam n c m) (icast b) + ∑ j : Option (Fin p.val), ((p.val : ℚ) : ℂ) •
        Abin n (BGL p j) (Lam (lam n c (arithmeticDelta p m j))
          (bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast b))) := by
  rw [edge_heckeTwo p (ρn n) c.val (rel_Uel n c) m b, map_add, map_add, map_sum]
  have h0 : resA n (R (ρn n) (sExpl p none) (edgeFun (ρn n) c.val m (epsP p • b))) =
      Lam (lam n c m) (icast b) := res_term_sigma n p c m b
  refine (congrArg₂ (· + ·) (congrArg₂ (· + ·) h0
    (Finset.sum_congr rfl (fun j _ => res_term_kappa n p c m j b))) (res_term_coboundary n b _)).trans ?_
  exact add_zero _

/-- The Hecke image as a relative cocycle. -/
def heckeRel : Rel n :=
  ⟨heckeTwo p (ρn n) c.val, by
    intro u v
    rw [inl_eq, inl_eq]
    exact heckeTwo_relative p (ρn n) c.val (rel_Uel n c) _ _⟩

theorem lam_generator (μ : GL (Fin 2) ℤ) (k : Fin 2) :
    lam n c μ k = res n (edgeFun (ρn n) c.val μ (if k = 0 then (1, 0) else (0, 1))) := by
  rw [edgeFun_eq]
  unfold lam genRes radicalLatticeGenerator radicalLatticeFirst radicalLatticeSecond
  split_ifs <;> rfl

theorem Lam_e0 {W : Type*} [AddCommGroup W] [Module ℂ W] (l : Fin 2 → W) :
    Lam l (icast (1, 0)) = l 0 := by simp [Lam, icast]

theorem Lam_e1 {W : Type*} [AddCommGroup W] [Module ℂ W] (l : Fin 2 → W) :
    Lam l (icast (0, 1)) = l 1 := by simp [Lam, icast]

theorem Lam_bmul_e {W : Type*} [AddCommGroup W] [Module ℂ W] (l : Fin 2 → W)
    (B : Matrix (Fin 2) (Fin 2) ℚ) (k : Fin 2) :
    Lam l (bmul B (icast (if k = 0 then (1, 0) else (0, 1)))) =
      ((B 0 k : ℚ) : ℂ) • l 0 + ((B 1 k : ℚ) : ℂ) • l 1 := by
  fin_cases k <;> simp [Lam, bmul, icast]

/-- **The restricted generator values of the Hecke image.** -/
theorem lam_hecke (m : GL (Fin 2) ℤ) (k : Fin 2) :
    lam n (heckeRel n p c) m k = lam n c m k + ∑ j : Option (Fin p.val), ((p.val : ℚ) : ℂ) •
      Abin n (BGL p j) ((((BGL p j)⁻¹ : GL (Fin 2) ℚ).val 0 k : ℂ) • lam n c (arithmeticDelta p m j) 0 +
        (((BGL p j)⁻¹ : GL (Fin 2) ℚ).val 1 k : ℂ) • lam n c (arithmeticDelta p m j) 1) := by
  rw [lam_generator]
  refine (res_edge_hecke n p c m _).trans ?_
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl (fun j _ => by rw [Lam_bmul_e]))
  fin_cases k
  · exact Lam_e0 _
  · exact Lam_e1 _

/-! ### The binary coordinate -/

theorem binaryEdge_val (μ : GL (Fin 2) ℤ) :
    (identityPlaneBinaryEdgeCycle n c μ).val =
      (n + 1 : ℂ)⁻¹ • (X 0 * (lam n c μ 0).val + X 1 * (lam n c μ 1).val) := by
  rw [identityPlaneBinaryEdgeCycle_apply, upperRadicalCocycleCoordinate_value]
  rfl

theorem cx2_inv_val (B : GL (Fin 2) ℚ) (i j : Fin 2) :
    ((cx2 B)⁻¹ : Binary.GL2).val i j = ((((B⁻¹ : GL (Fin 2) ℚ).val i j : ℚ)) : ℂ) := by
  rw [← map_inv]
  exact eq_ratCast (algebraMap ℚ ℂ) _

/-- **The binary action of `B` on a radical coordinate.** -/
theorem action_coord (B : GL (Fin 2) ℚ) (l : Fin 2 → Binary.HomogeneousPoly n) :
    (n + 1 : ℂ)⁻¹ • (X 0 * (Abin n B ((((B⁻¹ : GL (Fin 2) ℚ).val 0 0 : ℚ) : ℂ) • l 0 +
          (((B⁻¹ : GL (Fin 2) ℚ).val 1 0 : ℚ) : ℂ) • l 1)).val +
        X 1 * (Abin n B ((((B⁻¹ : GL (Fin 2) ℚ).val 0 1 : ℚ) : ℂ) • l 0 +
          (((B⁻¹ : GL (Fin 2) ℚ).val 1 1 : ℚ) : ℂ) • l 1)).val) =
      Binary.action (-1) (cx2 B) ((n + 1 : ℂ)⁻¹ • (X 0 * (l 0).val + X 1 * (l 1).val)) := by
  rw [map_smul, ← binaryPairContraction_equivariant (-1) (cx2 B) (fun i => (l i).val)]
  simp only [cx2_inv_val, map_add, map_smul, Binary.homogeneousAction_coe, Submodule.coe_add,
    Submodule.coe_smul]

/-- The underlying polynomial of a binary coefficient. -/
abbrev polyVal : arithmeticBinaryRep (n + 1) (-1) →ₗ[ℂ] Binary.Poly := (Binary.HomogeneousPoly (n + 1)).subtype

/-- **Cocycle-level Hecke formula for the identity-plane binary edge.** For a relative two-cocycle
`c`, the binary edge cocycle of its local Hecke image is
`E(Tc)(m) = E(c)(m) + p ∑_j A_{B_j} E(c)(μ_j)`, where `B_j a_j = p` and `a_j m = μ_j a_{k_j}`. -/
theorem binaryEdge_hecke (m : GL (Fin 2) ℤ) :
    identityPlaneBinaryEdgeCycle n (heckeRel n p c) m =
      identityPlaneBinaryEdgeCycle n c m + ((p.val : ℚ) : ℂ) • ∑ j : Option (Fin p.val),
        LevelOneHeckeH1.rationalRho (n + 1) (-1) (BGL p j)
          (identityPlaneBinaryEdgeCycle n c (arithmeticDelta p m j)) := by
  apply (show Function.Injective (polyVal n) from Subtype.val_injective)
  rw [map_add, map_smul, map_sum]
  change (identityPlaneBinaryEdgeCycle n (heckeRel n p c) m).val =
    (identityPlaneBinaryEdgeCycle n c m).val + ((p.val : ℚ) : ℂ) • ∑ j : Option (Fin p.val),
      Binary.action (-1) (cx2 (BGL p j)) (identityPlaneBinaryEdgeCycle n c (arithmeticDelta p m j)).val
  rw [binaryEdge_val, binaryEdge_val, lam_hecke, lam_hecke]
  simp only [binaryEdge_val, ← action_coord]
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, mul_add, Finset.mul_sum,
    smul_add, Finset.smul_sum, mul_smul_comm, smul_smul, Finset.sum_add_distrib]
  simp only [mul_comm ((n : ℂ) + 1)⁻¹ _]
  abel

end TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
