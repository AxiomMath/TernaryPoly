module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneCosetData
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Cosets

@[expose] public section


/-!
# The good-plane `T_p`-cosets: lattice arithmetic and Levi transitions

For a prime `p ≠ 3` the matrices `B_j` of `GoodPlaneCosetData` satisfy
`B_j⁻¹ = p⁻¹ α'_j` with `α'_j = δ⁻¹ α_j δ` the `κ`-conjugate of the `Γ₁'(3)`-Hecke representative
`α_j` (`BG_inv_val`, `BG_inv_eq`). The Levi transitions of `LevelThreeCosets` therefore transport to
`B_j⁻¹ κ(m) = κ(δ) B_k⁻¹` with `δ = levelDelta m j`, `k = levelNext m j` (`levi_transition`).
The representatives `w_{j,r}` split `ℤ² / B_j ℤ²` (`rep_spec`, `rep_unique`, `eq_repIdx`), and
distinct `j` give distinct lattices (`BG_unique`). This is the exact good-plane analogue of the
first half of `IdentityPlaneCosets`, with `Λ₀ = ℤ² ⋊ GL₂(ℤ)` replaced by the good-plane
stabilizer `ΛG` and the Levi group `GL₂(ℤ)` by `Γ₁'(3)` embedded through `κ`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneCosets

open TernaryPeriodPolynomials.Spectral
open PlaneCoordinates
open LevelOneCosets (integralEmbed integralEmbed_val integralEmbed_injective)
open IdentityPlaneCosets (icast icast_add icast_sub icast_neg icast_injective imul bmul_icast
  bmul_integralEmbed isInt_icast isInt_sub IsInt toNat_emod p_ne_zero)
open GoodPlaneCosetData GoodPlaneFrame GoodPlaneModel
open LevelThreeCosets (signP signP_mul_self heckeRep heckeRep_val N N_none N_some levelNext
  levelDelta levelDelta_spec levelCosets embed_eq_iff)

variable (p : Nat.Primes)

/-! ### The Hecke matrices in `Λ`-coordinates -/

theorem N_dvd (j : Option (Fin p.val)) : (3 : ℤ) ∣ N p j 1 0 := by
  cases j with
  | none => rw [N_none]; simp
  | some i => rw [N_some]; simp

/-- `α'_j = δ⁻¹ α_j δ`, so that `B_j⁻¹ = p⁻¹ α'_j`. -/
def alphaK (j : Option (Fin p.val)) : GL (Fin 2) ℚ := del⁻¹ * heckeRep p j * del

theorem alphaK_val (j : Option (Fin p.val)) :
    (alphaK p j : Matrix (Fin 2) (Fin 2) ℚ) = (kapMat (N p j)).map (Int.castRingHom ℚ) := by
  rw [kapMat_map (N_dvd p j), alphaK, Units.val_mul, Units.val_mul, heckeRep_val]

/-- The scalar matrix `p · 1`. -/
abbrev sc : GL (Fin 2) ℚ :=
  GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p.val : ℚ) (p_ne_zero p))

theorem sc_comm (g : GL (Fin 2) ℚ) : sc p * g = g * sc p :=
  GeneralLinearGroup.scalar_commute _ g

theorem sc_inv_comm (g : GL (Fin 2) ℚ) : (sc p)⁻¹ * g = g * (sc p)⁻¹ := by
  have h : Commute (sc p) g := sc_comm p g
  exact h.inv_left.eq

/-- **`B_j⁻¹ = p⁻¹ α'_j`** as rational matrices. -/
theorem BG_inv_val (j : Option (Fin p.val)) :
    ((BG p j)⁻¹ : GL (Fin 2) ℚ).val = (p.val : ℚ)⁻¹ • (alphaK p j).val := by
  have hp := p_ne_zero p
  have hPP : (p.val : ℚ) * (p.val : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hp
  have he : ((signP p : ℤ) : ℚ) * ((signP p : ℤ) : ℚ) = 1 := by
    exact_mod_cast signP_mul_self p
  have h : (BG p j).val * ((p.val : ℚ)⁻¹ • (alphaK p j).val) = 1 := by
    rw [BG_val, alphaK_val]
    cases j with
    | none =>
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Bmat, kapMat, N_none, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first
        | linear_combination ((p.val : ℚ) * (p.val : ℚ)⁻¹) * he + hPP
    | some i =>
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Bmat, kapMat, N_some, Matrix.mul_apply, Fin.sum_univ_two]
      first
      | linear_combination hPP
      | (field_simp; ring)
  calc ((BG p j)⁻¹ : GL (Fin 2) ℚ).val
      = ((BG p j)⁻¹ : GL (Fin 2) ℚ).val *
          ((BG p j).val * ((p.val : ℚ)⁻¹ • (alphaK p j).val)) := by rw [h, mul_one]
    _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- `B_j⁻¹ = p⁻¹ α'_j` in `GL₂(ℚ)`. -/
theorem BG_inv_eq (j : Option (Fin p.val)) :
    (BG p j)⁻¹ = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p.val : ℚ) (p_ne_zero p))⁻¹ *
      alphaK p j := by
  apply Units.ext
  rw [BG_inv_val, Units.val_mul]
  ext a b
  simp [GeneralLinearGroup.scalar, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply]

theorem BG_inv_eq_sc (j : Option (Fin p.val)) : (BG p j)⁻¹ = (sc p)⁻¹ * alphaK p j := by
  rw [BG_inv_eq, sc, map_inv]

/-! ### The Levi transition -/

theorem alphaK_mul_Em (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    alphaK p j * Em m = Em (levelDelta p hp3 m j) * alphaK p (levelNext p hp3 m j) := by
  have hδ : integralEmbed (levelDelta p hp3 m j).val =
      heckeRep p j * integralEmbed m.val * (heckeRep p (levelNext p hp3 m j))⁻¹ :=
    (embed_eq_iff p _ m.val j _).mpr (levelDelta_spec p hp3 m j)
  unfold alphaK
  rw [Em_apply, Em_apply, integralEmbed_kap, integralEmbed_kap, hδ]
  group

/-- **The Levi transition at the good plane**: `B_j⁻¹ κ(m) = κ(δ) B_k⁻¹`. -/
theorem levi_transition (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    (BG p j)⁻¹ * Em m = Em (levelDelta p hp3 m j) * (BG p (levelNext p hp3 m j))⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, BG_inv_val, BG_inv_val, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  have h := congrArg Units.val (alphaK_mul_Em p hp3 m j)
  rwa [Units.val_mul, Units.val_mul] at h

theorem levi_transition' (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    (BG p j)⁻¹ = Em (levelDelta p hp3 m j) * (BG p (levelNext p hp3 m j))⁻¹ * (Em m)⁻¹ := by
  rw [← levi_transition p hp3, mul_inv_cancel_right]

/-- `B_j κ(δ) = κ(m) B_k`. -/
theorem BG_mul_delta (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    BG p j * Em (levelDelta p hp3 m j) = Em m * BG p (levelNext p hp3 m j) := by
  have h := levi_transition p hp3 m j
  rw [eq_mul_inv_iff_mul_eq] at h
  rw [← h]
  group

theorem bmul_BG_delta (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val))
    (y : ℚ × ℚ) :
    bmul (BG p j).val (bmul (Em (levelDelta p hp3 m j)).val y) =
      bmul (Em m).val (bmul (BG p (levelNext p hp3 m j)).val y) := by
  rw [← bmul_mul, ← bmul_mul, ← Units.val_mul, ← Units.val_mul, BG_mul_delta p hp3]

theorem trans_levi (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    (BG p j)⁻¹ * (Em m * BG p (levelNext p hp3 m j)) = Em (levelDelta p hp3 m j) := by
  rw [← mul_assoc, levi_transition p hp3, mul_assoc, inv_mul_cancel, mul_one]

/-! ### Integral vectors under the Levi embedding -/

theorem Em_inv (m : binaryArithmeticLevel) : Em (m⁻¹) = (Em m)⁻¹ := map_inv Em m

theorem bmul_Em (m : binaryArithmeticLevel) (b : ℤ × ℤ) :
    bmul (Em m).val (icast b) = icast (imul (kap m).val b) :=
  bmul_integralEmbed (kap m) b

theorem icast_imul_kap (m : binaryArithmeticLevel) (b : ℤ × ℤ) :
    icast (imul (kap m).val b) = bmul (Em m).val (icast b) :=
  (bmul_Em m b).symm

theorem Em_inv_val (m : binaryArithmeticLevel) :
    ((Em m)⁻¹ : GL (Fin 2) ℚ).val =
      ((kap (m⁻¹) : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  rw [← Em_inv]
  exact integralEmbed_val (kap (m⁻¹))

theorem bmul_Em_inv (m : binaryArithmeticLevel) (b : ℤ × ℤ) :
    bmul ((Em m)⁻¹ : GL (Fin 2) ℚ).val (icast b) = icast (imul (kap (m⁻¹)).val b) := by
  rw [Em_inv_val, bmul_icast]

theorem imul_kap_cancel (m : binaryArithmeticLevel) (y : ℤ × ℤ) :
    imul (kap m).val (imul (kap (m⁻¹)).val y) = y := by
  rw [map_inv]
  exact IdentityPlaneCosets.imul_cancel_inv' (kap m) y

theorem imul_kap_cancel' (m : binaryArithmeticLevel) (y : ℤ × ℤ) :
    imul (kap (m⁻¹)).val (imul (kap m).val y) = y := by
  rw [map_inv]
  exact IdentityPlaneCosets.imul_inv_cancel' (kap m) y

/-! ### Coset representatives of `ℤ² / B_j ℤ²` -/

theorem bmul_BG_none_icast (q : ℤ × ℤ) :
    bmul (BG p none).val (icast q) =
      icast ((signP p : ℤ) * q.1, (signP p : ℤ) * p.val * q.2) := by
  refine Prod.ext ?_ ?_ <;> simp [bmul, BG_val, Bmat, icast]

theorem bmul_BG_some_icast (i : Fin p.val) (q : ℤ × ℤ) :
    bmul (BG p (some i)).val (icast q) =
      icast ((p.val : ℤ) * q.1 - 3 * i.val * q.2, q.2) := by
  refine Prod.ext ?_ ?_ <;> simp [bmul, BG_val, Bmat, icast]
  ring

/-- **`x = w_{j, rep x} + B_j q`** with `q = quotVec x`. -/
theorem rep_spec' (k : Option (Fin p.val)) (x : ℤ × ℤ) :
    icast x = icast (wint p k (repIdx p k x)) +
      bmul (BG p k).val (icast (quotVec p k x)) := by
  have he : (signP p : ℤ) * (signP p : ℤ) = 1 := signP_mul_self p
  cases k with
  | none =>
    have hr : (((repIdx p none x).val : ℕ) : ℤ) = x.2 % (p.val : ℤ) := toNat_emod p x.2
    have hdiv := Int.emod_add_mul_ediv x.2 (p.val : ℤ)
    rw [bmul_BG_none_icast, ← icast_add]
    refine congrArg icast ?_
    refine Prod.ext ?_ ?_
    · simp only [wint, quotVec, Prod.fst_add]
      linear_combination (-x.1) * he
    · simp only [wint, quotVec, Prod.snd_add]
      linear_combination (-1 : ℤ) * hr + (-1 : ℤ) * hdiv +
        (-((p.val : ℤ) * (x.2 / (p.val : ℤ)))) * he
  | some i =>
    have hr : (((repIdx p (some i) x).val : ℕ) : ℤ) =
        (x.1 + 3 * i.val * x.2) % (p.val : ℤ) := toNat_emod p (x.1 + 3 * i.val * x.2)
    have hdiv := Int.emod_add_mul_ediv (x.1 + 3 * i.val * x.2) (p.val : ℤ)
    rw [bmul_BG_some_icast, ← icast_add]
    refine congrArg icast ?_
    refine Prod.ext ?_ ?_
    · simp only [wint, quotVec, Prod.fst_add]
      linear_combination (-1 : ℤ) * hr + (-1 : ℤ) * hdiv
    · simp only [wint, quotVec, Prod.snd_add]
      ring

theorem bmul_BG_cancel_inv (j : Option (Fin p.val)) (x : ℚ × ℚ) :
    bmul (BG p j).val (bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val x) = x :=
  bmul_cancel_inv (BG p j) x

/-- **`b ≡ w_{j, rep b}` modulo `B_j ℤ²`.** -/
theorem rep_spec (j : Option (Fin p.val)) (b : ℤ × ℤ) :
    bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val (icast (b - wint p j (repIdx p j b))) =
      icast (quotVec p j b) := by
  have h : icast (b - wint p j (repIdx p j b)) = bmul (BG p j).val (icast (quotVec p j b)) := by
    rw [icast_sub, rep_spec' p j b]
    abel
  rw [h, bmul_inv_cancel]

/-- Distinct representatives are incongruent. -/
theorem rep_unique (j : Option (Fin p.val)) (r r' : Fin p.val)
    (h : IsInt (bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val (icast (wint p j r - wint p j r')))) :
    r = r' := by
  obtain ⟨c, hc⟩ := h
  have hc' : bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val (icast (wint p j r - wint p j r')) =
      icast c := hc
  have hx : icast (wint p j r - wint p j r') = bmul (BG p j).val (icast c) := by
    rw [← hc', bmul_cancel_inv]
  have key : ∃ z : ℤ, ((r.val : ℤ) - r'.val) = p.val * z := by
    cases j with
    | none =>
      rw [bmul_BG_none_icast] at hx
      have h2 := congrArg Prod.snd (icast_injective hx)
      refine ⟨(signP p : ℤ) * c.2, ?_⟩
      simp only [wint, Prod.snd_sub] at h2
      linear_combination h2
    | some i =>
      rw [bmul_BG_some_icast] at hx
      have h1 := congrArg Prod.fst (icast_injective hx)
      have h2 := congrArg Prod.snd (icast_injective hx)
      refine ⟨c.1, ?_⟩
      simp only [wint, Prod.fst_sub, Prod.snd_sub] at h1 h2
      linear_combination h1 + (3 * (i.val : ℤ)) * h2
  obtain ⟨z, hz⟩ := key
  have hr := r.isLt
  have hr' := r'.isLt
  have hzero := Int.eq_zero_of_abs_lt_dvd (⟨z, hz⟩ : (p.val : ℤ) ∣ (r.val : ℤ) - r'.val)
    (by rw [abs_lt]; constructor <;> omega)
  apply Fin.ext
  omega

/-- If `b ≡ w_{j,r}` then `r` is the representative index of `b`. -/
theorem eq_repIdx (j : Option (Fin p.val)) (r : Fin p.val) (b : ℤ × ℤ)
    (h : IsInt (bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val (icast (b - wint p j r)))) :
    r = repIdx p j b := by
  apply rep_unique p j
  have h2 := rep_spec p j b
  have : icast (wint p j r - wint p j (repIdx p j b)) =
      icast (b - wint p j (repIdx p j b)) - icast (b - wint p j r) := by
    simp only [icast_sub]; abel
  rw [this, bmul_sub, h2]
  exact isInt_sub (isInt_icast _) h

/-- Distinct indices give distinct lattices `B_j ℤ²`. -/
theorem BG_unique (hp3 : p.val ≠ 3) {j j' : Option (Fin p.val)} {μ : binaryArithmeticLevel}
    (h : (BG p j)⁻¹ * BG p j' = Em μ) : j = j' := by
  apply (levelCosets p hp3).disjoint j j' μ
  have e1 := BG_inv_eq_sc p j
  have e2 : BG p j' = (alphaK p j')⁻¹ * sc p := by
    rw [← inv_inv (BG p j'), BG_inv_eq_sc, _root_.mul_inv_rev, inv_inv]
  have hX : (BG p j)⁻¹ * BG p j' = alphaK p j * (alphaK p j')⁻¹ := by
    rw [e1, e2]
    calc (sc p)⁻¹ * alphaK p j * ((alphaK p j')⁻¹ * sc p)
        = (alphaK p j * (sc p)⁻¹) * (sc p * (alphaK p j')⁻¹) := by
          rw [sc_inv_comm p (alphaK p j), sc_comm p ((alphaK p j')⁻¹)]
      _ = alphaK p j * (alphaK p j')⁻¹ := by group
  have h2 : del⁻¹ * (heckeRep p j * (heckeRep p j')⁻¹) * del =
      del⁻¹ * integralEmbed μ.val * del := by
    calc del⁻¹ * (heckeRep p j * (heckeRep p j')⁻¹) * del
        = alphaK p j * (alphaK p j')⁻¹ := by unfold alphaK; group
      _ = Em μ := hX.symm.trans h
      _ = del⁻¹ * integralEmbed μ.val * del := (Em_apply μ).trans (integralEmbed_kap μ)
  exact (mul_left_cancel (mul_right_cancel h2)).symm

theorem BG_injective (hp3 : p.val ≠ 3) {j j' : Option (Fin p.val)} (h : BG p j = BG p j') :
    j = j' :=
  BG_unique p hp3 (μ := 1) (by rw [h, inv_mul_cancel, map_one])

end TernaryPeriodPolynomials.LevelThree.GoodPlaneCosets
