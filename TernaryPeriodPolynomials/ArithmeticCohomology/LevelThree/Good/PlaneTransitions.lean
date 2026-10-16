module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneCosets

@[expose] public section


/-!
# Identities between the good-plane transitions

Group and vector identities among the explicit transitions of the good-plane cosets
(`GoodPlaneCosets`), used to compute the local Hecke operator in edge coordinates: the product
formulas `s_{j,r} u(-κ(δ) q₁) = u(0)κ(m) s_{k,r₁} κ(δ⁻¹)` (`levi_product`) and
`s_{j,r} u(-q₃) = u(b) s_{j,r₃}` (`radical_product`), the cancellation of the mixed terms
(`mixed_cancel`), and the bijectivity of the induced maps on representatives (`levi_bijective`,
`radical_bijective`). This is the exact good-plane analogue of `IdentityPlaneTransitions`, with the
Levi group `GL₂(ℤ)` replaced by `Γ₁'(3)` embedded through `κ`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneTransitions

open TernaryPeriodPolynomials.Spectral
open PlaneCoordinates
open IdentityPlaneCosets (icast icast_zero icast_add icast_sub icast_neg icast_injective imul
  imul_one bmul_injective bmul_zero)
open GoodPlaneCosetData GoodPlaneFrame GoodPlaneModel GoodPlaneCosets
open LevelThreeCosets (heckeRep levelNext levelDelta levelCosets levelEmbed)

variable (p : Nat.Primes)

/-! ### Transitions under radical and Levi elements -/

theorem levelNext_one (hp3 : p.val ≠ 3) (j : Option (Fin p.val)) : levelNext p hp3 1 j = j := by
  symm
  apply (levelCosets p hp3).next_unique (h := 1)
  change levelEmbed 1 = heckeRep p j * levelEmbed 1 * (heckeRep p j)⁻¹
  simp

theorem nextIdx_one (hp3 : p.val ≠ 3) (x : ℤ × ℤ) (k : Option (Fin p.val)) (r : Fin p.val) :
    nextIdx p hp3 x 1 k r = (k, repIdx p k (wint p k r - x)) := by
  simp only [nextIdx, levelNext_one, inv_one, map_one, Units.val_one, imul_one]

theorem transVec_one (hp3 : p.val ≠ 3) (x : ℤ × ℤ) (k : Option (Fin p.val)) (r : Fin p.val) :
    transVec p hp3 x 1 k r = quotVec p k (wint p k r - x) := by
  simp only [transVec, levelNext_one, inv_one, map_one, Units.val_one, imul_one]

theorem nextIdx_zero (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val))
    (r : Fin p.val) :
    nextIdx p hp3 0 m j r =
      (levelNext p hp3 m j,
        repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))) := by
  simp only [nextIdx, sub_zero]

theorem transVec_zero (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val))
    (r : Fin p.val) :
    transVec p hp3 0 m j r =
      quotVec p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r)) := by
  simp only [transVec, sub_zero]

/-! ### Product formulas -/

/-- `s_{j,r} u(-κ(δ) q₁) = κ(m) s_{k,r₁} κ(δ⁻¹)`. -/
theorem levi_product (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val))
    (r : Fin p.val) :
    sExpl p (some (j, r)) *
        PK (-imul (kap (levelDelta p hp3 m j)).val (transVec p hp3 0 m j r)) 1 =
      PK 0 m * sExpl p (some (nextIdx p hp3 0 m j r)) * PK 0 (levelDelta p hp3 m j)⁻¹ := by
  have hspec := rep_spec' p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))
  have hx : icast (wint p j r) =
      bmul (Em m).val (icast (imul (kap (m⁻¹)).val (wint p j r))) := by
    rw [bmul_Em, imul_kap_cancel]
  rw [nextIdx_zero, transVec_zero]
  simp only [sExpl, PK]
  rw [P_mul, P_mul, P_mul]
  congr 1
  · simp only [inv_one, Units.val_one, one_smul, mul_one, icast_zero, zero_add, Units.val_mul,
      bmul_zero, add_zero]
    rw [icast_neg, bmul_neg, icast_imul_kap, bmul_BG_delta, hx, hspec, bmul_add]
    abel
  · rw [map_one, mul_one, map_inv, ← BG_mul_delta p hp3, mul_inv_cancel_right]
  · simp

/-- `s_{j,r} u(-q₃) = u(b) s_{j,r₃}`. -/
theorem radical_product (b : ℤ × ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    sExpl p (some (j, r)) * PK (-quotVec p j (wint p j r - b)) 1 =
      PK b 1 * sExpl p (some (j, repIdx p j (wint p j r - b))) := by
  have hspec := rep_spec' p j (wint p j r - b)
  simp only [sExpl, PK]
  rw [P_mul, P_mul]
  congr 1
  · simp only [inv_one, Units.val_one, one_smul, map_one, bmul_one]
    rw [icast_neg, bmul_neg]
    rw [icast_sub] at hspec
    rw [show icast (wint p j r) = icast b + (icast (wint p j r) - icast b) by abel, hspec]
    abel
  all_goals simp

theorem bmul_conj_delta (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val))
    (y : ℚ × ℚ) :
    bmul ((BG p (levelNext p hp3 m j))⁻¹ : GL (Fin 2) ℚ).val
        (bmul ((Em m)⁻¹ : GL (Fin 2) ℚ).val (bmul (BG p j).val y)) =
      bmul ((Em (levelDelta p hp3 m j))⁻¹ : GL (Fin 2) ℚ).val y := by
  have h := BG_mul_delta p hp3 m j
  have h' : ((BG p (levelNext p hp3 m j))⁻¹ * (Em m)⁻¹ * BG p j) =
      (Em (levelDelta p hp3 m j))⁻¹ := by
    rw [show BG p j = Em m * BG p (levelNext p hp3 m j) * (Em (levelDelta p hp3 m j))⁻¹ by
      rw [← h, mul_inv_cancel_right]]
    group
  rw [← bmul_mul, ← bmul_mul, ← Units.val_mul, ← Units.val_mul, h']

/-- Abstract form of the second-step comparison. -/
theorem second_aux (Bk Bj M μ : GL (Fin 2) ℚ) (hrel : Bj * μ = M * Bk)
    (wr b W1 W2 W3 Q1 Q2 Q3 : ℚ × ℚ)
    (h1 : bmul (M⁻¹ : GL (Fin 2) ℚ).val wr = W1 + bmul Bk.val Q1)
    (h2 : W1 - bmul (M⁻¹ : GL (Fin 2) ℚ).val b = W2 + bmul Bk.val Q2)
    (h3 : wr - b = W3 + bmul Bj.val Q3) :
    bmul (Bk⁻¹ : GL (Fin 2) ℚ).val (bmul (M⁻¹ : GL (Fin 2) ℚ).val W3 - W2) =
      Q1 + Q2 - bmul (μ⁻¹ : GL (Fin 2) ℚ).val Q3 := by
  have hW3 : W3 = wr - b - bmul Bj.val Q3 := by rw [h3]; abel
  have hW2 : W2 = W1 - bmul (M⁻¹ : GL (Fin 2) ℚ).val b - bmul Bk.val Q2 := by rw [h2]; abel
  have hconj : (Bk⁻¹ * M⁻¹ * Bj : GL (Fin 2) ℚ) = μ⁻¹ := by
    rw [show Bj = M * Bk * μ⁻¹ by rw [← hrel, mul_inv_cancel_right]]
    group
  have hc : bmul (Bk⁻¹ : GL (Fin 2) ℚ).val (bmul (M⁻¹ : GL (Fin 2) ℚ).val (bmul Bj.val Q3)) =
      bmul (μ⁻¹ : GL (Fin 2) ℚ).val Q3 := by
    rw [← bmul_mul, ← bmul_mul, ← Units.val_mul, ← Units.val_mul, hconj]
  rw [hW3, hW2]
  simp only [bmul_sub]
  rw [h1]
  simp only [bmul_add, bmul_inv_cancel, hc]
  abel

/-- The two second-step representatives agree: `r₂ = r₄`. -/
theorem second_rep_eq (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel)
    (j : Option (Fin p.val)) (r : Fin p.val) :
    repIdx p (levelNext p hp3 m j)
        (wint p (levelNext p hp3 m j)
            (repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))) -
          imul (kap (m⁻¹)).val b) =
      repIdx p (levelNext p hp3 m j)
        (imul (kap (m⁻¹)).val (wint p j (repIdx p j (wint p j r - b)))) := by
  have h1 := rep_spec' p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))
  have h2 := rep_spec' p (levelNext p hp3 m j)
    (wint p (levelNext p hp3 m j)
      (repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))) -
        imul (kap (m⁻¹)).val b)
  have h3 := rep_spec' p j (wint p j r - b)
  rw [icast_imul_kap, Em_inv] at h1
  rw [icast_sub, icast_imul_kap, Em_inv] at h2
  rw [icast_sub] at h3
  have key := second_aux (BG p (levelNext p hp3 m j)) (BG p j) (Em m)
    (Em (levelDelta p hp3 m j)) (BG_mul_delta p hp3 m j) _ _ _ _ _ _ _ _ h1 h2 h3
  apply eq_repIdx p (levelNext p hp3 m j)
  refine ⟨quotVec p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r)) +
      quotVec p (levelNext p hp3 m j)
        (wint p (levelNext p hp3 m j)
          (repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))) -
            imul (kap (m⁻¹)).val b) -
      imul (kap ((levelDelta p hp3 m j)⁻¹)).val (quotVec p j (wint p j r - b)), ?_⟩
  change _ = icast _
  simp only [icast_sub, icast_add, icast_imul_kap, Em_inv]
  exact key

/-- Abstract form of the cancellation of the mixed terms. -/
theorem mixed_aux (Bk Bj M μ : GL (Fin 2) ℚ) (hrel : Bj * μ = M * Bk)
    (wr b W1 W2 W3 W4 Q1 Q2 Q3 Q4 : ℚ × ℚ)
    (h1 : bmul (M⁻¹ : GL (Fin 2) ℚ).val wr = W1 + bmul Bk.val Q1)
    (h2 : W1 - bmul (M⁻¹ : GL (Fin 2) ℚ).val b = W2 + bmul Bk.val Q2)
    (h3 : wr - b = W3 + bmul Bj.val Q3)
    (h4 : bmul (M⁻¹ : GL (Fin 2) ℚ).val W3 = W4 + bmul Bk.val Q4) (h24 : W2 = W4) :
    bmul μ.val (Q1 + Q2) = Q3 + bmul μ.val Q4 := by
  apply bmul_injective Bj
  have hc : ∀ y, bmul Bj.val (bmul μ.val y) = bmul M.val (bmul Bk.val y) := by
    intro y
    rw [← bmul_mul, ← bmul_mul, ← Units.val_mul, ← Units.val_mul, hrel]
  have hBk1 : bmul Bk.val Q1 = bmul (M⁻¹ : GL (Fin 2) ℚ).val wr - W1 := by rw [h1]; abel
  have hBk2 : bmul Bk.val Q2 = W1 - bmul (M⁻¹ : GL (Fin 2) ℚ).val b - W2 := by rw [h2]; abel
  have hBk4 : bmul Bk.val Q4 = bmul (M⁻¹ : GL (Fin 2) ℚ).val W3 - W4 := by rw [h4]; abel
  have hBj3 : bmul Bj.val Q3 = wr - b - W3 := by rw [h3]; abel
  simp only [bmul_add, hc]
  rw [hBk1, hBk2, hBk4, hBj3, h24]
  simp only [bmul_sub, bmul_cancel_inv]
  abel

/-- **Cancellation of the mixed terms**: `κ(δ) (q₁ + q₂) = q₃ + κ(δ) q₄`. -/
theorem mixed_cancel (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel)
    (j : Option (Fin p.val)) (r : Fin p.val) :
    -imul (kap (levelDelta p hp3 m j)).val
        (quotVec p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))) +
      imul (kap (levelDelta p hp3 m j)).val
        (-quotVec p (levelNext p hp3 m j)
          (wint p (levelNext p hp3 m j)
              (repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))) -
            imul (kap (m⁻¹)).val b)) =
      -quotVec p j (wint p j r - b) +
        -imul (kap (levelDelta p hp3 m j)).val
          (quotVec p (levelNext p hp3 m j)
            (imul (kap (m⁻¹)).val (wint p j (repIdx p j (wint p j r - b))))) := by
  have h1 := rep_spec' p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))
  have h2 := rep_spec' p (levelNext p hp3 m j)
    (wint p (levelNext p hp3 m j)
      (repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))) -
        imul (kap (m⁻¹)).val b)
  have h3 := rep_spec' p j (wint p j r - b)
  have h4 := rep_spec' p (levelNext p hp3 m j)
    (imul (kap (m⁻¹)).val (wint p j (repIdx p j (wint p j r - b))))
  rw [icast_imul_kap, Em_inv] at h1 h4
  rw [icast_sub, icast_imul_kap, Em_inv] at h2
  rw [icast_sub] at h3
  have h24 : icast (wint p (levelNext p hp3 m j) (repIdx p (levelNext p hp3 m j)
      (wint p (levelNext p hp3 m j)
          (repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))) -
        imul (kap (m⁻¹)).val b))) =
      icast (wint p (levelNext p hp3 m j) (repIdx p (levelNext p hp3 m j)
        (imul (kap (m⁻¹)).val (wint p j (repIdx p j (wint p j r - b)))))) := by
    rw [second_rep_eq]
  have key := mixed_aux (BG p (levelNext p hp3 m j)) (BG p j) (Em m)
    (Em (levelDelta p hp3 m j)) (BG_mul_delta p hp3 m j) _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h24
  apply icast_injective
  simp only [icast_add, icast_neg, icast_imul_kap, bmul_neg]
  rw [← neg_add, ← neg_add, ← bmul_add, key]

/-! ### Bijectivity of the induced maps on representatives -/

theorem radical_injective (b : ℤ × ℤ) (j : Option (Fin p.val)) :
    Function.Injective fun r => repIdx p j (wint p j r - b) := by
  intro r r' h
  simp only at h
  apply rep_unique p j
  have h1 := rep_spec' p j (wint p j r - b)
  have h2 := rep_spec' p j (wint p j r' - b)
  rw [h] at h1
  refine ⟨quotVec p j (wint p j r - b) - quotVec p j (wint p j r' - b), ?_⟩
  change _ = icast _
  rw [icast_sub] at h1 h2 ⊢
  rw [icast_sub]
  have : icast (wint p j r) - icast (wint p j r') =
      bmul (BG p j).val (icast (quotVec p j (wint p j r - b))) -
        bmul (BG p j).val (icast (quotVec p j (wint p j r' - b))) := by
    have e1 : icast (wint p j r) = icast b + (icast (wint p j r) - icast b) := by abel
    have e2 : icast (wint p j r') = icast b + (icast (wint p j r') - icast b) := by abel
    rw [e1, e2, h1, h2]
    abel
  rw [this, ← bmul_sub, bmul_inv_cancel]

theorem radical_bijective (b : ℤ × ℤ) (j : Option (Fin p.val)) :
    Function.Bijective fun r => repIdx p j (wint p j r - b) :=
  Finite.injective_iff_bijective.mp (radical_injective p b j)

theorem levi_injective (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    Function.Injective fun r =>
      repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r)) := by
  intro r r' h
  simp only at h
  apply rep_unique p j
  have h1 := rep_spec' p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))
  have h2 := rep_spec' p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r'))
  rw [h] at h1
  refine ⟨imul (kap (levelDelta p hp3 m j)).val
    (quotVec p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r)) -
      quotVec p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r'))), ?_⟩
  change _ = icast _
  rw [icast_imul_kap, icast_sub]
  have hdiff : icast (wint p j r) - icast (wint p j r') =
      bmul (Em m).val (bmul (BG p (levelNext p hp3 m j)).val
        (icast (quotVec p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r))) -
          icast (quotVec p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r'))))) := by
    have e : ∀ w : ℤ × ℤ, icast w =
        bmul (Em m).val (icast (imul (kap (m⁻¹)).val w)) := by
      intro w
      rw [bmul_Em, imul_kap_cancel]
    rw [e (wint p j r), e (wint p j r'), h1, h2, ← bmul_sub, bmul_sub (BG p _).val]
    congr 1
    abel
  rw [hdiff, ← bmul_BG_delta p hp3, bmul_inv_cancel, icast_sub]

theorem levi_bijective (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    Function.Bijective fun r =>
      repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r)) :=
  Finite.injective_iff_bijective.mp (levi_injective p hp3 m j)

end TernaryPeriodPolynomials.LevelThree.GoodPlaneTransitions
