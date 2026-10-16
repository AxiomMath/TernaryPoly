module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCosets

@[expose] public section


/-!
# Identities between the identity-plane transitions

Group and vector identities among the explicit transitions of the identity-plane cosets
(`IdentityPlaneCosets`), used to compute the local Hecke operator in edge coordinates:
the product formulas `s_{j,r} u(-μ q₁) = L(m) s_{k,r₁} L(μ⁻¹)` (`levi_product`) and
`s_{j,r} u(-q₃) = u(b) s_{j,r₃}` (`radical_product`), the cancellation of the mixed terms
(`mixed_cancel`), and the bijectivity of the induced maps on representatives (`levi_bijective`,
`radical_bijective`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.Spectral.IdentityPlaneTransitions

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets

variable (p : Nat.Primes)

/-! ### Transitions under radical elements -/

theorem nextIdx_one (x : ℤ × ℤ) (k : Option (Fin p.val)) (r : Fin p.val) :
    nextIdx p x 1 k r = (k, repIdx p k (wint p k r - x)) := by
  simp only [nextIdx, arithmeticNext_one, inv_one, Units.val_one, imul_one]

theorem transVec_one (x : ℤ × ℤ) (k : Option (Fin p.val)) (r : Fin p.val) :
    transVec p x 1 k r = quotVec p k (wint p k r - x) := by
  simp only [transVec, arithmeticNext_one, inv_one, Units.val_one, imul_one]

theorem nextIdx_zero (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    nextIdx p 0 m j r =
      (arithmeticNext p m j, repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) := by
  simp only [nextIdx, sub_zero]

theorem transVec_zero (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    transVec p 0 m j r =
      quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r)) := by
  simp only [transVec, sub_zero]

/-! ### Product formulas -/

/-- `s_{j,r} u(-μ q₁) = L(m) s_{k,r₁} L(μ⁻¹)`. -/
theorem levi_product (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    sExpl p (some (j, r)) *
        Pint (-imul (arithmeticDelta p m j).val (transVec p 0 m j r)) 1 =
      Pint 0 m * sExpl p (some (nextIdx p 0 m j r)) * Pint 0 (arithmeticDelta p m j)⁻¹ := by
  have hspec := rep_spec' p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))
  have hx : icast (wint p j r) =
      bmul (integralEmbed m).val (icast (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) := by
    rw [← icast_imul, imul_cancel_inv']
  rw [nextIdx_zero, transVec_zero]
  simp only [sExpl, Pint_eq]
  rw [P_mul, P_mul, P_mul]
  congr 1
  · simp only [inv_one, Units.val_one, one_smul, mul_one, icast_zero, zero_add, Units.val_mul,
      bmul_zero, add_zero]
    rw [icast_neg, bmul_neg, icast_imul, bmul_BGL_delta, hx, hspec, bmul_add]
    abel
  · rw [map_one, mul_one, integralEmbed_inv, ← BGL_mul_delta, mul_inv_cancel_right]
  · simp

/-- `s_{j,r} u(-q₃) = u(b) s_{j,r₃}`. -/
theorem radical_product (b : ℤ × ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    sExpl p (some (j, r)) * Pint (-quotVec p j (wint p j r - b)) 1 =
      Pint b 1 * sExpl p (some (j, repIdx p j (wint p j r - b))) := by
  have hspec := rep_spec' p j (wint p j r - b)
  simp only [sExpl, Pint_eq]
  rw [P_mul, P_mul]
  congr 1
  · simp only [inv_one, Units.val_one, one_smul, map_one, bmul_one]
    rw [icast_neg, bmul_neg]
    rw [icast_sub] at hspec
    rw [show icast (wint p j r) = icast b + (icast (wint p j r) - icast b) by abel, hspec]
    abel
  all_goals simp

theorem bmul_conj_delta (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (y : ℚ × ℚ) :
    bmul ((BGL p (arithmeticNext p m j))⁻¹ : GL (Fin 2) ℚ).val
        (bmul ((integralEmbed m)⁻¹ : GL (Fin 2) ℚ).val (bmul (BGL p j).val y)) =
      bmul ((integralEmbed (arithmeticDelta p m j))⁻¹ : GL (Fin 2) ℚ).val y := by
  have h := BGL_mul_delta p m j
  have h' : ((BGL p (arithmeticNext p m j))⁻¹ * (integralEmbed m)⁻¹ * BGL p j) =
      (integralEmbed (arithmeticDelta p m j))⁻¹ := by
    rw [show BGL p j = integralEmbed m * BGL p (arithmeticNext p m j) *
      (integralEmbed (arithmeticDelta p m j))⁻¹ by rw [← h, mul_inv_cancel_right]]
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
theorem second_rep_eq (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    repIdx p (arithmeticNext p m j)
        (wint p (arithmeticNext p m j)
            (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
          imul (m⁻¹ : GL (Fin 2) ℤ).val b) =
      repIdx p (arithmeticNext p m j)
        (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j (repIdx p j (wint p j r - b)))) := by
  have h1 := rep_spec' p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))
  have h2 := rep_spec' p (arithmeticNext p m j)
    (wint p (arithmeticNext p m j)
      (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
        imul (m⁻¹ : GL (Fin 2) ℤ).val b)
  have h3 := rep_spec' p j (wint p j r - b)
  rw [icast_imul, integralEmbed_inv] at h1
  rw [icast_sub, icast_imul, integralEmbed_inv] at h2
  rw [icast_sub] at h3
  have key := second_aux (BGL p (arithmeticNext p m j)) (BGL p j) (integralEmbed m)
    (integralEmbed (arithmeticDelta p m j)) (BGL_mul_delta p m j) _ _ _ _ _ _ _ _ h1 h2 h3
  apply eq_repIdx p (arithmeticNext p m j)
  refine ⟨quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r)) +
      quotVec p (arithmeticNext p m j)
        (wint p (arithmeticNext p m j)
          (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
            imul (m⁻¹ : GL (Fin 2) ℤ).val b) -
      imul ((arithmeticDelta p m j)⁻¹ : GL (Fin 2) ℤ).val (quotVec p j (wint p j r - b)), ?_⟩
  change _ = icast _
  simp only [icast_sub, icast_add, icast_imul, integralEmbed_inv]
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

/-- **Cancellation of the mixed terms**: `μ (q₁ + q₂) = q₃ + μ q₄`. -/
theorem mixed_cancel (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    -imul (arithmeticDelta p m j).val
        (quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) +
      imul (arithmeticDelta p m j).val
        (-quotVec p (arithmeticNext p m j)
          (wint p (arithmeticNext p m j)
              (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
            imul (m⁻¹ : GL (Fin 2) ℤ).val b)) =
      -quotVec p j (wint p j r - b) +
        -imul (arithmeticDelta p m j).val
          (quotVec p (arithmeticNext p m j)
            (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j (repIdx p j (wint p j r - b))))) := by
  have h1 := rep_spec' p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))
  have h2 := rep_spec' p (arithmeticNext p m j)
    (wint p (arithmeticNext p m j)
      (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
        imul (m⁻¹ : GL (Fin 2) ℤ).val b)
  have h3 := rep_spec' p j (wint p j r - b)
  have h4 := rep_spec' p (arithmeticNext p m j)
    (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j (repIdx p j (wint p j r - b))))
  rw [icast_imul, integralEmbed_inv] at h1 h4
  rw [icast_sub, icast_imul, integralEmbed_inv] at h2
  rw [icast_sub] at h3
  have h24 : icast (wint p (arithmeticNext p m j) (repIdx p (arithmeticNext p m j)
      (wint p (arithmeticNext p m j)
          (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
        imul (m⁻¹ : GL (Fin 2) ℤ).val b))) =
      icast (wint p (arithmeticNext p m j) (repIdx p (arithmeticNext p m j)
        (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j (repIdx p j (wint p j r - b)))))) := by
    rw [second_rep_eq]
  have key := mixed_aux (BGL p (arithmeticNext p m j)) (BGL p j) (integralEmbed m)
    (integralEmbed (arithmeticDelta p m j)) (BGL_mul_delta p m j) _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h24
  apply icast_injective
  simp only [icast_add, icast_neg, icast_imul, bmul_neg]
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
      bmul (BGL p j).val (icast (quotVec p j (wint p j r - b))) -
        bmul (BGL p j).val (icast (quotVec p j (wint p j r' - b))) := by
    have e1 : icast (wint p j r) = icast b + (icast (wint p j r) - icast b) := by abel
    have e2 : icast (wint p j r') = icast b + (icast (wint p j r') - icast b) := by abel
    rw [e1, e2, h1, h2]
    abel
  rw [this, ← bmul_sub, bmul_inv_cancel]

theorem radical_bijective (b : ℤ × ℤ) (j : Option (Fin p.val)) :
    Function.Bijective fun r => repIdx p j (wint p j r - b) :=
  Finite.injective_iff_bijective.mp (radical_injective p b j)

theorem levi_injective (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    Function.Injective fun r =>
      repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r)) := by
  intro r r' h
  simp only at h
  apply rep_unique p j
  have h1 := rep_spec' p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))
  have h2 := rep_spec' p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r'))
  rw [h] at h1
  refine ⟨imul (arithmeticDelta p m j).val
    (quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r)) -
      quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r'))), ?_⟩
  change _ = icast _
  rw [icast_imul, icast_sub]
  have hdiff : icast (wint p j r) - icast (wint p j r') =
      bmul (integralEmbed m).val (bmul (BGL p (arithmeticNext p m j)).val
        (icast (quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
          icast (quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r'))))) := by
    have e : ∀ w : ℤ × ℤ, icast w =
        bmul (integralEmbed m).val (icast (imul (m⁻¹ : GL (Fin 2) ℤ).val w)) := by
      intro w
      rw [← icast_imul, imul_cancel_inv']
    rw [e (wint p j r), e (wint p j r'), h1, h2, ← bmul_sub, bmul_sub (BGL p _).val]
    congr 1
    abel
  rw [hdiff, ← bmul_BGL_delta, bmul_inv_cancel, icast_sub]

theorem levi_bijective (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    Function.Bijective fun r =>
      repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r)) :=
  Finite.injective_iff_bijective.mp (levi_injective p m j)

end TernaryPeriodPolynomials.Spectral.IdentityPlaneTransitions
