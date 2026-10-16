module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.FlagGeometry
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Basic

@[expose] public section


/-!
# L2/L3: the geometric level `K` versus the model level

The geometric side's level `K = TernaryPoly.ModThreeGoodAction.K` fixes the row `(1,1,1)` modulo three,
the model level `arithmeticLevel` fixes `(0,0,1)`. They are conjugate by the integral matrix `conjG`
with last row `(1,1,1)` (`mem_K_iff_conj`), `Γ(6)` is stable under this conjugation
(`conj_mem_principalSix_iff`), and goodness of a rational line or plane (an integral vector with nonzero
coordinate sum mod 3) is goodness of the model flag after conjugation (`good_iff_goodFlag`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPoly.ModThreeGoodAction (K fixedRow reduction)

/-- The integral matrix with last row `(1, 1, 1)` conjugating the model level to `K`. -/
def conjG : IntegralGL3 :=
  ⟨!![1, 0, 0; 0, 1, 0; 1, 1, 1], !![1, 0, 0; 0, 1, 0; -1, -1, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem lastRow_vecMul_conjG :
    GeneralEisenstein.lastRow ᵥ* (GeneralEisenstein.reductionThree conjG).val = fixedRow := by
  funext j
  fin_cases j <;> simp [GeneralEisenstein.lastRow, conjG, GeneralEisenstein.reductionThree,
    TernaryPoly.ModThreeGoodAction.fixedRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

/-- `K = conjG⁻¹ · Γ · conjG`: the geometric side's level is conjugate to the model level. -/
theorem mem_K_iff_conj (g : IntegralGL3) :
    g ∈ K ↔ conjG * g * conjG⁻¹ ∈ GeneralEisenstein.arithmeticLevel := by
  set Rc := (GeneralEisenstein.reductionThree conjG) with hRc
  set Rg := (GeneralEisenstein.reductionThree g) with hRg
  have hred : GeneralEisenstein.reductionThree (conjG * g * conjG⁻¹) = Rc * Rg * Rc⁻¹ := by
    simp [GeneralEisenstein.reductionThree, hRc, hRg]
  have hl : GeneralEisenstein.lastRow ᵥ* Rc.val = fixedRow := lastRow_vecMul_conjG
  change fixedRow ᵥ* (reduction g).val = fixedRow ↔
    GeneralEisenstein.lastRow ᵥ* (GeneralEisenstein.reductionThree (conjG * g * conjG⁻¹)).val =
      GeneralEisenstein.lastRow
  rw [hred, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hl]
  have hinv : Rc.val * (Rc⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv' : (Rc⁻¹).val * Rc.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  constructor
  · intro h
    have : fixedRow ᵥ* Rg.val = fixedRow := h
    rw [this, ← hl, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  · intro h
    have := congrArg (fun r => r ᵥ* Rc.val) h
    simp only [Matrix.vecMul_vecMul, mul_assoc, hinv', mul_one, hl] at this
    exact this

theorem flagSubspace_smul (side : Side) (g : RationalGL3) (F : Flags side) :
    flagSubspace side (g • F) = (flagSubspace side F).map g.val.mulVecLin := by
  induction F using Quotient.inductionOn with
  | h h =>
    change flagSubspace side (QuotientGroup.mk (g * h)) = _
    rw [flagSubspace_mk, flagSubspace_mk]
    change Submodule.map (g * h).val.mulVecLin (standardSubspace side) = _
    rw [Units.val_mul, Matrix.mulVecLin_mul, Submodule.map_comp]
    rfl

/-- The model's rational conjugating matrix. -/
def conjQ : RationalGL3 := Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) conjG

/-- **Goodness on the geometric side is goodness in the model after conjugation.** A rational line
(or plane) is good for `K` (some integral vector with nonzero coordinate sum mod 3) exactly when its
conjugate by the model-level matrix is a good flag (nonzero third coordinate mod 3). -/
theorem good_iff_goodFlag (side : Side) (F : Flags side) :
    (∃ v : Fin 3 → ℤ, (fun i => (v i : ℚ)) ∈ flagSubspace side F ∧
        ∑ i, (v i : ZMod 3) ≠ 0) ↔ GoodFlag side (conjQ • F) := by
  rw [goodFlag_iff, flagSubspace_smul]
  have hmul : ∀ v : Fin 3 → ℤ, (fun i => ((conjG.val *ᵥ v) i : ℚ)) =
      conjQ.val *ᵥ (fun i => (v i : ℚ)) := by
    intro v
    funext i
    simp [conjQ, Matrix.GeneralLinearGroup.map, Matrix.mulVec, dotProduct]
  have h2 : ∀ v : Fin 3 → ℤ, ((conjG.val *ᵥ v) 2 : ZMod 3) = ∑ i, (v i : ZMod 3) := by
    intro v
    simp [conjG, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  constructor
  · rintro ⟨v, hv, hs⟩
    refine ⟨conjG.val *ᵥ v, ?_, by rw [h2]; exact hs⟩
    rw [hmul]
    exact ⟨_, hv, rfl⟩
  · rintro ⟨w, ⟨x, hx, hxw⟩, hw⟩
    have hinvG : conjG.val *ᵥ (conjG⁻¹.val *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hcast : (fun i => ((conjG⁻¹.val *ᵥ w) i : ℚ)) = x := by
      have h1 := hmul (conjG⁻¹.val *ᵥ w)
      rw [hinvG] at h1
      have h3 : (fun i => (w i : ℚ)) = conjQ.val *ᵥ (fun i => ((conjG⁻¹.val *ᵥ w) i : ℚ)) := h1
      have h4 : conjQ.val *ᵥ x = (fun i => (w i : ℚ)) := hxw
      have h5 : conjQ.val *ᵥ ((fun i => ((conjG⁻¹.val *ᵥ w) i : ℚ)) - x) = 0 := by
        rw [Matrix.mulVec_sub, ← h3, h4, sub_self]
      have h6 := congrArg (fun y => conjQ⁻¹.val *ᵥ y) h5
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec, Matrix.mulVec_zero] at h6
      exact sub_eq_zero.mp h6
    refine ⟨conjG⁻¹.val *ᵥ w, ?_, ?_⟩
    · rw [hcast]; exact hx
    · have := h2 (conjG⁻¹.val *ᵥ w)
      rw [hinvG] at this
      rw [← this]
      exact hw

/-- `Γ(6)` is stable under the conjugation `conjG`, so it is common to `K` and the model level. -/
theorem conj_mem_principalSix_iff (g : IntegralGL3) :
    conjG * g * conjG⁻¹ ∈ TernaryPoly.IntegralGL3Congruence.principalSix ↔
      g ∈ TernaryPoly.IntegralGL3Congruence.principalSix := by
  constructor
  · intro h
    have := (TernaryPoly.IntegralGL3Congruence.principal_normal 6).conj_mem _ h conjG⁻¹
    simpa [mul_assoc] using this
  · intro h
    have := (TernaryPoly.IntegralGL3Congruence.principal_normal 6).conj_mem _ h conjG
    simpa [mul_assoc] using this

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
