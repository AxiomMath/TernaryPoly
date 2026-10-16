module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLiftFinite
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Transfer

@[expose] public section


/-!
# The two indices of the binary Hecke datum agree

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeIndex

open TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.HeckeHomology

variable (p : ℕ) [Fact p.Prime]

/-- The coordinate swap in `GL₂(ℤ)`. -/
def swapW : IntegralGL :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem swapW_mul_self : swapW * swapW = 1 := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapW, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapW_conj_val (k : IntegralGL) :
    (swapW * k * swapW).val = !![k.val 1 1, k.val 1 0; k.val 0 1, k.val 0 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapW, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem mem_range_dvd (k : IntegralGL) : k ∈ (binDatum p).f.range ↔ (p : ℤ) ∣ k.val 1 0 := by
  constructor
  · rintro ⟨s, rfl⟩
    rw [binDatum_f_val]
    simp [cjMat]
  · intro h
    have hk' : (p : ℤ) ∣ (swapW * k * swapW).val 0 1 := by
      rw [swapW_conj_val]; simpa using h
    set s : IntegralGL := swapW * cjUnit p (swapW * k * swapW) hk' * swapW with hs
    have hsv : s.val = !![k.val 0 0, (p : ℤ) * k.val 0 1; k.val 1 0 / p, k.val 1 1] := by
      rw [hs]
      simp only [Units.val_mul, cjUnit, cjMat]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [swapW, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have hsS : s ∈ (binDatum p).S := by
      rw [binDatum_S, mem_commSubgroup_C1, hsv]
      simp
    refine ⟨⟨s, hsS⟩, ?_⟩
    apply Units.ext
    rw [binDatum_f_val, hsv]
    obtain ⟨b, hb⟩ := h
    have hp' := p_ne_zero_int (p := p)
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [cjMat, hb, Int.mul_ediv_cancel_left _ hp']

theorem swapW_inv : swapW⁻¹ = swapW := inv_eq_of_mul_eq_one_right swapW_mul_self

theorem range_eq_map : (binDatum p).f.range =
    (binDatum p).S.map (MulAut.conj swapW : IntegralGL ≃* IntegralGL).toMonoidHom := by
  ext k
  rw [mem_range_dvd, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨swapW * k * swapW, ?_, ?_⟩
    · rw [binDatum_S, mem_commSubgroup_C1, swapW_conj_val]; simpa using h
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, swapW_inv]
      rw [← mul_assoc, ← mul_assoc, swapW_mul_self, one_mul, mul_assoc, swapW_mul_self, mul_one]
  · rintro ⟨s, hs, rfl⟩
    rw [binDatum_S, mem_commSubgroup_C1] at hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, swapW_inv]
    rw [swapW_conj_val]
    simpa using hs

theorem index_range_eq : (binDatum p).f.range.index = (binDatum p).S.index := by
  have := Subgroup.index_map_equiv (H := (binDatum p).S) (MulAut.conj swapW : IntegralGL ≃* IntegralGL)
  rw [range_eq_map]
  exact this

theorem card_rc_eq : Nat.card (RC (binDatum p).S) = Nat.card (IntegralGL ⧸ (binDatum p).f.range) := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (binDatum p).S)]
  exact (index_range_eq p).symm

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeIndex
