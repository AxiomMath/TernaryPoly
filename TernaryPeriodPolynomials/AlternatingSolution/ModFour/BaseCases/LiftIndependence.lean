module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Basics
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.ThreeTermNormReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Lemma54
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.OperatorAdditivity
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.ReduceTwoBasic

@[expose] public section



/-!
# Lemma 5.5, clause 2 (well-definedness / lift independence)

If `v, v'` are both symmetric (or both alternating) integral lifts of the same odd
reduction, `v - v'` is symmetric (resp. alternating) and reduces to zero mod two, hence
equals `C 2 * k` for some integral `k` which itself inherits the symmetric/alternating
property (cancelling the nonzero-divisor `C 2`). Since `reduceTwo k` is then symmetric
(directly, or via `alternating_reduceTwo_symmetric`), `lemma_5_4_proof` kills
`piOperator (reduceTwo (threeTermNorm k)) = piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo k))`,
and `g - g' = threeTermNorm k` (from cancelling `C 2` in `threeTermNorm`'s own additivity),
giving `piOperator (reduceTwo g) = piOperator (reduceTwo g')`.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem isAlternating_sub {s t : MvPolynomial (Fin 3) ℤ} (hs : IsAlternating s)
    (ht : IsAlternating t) : IsAlternating (s - t) := by
  intro σ
  rw [map_sub, hs σ, ht σ, ← smul_sub]

private theorem zsmul_C2_mul (n : ℤ) (k : MvPolynomial (Fin 3) ℤ) :
    n • ((C 2 : MvPolynomial (Fin 3) ℤ) * k) = C 2 * (n • k) := by
  simp only [zsmul_eq_mul]
  ring

private theorem hC2ne : (C 2 : MvPolynomial (Fin 3) ℤ) ≠ 0 := by
  intro hz
  rw [MvPolynomial.C_eq_zero] at hz
  norm_num at hz

private theorem symmetric_of_C2mul_symmetric {k : MvPolynomial (Fin 3) ℤ}
    (h : ((C 2 : MvPolynomial (Fin 3) ℤ) * k).IsSymmetric) : k.IsSymmetric := by
  intro σ
  have h1 := h σ
  rw [map_mul, MvPolynomial.rename_C] at h1
  exact mul_left_cancel₀ hC2ne h1

private theorem alternating_of_C2mul_alternating {k : MvPolynomial (Fin 3) ℤ}
    (h : IsAlternating ((C 2 : MvPolynomial (Fin 3) ℤ) * k)) : IsAlternating k := by
  intro σ
  have h1 := h σ
  rw [map_mul, MvPolynomial.rename_C, zsmul_C2_mul] at h1
  exact mul_left_cancel₀ hC2ne h1

private theorem threeTermNorm_sub (p q : MvPolynomial (Fin 3) ℤ) :
    threeTermNorm (p - q) = threeTermNorm p - threeTermNorm q := by
  simp only [threeTermNorm, map_sub]
  ring

private theorem threeTermNorm_C2mul (k : MvPolynomial (Fin 3) ℤ) :
    threeTermNorm ((C 2 : MvPolynomial (Fin 3) ℤ) * k) = C 2 * threeTermNorm k := by
  simp only [threeTermNorm, map_mul, MvPolynomial.bind₁_C_right]
  ring

/-- **Lemma 5.5, clause 2** (lift independence / well-definedness of `β`). -/
theorem lemma_5_5_clause2 :
    ∀ v v' g g' : MvPolynomial (Fin 3) ℤ,
      ((v.IsSymmetric ∧ v'.IsSymmetric) ∨ (IsAlternating v ∧ IsAlternating v')) →
      reduceTwo v = reduceTwo v' → threeTermNorm v = C 2 * g → threeTermNorm v' = C 2 * g' →
      piOperator (reduceTwo g) = piOperator (reduceTwo g') := by
  intro v v' g g' hsym hred hv hv'
  have hr0 : reduceTwo (v - v') = 0 := by rw [map_sub, hred, sub_self]
  obtain ⟨k, hk⟩ := exists_half hr0
  have hksymm : (reduceTwo k).IsSymmetric := by
    rcases hsym with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    · have hvv' : (v - v').IsSymmetric := hv1.sub hv2
      rw [hk] at hvv'
      exact (symmetric_of_C2mul_symmetric hvv').map (Int.castRingHom (ZMod 2))
    · have hvv' : IsAlternating (v - v') := isAlternating_sub hv1 hv2
      rw [hk] at hvv'
      exact alternating_reduceTwo_symmetric (alternating_of_C2mul_alternating hvv')
  have hzero : piOperator (reduceTwo (threeTermNorm k)) = 0 := by
    rw [reduceTwo_threeTermNorm]
    exact lemma_5_4_proof (reduceTwo k) hksymm
  have hv_sub : threeTermNorm (v - v') = C 2 * (g - g') := by
    rw [threeTermNorm_sub, hv, hv']; ring
  have hv_sub' : threeTermNorm (v - v') = C 2 * threeTermNorm k := by
    rw [hk, threeTermNorm_C2mul]
  have hgdiff : g - g' = threeTermNorm k := mul_left_cancel₀ hC2ne (hv_sub.symm.trans hv_sub')
  have heq : reduceTwo g - reduceTwo g' = reduceTwo (threeTermNorm k) := by
    rw [← map_sub, hgdiff]
  have hsplit : reduceTwo g = reduceTwo g' + (reduceTwo g - reduceTwo g') := by ring
  rw [hsplit, piOperator_add, heq, hzero, add_zero]

end TernaryPeriodPolynomials.Argument.ModFourBeta
