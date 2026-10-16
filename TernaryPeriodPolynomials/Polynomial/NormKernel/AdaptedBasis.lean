module

public import TernaryPeriodPolynomials.Polynomial.NormKernel.GroebnerProperty
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.Bridge
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.GeneratorAbstract
public import TernaryPeriodPolynomials.Polynomial.CharTwo.ProjectorImages
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section


/-!
# Appendix D: normal forms and the basis of `S/I` adapted to the projector

`NF_I` (the remainder of division by the printed Gröbner basis, `nf`, `remainder_eq_nf`) of the
eight `Kⱼ = a c₊ Bⱼ` and of `(1 + π)m` for `m ∈ 𝓜` are the printed ones (`nf_K`, `nf_onePlusProjector`,, including the five exceptional cases), and the residue classes of
`K₀, …, K₇, (1 + π)m (m ∈ 𝓜)` form an `𝔽₂`-basis of `S/I` (`adaptedBasis`). The
projector `π` on `S = 𝔽₂[a, b, c]` is the literal eighteen-substitution projector of
`TernaryPoly.CharTwoProjector`, transported through the elementary-symmetric identification
`elementaryEval` (`projS`, `elementaryEval_projS`).

Written by Claude Opus 5.5.
-/


noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixD

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly a b c d4 d6 d7 invariantEval standardMonomial dicksonIdeal)
open TernaryPeriodPolynomials.Argument.CharTwoKernel (genAbs cplusAbs basisAbs elementaryEval_genAbs
  elementaryEval_dickson_a elementaryEval_dickson_b elementaryEval_dickson_c elementaryEval_dickson_d4
  elementaryEval_dickson_d6 elementaryEval_dickson_d7)

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) :=
  CharP.cast_eq_mod Poly 2 n

/-- The projector `π` on `S = 𝔽₂[a, b, c]`: the literal eighteen-substitution projector on symmetric
polynomials, read in elementary-symmetric coordinates. -/
def projS (f : Poly) : Poly :=
  Classical.choose (TernaryPoly.CharTwoNorm.exists_elementaryEval
    (TernaryPoly.CharTwoProjector.symmetric_projector
      (TernaryPoly.CharTwoNorm.symmetric_elementaryEval f)))

theorem elementaryEval_projS (f : Poly) :
    TernaryPoly.CharTwoNorm.elementaryEval (projS f) =
      TernaryPoly.CharTwoProjector.projector (TernaryPoly.CharTwoNorm.elementaryEval f) :=
  Classical.choose_spec (TernaryPoly.CharTwoNorm.exists_elementaryEval
    (TernaryPoly.CharTwoProjector.symmetric_projector
      (TernaryPoly.CharTwoNorm.symmetric_elementaryEval f)))


/-- The abstract projector images `π(mₖ)` of the standard monomials, in the generators `Kⱼ`. -/
def absImage : Fin 28 → Poly :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    genAbs 0,
    0,
    genAbs 1,
    genAbs 1,
    0,
    0,
    genAbs 2,
    0,
    0,
    genAbs 3,
    genAbs 4,
    genAbs 3 + genAbs 4,
    genAbs 5,
    0,
    genAbs 5,
    genAbs 6,
    0,
    genAbs 7,
    d7 * genAbs 0 + d6 * genAbs 1 + d4 * genAbs 4]

/-- The adapted lifts `Kⱼ, (1 + π)m`, ordered so that the `k`-th has the weighted degree
of the `k`-th standard monomial. -/
def adapted : Fin 28 → Poly :=
  ![standardMonomial 0 + projS (standardMonomial 0),
    standardMonomial 1 + projS (standardMonomial 1),
    standardMonomial 2 + projS (standardMonomial 2),
    standardMonomial 3 + projS (standardMonomial 3),
    standardMonomial 4 + projS (standardMonomial 4),
    standardMonomial 5 + projS (standardMonomial 5),
    standardMonomial 6 + projS (standardMonomial 6),
    genAbs 0,
    standardMonomial 7 + projS (standardMonomial 7),
    standardMonomial 8 + projS (standardMonomial 8),
    genAbs 1,
    standardMonomial 10 + projS (standardMonomial 10),
    standardMonomial 11 + projS (standardMonomial 11),
    standardMonomial 12 + projS (standardMonomial 12),
    genAbs 2,
    standardMonomial 14 + projS (standardMonomial 14),
    standardMonomial 15 + projS (standardMonomial 15),
    standardMonomial 17 + projS (standardMonomial 17),
    genAbs 3,
    genAbs 4,
    standardMonomial 19 + projS (standardMonomial 19),
    genAbs 5,
    standardMonomial 21 + projS (standardMonomial 21),
    standardMonomial 22 + projS (standardMonomial 22),
    genAbs 6,
    standardMonomial 25 + projS (standardMonomial 25),
    genAbs 7,
    standardMonomial 27 + projS (standardMonomial 27)]


theorem elementaryEval_standardMonomial (k : Fin 28) :
    TernaryPoly.CharTwoNorm.elementaryEval (standardMonomial k) =
      TernaryPoly.CharTwoProjectorImages.standardMonomial k := by
  fin_cases k <;>
    simp [TernaryPoly.DicksonQuotient.standardMonomial, TernaryPoly.CharTwoProjectorImages.standardMonomial,
      elementaryEval_dickson_a, elementaryEval_dickson_b, elementaryEval_dickson_c]

theorem elementaryEval_absImage (k : Fin 28) :
    TernaryPoly.CharTwoNorm.elementaryEval (absImage k) =
      TernaryPoly.CharTwoProjectorImages.generatorImage k := by
  fin_cases k <;>
    simp [absImage, TernaryPoly.CharTwoProjectorImages.generatorImage, elementaryEval_genAbs,
      elementaryEval_dickson_d4, elementaryEval_dickson_d6, elementaryEval_dickson_d7]

/-- `π` on the standard monomials (`CharTwoProjectorImages.projector_standardMonomial`). -/
theorem projS_standardMonomial (k : Fin 28) : projS (standardMonomial k) = absImage k := by
  apply TernaryPoly.CharTwoNorm.elementaryEval_injective
  rw [elementaryEval_projS, elementaryEval_standardMonomial, elementaryEval_absImage,
    TernaryPoly.CharTwoProjectorImages.projector_standardMonomial]

/-! ### Normal forms -/

/-- The `𝔽₂`-span of the standard monomials. -/
def stdSpan : Submodule (ZMod 2) Poly := Submodule.span (ZMod 2) (Set.range standardMonomial)

theorem eq_zero_of_mem_stdSpan_of_mem {x : Poly} (hx : x ∈ stdSpan) (hI : x ∈ dicksonIdeal) :
    x = 0 := by
  obtain ⟨γ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hx
  have h : ∑ k, C (γ k) * standardMonomial k = ∑ k, γ k • standardMonomial k :=
    Finset.sum_congr rfl fun k _ => (smul_eq_C_mul _ _).symm
  rw [← h] at hI
  have hz := std_coeff_eq_zero_of_mem γ hI
  simp [hz]

/-- The normal form modulo `I`: the standard-monomial representative of the residue class. -/
def nf (f : Poly) : Poly :=
  ∑ k, C (quotientBasis.repr (Ideal.Quotient.mk dicksonIdeal f) k) * standardMonomial k

theorem nf_mem_stdSpan (f : Poly) : nf f ∈ stdSpan :=
  Submodule.sum_mem _ fun k _ => by
    rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem sub_nf_mem (f : Poly) : f - nf f ∈ dicksonIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  conv_lhs => rw [← quotientBasis.sum_repr (Ideal.Quotient.mk dicksonIdeal f)]
  simp only [nf, map_sum, quotientBasis_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← smul_eq_C_mul]
  exact (map_smul (Ideal.Quotient.mkₐ (ZMod 2) dicksonIdeal) _ _).symm

/-- `NF_I` is characterized by: standard support and the same residue class. -/
theorem nf_eq_of {f r : Poly} (hr : r ∈ stdSpan) (h : f - r ∈ dicksonIdeal) : nf f = r := by
  have h1 : nf f - r ∈ stdSpan := sub_mem (nf_mem_stdSpan f) hr
  have h2 : nf f - r ∈ dicksonIdeal := by
    have := sub_mem h (sub_nf_mem f)
    convert this using 1; ring
  exact sub_eq_zero.mp (eq_zero_of_mem_stdSpan_of_mem h1 h2)

theorem mem_stdSpan_of_standard (r : Poly)
    (hsupp : ∀ e ∈ r.support, ∀ i : Fin 14, ¬ MonomialOrder.lex.degree (groebnerBasis i) ≤ e) :
    r ∈ stdSpan := by
  have hexp : r = ∑ k, C (r.coeff (e3t (stdTriple k))) * standardMonomial k := by
    ext e
    simp only [coeff_sum, coeff_C_mul, standardMonomial_eq_monomial, coeff_monomial, mul_ite,
      mul_one, mul_zero]
    by_cases he : e ∈ r.support
    · obtain ⟨k₀, hk₀⟩ := (standard_iff e).mp (hsupp e he)
      rw [Finset.sum_eq_single k₀]
      · rw [ite_eq_left hk₀.symm, hk₀]
      · intro k _ hk
        rw [ite_eq_right]
        intro h
        exact hk (stdTriple_injective (e3t_injective (h.trans hk₀)))
      · simp
    · rw [notMem_support_iff.mp he]
      symm
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · rw [h]; exact notMem_support_iff.mp he
      · rfl
  rw [hexp]
  exact Submodule.sum_mem _ fun k _ => by
    rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- **`NF_I` is the remainder on division by the printed Gröbner basis.** Any decomposition
`f = Σ qᵢ gᵢ + r` with no monomial of `r` divisible by a leading monomial `lm(gᵢ)` (as produced by
`MonomialOrder.div`) has `r = NF_I(f)`. -/
theorem remainder_eq_nf (f r : Poly) (q : Fin 14 →₀ Poly)
    (hfr : f = Finsupp.linearCombination Poly groebnerBasis q + r)
    (hsupp : ∀ e ∈ r.support, ∀ i : Fin 14, ¬ MonomialOrder.lex.degree (groebnerBasis i) ≤ e) :
    r = nf f := by
  symm
  apply nf_eq_of (mem_stdSpan_of_standard r hsupp)
  have : f - r = Finsupp.linearCombination Poly groebnerBasis q := by rw [hfr]; ring
  rw [this, Finsupp.linearCombination_apply]
  exact Ideal.sum_mem _ fun i _ => by
    simp only [smul_eq_mul]; exact Ideal.mul_mem_left _ _ (groebnerBasis_mem i)

private theorem mem_of_cert {x p q r : Poly} (h : x = p * d4 + q * d6 + r * d7) :
    x ∈ dicksonIdeal :=
  (mem_dicksonIdeal_iff x).mpr ⟨p, q, r, h⟩

private theorem std_mem (k : Fin 28) : standardMonomial k ∈ stdSpan := Submodule.subset_span ⟨k, rfl⟩


/-- The printed `NF_I(Kⱼ)`. -/
def printedNFK : Fin 8 → Poly :=
  ![a ^ 2 * b + a * c, a ^ 3 * b + a ^ 2 * c, a * b * c + b ^ 3 + c ^ 2, b ^ 2 * c, a * b ^ 3 + b ^ 2 * c, a * b ^ 2 * c, c ^ 3, b ^ 5]

/-- The printed `NF_I((1 + π)m)` in the five exceptional cases, indexed by `ab², a²c, b³, ac², bc²`. -/
def printedNFExc : Fin 5 → Poly :=
  ![a ^ 3 * b + a ^ 2 * c + a * b ^ 2, a ^ 3 * b, a * b * c + c ^ 2, a * b ^ 3 + a * c ^ 2 + b ^ 2 * c, a * b ^ 2 * c + b * c ^ 2]

/-- The indices of `ab², a²c, b³, ac², bc²` among the standard monomials. -/
def excIndex : Fin 5 → Fin 28 := ![11, 12, 15, 19, 21]

theorem nf_K_0 : nf (genAbs 0) = printedNFK 0 := by
  have hr : printedNFK 0 = standardMonomial 8 + standardMonomial 9 := by
    simp [printedNFK, TernaryPoly.DicksonQuotient.standardMonomial]
    try ring
  apply nf_eq_of
  · rw [hr]; exact add_mem (std_mem 8) (std_mem 9)
  · apply mem_of_cert (p := 0) (q := 0) (r := 0)
    rw [← sub_eq_zero]
    simp only [printedNFK, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf

theorem nf_K_1 : nf (genAbs 1) = printedNFK 1 := by
  have hr : printedNFK 1 = standardMonomial 12 + standardMonomial 13 := by
    simp [printedNFK, TernaryPoly.DicksonQuotient.standardMonomial]
    try ring
  apply nf_eq_of
  · rw [hr]; exact add_mem (std_mem 12) (std_mem 13)
  · apply mem_of_cert (p := 0) (q := 0) (r := 0)
    rw [← sub_eq_zero]
    simp only [printedNFK, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf

theorem nf_K_2 : nf (genAbs 2) = printedNFK 2 := by
  have hr : printedNFK 2 = standardMonomial 14 + standardMonomial 15 + standardMonomial 16 := by
    simp [printedNFK, TernaryPoly.DicksonQuotient.standardMonomial]
    try ring
  apply nf_eq_of
  · rw [hr]; exact add_mem (add_mem (std_mem 14) (std_mem 15)) (std_mem 16)
  · apply mem_of_cert (p := b) (q := 1) (r := 0)
    rw [← sub_eq_zero]
    simp only [printedNFK, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf
    try simp only [ofNat_mod]
    try norm_num

theorem nf_K_3 : nf (genAbs 3) = printedNFK 3 := by
  have hr : printedNFK 3 = standardMonomial 18 := by
    simp [printedNFK, TernaryPoly.DicksonQuotient.standardMonomial]
  apply nf_eq_of
  · rw [hr]; exact std_mem 18
  · apply mem_of_cert (p := c) (q := a) (r := 0)
    rw [← sub_eq_zero]
    simp only [printedNFK, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf
    try simp only [ofNat_mod]
    try norm_num

theorem nf_K_4 : nf (genAbs 4) = printedNFK 4 := by
  have hr : printedNFK 4 = standardMonomial 18 + standardMonomial 20 := by
    simp [printedNFK, TernaryPoly.DicksonQuotient.standardMonomial]
    try ring
  apply nf_eq_of
  · rw [hr]; exact add_mem (std_mem 18) (std_mem 20)
  · apply mem_of_cert (p := a * b + c) (q := 0) (r := 0)
    rw [← sub_eq_zero]
    simp only [printedNFK, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf
    try simp only [ofNat_mod]
    try norm_num

theorem nf_K_5 : nf (genAbs 5) = printedNFK 5 := by
  have hr : printedNFK 5 = standardMonomial 23 := by
    simp [printedNFK, TernaryPoly.DicksonQuotient.standardMonomial]
  apply nf_eq_of
  · rw [hr]; exact std_mem 23
  · apply mem_of_cert (p := a * c) (q := a ^ 2) (r := a)
    rw [← sub_eq_zero]
    simp only [printedNFK, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf
    try simp only [ofNat_mod]
    try norm_num

theorem nf_K_6 : nf (genAbs 6) = printedNFK 6 := by
  have hr : printedNFK 6 = standardMonomial 24 := by
    simp [printedNFK, TernaryPoly.DicksonQuotient.standardMonomial]
  apply nf_eq_of
  · rw [hr]; exact std_mem 24
  · apply mem_of_cert (p := a ^ 3 * b) (q := a ^ 3 + a * b + c) (r := 0)
    rw [← sub_eq_zero]
    simp only [printedNFK, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf
    try simp only [ofNat_mod]
    try norm_num

theorem nf_K_7 : nf (genAbs 7) = printedNFK 7 := by
  have hr : printedNFK 7 = standardMonomial 26 := by
    simp [printedNFK, TernaryPoly.DicksonQuotient.standardMonomial]
  apply nf_eq_of
  · rw [hr]; exact std_mem 26
  · apply mem_of_cert (p := a ^ 4 * b + a ^ 3 * c + a * b * c + b ^ 3 + c ^ 2) (q := b ^ 2) (r := a ^ 3)
    rw [← sub_eq_zero]
    simp only [printedNFK, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf
    try simp only [ofNat_mod]
    try norm_num

theorem nf_exc_0 : nf (standardMonomial 11 + projS (standardMonomial 11)) = printedNFExc 0 := by
  have hr : printedNFExc 0 = standardMonomial 11 + standardMonomial 12 + standardMonomial 13 := by
    simp [printedNFExc, TernaryPoly.DicksonQuotient.standardMonomial]
    try ring
  apply nf_eq_of
  · rw [hr]; exact add_mem (add_mem (std_mem 11) (std_mem 12)) (std_mem 13)
  · apply mem_of_cert (p := 0) (q := 0) (r := 0)
    rw [projS_standardMonomial, ← sub_eq_zero]
    simp only [printedNFExc, absImage, TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf

theorem nf_exc_1 : nf (standardMonomial 12 + projS (standardMonomial 12)) = printedNFExc 1 := by
  have hr : printedNFExc 1 = standardMonomial 13 := by
    simp [printedNFExc, TernaryPoly.DicksonQuotient.standardMonomial]
  apply nf_eq_of
  · rw [hr]; exact std_mem 13
  · apply mem_of_cert (p := 0) (q := 0) (r := 0)
    rw [projS_standardMonomial, ← sub_eq_zero]
    simp only [printedNFExc, absImage, TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf
    try simp only [ofNat_mod]
    try norm_num

theorem nf_exc_2 : nf (standardMonomial 15 + projS (standardMonomial 15)) = printedNFExc 2 := by
  have hr : printedNFExc 2 = standardMonomial 14 + standardMonomial 16 := by
    simp [printedNFExc, TernaryPoly.DicksonQuotient.standardMonomial]
    try ring
  apply nf_eq_of
  · rw [hr]; exact add_mem (std_mem 14) (std_mem 16)
  · apply mem_of_cert (p := b) (q := 1) (r := 0)
    rw [projS_standardMonomial, ← sub_eq_zero]
    simp only [printedNFExc, absImage, TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf
    try simp only [ofNat_mod]
    try norm_num

theorem nf_exc_3 : nf (standardMonomial 19 + projS (standardMonomial 19)) = printedNFExc 3 := by
  have hr : printedNFExc 3 = standardMonomial 18 + standardMonomial 19 + standardMonomial 20 := by
    simp [printedNFExc, TernaryPoly.DicksonQuotient.standardMonomial]
    try ring
  apply nf_eq_of
  · rw [hr]; exact add_mem (add_mem (std_mem 18) (std_mem 19)) (std_mem 20)
  · apply mem_of_cert (p := a * b + c) (q := 0) (r := 0)
    rw [projS_standardMonomial, ← sub_eq_zero]
    simp only [printedNFExc, absImage, TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf
    try simp only [ofNat_mod]
    try norm_num

theorem nf_exc_4 : nf (standardMonomial 21 + projS (standardMonomial 21)) = printedNFExc 4 := by
  have hr : printedNFExc 4 = standardMonomial 21 + standardMonomial 23 := by
    simp [printedNFExc, TernaryPoly.DicksonQuotient.standardMonomial]
    try ring
  apply nf_eq_of
  · rw [hr]; exact add_mem (std_mem 21) (std_mem 23)
  · apply mem_of_cert (p := a * c) (q := a ^ 2) (r := a)
    rw [projS_standardMonomial, ← sub_eq_zero]
    simp only [printedNFExc, absImage, TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
    ring_nf
    try simp only [ofNat_mod]
    try norm_num

theorem nf_onePlusProjector_0 :
    nf (standardMonomial 0 + projS (standardMonomial 0)) = standardMonomial 0 := by
  apply nf_eq_of (std_mem 0)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_1 :
    nf (standardMonomial 1 + projS (standardMonomial 1)) = standardMonomial 1 := by
  apply nf_eq_of (std_mem 1)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_2 :
    nf (standardMonomial 2 + projS (standardMonomial 2)) = standardMonomial 2 := by
  apply nf_eq_of (std_mem 2)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_3 :
    nf (standardMonomial 3 + projS (standardMonomial 3)) = standardMonomial 3 := by
  apply nf_eq_of (std_mem 3)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_4 :
    nf (standardMonomial 4 + projS (standardMonomial 4)) = standardMonomial 4 := by
  apply nf_eq_of (std_mem 4)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_5 :
    nf (standardMonomial 5 + projS (standardMonomial 5)) = standardMonomial 5 := by
  apply nf_eq_of (std_mem 5)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_6 :
    nf (standardMonomial 6 + projS (standardMonomial 6)) = standardMonomial 6 := by
  apply nf_eq_of (std_mem 6)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_7 :
    nf (standardMonomial 7 + projS (standardMonomial 7)) = standardMonomial 7 := by
  apply nf_eq_of (std_mem 7)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_8 :
    nf (standardMonomial 8 + projS (standardMonomial 8)) = standardMonomial 8 := by
  apply nf_eq_of (std_mem 8)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_10 :
    nf (standardMonomial 10 + projS (standardMonomial 10)) = standardMonomial 10 := by
  apply nf_eq_of (std_mem 10)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_14 :
    nf (standardMonomial 14 + projS (standardMonomial 14)) = standardMonomial 14 := by
  apply nf_eq_of (std_mem 14)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_17 :
    nf (standardMonomial 17 + projS (standardMonomial 17)) = standardMonomial 17 := by
  apply nf_eq_of (std_mem 17)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_22 :
    nf (standardMonomial 22 + projS (standardMonomial 22)) = standardMonomial 22 := by
  apply nf_eq_of (std_mem 22)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_25 :
    nf (standardMonomial 25 + projS (standardMonomial 25)) = standardMonomial 25 := by
  apply nf_eq_of (std_mem 25)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact dicksonIdeal.zero_mem

theorem nf_onePlusProjector_27 :
    nf (standardMonomial 27 + projS (standardMonomial 27)) = standardMonomial 27 := by
  apply nf_eq_of (std_mem 27)
  rw [projS_standardMonomial, add_sub_cancel_left]
  exact mem_of_cert (p := genAbs 4) (q := genAbs 1) (r := genAbs 0) (by show d7 * genAbs 0 + d6 * genAbs 1 + d4 * genAbs 4 = _; ring)

theorem std_sub_adapted_0 : standardMonomial 0 - (adapted 0) ∈ dicksonIdeal := by
  have e : adapted 0 = (standardMonomial 0 + (0)) := by
    show (standardMonomial 0 + projS (standardMonomial 0)) = _
    rw [projS_standardMonomial 0]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_1 : standardMonomial 1 - (adapted 1) ∈ dicksonIdeal := by
  have e : adapted 1 = (standardMonomial 1 + (0)) := by
    show (standardMonomial 1 + projS (standardMonomial 1)) = _
    rw [projS_standardMonomial 1]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_2 : standardMonomial 2 - (adapted 2) ∈ dicksonIdeal := by
  have e : adapted 2 = (standardMonomial 2 + (0)) := by
    show (standardMonomial 2 + projS (standardMonomial 2)) = _
    rw [projS_standardMonomial 2]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_3 : standardMonomial 3 - (adapted 3) ∈ dicksonIdeal := by
  have e : adapted 3 = (standardMonomial 3 + (0)) := by
    show (standardMonomial 3 + projS (standardMonomial 3)) = _
    rw [projS_standardMonomial 3]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_4 : standardMonomial 4 - (adapted 4) ∈ dicksonIdeal := by
  have e : adapted 4 = (standardMonomial 4 + (0)) := by
    show (standardMonomial 4 + projS (standardMonomial 4)) = _
    rw [projS_standardMonomial 4]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_5 : standardMonomial 5 - (adapted 5) ∈ dicksonIdeal := by
  have e : adapted 5 = (standardMonomial 5 + (0)) := by
    show (standardMonomial 5 + projS (standardMonomial 5)) = _
    rw [projS_standardMonomial 5]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_6 : standardMonomial 6 - (adapted 6) ∈ dicksonIdeal := by
  have e : adapted 6 = (standardMonomial 6 + (0)) := by
    show (standardMonomial 6 + projS (standardMonomial 6)) = _
    rw [projS_standardMonomial 6]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_7 : standardMonomial 7 - (adapted 8) ∈ dicksonIdeal := by
  have e : adapted 8 = (standardMonomial 7 + (0)) := by
    show (standardMonomial 7 + projS (standardMonomial 7)) = _
    rw [projS_standardMonomial 7]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_8 : standardMonomial 8 - (adapted 9) ∈ dicksonIdeal := by
  have e : adapted 9 = (standardMonomial 8 + (0)) := by
    show (standardMonomial 8 + projS (standardMonomial 8)) = _
    rw [projS_standardMonomial 8]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_9 : standardMonomial 9 - (adapted 7 + adapted 9) ∈ dicksonIdeal := by
  have e : adapted 7 + adapted 9 = genAbs 0 + (standardMonomial 8 + (0)) := by
    show genAbs 0 + (standardMonomial 8 + projS (standardMonomial 8)) = _
    rw [projS_standardMonomial 8]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_10 : standardMonomial 10 - (adapted 11) ∈ dicksonIdeal := by
  have e : adapted 11 = (standardMonomial 10 + (0)) := by
    show (standardMonomial 10 + projS (standardMonomial 10)) = _
    rw [projS_standardMonomial 10]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_11 : standardMonomial 11 - (adapted 10 + adapted 12) ∈ dicksonIdeal := by
  have e : adapted 10 + adapted 12 = genAbs 1 + (standardMonomial 11 + (genAbs 1)) := by
    show genAbs 1 + (standardMonomial 11 + projS (standardMonomial 11)) = _
    rw [projS_standardMonomial 11]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_12 : standardMonomial 12 - (adapted 10 + adapted 13) ∈ dicksonIdeal := by
  have e : adapted 10 + adapted 13 = genAbs 1 + (standardMonomial 12 + (genAbs 1)) := by
    show genAbs 1 + (standardMonomial 12 + projS (standardMonomial 12)) = _
    rw [projS_standardMonomial 12]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_13 : standardMonomial 13 - (adapted 13) ∈ dicksonIdeal := by
  have e : adapted 13 = (standardMonomial 12 + (genAbs 1)) := by
    show (standardMonomial 12 + projS (standardMonomial 12)) = _
    rw [projS_standardMonomial 12]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_14 : standardMonomial 14 - (adapted 15) ∈ dicksonIdeal := by
  have e : adapted 15 = (standardMonomial 14 + (0)) := by
    show (standardMonomial 14 + projS (standardMonomial 14)) = _
    rw [projS_standardMonomial 14]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_15 : standardMonomial 15 - (adapted 14 + adapted 16) ∈ dicksonIdeal := by
  have e : adapted 14 + adapted 16 = genAbs 2 + (standardMonomial 15 + (genAbs 2)) := by
    show genAbs 2 + (standardMonomial 15 + projS (standardMonomial 15)) = _
    rw [projS_standardMonomial 15]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_16 : standardMonomial 16 - (adapted 15 + adapted 16) ∈ dicksonIdeal := by
  have e : adapted 15 + adapted 16 = (standardMonomial 14 + (0)) + (standardMonomial 15 + (genAbs 2)) := by
    show (standardMonomial 14 + projS (standardMonomial 14)) + (standardMonomial 15 + projS (standardMonomial 15)) = _
    rw [projS_standardMonomial 14, projS_standardMonomial 15]
    rfl
  rw [e]
  apply mem_of_cert (p := b) (q := 1) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_17 : standardMonomial 17 - (adapted 17) ∈ dicksonIdeal := by
  have e : adapted 17 = (standardMonomial 17 + (0)) := by
    show (standardMonomial 17 + projS (standardMonomial 17)) = _
    rw [projS_standardMonomial 17]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_18 : standardMonomial 18 - (adapted 18) ∈ dicksonIdeal := by
  have e : adapted 18 = genAbs 3 := rfl
  rw [e]
  apply mem_of_cert (p := c) (q := a) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_19 : standardMonomial 19 - (adapted 19 + adapted 20) ∈ dicksonIdeal := by
  have e : adapted 19 + adapted 20 = genAbs 4 + (standardMonomial 19 + (genAbs 4)) := by
    show genAbs 4 + (standardMonomial 19 + projS (standardMonomial 19)) = _
    rw [projS_standardMonomial 19]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_20 : standardMonomial 20 - (adapted 18 + adapted 19) ∈ dicksonIdeal := by
  have e : adapted 18 + adapted 19 = genAbs 3 + genAbs 4 := rfl
  rw [e]
  apply mem_of_cert (p := a * b) (q := a) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_21 : standardMonomial 21 - (adapted 21 + adapted 22) ∈ dicksonIdeal := by
  have e : adapted 21 + adapted 22 = genAbs 5 + (standardMonomial 21 + (genAbs 5)) := by
    show genAbs 5 + (standardMonomial 21 + projS (standardMonomial 21)) = _
    rw [projS_standardMonomial 21]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_22 : standardMonomial 22 - (adapted 23) ∈ dicksonIdeal := by
  have e : adapted 23 = (standardMonomial 22 + (0)) := by
    show (standardMonomial 22 + projS (standardMonomial 22)) = _
    rw [projS_standardMonomial 22]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_23 : standardMonomial 23 - (adapted 21) ∈ dicksonIdeal := by
  have e : adapted 21 = genAbs 5 := rfl
  rw [e]
  apply mem_of_cert (p := a * c) (q := a ^ 2) (r := a)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_24 : standardMonomial 24 - (adapted 24) ∈ dicksonIdeal := by
  have e : adapted 24 = genAbs 6 := rfl
  rw [e]
  apply mem_of_cert (p := a ^ 3 * b) (q := a ^ 3 + a * b + c) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_25 : standardMonomial 25 - (adapted 25) ∈ dicksonIdeal := by
  have e : adapted 25 = (standardMonomial 25 + (0)) := by
    show (standardMonomial 25 + projS (standardMonomial 25)) = _
    rw [projS_standardMonomial 25]
    rfl
  rw [e]
  apply mem_of_cert (p := 0) (q := 0) (r := 0)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, d4, d6, d7, a, b, c]
  ring_nf

theorem std_sub_adapted_26 : standardMonomial 26 - (adapted 26) ∈ dicksonIdeal := by
  have e : adapted 26 = genAbs 7 := rfl
  rw [e]
  apply mem_of_cert (p := a ^ 4 * b + a ^ 3 * c + a * b * c + b ^ 3 + c ^ 2) (q := b ^ 2) (r := a ^ 3)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

theorem std_sub_adapted_27 : standardMonomial 27 - (adapted 27) ∈ dicksonIdeal := by
  have e : adapted 27 = (standardMonomial 27 + (d7 * genAbs 0 + d6 * genAbs 1 + d4 * genAbs 4)) := by
    show (standardMonomial 27 + projS (standardMonomial 27)) = _
    rw [projS_standardMonomial 27]
    rfl
  rw [e]
  apply mem_of_cert (p := a ^ 5 * b + a ^ 4 * c + a ^ 2 * b * c + a * c ^ 2) (q := a ^ 3 * b + a ^ 2 * c) (r := a ^ 2 * b + a * c)
  rw [← sub_eq_zero]
  simp only [TernaryPoly.DicksonQuotient.standardMonomial, genAbs, cplusAbs, basisAbs, Matrix.cons_val, d4, d6, d7, a, b, c]
  ring_nf
  try simp only [ofNat_mod]
  try norm_num

private theorem qb_mem_0 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 0) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨0, rfl⟩

private theorem qb_mem_1 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 1) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_1
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨1, rfl⟩

private theorem qb_mem_2 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 2) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_2
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨2, rfl⟩

private theorem qb_mem_3 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 3) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_3
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨3, rfl⟩

private theorem qb_mem_4 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 4) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_4
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨4, rfl⟩

private theorem qb_mem_5 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 5) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_5
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨5, rfl⟩

private theorem qb_mem_6 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 6) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_6
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨6, rfl⟩

private theorem qb_mem_7 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 7) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_7
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨8, rfl⟩

private theorem qb_mem_8 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 8) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_8
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨9, rfl⟩

private theorem qb_mem_9 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 9) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_9
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h, map_add]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨7, rfl⟩) (Submodule.subset_span ⟨9, rfl⟩)

private theorem qb_mem_10 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 10) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_10
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨11, rfl⟩

private theorem qb_mem_11 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 11) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_11
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h, map_add]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨10, rfl⟩) (Submodule.subset_span ⟨12, rfl⟩)

private theorem qb_mem_12 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 12) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_12
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h, map_add]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨10, rfl⟩) (Submodule.subset_span ⟨13, rfl⟩)

private theorem qb_mem_13 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 13) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_13
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨13, rfl⟩

private theorem qb_mem_14 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 14) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_14
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨15, rfl⟩

private theorem qb_mem_15 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 15) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_15
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h, map_add]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨14, rfl⟩) (Submodule.subset_span ⟨16, rfl⟩)

private theorem qb_mem_16 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 16) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_16
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h, map_add]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨15, rfl⟩) (Submodule.subset_span ⟨16, rfl⟩)

private theorem qb_mem_17 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 17) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_17
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨17, rfl⟩

private theorem qb_mem_18 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 18) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_18
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨18, rfl⟩

private theorem qb_mem_19 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 19) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_19
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h, map_add]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨19, rfl⟩) (Submodule.subset_span ⟨20, rfl⟩)

private theorem qb_mem_20 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 20) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_20
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h, map_add]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨18, rfl⟩) (Submodule.subset_span ⟨19, rfl⟩)

private theorem qb_mem_21 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 21) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_21
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h, map_add]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨21, rfl⟩) (Submodule.subset_span ⟨22, rfl⟩)

private theorem qb_mem_22 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 22) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_22
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨23, rfl⟩

private theorem qb_mem_23 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 23) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_23
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨21, rfl⟩

private theorem qb_mem_24 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 24) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_24
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨24, rfl⟩

private theorem qb_mem_25 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 25) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_25
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨25, rfl⟩

private theorem qb_mem_26 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 26) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_26
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨26, rfl⟩

private theorem qb_mem_27 : Ideal.Quotient.mk dicksonIdeal (standardMonomial 27) ∈
    Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  have h := std_sub_adapted_27
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
  rw [h]; exact Submodule.subset_span ⟨27, rfl⟩

theorem quotientBasis_mem_span_adapted (k : Fin 28) :
    quotientBasis k ∈ Submodule.span (ZMod 2)
      (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  rw [quotientBasis_apply]
  fin_cases k
  · exact qb_mem_0
  · exact qb_mem_1
  · exact qb_mem_2
  · exact qb_mem_3
  · exact qb_mem_4
  · exact qb_mem_5
  · exact qb_mem_6
  · exact qb_mem_7
  · exact qb_mem_8
  · exact qb_mem_9
  · exact qb_mem_10
  · exact qb_mem_11
  · exact qb_mem_12
  · exact qb_mem_13
  · exact qb_mem_14
  · exact qb_mem_15
  · exact qb_mem_16
  · exact qb_mem_17
  · exact qb_mem_18
  · exact qb_mem_19
  · exact qb_mem_20
  · exact qb_mem_21
  · exact qb_mem_22
  · exact qb_mem_23
  · exact qb_mem_24
  · exact qb_mem_25
  · exact qb_mem_26
  · exact qb_mem_27

theorem adapted_span :
    ⊤ ≤ Submodule.span (ZMod 2) (Set.range fun j => Ideal.Quotient.mk dicksonIdeal (adapted j)) := by
  rw [← quotientBasis.span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact quotientBasis_mem_span_adapted k

/-- **Appendix D: the basis of `S/I` adapted to the projector.** The residue classes of
`K₀, …, K₇` and `(1 + π)m`, `m ∈ 𝓜`. -/
def adaptedBasis : Module.Basis (Fin 28) (ZMod 2) (Poly ⧸ dicksonIdeal) :=
  basisOfTopLeSpanOfCardEqFinrank _ adapted_span (by rw [Fintype.card_fin, finrank_quotient])

theorem adaptedBasis_apply (k : Fin 28) :
    adaptedBasis k = Ideal.Quotient.mk dicksonIdeal (adapted k) := by
  rw [adaptedBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

end TernaryPeriodPolynomials.Argument.AppendixD
