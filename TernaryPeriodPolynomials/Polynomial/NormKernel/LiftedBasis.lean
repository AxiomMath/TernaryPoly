module

public import TernaryPeriodPolynomials.Polynomial.NormKernel.AdaptedBasis

@[expose] public section


/-!
# Appendix D: the 28 adapted lifts form an `R`-basis of `S`

The homogeneous lifts `K₀, …, K₇, (1 + π)m` (`adapted`) of the adapted basis of `S/I` generate
`S = 𝔽₂[a, b, c]` over `R = 𝔽₂[d₄, d₆, d₇]` (by induction on the weighted degree: reduce modulo `I`,
subtract the lifts, write the remainder as `d₄s₄ + d₆s₆ + d₇s₇` with `sᵢ` of smaller degree), their degrees have the generating polynomial
`(1 - t⁴)(1 - t⁶)(1 - t⁷)/((1 - t)(1 - t²)(1 - t³))`, and therefore in each degree the
surjection from the free graded module is an isomorphism (dimension count): every `f ∈ S` has a
unique expansion `f = Σ invariantEval(pₖ)·liftₖ` (`adapted_expansion_existsUnique`), i.e. the lifts
form an `R`-basis of `S` (`adaptedRBasis`). Algebraic independence of `d₄, d₆, d₇` is
`CharTwoKernel.lemma_5_3_conjunct1`.

Written by Claude Opus 5.5.
-/


noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixD

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly a b c d4 d6 d7 invariantEval standardMonomial dicksonIdeal
  invariantEval_a invariantEval_b invariantEval_c)
open TernaryPeriodPolynomials.Argument.CharTwoKernel

private theorem isWH_adapted_0 : IsWeightedHomogeneous stdWeight (adapted 0) (stdDeg 0) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 0 + projS (standardMonomial 0)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 0).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_1 : IsWeightedHomogeneous stdWeight (adapted 1) (stdDeg 1) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 1 + projS (standardMonomial 1)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 1).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_2 : IsWeightedHomogeneous stdWeight (adapted 2) (stdDeg 2) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 2 + projS (standardMonomial 2)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 2).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_3 : IsWeightedHomogeneous stdWeight (adapted 3) (stdDeg 3) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 3 + projS (standardMonomial 3)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 3).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_4 : IsWeightedHomogeneous stdWeight (adapted 4) (stdDeg 4) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 4 + projS (standardMonomial 4)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 4).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_5 : IsWeightedHomogeneous stdWeight (adapted 5) (stdDeg 5) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 5 + projS (standardMonomial 5)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 5).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_6 : IsWeightedHomogeneous stdWeight (adapted 6) (stdDeg 6) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 6 + projS (standardMonomial 6)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 6).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_7 : IsWeightedHomogeneous stdWeight (adapted 7) (stdDeg 7) := by
  exact isWeightedHomogeneous_genAbs 0

private theorem isWH_adapted_8 : IsWeightedHomogeneous stdWeight (adapted 8) (stdDeg 8) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 7 + projS (standardMonomial 7)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 7).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_9 : IsWeightedHomogeneous stdWeight (adapted 9) (stdDeg 9) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 8 + projS (standardMonomial 8)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 8).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_10 : IsWeightedHomogeneous stdWeight (adapted 10) (stdDeg 10) := by
  exact isWeightedHomogeneous_genAbs 1

private theorem isWH_adapted_11 : IsWeightedHomogeneous stdWeight (adapted 11) (stdDeg 11) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 10 + projS (standardMonomial 10)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 10).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_12 : IsWeightedHomogeneous stdWeight (adapted 12) (stdDeg 12) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 11 + projS (standardMonomial 11)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 11).add (show IsWeightedHomogeneous stdWeight (genAbs 1) _ from isWeightedHomogeneous_genAbs 1)

private theorem isWH_adapted_13 : IsWeightedHomogeneous stdWeight (adapted 13) (stdDeg 13) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 12 + projS (standardMonomial 12)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 12).add (show IsWeightedHomogeneous stdWeight (genAbs 1) _ from isWeightedHomogeneous_genAbs 1)

private theorem isWH_adapted_14 : IsWeightedHomogeneous stdWeight (adapted 14) (stdDeg 14) := by
  exact isWeightedHomogeneous_genAbs 2

private theorem isWH_adapted_15 : IsWeightedHomogeneous stdWeight (adapted 15) (stdDeg 15) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 14 + projS (standardMonomial 14)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 14).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_16 : IsWeightedHomogeneous stdWeight (adapted 16) (stdDeg 16) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 15 + projS (standardMonomial 15)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 15).add (show IsWeightedHomogeneous stdWeight (genAbs 2) _ from isWeightedHomogeneous_genAbs 2)

private theorem isWH_adapted_17 : IsWeightedHomogeneous stdWeight (adapted 17) (stdDeg 17) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 17 + projS (standardMonomial 17)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 17).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_18 : IsWeightedHomogeneous stdWeight (adapted 18) (stdDeg 18) := by
  exact isWeightedHomogeneous_genAbs 3

private theorem isWH_adapted_19 : IsWeightedHomogeneous stdWeight (adapted 19) (stdDeg 19) := by
  exact isWeightedHomogeneous_genAbs 4

private theorem isWH_adapted_20 : IsWeightedHomogeneous stdWeight (adapted 20) (stdDeg 20) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 19 + projS (standardMonomial 19)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 19).add (show IsWeightedHomogeneous stdWeight (genAbs 4) _ from isWeightedHomogeneous_genAbs 4)

private theorem isWH_adapted_21 : IsWeightedHomogeneous stdWeight (adapted 21) (stdDeg 21) := by
  exact isWeightedHomogeneous_genAbs 5

private theorem isWH_adapted_22 : IsWeightedHomogeneous stdWeight (adapted 22) (stdDeg 22) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 21 + projS (standardMonomial 21)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 21).add (show IsWeightedHomogeneous stdWeight (genAbs 5) _ from isWeightedHomogeneous_genAbs 5)

private theorem isWH_adapted_23 : IsWeightedHomogeneous stdWeight (adapted 23) (stdDeg 23) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 22 + projS (standardMonomial 22)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 22).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_24 : IsWeightedHomogeneous stdWeight (adapted 24) (stdDeg 24) := by
  exact isWeightedHomogeneous_genAbs 6

private theorem isWH_adapted_25 : IsWeightedHomogeneous stdWeight (adapted 25) (stdDeg 25) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 25 + projS (standardMonomial 25)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 25).add (show IsWeightedHomogeneous stdWeight (0) _ from isWeightedHomogeneous_zero _ _ _)

private theorem isWH_adapted_26 : IsWeightedHomogeneous stdWeight (adapted 26) (stdDeg 26) := by
  exact isWeightedHomogeneous_genAbs 7

private theorem isWH_adapted_27 : IsWeightedHomogeneous stdWeight (adapted 27) (stdDeg 27) := by
  show IsWeightedHomogeneous stdWeight (standardMonomial 27 + projS (standardMonomial 27)) _
  rw [projS_standardMonomial]
  exact (isWeightedHomogeneous_standardMonomial 27).add (show IsWeightedHomogeneous stdWeight (d7 * genAbs 0 + d6 * genAbs 1 + d4 * genAbs 4) _ from ((isWeightedHomogeneous_d7.mul (isWeightedHomogeneous_genAbs 0)).add (isWeightedHomogeneous_d6.mul (isWeightedHomogeneous_genAbs 1))).add (isWeightedHomogeneous_d4.mul (isWeightedHomogeneous_genAbs 4)))

theorem isWeightedHomogeneous_adapted (k : Fin 28) :
    IsWeightedHomogeneous stdWeight (adapted k) (stdDeg k) := by
  fin_cases k
  · exact isWH_adapted_0
  · exact isWH_adapted_1
  · exact isWH_adapted_2
  · exact isWH_adapted_3
  · exact isWH_adapted_4
  · exact isWH_adapted_5
  · exact isWH_adapted_6
  · exact isWH_adapted_7
  · exact isWH_adapted_8
  · exact isWH_adapted_9
  · exact isWH_adapted_10
  · exact isWH_adapted_11
  · exact isWH_adapted_12
  · exact isWH_adapted_13
  · exact isWH_adapted_14
  · exact isWH_adapted_15
  · exact isWH_adapted_16
  · exact isWH_adapted_17
  · exact isWH_adapted_18
  · exact isWH_adapted_19
  · exact isWH_adapted_20
  · exact isWH_adapted_21
  · exact isWH_adapted_22
  · exact isWH_adapted_23
  · exact isWH_adapted_24
  · exact isWH_adapted_25
  · exact isWH_adapted_26
  · exact isWH_adapted_27

theorem component_invariantEval_mul_adapted (k : Fin 28) (q : Poly) (N : ℕ) :
    weightedHomogeneousComponent stdWeight N (invariantEval q * adapted k) =
      if stdDeg k ≤ N then
        invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (N - stdDeg k) q) *
          adapted k
      else 0 := by
  split_ifs with h
  · have e1 := weightedHomogeneousComponent_mul_of_homog (isWeightedHomogeneous_adapted k)
      (invariantEval q) (N - stdDeg k)
    rw [Nat.sub_add_cancel h] at e1
    rw [e1, show invariantEval = aeval (R := ZMod 2) ![d4, d6, d7] from rfl,
      weightedHomogeneousComponent_aeval hhom_467]
  · exact weightedHomogeneousComponent_mul_eq_zero_of_lt (isWeightedHomogeneous_adapted k) _
      (by omega)

private theorem component_mul_homog {p q : Poly} {w : ℕ} (hq : IsWeightedHomogeneous stdWeight q w)
    (N : ℕ) : weightedHomogeneousComponent stdWeight N (p * q) =
      if w ≤ N then weightedHomogeneousComponent stdWeight (N - w) p * q else 0 := by
  split_ifs with h
  · have e1 := weightedHomogeneousComponent_mul_of_homog hq p (N - w)
    rwa [Nat.sub_add_cancel h] at e1
  · exact weightedHomogeneousComponent_mul_eq_zero_of_lt hq _ (by omega)

/-- A homogeneous element of `I` of degree `D` is `t₄d₄ + t₆d₆ + t₇d₇` with `tᵢ` homogeneous of degree
`D - wᵢ`, and `tᵢ = 0` when `wᵢ > D`. -/
theorem homogeneous_mem_dicksonIdeal {x : Poly} {D : ℕ} (hx : x ∈ dicksonIdeal)
    (hhom : IsWeightedHomogeneous stdWeight x D) :
    ∃ t4 t6 t7 : Poly, x = t4 * d4 + t6 * d6 + t7 * d7 ∧
      (4 ≤ D → IsWeightedHomogeneous stdWeight t4 (D - 4)) ∧ (D < 4 → t4 = 0) ∧
      (6 ≤ D → IsWeightedHomogeneous stdWeight t6 (D - 6)) ∧ (D < 6 → t6 = 0) ∧
      (7 ≤ D → IsWeightedHomogeneous stdWeight t7 (D - 7)) ∧ (D < 7 → t7 = 0) := by
  obtain ⟨s4, s6, s7, hrep⟩ := (mem_dicksonIdeal_iff x).mp hx
  have h := hhom.weightedHomogeneousComponent_same
  rw [hrep, map_add, map_add, component_mul_homog isWeightedHomogeneous_d4,
    component_mul_homog isWeightedHomogeneous_d6, component_mul_homog isWeightedHomogeneous_d7,
    ← hrep] at h
  refine ⟨if 4 ≤ D then weightedHomogeneousComponent stdWeight (D - 4) s4 else 0,
    if 6 ≤ D then weightedHomogeneousComponent stdWeight (D - 6) s6 else 0,
    if 7 ≤ D then weightedHomogeneousComponent stdWeight (D - 7) s7 else 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h]; split_ifs <;> simp
  · intro hD; rw [ite_eq_left hD]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · intro hD; rw [ite_eq_right (by omega)]
  · intro hD; rw [ite_eq_left hD]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · intro hD; rw [ite_eq_right (by omega)]
  · intro hD; rw [ite_eq_left hD]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · intro hD; rw [ite_eq_right (by omega)]

/-- The `R`-span of the lifts. -/
def liftSpan : Submodule TernaryPoly.DicksonQuotient.invariantRing Poly :=
  Submodule.span TernaryPoly.DicksonQuotient.invariantRing (Set.range adapted)

private theorem invariantEval_mul_mem {x : Poly} (p : Poly) (hx : x ∈ liftSpan) :
    invariantEval p * x ∈ liftSpan :=
  liftSpan.smul_mem (⟨invariantEval p, invariantEval.mem_range_self p⟩ :
    TernaryPoly.DicksonQuotient.invariantRing) hx

private theorem const_mul_mem {x : Poly} (r : ZMod 2) (hx : x ∈ liftSpan) : C r * x ∈ liftSpan := by
  have := invariantEval_mul_mem (C r) hx
  rwa [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq] at this

private theorem dmul_mem {t : Poly} (j : Fin 3) (ht : t ∈ liftSpan) :
    t * (![d4, d6, d7] : Fin 3 → Poly) j ∈ liftSpan := by
  have hj : (![d4, d6, d7] : Fin 3 → Poly) j = invariantEval (X j) := by
    fin_cases j
    · exact invariantEval_a.symm
    · exact invariantEval_b.symm
    · exact invariantEval_c.symm
  rw [hj, mul_comm]
  exact invariantEval_mul_mem _ ht

/-- **Generation.** Every homogeneous polynomial lies in the `R`-span of the 28 lifts. -/
theorem homogeneous_mem_liftSpan (D : ℕ) :
    ∀ y : Poly, IsWeightedHomogeneous stdWeight y D → y ∈ liftSpan := by
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro y hy
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = adaptedBasis.repr (Ideal.Quotient.mk dicksonIdeal y) := ⟨_, rfl⟩
  have hres : y - ∑ k, C (γ k) * adapted k ∈ dicksonIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, hγ]
    conv_lhs => rw [← adaptedBasis.sum_repr (Ideal.Quotient.mk dicksonIdeal y)]
    simp only [map_sum, adaptedBasis_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_eq_C_mul]
    exact (map_smul (Ideal.Quotient.mkₐ (ZMod 2) dicksonIdeal) _ _).symm
  obtain ⟨z, hz⟩ : ∃ z, z = ∑ k, (if stdDeg k = D then C (γ k) * adapted k else 0) := ⟨_, rfl⟩
  have hcomp : weightedHomogeneousComponent stdWeight D (y - ∑ k, C (γ k) * adapted k) =
      y - z := by
    rw [map_sub, hy.weightedHomogeneousComponent_same, map_sum, hz]
    refine congrArg (fun t => y - t) (Finset.sum_congr rfl fun k _ => ?_)
    have hk : IsWeightedHomogeneous stdWeight (C (γ k) * adapted k) (stdDeg k) := by
      simpa using (isWeightedHomogeneous_C stdWeight (γ k)).mul (isWeightedHomogeneous_adapted k)
    split_ifs with h
    · rw [← h]; exact hk.weightedHomogeneousComponent_same
    · exact hk.weightedHomogeneousComponent_ne D (Ne.symm h)
  have hzmem : z ∈ liftSpan := by
    rw [hz]
    exact Submodule.sum_mem _ fun k _ => by
      split_ifs
      · exact const_mul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
      · exact liftSpan.zero_mem
  have hdiff : y - z ∈ dicksonIdeal := by
    rw [← hcomp]
    obtain ⟨s4, s6, s7, hs⟩ := (mem_dicksonIdeal_iff _).mp hres
    rw [hs, map_add, map_add, component_mul_homog isWeightedHomogeneous_d4,
      component_mul_homog isWeightedHomogeneous_d6, component_mul_homog isWeightedHomogeneous_d7]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;> split_ifs <;>
      first | exact dicksonIdeal.zero_mem | exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have hhom : IsWeightedHomogeneous stdWeight (y - z) D := by
    rw [← hcomp]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨t4, t6, t7, hdec, h4, h4', h6, h6', h7, h7'⟩ := homogeneous_mem_dicksonIdeal hdiff hhom
  have hterm : ∀ (w : ℕ) (j : Fin 3) (t : Poly), (![4, 6, 7] : Fin 3 → ℕ) j = w →
      (w ≤ D → IsWeightedHomogeneous stdWeight t (D - w)) → (D < w → t = 0) →
      t * (![d4, d6, d7] : Fin 3 → Poly) j ∈ liftSpan := by
    intro w j t hw hh hz0
    by_cases hD : w ≤ D
    · have hwpos : 0 < w := by rw [← hw]; fin_cases j <;> simp
      exact dmul_mem j (ih _ (by omega) _ (hh hD))
    · rw [hz0 (by omega), zero_mul]; exact liftSpan.zero_mem
  have hyz : y = z + (y - z) := by ring
  rw [hyz, hdec]
  refine liftSpan.add_mem hzmem (liftSpan.add_mem (liftSpan.add_mem ?_ ?_) ?_)
  · exact hterm 4 0 t4 rfl h4 h4'
  · exact hterm 6 1 t6 rfl h6 h6'
  · exact hterm 7 2 t7 rfl h7 h7'

/-- **The 28 lifts generate `S` over `R`.** -/
theorem mem_liftSpan (f : Poly) : f ∈ liftSpan := by
  induction f using MvPolynomial.induction_on' with
  | monomial s r =>
    exact homogeneous_mem_liftSpan _ _ (isWeightedHomogeneous_monomial stdWeight s r rfl)
  | add p q hp hq => exact liftSpan.add_mem hp hq

/-! ### Uniqueness: a dimension count in each degree -/

theorem isWeightedHomogeneous_adapted_term {d : ℕ} {i : Fin 28} (h : stdDeg i ≤ d) {q : Poly}
    (hq : IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) q (d - stdDeg i)) :
    IsWeightedHomogeneous stdWeight (invariantEval q * adapted i) d := by
  have h1 : IsWeightedHomogeneous stdWeight (invariantEval q) (d - stdDeg i) :=
    isWeightedHomogeneous_invariantEval hq
  have h2 := h1.mul (isWeightedHomogeneous_adapted i)
  rwa [Nat.sub_add_cancel h] at h2

/-- The degree-`d` part of the lift map. -/
def psiAFun (d : ℕ)
    (c : (m : {m : Fin 28 // stdDeg m ≤ d}) →
      ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
        (d - stdDeg m.1))) :
    ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) stdWeight d) :=
  ⟨∑ m : {m : Fin 28 // stdDeg m ≤ d}, invariantEval (c m : Poly) * adapted m.1,
    Submodule.sum_mem _ (fun m _ =>
      (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (isWeightedHomogeneous_adapted_term m.2
          ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (c m).2)))⟩

/-- The degree-`d` part of the lift map, as a linear map. -/
def psiA (d : ℕ) :
    ((m : {m : Fin 28 // stdDeg m ≤ d}) →
      ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
        (d - stdDeg m.1))) →ₗ[ZMod 2]
    ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) stdWeight d) where
  toFun := psiAFun d
  map_add' c c' := by
    refine Subtype.ext ?_
    simp only [psiAFun, Submodule.coe_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_add, add_mul]
  map_smul' r c := by
    refine Subtype.ext ?_
    simp only [psiAFun, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_smul, smul_mul_assoc]

private theorem expansion_of_span (f : Poly) :
    ∃ p : Fin 28 → Poly, f = ∑ k, invariantEval (p k) * adapted k := by
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (mem_liftSpan f)
  choose p hp using fun k => (r k).2
  refine ⟨p, ?_⟩
  rw [← hr]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Subalgebra.smul_def, ← hp k]
  rfl

theorem psiA_surjective (d : ℕ) : Function.Surjective (psiA d) := by
  intro y
  have hyhom : IsWeightedHomogeneous stdWeight (y : Poly) d :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp y.2
  obtain ⟨p, hy⟩ := expansion_of_span (y : Poly)
  refine ⟨fun m => ⟨weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (d - stdDeg m.1) (p m.1),
      (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩, ?_⟩
  refine Subtype.ext ?_
  show (∑ m : {m : Fin 28 // stdDeg m ≤ d}, invariantEval
      (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (d - stdDeg m.1) (p m.1)) *
        adapted m.1 : Poly) = (y : Poly)
  rw [← hyhom.weightedHomogeneousComponent_same, hy, map_sum]
  simp only [component_invariantEval_mul_adapted]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter fun i : Fin 28 => stdDeg i ≤ d) (by simp)
    (fun i => invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ)
      (d - stdDeg i) (p i)) * adapted i)).symm

theorem psiA_injective (d : ℕ) : Function.Injective (psiA d) := by
  have hfin := (LinearEquiv.ofBijective (psi d) ⟨psi_injective d, psi_surjective d⟩).finrank_eq
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr (psiA_surjective d)

/-- **Uniqueness of the expansion in the lifts.** -/
theorem adapted_expansion_unique (p : Fin 28 → Poly)
    (h : ∑ i, invariantEval (p i) * adapted i = 0) : ∀ i, p i = 0 := by
  intro i
  apply eq_zero_of_forall_weightedHomogeneousComponent_eq_zero (w := (![4, 6, 7] : Fin 3 → ℕ))
  intro d
  have hc := congrArg (weightedHomogeneousComponent stdWeight (d + stdDeg i)) h
  rw [map_sum, map_zero] at hc
  simp only [component_invariantEval_mul_adapted] at hc
  rw [← Finset.sum_filter] at hc
  rw [Finset.sum_subtype (Finset.univ.filter fun j => stdDeg j ≤ d + stdDeg i)
    (p := fun j => stdDeg j ≤ d + stdDeg i) (by simp)] at hc
  let c : (m : {m : Fin 28 // stdDeg m ≤ d + stdDeg i}) →
      ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
        (d + stdDeg i - stdDeg m.1)) :=
    fun m => ⟨weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (d + stdDeg i - stdDeg m.1)
      (p m.1), (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩
  have hzero : psiA (d + stdDeg i) c = psiA (d + stdDeg i) 0 := by
    rw [map_zero]
    exact Subtype.ext hc
  have := congrArg Subtype.val (congrFun (psiA_injective _ hzero) ⟨i, by omega⟩)
  simpa [c] using this

/-- **Appendix D: the 28 lifts form an `R`-basis of `S`.** Every `f ∈ S` has a unique expansion
`f = Σₖ invariantEval(pₖ) · liftₖ` with `pₖ ∈ 𝔽₂[u₄, u₆, u₇]`. -/
theorem adapted_expansion_existsUnique (f : Poly) :
    ∃! p : Fin 28 → Poly, f = ∑ k, invariantEval (p k) * adapted k := by
  obtain ⟨p, hp⟩ := expansion_of_span f
  refine ⟨p, hp, fun q hq => ?_⟩
  have hdiff : ∑ k, invariantEval (q k - p k) * adapted k = 0 := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [← hq, ← hp, sub_self]
  funext k
  exact sub_eq_zero.mp (adapted_expansion_unique _ hdiff k)

theorem adapted_linearIndependent :
    LinearIndependent TernaryPoly.DicksonQuotient.invariantRing adapted := by
  rw [Fintype.linearIndependent_iff]
  intro r hr k
  choose p hp using fun k => (r k).2
  have h : ∑ k, invariantEval (p k) * adapted k = 0 := by
    rw [← hr]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Subalgebra.smul_def, ← hp k]
    rfl
  have := adapted_expansion_unique p h k
  apply Subtype.ext
  rw [← hp k, this, map_zero]
  rfl

/-- **Appendix D: the `R`-basis of `S` given by the 28 adapted lifts.** -/
def adaptedRBasis : Module.Basis (Fin 28) TernaryPoly.DicksonQuotient.invariantRing Poly :=
  Module.Basis.mk adapted_linearIndependent (show ⊤ ≤ liftSpan from fun f _ => mem_liftSpan f)

theorem adaptedRBasis_apply (k : Fin 28) : adaptedRBasis k = adapted k := by
  exact Module.Basis.mk_apply _ _ k

/-- **The Hilbert generating polynomial of the lifts.** The `k`-th lift is homogeneous of weighted
degree `stdDeg k`, and `Σₖ t^{stdDeg k} = (1 - t⁴)(1 - t⁶)(1 - t⁷)/((1 - t)(1 - t²)(1 - t³))`. -/
theorem adapted_hilbert :
    (∀ k, IsWeightedHomogeneous stdWeight (adapted k) (stdDeg k)) ∧
      (∑ k : Fin 28, PowerSeries.X ^ (stdDeg k) : PowerSeries ℤ) *
          ((1 - PowerSeries.X ^ 1) * (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X ^ 3)) =
        (1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6) * (1 - PowerSeries.X ^ 7) :=
  ⟨isWeightedHomogeneous_adapted, P_mul_DA_eq_DB⟩

theorem projector_add (f g : TernaryPoly.CharTwoProjector.Poly) :
    TernaryPoly.CharTwoProjector.projector (f + g) =
      TernaryPoly.CharTwoProjector.projector f + TernaryPoly.CharTwoProjector.projector g := by
  simp only [TernaryPoly.CharTwoProjector.projector, TernaryPoly.CharTwoProjector.atom,
    TernaryPoly.CharTwoProjector.sub, map_add]
  ring

/-- **`π` vanishes on `(1 + π)m`** (characteristic two). -/
theorem projS_onePlus (f : Poly) : projS (f + projS f) = 0 := by
  apply TernaryPoly.CharTwoNorm.elementaryEval_injective
  rw [elementaryEval_projS, map_add, elementaryEval_projS, projector_add,
    TernaryPoly.CharTwoProjector.projector_idempotent
      (TernaryPoly.CharTwoNorm.symmetric_elementaryEval f), map_zero, CharTwo.add_self_eq_zero]

end TernaryPeriodPolynomials.Argument.AppendixD
