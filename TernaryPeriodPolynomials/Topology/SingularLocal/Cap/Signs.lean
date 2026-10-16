module

/-
SPDX-License-Identifier: Apache-2.0
The finite-sum proof adapts the sum_split_char2 proof from akopjan/HamSandwich, to genuine signed endpoint cancellation.
-/
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Geometry

@[expose] public section


namespace TernaryPoly.SingularLocalCap

/-- Splitting a boundary sum at its front/back cut cancels the two common endpoints. -/
theorem sum_split_cancel {M : Type*} [AddCommGroup M]
    (a b : ℕ) (L : Fin (a+b+2) → M) (A : Fin (a+2) → M) (B : Fin (b+2) → M)
    (hle : ∀ k : Fin (a+b+2), (hk : k.val ≤ a) → L k = A ⟨k.val, by omega⟩)
    (hgt : ∀ k : Fin (a+b+2), (hk : a < k.val) →
      L k = B ⟨k.val-a, by have := k.isLt; omega⟩)
    (hend : A (Fin.last (a+1)) + B 0 = 0) :
    ∑ k, L k = (∑ i, A i) + ∑ j, B j := by
  rw [Fin.sum_univ_castSucc (n := a+1) A, Fin.sum_univ_succ (n := b+1) B]
  let e : Fin (a+1) ⊕ Fin (b+1) ≃ Fin (a+b+2) :=
    finSumFinEquiv.trans (finCongr (by omega))
  rw [← Equiv.sum_comp e L, Fintype.sum_sum_type]
  have hL : ∑ i : Fin (a+1), L (e (Sum.inl i)) = ∑ i : Fin (a+1), A i.castSucc := by
    apply Finset.sum_congr rfl
    intro i _
    have hv : (e (Sum.inl i)).val = i.val := by simp [e, finSumFinEquiv_apply_left]
    rw [hle (e (Sum.inl i)) (by rw [hv]; omega)]
    congr 1
  have hR : ∑ j : Fin (b+1), L (e (Sum.inr j)) = ∑ j : Fin (b+1), B j.succ := by
    apply Finset.sum_congr rfl
    intro j _
    have hv : (e (Sum.inr j)).val = a+1+j.val := by simp [e, finSumFinEquiv_apply_right]
    rw [hgt (e (Sum.inr j)) (by rw [hv]; omega)]
    congr 1
    apply Fin.ext
    simp only [hv, Fin.val_succ]
    omega
  rw [hL, hR]
  have he : (∑ i : Fin (a+1), A i.castSucc + A (Fin.last (a+1))) +
      (B 0 + ∑ j : Fin (b+1), B j.succ) =
      (∑ i : Fin (a+1), A i.castSucc + ∑ j : Fin (b+1), B j.succ) +
        (A (Fin.last (a+1)) + B 0) := by abel
  rw [he, hend, add_zero]

/-- The alternating front/back split carries the exact Koszul sign. -/
theorem signed_sum_split {M : Type*} [AddCommGroup M]
    (a b : ℕ) (L : Fin (a+b+2) → M) (A : Fin (a+2) → M) (B : Fin (b+2) → M)
    (hle : ∀ k : Fin (a+b+2), (hk : k.val ≤ a) → L k = A ⟨k.val, by omega⟩)
    (hgt : ∀ k : Fin (a+b+2), (hk : a < k.val) →
      L k = B ⟨k.val-a, by have := k.isLt; omega⟩)
    (hend : A (Fin.last (a+1)) = B 0) :
    ∑ k, (-1 : ℤ)^k.val • L k =
      (∑ i, (-1 : ℤ)^i.val • A i) + (-1 : ℤ)^a • ∑ j, (-1 : ℤ)^j.val • B j := by
  rw [Finset.smul_sum]
  apply sum_split_cancel a b
  · intro k hk
    rw [hle k hk]
  · intro k hk
    rw [hgt k hk]
    have he : a + (k.val-a) = k.val := by omega
    rw [← mul_smul, ← pow_add, he]
  · simp only [Fin.val_last, Fin.val_zero, pow_zero, one_zsmul,
      pow_succ, mul_neg, mul_one, neg_smul, hend]
    exact neg_add_cancel _

open FreeActionLinearization
open SphereOddDegree SphereOddDegree.AlexanderWhitney

/-- The actual Alexander–Whitney face formula with signs, evaluated by any linear
coefficient attachment to its back simplex. This is the combinatorial cap Leibniz identity. -/
theorem aw_signed_identity {X : TopCat.{0}} {W M : Type} [AddCommGroup W] [Module ℚ W]
    [AddCommGroup M] [Module ℚ M] (a b : ℕ)
    (F : SingularSimplex X a → W) (T : SingularSimplex X b → W →ₗ[ℚ] M)
    (σ : SingularSimplex X (a+b+1)) :
    ∑ k : Fin (a+b+2), (-1 : ℤ)^k.val •
      T (backSimplex X a b (faceSimplex X (a+b) k σ))
        (F (frontSimplex X a b (faceSimplex X (a+b) k σ))) =
      T (backSimplex X (a+1) b (awCastSimplex X a b σ))
        (∑ i : Fin (a+2), (-1 : ℤ)^i.val •
          F (faceSimplex X a i (frontSimplex X (a+1) b (awCastSimplex X a b σ)))) +
      (-1 : ℤ)^a • ∑ j : Fin (b+2), (-1 : ℤ)^j.val •
        T (faceSimplex X b j (backSimplex X a (b+1) σ))
          (F (frontSimplex X a (b+1) σ)) := by
  simp only [map_sum, map_zsmul]
  apply signed_sum_split a b
  · intro k hk
    rw [frontSimplex_faceSimplex_of_le X a b k hk,
      backSimplex_faceSimplex_of_le X a b k hk]
  · intro k hk
    rw [frontSimplex_faceSimplex_of_gt X a b k hk,
      backSimplex_faceSimplex_of_gt X a b k hk]
  · rw [frontSimplex_faceSimplex_endpoint X a b,
      backSimplex_faceSimplex_endpoint X a b]

end TernaryPoly.SingularLocalCap
