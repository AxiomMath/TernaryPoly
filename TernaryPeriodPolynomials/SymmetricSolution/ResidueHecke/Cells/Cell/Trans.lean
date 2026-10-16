module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.Cell0Geometry

@[expose] public section


/-!
# Lemma B.1, boundary route: top cells are unimodular and translates of the standard cell

Three independent minimal lines of a vertex form a unimodular triple (`det_unimodular_of_subset_M`: a finite check in
the six minimal lines of `A₃`), hence every top cell of the well-rounded complex is a `GL₃(ℤ)`-translate of the
standard cell `{e₀, e₁, e₂}` (`exists_gl_T0`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.FreeResolution GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

theorem det_m_triples : ∀ i j k : Fin 6, det3v (m i) (m j) (m k) ≠ 0 →
    det3v (m i) (m j) (m k) = 1 ∨ det3v (m i) (m j) (m k) = -1 := by
  decide

theorem det_unit_cases (h : IntegralGL3) :
    (h : Matrix (Fin 3) (Fin 3) ℤ).det = 1 ∨ (h : Matrix (Fin 3) (Fin 3) ℤ).det = -1 := by
  have h1 := congrArg Matrix.det h.mul_inv
  rw [Matrix.det_mul, Matrix.det_one] at h1
  exact Int.eq_one_or_neg_one_of_mul_eq_one h1

theorem det3v_mem_M0_cases (a b c : Vec) (ha : Line.mk a ∈ M0) (hb : Line.mk b ∈ M0) (hc : Line.mk c ∈ M0)
    (hd : det3v a b c ≠ 0) : det3v a b c = 1 ∨ det3v a b c = -1 := by
  have key : ∀ x : Vec, Line.mk x ∈ M0 → ∃ i : Fin 6, x = m i ∨ x = -m i := fun x hx =>
    (qf_A0_eq_one_iff x).mp ((mem_M0_mk x).mp hx)
  obtain ⟨i, hi⟩ := key a ha
  obtain ⟨j, hj⟩ := key b hb
  obtain ⟨k, hk⟩ := key c hc
  have hne : det3v (m i) (m j) (m k) ≠ 0 := by
    rwa [← det3v_ne_zero_iff_of_sign (x := m i) (y := m j) (z := m k) hi hj hk]
  rcases det_m_triples i j k hne with h | h
  · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;>
      simp only [det3v_neg_left, det3v_neg_mid, det3v_neg_right, neg_neg, h] <;> simp
  · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;>
      simp only [det3v_neg_left, det3v_neg_mid, det3v_neg_right, neg_neg, h] <;> simp

theorem det_unimodular_of_subset_M (v : Vtx) (a b c : Vec)
    (hmem : ({Line.mk a, Line.mk b, Line.mk c} : Finset Line) ⊆ v.M) (hdet : det3v a b c ≠ 0) :
    det3v a b c = 1 ∨ det3v a b c = -1 := by
  have ha : Line.mk a ∈ v.M := hmem (by simp)
  have hb : Line.mk b ∈ v.M := hmem (by simp)
  have hc : Line.mk c ∈ v.M := hmem (by simp)
  rw [Vtx.mem_M_iff_smul, smul_mk] at ha hb hc
  have hF := det3v_mv v.frame a b c
  have hne : det3v (mv v.frame a) (mv v.frame b) (mv v.frame c) ≠ 0 := by
    rw [hF]
    exact mul_ne_zero (det_ne_zero_of_unit _) hdet
  have h1 := det3v_mem_M0_cases _ _ _ ha hb hc hne
  rw [hF] at h1
  have hu : IsUnit ((v.frame : Matrix (Fin 3) (Fin 3) ℤ).det * det3v a b c) := by
    rcases h1 with h | h <;> rw [h] <;> simp
  exact Int.isUnit_iff.mp (isUnit_of_mul_isUnit_right hu)

theorem exists_gl_T0 (C : Cell) (hC : C.val.card = 3) : ∃ g : IntegralGL3, C.val = g • T0set := by
  obtain ⟨⟨a, ha, b, hb, c, hc, habc⟩, v, hv⟩ := C.isCell
  have hsub : ({a, b, c} : Finset Line) ⊆ C.val := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset Line).card = 3 := by
    have h12 := habc.ne12
    have h23 := habc.ne23
    have h13 := habc.ne13
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_insert_of_notMem (by simp [h23]),
      Finset.card_singleton]
  have heq : C.val = {a, b, c} := (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hC])).symm
  set xa : Vec := Quotient.out a
  set xb : Vec := Quotient.out b
  set xc : Vec := Quotient.out c
  have hdet : det3v xa xb xc ≠ 0 := habc
  have hmem : ({Line.mk xa, Line.mk xb, Line.mk xc} : Finset Line) ⊆ v.M := by
    rw [Line.mk_out, Line.mk_out, Line.mk_out, ← heq]
    exact hv
  have hunit := det_unimodular_of_subset_M v xa xb xc hmem hdet
  let M : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => ![xa, xb, xc] j i
  have hMdet : M.det = det3v xa xb xc := by
    simp only [M, Matrix.det_fin_three, det3v, Matrix.of_apply]
    simp
    ring
  have hMunit : IsUnit M.det := by
    rw [hMdet]; rcases hunit with h | h <;> rw [h] <;> simp
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hMunit, ?_⟩
  rw [heq]
  have e0' : mv (Matrix.GeneralLinearGroup.mk'' M hMunit) e0 = xa := by
    funext i; simp [mv, M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0]
  have e1' : mv (Matrix.GeneralLinearGroup.mk'' M hMunit) e1 = xb := by
    funext i; simp [mv, M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, e1]
  have e2' : mv (Matrix.GeneralLinearGroup.mk'' M hMunit) e2 = xc := by
    funext i; simp [mv, M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, e2]
  simp only [T0set, Finset.smul_finset_insert, Finset.smul_finset_singleton, smul_mk, e0', e1', e2']
  rw [show Line.mk xa = a from Line.mk_out a, show Line.mk xb = b from Line.mk_out b,
    show Line.mk xc = c from Line.mk_out c]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
