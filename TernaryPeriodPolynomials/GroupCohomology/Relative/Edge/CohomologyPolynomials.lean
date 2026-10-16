module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantAlgebra
public import TernaryPeriodPolynomials.Polynomial.Translation
public import TernaryPeriodPolynomials.Polynomial.Parity
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.RelativeEdgeCohomologyPolynomials
open RadicalCoinvariantAlgebra

/-- A nontrivial first-coordinate shear forces independence of that coordinate. -/
lemma shear_fixed_erase (j : Fin 2) (p : Poly) (h : shear 0 j.succ p = p) :
    erase 0 p = p := by
  have ht : Polynomial.taylor (-X j) (finSuccEquiv ℚ 2 p) = finSuccEquiv ℚ 2 p := by
    rw [← finSuccEquiv_shear, h]
  have hc := polynomial_eq_constant_of_translation (finSuccEquiv ℚ 2 p) (-X j)
    (by simp) ht
  have he (q : MvPolynomial (Fin 2) ℚ) :
      finSuccEquiv ℚ 2 (rename Fin.succ q) = Polynomial.C q := by
    induction q using MvPolynomial.induction_on with
    | C r => simp [finSuccEquiv_apply]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, rename_X, finSuccEquiv_X_succ, hp]
  have hp : p = rename Fin.succ ((finSuccEquiv ℚ 2 p).coeff 0) :=
    (finSuccEquiv ℚ 2).injective (hc.trans (he _).symm)
  rw [hp]
  have he' (q : MvPolynomial (Fin 2) ℚ) : erase 0 (rename Fin.succ q) = rename Fin.succ q := by
    induction q using MvPolynomial.induction_on with
    | C r => simp [erase]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp [hp]
  exact he' _

lemma erase_idempotent (i : Fin 3) (p : Poly) : erase i (erase i p) = erase i p := by
  have he : (erase i).comp (erase i) = erase i := by
    ext k
    by_cases hk : k = i <;> simp [hk]
  exact DFunLike.congr_fun he p

lemma erase_homogeneous (i : Fin 3) {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    (erase i p).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hp
  intro k
  split_ifs
  · exact isHomogeneous_zero _ _ _
  · exact isHomogeneous_X ℚ k

/-- A rational step retains the actual root-lattice parameter. -/
def shearStep (i j : Fin 3) (c : ℚ) : Poly →ₐ[ℚ] Poly :=
  bind₁ fun k => if k=i then X i - C c * X j else X k

@[simp] lemma shearStep_X (i j k : Fin 3) (c : ℚ) :
    shearStep i j c (X k) = if k=i then X i-C c*X j else X k := by simp [shearStep]

@[simp] lemma shearStep_one (i j : Fin 3) : shearStep i j 1 = shear i j := by
  ext k
  simp [shearStep, shear]

lemma erase_shearStep (i j : Fin 3) (hij : i ≠ j) (c : ℚ) (p : Poly) :
    erase j (shearStep i j c p) = erase j p := by
  have he : (erase j).comp (shearStep i j c) = erase j := by
    ext k
    by_cases hk : k=i
    · subst k; simp [hij]
    · simp [hk]
  exact DFunLike.congr_fun he p

lemma erase_comm_shearStep (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (c : ℚ) (p : Poly) :
    erase k (shearStep i j c p) = shearStep i j c (erase k p) := by
  have he : (erase k).comp (shearStep i j c) = (shearStep i j c).comp (erase k) := by
    ext l
    by_cases hli : l=i
    · subst l; simp [hki.symm, hkj.symm]
    · by_cases hlk : l=k
      · subst l; simp [hki]
      · simp [hli, hlk]
  exact DFunLike.congr_fun he p

lemma first_shearStep_fixed (j : Fin 3) (c : ℚ) (p : Poly) (hp : erase 0 p = p) :
    shearStep 0 j c p = p := by
  have he : (shearStep 0 j c).comp (erase 0) = erase 0 := by
    ext k
    by_cases hk : k=0 <;> simp [hk]
  rw [← hp]
  exact DFunLike.congr_fun he p

lemma finSuccEquiv_shearStep (j : Fin 2) (c : ℚ) (p : Poly) :
    finSuccEquiv ℚ 2 (shearStep 0 j.succ c p) =
      Polynomial.taylor (-(C c * X j)) (finSuccEquiv ℚ 2 p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [shearStep, finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    simp only [map_mul, Polynomial.taylor_mul, hp]
    apply congrArg (fun q : Polynomial (MvPolynomial (Fin 2) ℚ) =>
      Polynomial.taylor (-(C c * X j)) (finSuccEquiv ℚ 2 p) * q)
    refine Fin.cases ?_ (fun l => ?_) k
    · simp [shearStep, finSuccEquiv_apply, sub_eq_add_neg]
    · simp [shearStep, finSuccEquiv_apply]

/-- The rational step is divided in the coefficients, never in the matrix lattice. -/
lemma exists_first_shearStep (j : Fin 2) (c : ℚ) (hc : c ≠ 0) (p : Poly)
    (hp : erase j.succ p = 0) : ∃ q, shearStep 0 j.succ c q-q=p := by
  obtain ⟨r, rfl⟩ := (erase_eq_zero_iff j.succ p).mp hp
  obtain ⟨q, hq⟩ := exists_taylor_sub_eq_mul (C c * X j)
    (Polynomial.C (C c⁻¹) * finSuccEquiv ℚ 2 r)
  refine ⟨(finSuccEquiv ℚ 2).symm q, ?_⟩
  apply (finSuccEquiv ℚ 2).injective
  simp only [map_sub, finSuccEquiv_shearStep, AlgEquiv.apply_symm_apply, map_mul,
    finSuccEquiv_X_succ]
  rw [hq, Polynomial.smul_eq_C_mul]
  have he : (C c : MvPolynomial (Fin 2) ℚ) * C c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  calc
    _ = Polynomial.C ((C c*C c⁻¹)*X j) * finSuccEquiv ℚ 2 r := by
      simp only [map_mul]
      ring
    _ = _ := by rw [he, one_mul]

lemma rename_shearStep (e : Fin 3 ≃ Fin 3) (i j : Fin 3) (c : ℚ) (p : Poly) :
    rename e (shearStep i j c p) = shearStep (e i) (e j) c (rename e p) := by
  have he : (rename e).comp (shearStep i j c) =
      (shearStep (e i) (e j) c).comp (rename e) := by
    ext k
    simp only [AlgHom.comp_apply, shearStep_X, rename_X]
    by_cases hk : k=i
    · subst k; simp
    · simp [hk, e.injective.ne hk]
  exact DFunLike.congr_fun he p

lemma rename_erase (e : Fin 3 ≃ Fin 3) (j : Fin 3) (p : Poly) :
    rename e (erase j p) = erase (e j) (rename e p) := by
  have he : (rename e).comp (erase j) = (erase (e j)).comp (rename e) := by
    ext k
    simp only [AlgHom.comp_apply, erase_X, rename_X]
    by_cases hk : k=j
    · subst k; simp
    · simp [hk, e.injective.ne hk]
  exact DFunLike.congr_fun he p

lemma exists_shearStep (i j : Fin 3) (hij : i ≠ j) (c : ℚ) (hc : c ≠ 0)
    (p : Poly) (hp : erase j p = 0) : ∃ q, shearStep i j c q-q=p := by
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have hi : e i = 0 := Equiv.swap_apply_right _ _
  have hj : e j ≠ 0 := by rw [← hi]; exact e.injective.ne hij.symm
  obtain ⟨j', hj'⟩ := Fin.eq_succ_of_ne_zero hj
  have he : erase j'.succ (rename e p) = 0 := by
    rw [← hj', ← rename_erase, hp, map_zero]
  obtain ⟨q,hq⟩ := exists_first_shearStep j' c hc (rename e p) he
  refine ⟨rename e.symm q, ?_⟩
  have hq' := congrArg (rename e.symm) hq
  rw [map_sub, rename_shearStep] at hq'
  have h0 : e.symm 0 = i := by rw [← hi]; exact e.symm_apply_apply i
  have hj0 : e.symm j'.succ = j := by rw [← hj']; exact e.symm_apply_apply j
  simpa only [h0, hj0, rename_rename, e.symm_comp_self, rename_id_apply] using hq'

lemma shearStep_linear (i j k : Fin 3) (c : ℚ) :
    (if k=i then X i-C c*X j else (X k : Poly)).IsHomogeneous 1 := by
  split_ifs
  · exact (isHomogeneous_X ℚ i).sub ((isHomogeneous_X ℚ j).C_mul c)
  · exact isHomogeneous_X ℚ k

lemma exists_homogeneous_shearStep (i j : Fin 3) (hij : i ≠ j) (c : ℚ) (hc : c ≠ 0)
    {n : ℕ} (p : Poly) (hn : p.IsHomogeneous n) (hp : erase j p = 0) :
    ∃ q, q.IsHomogeneous n ∧ shearStep i j c q-q=p := by
  obtain ⟨q,hq⟩ := exists_shearStep i j hij c hc p hp
  refine ⟨homogeneousComponent n q, homogeneousComponent_isHomogeneous n q, ?_⟩
  have h := congrArg (homogeneousComponent n) hq
  change homogeneousComponent n (bind₁ _ q - q) = homogeneousComponent n p at h
  rw [map_sub, homogeneousComponent_bind₁_linear _ (fun k => shearStep_linear i j k c)] at h
  simpa [shearStep, homogeneousComponent_of_mem hn] using h

/-- Integrating inside the binary coefficient subspace preserves killed roots. -/
lemma exists_independent_shearStep (i j : Fin 3) (hij : i ≠ j)
    (hi : 0 ≠ i) (hj : 0 ≠ j) (c : ℚ) (hc : c ≠ 0)
    {n : ℕ} (p : Poly) (hn : p.IsHomogeneous n)
    (hp : erase j p = 0) (h0 : erase 0 p = p) :
    ∃ q, q.IsHomogeneous n ∧ erase 0 q = q ∧ shearStep i j c q-q=p := by
  obtain ⟨q,hqn,hq⟩ := exists_homogeneous_shearStep i j hij c hc p hn hp
  refine ⟨erase 0 q, erase_homogeneous 0 hqn, erase_idempotent 0 q, ?_⟩
  have h := congrArg (erase 0) hq
  simpa only [map_sub, erase_comm_shearStep i j 0 hi hj, h0] using h

end TernaryPoly.RelativeEdgeCohomologyPolynomials
