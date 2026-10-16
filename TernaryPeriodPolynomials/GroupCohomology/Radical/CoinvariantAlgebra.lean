module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Difference
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Transport
public import TernaryPeriodPolynomials.Polynomial.Integral
public import TernaryPeriodPolynomials.Polynomial.Homogeneous
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section


open MvPolynomial

noncomputable section
namespace TernaryPoly.RadicalCoinvariantAlgebra

abbrev Poly := MvPolynomial (Fin 3) ℚ

def shear (i j : Fin 3) : Poly →ₐ[ℚ] Poly :=
  bind₁ fun k => if k = i then X i - X j else X k

def erase (j : Fin 3) : Poly →ₐ[ℚ] Poly :=
  bind₁ fun k => if k = j then 0 else X k

@[simp] theorem erase_X (i j : Fin 3) :
    erase j (X i) = if i = j then 0 else X i := by simp [erase]

@[simp] theorem shear_X (i j k : Fin 3) :
    shear i j (X k) = if k = i then X i - X j else X k := by simp [shear]

theorem erase_shear (i j : Fin 3) (hij : i ≠ j) (f : Poly) :
    erase j (shear i j f) = erase j f := by
  have h : (erase j).comp (shear i j) = erase j := by
    ext k
    by_cases hk : k = i
    · subst k; simp [hij]
    · simp [hk]
  exact DFunLike.congr_fun h f

theorem exists_sub_erase (j : Fin 3) (f : Poly) :
    ∃ q : Poly, f - erase j f = X j * q := by
  induction f using MvPolynomial.induction_on with
  | C r => exact ⟨0, by simp [erase]⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, add_sub_add_comm, ha, hb, mul_add]⟩
  | mul_X p k hp =>
    by_cases hk : k = j
    · subst k
      exact ⟨p, by simp [mul_comm]⟩
    · obtain ⟨a, ha⟩ := hp
      refine ⟨a * X k, ?_⟩
      rw [map_mul, erase_X, ite_eq_right hk, ← sub_mul, ha, mul_assoc]

theorem erase_eq_zero_iff (j : Fin 3) (f : Poly) :
    erase j f = 0 ↔ ∃ q : Poly, f = X j * q := by
  constructor
  · intro h
    simpa only [h, sub_zero] using exists_sub_erase j f
  · rintro ⟨q, rfl⟩
    simp

theorem exists_taylor_sub_eq_mul {R : Type*} [CommRing R] [Algebra ℚ R]
    (u : R) (p : Polynomial R) :
    ∃ q : Polynomial R, Polynomial.taylor (-u) q - q = u • p := by
  refine ⟨todd u (polyIntegral (-p)), ?_⟩
  rw [taylor_todd, ← map_sub, todd_difference, derivative_polyIntegral]
  simp

theorem finSuccEquiv_shear (j : Fin 2) (f : Poly) :
    finSuccEquiv ℚ 2 (shear 0 j.succ f) =
      Polynomial.taylor (-X j) (finSuccEquiv ℚ 2 f) := by
  have h : (fun k : Fin 3 => if k = 0 then X (0 : Fin 3) - X j.succ else X k) =
      (![X 0 - X j.succ, X 1, X 2] : Fin 3 → Poly) := by
    funext k
    fin_cases k <;> simp
  rw [shear, h]
  fin_cases j
  · exact finSuccEquiv_shift_Y f
  · exact finSuccEquiv_shift_Z f

/-- Every multiple of either coefficient variable is one literal shear difference. -/
theorem exists_shear_sub_eq_mul (j : Fin 2) (p : Poly) :
    ∃ q : Poly, shear 0 j.succ q - q = X j.succ * p := by
  obtain ⟨q, hq⟩ := exists_taylor_sub_eq_mul (X j) (finSuccEquiv ℚ 2 p)
  refine ⟨(finSuccEquiv ℚ 2).symm q, ?_⟩
  apply (finSuccEquiv ℚ 2).injective
  simpa only [map_sub, finSuccEquiv_shear, AlgEquiv.apply_symm_apply,
    map_mul, finSuccEquiv_X_succ, Polynomial.smul_eq_C_mul] using hq

/-- A single shear has exactly the expected polynomial image. -/
theorem exists_shear_sub_iff (j : Fin 2) (p : Poly) :
    (∃ q : Poly, shear 0 j.succ q - q = p) ↔ erase j.succ p = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [map_sub, erase_shear 0 j.succ (Ne.symm (Fin.succ_ne_zero j)), sub_self]
  · intro h
    obtain ⟨q, rfl⟩ := (erase_eq_zero_iff j.succ p).mp h
    exact exists_shear_sub_eq_mul j q

theorem shear_homogeneous (i j : Fin 3) {n : ℕ} {p : Poly}
    (hp : p.IsHomogeneous n) : (shear i j p).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hp
  intro k
  split_ifs
  · exact (isHomogeneous_X ℚ i).sub (isHomogeneous_X ℚ j)
  · exact isHomogeneous_X ℚ k

/-- Homogeneous projection makes the primitive preserve the exact degree. -/
theorem exists_homogeneous_shear_sub_iff (j : Fin 2) {n : ℕ} (p : Poly)
    (hp : p.IsHomogeneous n) :
    (∃ q : Poly, q.IsHomogeneous n ∧ shear 0 j.succ q - q = p) ↔
      erase j.succ p = 0 := by
  constructor
  · rintro ⟨q, _, hq⟩
    exact (exists_shear_sub_iff j p).mp ⟨q, hq⟩
  · intro h
    obtain ⟨q, hq⟩ := (exists_shear_sub_iff j p).mpr h
    refine ⟨homogeneousComponent n q, homogeneousComponent_isHomogeneous n q, ?_⟩
    have h' := congrArg (homogeneousComponent n) hq
    change homogeneousComponent n (bind₁ _ q - q) = homogeneousComponent n p at h'
    rw [map_sub, homogeneousComponent_bind₁_linear] at h'
    · simpa [shear, homogeneousComponent_of_mem hp] using h'
    · intro k
      split_ifs
      · exact (isHomogeneous_X ℚ 0).sub (isHomogeneous_X ℚ j.succ)
      · exact isHomogeneous_X ℚ k

end TernaryPoly.RadicalCoinvariantAlgebra
