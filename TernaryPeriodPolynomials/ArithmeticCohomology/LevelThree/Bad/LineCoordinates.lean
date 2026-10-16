module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LineCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Cosets

@[expose] public section


/-!
# Upper line-parabolic coordinates for the bad line

The stabilizer of the bad line `ℤ e₁` in `GL₃(ℚ)` is the upper line parabolic
`R(w, a, B) = u(w) · diag(a, B) = [[a, w B], [0, B]]`
(`w ∈ ℚ²` a row vector, `a ∈ ℚˣ`, `B ∈ GL₂(ℚ)`). In these coordinates
`R(w,a,B) R(w',a',B') = R(w + a · w' B⁻¹, a a', B B')` (`R_mul`).

The arithmetic stabilizer `ΛB = fixedPointLevel rationalLevel standardBadLine` (the stabilizer of
the bad-line cusp `cuspFlag .line false`) is Sol's split extension `ℤ² ⋊ (ℤˣ × Γ₁'(3))` via
`ψ = standardBadLineSemidirectEquiv`, and `ψ ⟨x, (e, A)⟩ = R(x, e, A)` (`psi_val`). Hence
`R(w, a, B) ∈ ΛB` iff `w ∈ ℤ²`, `a = ±1` and `B ∈ Γ₁'(3)` (`R_mem_iff`). The radical and Levi
elements are `rad x = R(x, 1, 1)` and `lev (e, A) = R(0, e, A)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineCoordinates

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets

/-! ### Rational coordinates -/

/-- `R(w, a, B) = u(w) diag(a, B) = [[a, w B], [0, B]]`. -/
def R (w : ℚ × ℚ) (a : ℚˣ) (B : GL (Fin 2) ℚ) : RationalGL3 :=
  lineUnipotent w.1 w.2 * lineLevi a B

theorem R_val (w : ℚ × ℚ) (a : ℚˣ) (B : GL (Fin 2) ℚ) :
    (R w a B).val = !![(a : ℚ), (vmul w B.val).1, (vmul w B.val).2;
      0, B.val 0 0, B.val 0 1; 0, B.val 1 0, B.val 1 1] := by
  rw [R, Units.val_mul, lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineUnipotent, upperUnipotent, vmul, Matrix.mul_apply, Fin.sum_univ_three]

theorem R_mul (w w' : ℚ × ℚ) (a a' : ℚˣ) (B B' : GL (Fin 2) ℚ) :
    R w a B * R w' a' B' = R (w + (a : ℚ) • vmul w' (B⁻¹ : GL (Fin 2) ℚ).val) (a * a') (B * B') := by
  apply Units.ext
  rw [Units.val_mul, R_val, R_val, R_val]
  have hB : (B⁻¹ : GL (Fin 2) ℚ).val * B.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e00 := congrFun (congrFun hB 0) 0
  have e01 := congrFun (congrFun hB 0) 1
  have e10 := congrFun (congrFun hB 1) 0
  have e11 := congrFun (congrFun hB 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Fin.isValue,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  simp only [Matrix.coe_units_inv] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, vmul, Units.val_mul]
  · linear_combination (-(a : ℚ) * w'.1 * B'.val 0 0) * e00 +
      (-(a : ℚ) * w'.2 * B'.val 0 0) * e10 + (-(a : ℚ) * w'.1 * B'.val 1 0) * e01 +
      (-(a : ℚ) * w'.2 * B'.val 1 0) * e11
  · linear_combination (-(a : ℚ) * w'.1 * B'.val 0 1) * e00 +
      (-(a : ℚ) * w'.2 * B'.val 0 1) * e10 + (-(a : ℚ) * w'.1 * B'.val 1 1) * e01 +
      (-(a : ℚ) * w'.2 * B'.val 1 1) * e11

theorem R_one : R 0 1 1 = 1 := by
  apply Units.ext
  rw [R_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vmul]

theorem R_inv (w : ℚ × ℚ) (a : ℚˣ) (B : GL (Fin 2) ℚ) :
    (R w a B)⁻¹ = R (-((a⁻¹ : ℚˣ) : ℚ) • vmul w B.val) a⁻¹ B⁻¹ := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [R_mul, inv_mul_cancel, inv_mul_cancel, ← R_one, inv_inv, neg_smul, neg_add_cancel]

theorem R_injective {w w' : ℚ × ℚ} {a a' : ℚˣ} {B B' : GL (Fin 2) ℚ}
    (h : R w a B = R w' a' B') : w = w' ∧ a = a' ∧ B = B' := by
  have hv := congrArg Units.val h
  rw [R_val, R_val] at hv
  have e00 := congrFun (congrFun hv 0) 0
  simp at e00
  have hB : B = B' := by
    apply Units.ext
    ext i j
    have := congrFun (congrFun hv (Fin.succ i)) (Fin.succ j)
    fin_cases i <;> fin_cases j <;> simpa using this
  subst hB
  refine ⟨?_, Units.ext e00, rfl⟩
  apply vmul_injective B
  have e01 := congrFun (congrFun hv 0) 1
  have e02 := congrFun (congrFun hv 0) 2
  simp at e01 e02
  exact Prod.ext e01 e02

/-! ### The arithmetic stabilizer -/

/-- The arithmetic stabilizer of the bad line (`= cuspLevel .line false`). -/
abbrev ΛB : Subgroup RationalGL3 := fixedPointLevel rationalLevel standardBadLine

/-- Sol's identification `ℤ² ⋊ (ℤˣ × Γ₁'(3)) ≃* ΛB`. -/
abbrev ψ : BadLineSemidirect ≃* ΛB := standardBadLineSemidirectEquiv

/-- `ℤˣ → ℚˣ`. -/
abbrev ucast : ℤˣ →* ℚˣ := Units.map (Int.castRingHom ℚ)

theorem ucast_val (e : ℤˣ) : ((ucast e : ℚˣ) : ℚ) = ((e : ℤ) : ℚ) := rfl

theorem psi_inl_val (x : Multiplicative (ℤ × ℤ)) :
    (ψ (SemidirectProduct.inl x) : RationalGL3) = R (icast x.toAdd) 1 1 := by
  apply Units.ext
  have h : (ψ (SemidirectProduct.inl x) : RationalGL3).val =
      (lineUnipotent x.toAdd.1 x.toAdd.2 : GL (Fin 3) ℤ).val.map (Int.castRingHom ℚ) := by
    change (standardBadLineSemidirectEquiv (SemidirectProduct.inl x)).val.val = _
    rw [standardBadLineSemidirectEquiv_inl]
    rfl
  rw [h, R_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lineUnipotent, upperUnipotent, vmul, icast]

theorem psi_inr_val (m : ℤˣ × binaryArithmeticLevel) :
    (ψ (SemidirectProduct.inr m) : RationalGL3) = R 0 (ucast m.1) (levelEmbed m.2) := by
  apply Units.ext
  have h : (ψ (SemidirectProduct.inr m) : RationalGL3).val =
      (lineLevi (m.1) (m.2.val)).val.map (Int.castRingHom ℚ) := by
    change (integralBadLineStabilizerEquiv
      (integralBadLineRadicalEmbedding 1 * integralBadLineLeviSection m)).val.val = _
    rw [map_one, one_mul]
    rfl
  rw [h, R_val, lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vmul, levelEmbed_apply, integralEmbed_val]

theorem psi_val (g : BadLineSemidirect) :
    (ψ g : RationalGL3) = R (icast g.left.toAdd) (ucast g.right.1) (levelEmbed g.right.2) := by
  rw [← SemidirectProduct.inl_left_mul_inr_right g, map_mul, Subgroup.coe_mul, psi_inl_val,
    psi_inr_val, R_mul]
  simp [vmul_zero]

/-- **Membership in `ΛB` in coordinates.** -/
theorem R_mem_iff (w : ℚ × ℚ) (a : ℚˣ) (B : GL (Fin 2) ℚ) :
    R w a B ∈ ΛB ↔ ∃ (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel),
      w = icast x ∧ a = ucast e ∧ B = levelEmbed A := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := ψ.surjective ⟨_, h⟩
    have hv := congrArg Subtype.val hg
    rw [psi_val] at hv
    obtain ⟨h1, h2, h3⟩ := R_injective hv
    exact ⟨g.left.toAdd, g.right.1, g.right.2, h1.symm, h2.symm, h3.symm⟩
  · rintro ⟨x, e, A, rfl, rfl, rfl⟩
    have h := (ψ ⟨Multiplicative.ofAdd x, (e, A)⟩).property
    rw [psi_val] at h
    exact h

/-- The radical element `rad x = R(x, 1, 1)`. -/
def rad (x : ℤ × ℤ) : ΛB := ψ (SemidirectProduct.inl (Multiplicative.ofAdd x))

/-- The Levi element `lev (e, A) = R(0, e, A)`. -/
def lev (m : ℤˣ × binaryArithmeticLevel) : ΛB := ψ (SemidirectProduct.inr m)

theorem rad_val (x : ℤ × ℤ) : (rad x : RationalGL3) = R (icast x) 1 1 := psi_inl_val _

theorem lev_val (m : ℤˣ × binaryArithmeticLevel) :
    (lev m : RationalGL3) = R 0 (ucast m.1) (levelEmbed m.2) := psi_inr_val _

theorem rad_add (x y : ℤ × ℤ) : rad (x + y) = rad x * rad y := by
  rw [rad, rad, rad, ← map_mul, ← map_mul]
  rfl

theorem rad_zero : rad 0 = 1 := by
  rw [rad, ofAdd_zero, map_one, map_one]

theorem lev_mul (m m' : ℤˣ × binaryArithmeticLevel) : lev (m * m') = lev m * lev m' := by
  rw [lev, lev, lev, ← map_mul, ← map_mul]

theorem lev_one : lev 1 = 1 := by
  rw [lev, map_one, map_one]

end TernaryPeriodPolynomials.LevelThree.BadLineCoordinates
