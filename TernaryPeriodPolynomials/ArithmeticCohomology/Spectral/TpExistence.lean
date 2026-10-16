module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AllCorrespondences
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.PrimeCoset
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.Involution

@[expose] public section


/-!
# The `T_p` Hecke correspondence exists

For a prime `p ≠ 3`, the double coset `Γ diag(p,1,1) Γ` of the arithmetic level is a finite union
of cosets `x Γ`: the coset `a · diag(p,1,1) · Γ` (`a ∈ Γ`) depends only on `a mod p`, because for
`a ≡ a' (mod p)` the conjugate `diag(p,1,1)⁻¹ (a⁻¹ a') diag(p,1,1)` is an integral matrix of unit
determinant whose last row is still `e₃*` modulo three (`conj_mem`). Hence
`HeckeCommutativity.ofFinite` gives a `HeckeCorrespondence` with `g = diag(p,1,1)`, and it is away
from three (`exists_Tp`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.HeckeEigen.Satake TernaryPeriodPolynomials.HeckeCommutativity

namespace TernaryPeriodPolynomials.Spectral.TpExistence

open Classical in
/-- The integer matrix of an element of the level (zero outside). -/
def intOf (x : RationalGL3) : Matrix (Fin 3) (Fin 3) ℤ :=
  if h : x ∈ rationalLevel then Classical.choose (int_of_mem_rationalLevel h) else 0

theorem intOf_spec {x : RationalGL3} (h : x ∈ rationalLevel) :
    x.val = (intOf x).map (Int.cast : ℤ → ℚ) ∧ IsUnit (intOf x).det ∧
      ∀ j, ((intOf x 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
  classical
  unfold intOf
  rw [dite_eq_left h]
  exact Classical.choose_spec (int_of_mem_rationalLevel h)

theorem cast_inj {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (h : A.map (Int.cast : ℤ → ℚ) = B.map (Int.cast : ℤ → ℚ)) : A = B := by
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

theorem intOf_mul {x y : RationalGL3} (hx : x ∈ rationalLevel) (hy : y ∈ rationalLevel) :
    intOf (x * y) = intOf x * intOf y := by
  apply cast_inj
  rw [← (intOf_spec (rationalLevel.mul_mem hx hy)).1, Units.val_mul, (intOf_spec hx).1,
    (intOf_spec hy).1, intCast_map_mul3]

theorem intOf_one : intOf 1 = 1 := by
  apply cast_inj
  rw [← (intOf_spec rationalLevel.one_mem).1, Units.val_one]
  ext i j
  simp [Matrix.one_apply]

/-- Reduction modulo `p` of the integer matrix. -/
def red (p : ℕ) (x : RationalGL3) : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  (intOf x).map (Int.cast : ℤ → ZMod p)

variable (p : Nat.Primes)

/-- If `x ≡ y (mod p)` then `x⁻¹ y ≡ 1 (mod p)`. -/
theorem dvd_sub_one {x y : RationalGL3} (hx : x ∈ rationalLevel) (hy : y ∈ rationalLevel)
    (h : red p.val x = red p.val y) (i j : Fin 3) :
    (p.val : ℤ) ∣ intOf (x⁻¹ * y) i j - if i = j then 1 else 0 := by
  have hxi := rationalLevel.inv_mem hx
  have hXX : intOf x⁻¹ * intOf x = 1 := by
    rw [← intOf_mul hxi hx, inv_mul_cancel, intOf_one]
  have e : intOf (x⁻¹ * y) - 1 = intOf x⁻¹ * (intOf y - intOf x) := by
    rw [intOf_mul hxi hy, Matrix.mul_sub, hXX]
  have hdiv : ∀ k l, (p.val : ℤ) ∣ (intOf y - intOf x) k l := by
    intro k l
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p.val).mp
    have := congrFun (congrFun h k) l
    simp only [red, Matrix.map_apply] at this
    simp [Matrix.sub_apply, this]
  have : (p.val : ℤ) ∣ (intOf x⁻¹ * (intOf y - intOf x)) i j := by
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (hdiv k j) _
  rw [← e] at this
  simpa [Matrix.sub_apply, Matrix.one_apply] using this

/-- **Conjugation by `diag(p,1,1)` preserves congruence classes modulo `p`.** -/
theorem conj_mem {x y : RationalGL3} (hx : x ∈ rationalLevel) (hy : y ∈ rationalLevel)
    (h : red p.val x = red p.val y) :
    (gP p.property)⁻¹ * (x⁻¹ * y) * gP p.property ∈ rationalLevel := by
  have hz := rationalLevel.mul_mem (rationalLevel.inv_mem hx) hy
  obtain ⟨hNval, hNdet, hNrow⟩ := intOf_spec hz
  set N := intOf (x⁻¹ * y)
  obtain ⟨q1, hq1⟩ := dvd_sub_one p hx hy h 0 1
  obtain ⟨q2, hq2⟩ := dvd_sub_one p hx hy h 0 2
  simp only [Fin.isValue, show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    ite_false, sub_zero] at hq1 hq2
  have hp0 : (p.val : ℚ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  let M' : Matrix (Fin 3) (Fin 3) ℤ :=
    !![N 0 0, q1, q2; p.val * N 1 0, N 1 1, N 1 2; p.val * N 2 0, N 2 1, N 2 2]
  have hval : ((gP p.property)⁻¹ * (x⁻¹ * y) * gP p.property).val = M'.map (Int.cast : ℤ → ℚ) := by
    rw [Units.val_mul, Units.val_mul, hNval]
    change diagonal ![(p.val : ℚ)⁻¹, 1, 1] * N.map (Int.cast : ℤ → ℚ) * diagonal ![(p.val : ℚ), 1, 1] = _
    ext i j
    simp only [mul_diagonal, diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [M', N, hq1, hq2] <;> field_simp
  apply mem_rationalLevel_of_int _ M' hval
  · have hdet : ((M'.det : ℤ) : ℚ) = ((N.det : ℤ) : ℚ) := by
      rw [← intCast_det, ← hval, ← intCast_det, ← hNval, Units.val_mul, Units.val_mul, det_mul,
        det_mul, mul_comm, ← mul_assoc, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        det_one, one_mul]
    rw [show M'.det = N.det by exact_mod_cast hdet]
    exact hNdet
  · intro j
    have := hNrow j
    fin_cases j <;> simp_all [M']

/-- **The double coset of `diag(p,1,1)` is a finite union of cosets.** -/
theorem dcosetCosets_gP_finite : (dcosetCosets (gP p.property)).Finite := by
  classical
  have : NeZero p.val := ⟨p.property.ne_zero⟩
  let F : Matrix (Fin 3) (Fin 3) (ZMod p.val) → RationalGL3 ⧸ rationalLevel := fun M =>
    if h : ∃ a ∈ rationalLevel, red p.val a = M then
      ((Classical.choose h * gP p.property : RationalGL3) : RationalGL3 ⧸ rationalLevel)
    else ((1 : RationalGL3) : RationalGL3 ⧸ rationalLevel)
  refine (Set.finite_range F).subset ?_
  rintro q ⟨x, ⟨h₁, hh₁, h₂, hh₂, rfl⟩, rfl⟩
  have hex : ∃ a ∈ rationalLevel, red p.val a = red p.val h₁ := ⟨h₁, hh₁, rfl⟩
  refine ⟨red p.val h₁, ?_⟩
  simp only [F, dite_eq_left hex]
  obtain ⟨ha, hred⟩ := Classical.choose_spec hex
  apply QuotientGroup.eq.mpr
  have hc := conj_mem p ha hh₁ hred
  have := rationalLevel.mul_mem hc hh₂
  convert this using 1
  group

theorem integralAtThree_int (z : ℤ) : IntegralAtThree (z : ℚ) :=
  ⟨z, 1, by simp, by simp⟩

/-- **The `T_p` correspondence.** -/
def tp : HeckeCorrespondence := ofFinite (gP p.property) (dcosetCosets_gP_finite p)

theorem tp_g : (tp p).g = gP p.property := rfl

theorem tp_awayThree (hp3 : p.val ≠ 3) : AwayThree (tp p) := by
  have h3 : ((p.val : ℤ) : ZMod 3) ≠ 0 := by
    intro h
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h
    have : (3 : ℕ) ∣ p.val := by exact_mod_cast hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three p.property).mp this).symm
  have hpinv : IntegralAtThree ((p.val : ℚ)⁻¹) := ⟨1, p.val, h3, by simp⟩
  have h0 : IntegralAtThree (0 : ℚ) := by exact_mod_cast integralAtThree_int 0
  have h1 : IntegralAtThree (1 : ℚ) := by exact_mod_cast integralAtThree_int 1
  have hpn : IntegralAtThree (p.val : ℚ) := by exact_mod_cast integralAtThree_int p.val
  refine ⟨fun i j => ⟨?_, ?_⟩, fun j => ?_⟩
  · change IntegralAtThree ((diagonal ![(p.val : ℚ), 1, 1]) i j)
    fin_cases i <;> fin_cases j <;> simpa [diagonal]
  · change IntegralAtThree ((diagonal ![(p.val : ℚ)⁻¹, 1, 1]) i j)
    fin_cases i <;> fin_cases j <;> simpa [diagonal]
  · change IntegralAtThree (((diagonal ![(p.val : ℚ), 1, 1]) 2 j - if j = 2 then 1 else 0) / 3)
    fin_cases j <;> simpa [diagonal]

end TernaryPeriodPolynomials.Spectral.TpExistence
