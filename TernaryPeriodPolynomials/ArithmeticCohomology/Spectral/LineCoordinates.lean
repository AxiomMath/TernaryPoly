module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCosets

@[expose] public section


/-!
# Lower-parabolic coordinates for the good line

The stabilizer of the good line `⟨e₃⟩` in the rational group is the lower plane parabolic
`Q(c, B, d) = l(c) · diag(B, d) = [[B, 0], [c B, d]]` (`c ∈ ℚ²` a row vector, `B ∈ GL₂(ℚ)`,
`d ∈ ℚˣ`). In these coordinates `Q(c,B,d) Q(c',B',d') = Q(c + d c' B⁻¹, B B', d d')` (`Q_mul`), and the
arithmetic stabilizer `Λ₁` of the good line consists of the `Q(3b, m, 1)` with `b ∈ ℤ²`,
`m ∈ GL₂(ℤ)` (`Q_mem_iff`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.LineCoordinates

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets

/-- Row vector times matrix. -/
def vmul (x : ℚ × ℚ) (B : Matrix (Fin 2) (Fin 2) ℚ) : ℚ × ℚ :=
  (x.1 * B 0 0 + x.2 * B 1 0, x.1 * B 0 1 + x.2 * B 1 1)

theorem vmul_add (x y : ℚ × ℚ) (B : Matrix (Fin 2) (Fin 2) ℚ) :
    vmul (x + y) B = vmul x B + vmul y B := by
  simp only [vmul, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  congr 1 <;> ring

theorem vmul_neg (x : ℚ × ℚ) (B : Matrix (Fin 2) (Fin 2) ℚ) : vmul (-x) B = -vmul x B := by
  simp only [vmul, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
  congr 1 <;> ring

theorem vmul_sub (x y : ℚ × ℚ) (B : Matrix (Fin 2) (Fin 2) ℚ) :
    vmul (x - y) B = vmul x B - vmul y B := by
  rw [sub_eq_add_neg, vmul_add, vmul_neg, ← sub_eq_add_neg]

theorem vmul_smul (c : ℚ) (x : ℚ × ℚ) (B : Matrix (Fin 2) (Fin 2) ℚ) :
    vmul (c • x) B = c • vmul x B := by
  simp only [vmul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk]
  congr 1 <;> ring

theorem vmul_zero (B : Matrix (Fin 2) (Fin 2) ℚ) : vmul 0 B = 0 := by simp [vmul]

theorem vmul_mul (x : ℚ × ℚ) (B C : Matrix (Fin 2) (Fin 2) ℚ) :
    vmul x (B * C) = vmul (vmul x B) C := by
  simp only [vmul, Matrix.mul_apply, Fin.sum_univ_two]
  congr 1 <;> ring

theorem vmul_one (x : ℚ × ℚ) : vmul x 1 = x := by simp [vmul]

theorem vmul_inv_cancel (B : GL (Fin 2) ℚ) (x : ℚ × ℚ) :
    vmul (vmul x B.val) (B⁻¹ : GL (Fin 2) ℚ).val = x := by
  rw [← vmul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vmul_one]

theorem vmul_cancel_inv (B : GL (Fin 2) ℚ) (x : ℚ × ℚ) :
    vmul (vmul x (B⁻¹ : GL (Fin 2) ℚ).val) B.val = x := by
  rw [← vmul_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vmul_one]

theorem vmul_injective (B : GL (Fin 2) ℚ) {x y : ℚ × ℚ} (h : vmul x B.val = vmul y B.val) : x = y := by
  have := congrArg (fun z => vmul z (B⁻¹ : GL (Fin 2) ℚ).val) h
  simpa only [vmul_inv_cancel] using this

/-- `Q(c, B, d) = l(c) diag(B, d)`. -/
def Q (c : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) : RationalGL3 :=
  lowerPlaneUnipotent c.1 c.2 * planeLevi B d

theorem Q_val (c : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    (Q c B d).val = !![B.val 0 0, B.val 0 1, 0; B.val 1 0, B.val 1 1, 0;
      (vmul c B.val).1, (vmul c B.val).2, (d : ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, vmul, lowerPlaneUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem Q_mul (c c' : ℚ × ℚ) (B B' : GL (Fin 2) ℚ) (d d' : ℚˣ) :
    Q c B d * Q c' B' d' = Q (c + (d : ℚ) • vmul c' (B⁻¹ : GL (Fin 2) ℚ).val) (B * B') (d * d') := by
  apply Units.ext
  rw [Units.val_mul, Q_val, Q_val, Q_val]
  have hB : (B⁻¹ : GL (Fin 2) ℚ).val * B.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
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
  · linear_combination (-(d : ℚ) * c'.1 * B'.val 0 0) * e00 + (-(d : ℚ) * c'.2 * B'.val 0 0) * e10 +
      (-(d : ℚ) * c'.1 * B'.val 1 0) * e01 + (-(d : ℚ) * c'.2 * B'.val 1 0) * e11
  · linear_combination (-(d : ℚ) * c'.1 * B'.val 0 1) * e00 + (-(d : ℚ) * c'.2 * B'.val 0 1) * e10 +
      (-(d : ℚ) * c'.1 * B'.val 1 1) * e01 + (-(d : ℚ) * c'.2 * B'.val 1 1) * e11

theorem Q_one : Q 0 1 1 = 1 := by
  apply Units.ext
  rw [Q_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vmul]

theorem Q_inv (c : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    (Q c B d)⁻¹ = Q (-((d⁻¹ : ℚˣ) : ℚ) • vmul c B.val) B⁻¹ d⁻¹ := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [Q_mul, inv_mul_cancel, inv_mul_cancel, ← Q_one, inv_inv, neg_smul, neg_add_cancel]

theorem Q_injective {c c' : ℚ × ℚ} {B B' : GL (Fin 2) ℚ} {d d' : ℚˣ} (h : Q c B d = Q c' B' d') :
    c = c' ∧ B = B' ∧ d = d' := by
  have hv := congrArg Units.val h
  rw [Q_val, Q_val] at hv
  have e22 := congrFun (congrFun hv 2) 2
  simp at e22
  have hB : B = B' := by
    apply Units.ext
    ext i j
    have := congrFun (congrFun hv (Fin.castSucc i)) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;> simpa using this
  subst hB
  refine ⟨?_, rfl, Units.ext e22⟩
  apply vmul_injective B
  have e20 := congrFun (congrFun hv 2) 0
  have e21 := congrFun (congrFun hv 2) 1
  simp at e20 e21
  exact Prod.ext e20 e21

theorem lower_eq_Q (a b : ℚ) : lowerPlaneUnipotent a b = Q (a, b) 1 1 := by
  apply Units.ext
  rw [Q_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerPlaneUnipotent, vmul]

theorem levi_eq_Q (B : GL (Fin 2) ℚ) (d : ℚˣ) : planeLevi B d = Q 0 B d := by
  apply Units.ext
  rw [Q_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeLevi, planeBlock, vmul]

/-- Integral row vector times matrix. -/
def ivmul (b : ℤ × ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) : ℤ × ℤ :=
  (b.1 * A 0 0 + b.2 * A 1 0, b.1 * A 0 1 + b.2 * A 1 1)

theorem vmul_icast (b : ℤ × ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    vmul (icast b) (A.map (Int.castRingHom ℚ)) = icast (ivmul b A) := by
  simp [vmul, ivmul, icast]

theorem vmul_integralEmbed (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) :
    vmul (icast b) (integralEmbed m).val = icast (ivmul b m.val) := by
  rw [integralEmbed_val, vmul_icast]

theorem ivmul_mul (b : ℤ × ℤ) (A A' : Matrix (Fin 2) (Fin 2) ℤ) :
    ivmul b (A * A') = ivmul (ivmul b A) A' := by
  simp only [ivmul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp <;> ring

theorem ivmul_one (b : ℤ × ℤ) : ivmul b 1 = b := by simp [ivmul]

theorem ivmul_inv_cancel (m : GL (Fin 2) ℤ) (b : ℤ × ℤ) :
    ivmul (ivmul b m.val) (m⁻¹ : GL (Fin 2) ℤ).val = b := by
  rw [← ivmul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ivmul_one]

theorem ivmul_cancel_inv (m : GL (Fin 2) ℤ) (b : ℤ × ℤ) :
    ivmul (ivmul b (m⁻¹ : GL (Fin 2) ℤ).val) m.val = b := by
  rw [← ivmul_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ivmul_one]

/-- The arithmetic stabilizer of the good line. -/
abbrev Λ₁ : Subgroup RationalGL3 := flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)

/-- The integral elements `Q(3b, m, 1)`. -/
def Qint (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) : RationalGL3 := Q ((3 : ℚ) • icast b) (integralEmbed m) 1

theorem map_goodBlocks (f s : ℤ) (m : GL (Fin 2) ℤ) :
    GeneralLinearGroup.map (Int.castRingHom ℚ) (planeLevi m 1 * lowerPlaneUnipotent (3 * f) (3 * s)) =
      Qint (ivmul (f, s) (m⁻¹ : GL (Fin 2) ℤ).val) m := by
  rw [map_mul, map_planeLevi_one, map_lowerPlaneUnipotent, levi_eq_Q, lower_eq_Q, Q_mul, Qint]
  have h : ((Int.castRingHom ℚ (3 * f), Int.castRingHom ℚ (3 * s)) : ℚ × ℚ) = (3 : ℚ) • icast (f, s) := by
    simp [icast]
  rw [h, mul_one, mul_one, Units.val_one, one_smul, zero_add, vmul_smul,
    show (GeneralLinearGroup.map (Int.castRingHom ℚ) m) = integralEmbed m from rfl, ← map_inv,
    vmul_integralEmbed]

theorem Qint_mem (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) : Qint b m ∈ Λ₁ := by
  have h := map_goodBlocks (ivmul b m.val).1 (ivmul b m.val).2 m
  rw [show (((ivmul b m.val).1, (ivmul b m.val).2) : ℤ × ℤ) = ivmul b m.val from rfl,
    ivmul_inv_cancel] at h
  rw [← h]
  exact (goodLine_stabilizer_blocks_iff _).mpr ⟨_, _, m, rfl⟩

theorem mem_Λ₁_iff (g : RationalGL3) : g ∈ Λ₁ ↔ ∃ b m, g = Qint b m := by
  rw [goodLine_stabilizer_blocks_iff]
  constructor
  · rintro ⟨f, s, m, rfl⟩
    exact ⟨_, m, map_goodBlocks f s m⟩
  · rintro ⟨b, m, rfl⟩
    have h := map_goodBlocks (ivmul b m.val).1 (ivmul b m.val).2 m
    rw [show (((ivmul b m.val).1, (ivmul b m.val).2) : ℤ × ℤ) = ivmul b m.val from rfl,
      ivmul_inv_cancel] at h
    exact ⟨_, _, m, h.symm⟩

/-- **Membership in `Λ₁` in coordinates.** -/
theorem Q_mem_iff (c : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    Q c B d ∈ Λ₁ ↔ d = 1 ∧ (∃ b : ℤ × ℤ, c = (3 : ℚ) • icast b) ∧
      ∃ m : GL (Fin 2) ℤ, B = integralEmbed m := by
  rw [mem_Λ₁_iff]
  constructor
  · rintro ⟨b, m, h⟩
    obtain ⟨h1, h2, h3⟩ := Q_injective h
    exact ⟨h3, ⟨b, h1⟩, ⟨m, h2⟩⟩
  · rintro ⟨rfl, ⟨b, rfl⟩, ⟨m, rfl⟩⟩
    exact ⟨b, m, rfl⟩

end TernaryPeriodPolynomials.Spectral.LineCoordinates
