module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.FlagBlocks

@[expose] public section


/-!
# Parabolic coordinates of the rational plane parabolic

Every element of the rational plane parabolic is `P(x, B, d) = u(x) · diag(B, d)` with
`x ∈ ℚ²`, `B ∈ GL₂(ℚ)`, `d ∈ ℚˣ`. In these coordinates
`P(x,B,d) P(y,C,e) = P(x + d⁻¹ B y, BC, de)` (`P_mul`) and
`P(x,B,d)⁻¹ = P(-d B⁻¹ x, B⁻¹, d⁻¹)` (`P_inv`), and the stabilizer `Λ₀` of the identity plane in
the arithmetic level consists exactly of `P(b, m, 1)` with `b ∈ ℤ²`, `m ∈ GL₂(ℤ)` (`P_mem_iff`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.PlaneCoordinates

/-- Matrix–vector product on `ℚ × ℚ`. -/
def bmul (B : Matrix (Fin 2) (Fin 2) ℚ) (x : ℚ × ℚ) : ℚ × ℚ :=
  (B 0 0 * x.1 + B 0 1 * x.2, B 1 0 * x.1 + B 1 1 * x.2)

theorem bmul_add (B : Matrix (Fin 2) (Fin 2) ℚ) (x y : ℚ × ℚ) :
    bmul B (x + y) = bmul B x + bmul B y := by
  simp only [bmul, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  congr 1 <;> ring

theorem bmul_neg (B : Matrix (Fin 2) (Fin 2) ℚ) (x : ℚ × ℚ) : bmul B (-x) = -bmul B x := by
  simp only [bmul, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
  congr 1 <;> ring

theorem bmul_sub (B : Matrix (Fin 2) (Fin 2) ℚ) (x y : ℚ × ℚ) :
    bmul B (x - y) = bmul B x - bmul B y := by
  rw [sub_eq_add_neg, bmul_add, bmul_neg, ← sub_eq_add_neg]

theorem bmul_smul (B : Matrix (Fin 2) (Fin 2) ℚ) (c : ℚ) (x : ℚ × ℚ) :
    bmul B (c • x) = c • bmul B x := by
  simp only [bmul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk]
  congr 1 <;> ring

theorem bmul_mul (B C : Matrix (Fin 2) (Fin 2) ℚ) (x : ℚ × ℚ) :
    bmul (B * C) x = bmul B (bmul C x) := by
  simp only [bmul, Matrix.mul_apply, Fin.sum_univ_two]
  congr 1 <;> ring

theorem bmul_one (x : ℚ × ℚ) : bmul 1 x = x := by
  simp [bmul]

theorem bmul_inv_cancel (B : GL (Fin 2) ℚ) (x : ℚ × ℚ) :
    bmul (B⁻¹ : GL (Fin 2) ℚ).val (bmul B.val x) = x := by
  rw [← bmul_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, bmul_one]

theorem bmul_cancel_inv (B : GL (Fin 2) ℚ) (x : ℚ × ℚ) :
    bmul B.val (bmul (B⁻¹ : GL (Fin 2) ℚ).val x) = x := by
  rw [← bmul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, bmul_one]

/-- `P(x, B, d) = u(x) diag(B, d)`. -/
def P (x : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) : RationalGL3 :=
  planeUnipotent x.1 x.2 * planeLevi B d

theorem P_val (x : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    (P x B d).val = !![B.val 0 0, B.val 0 1, x.1 * d; B.val 1 0, B.val 1 1, x.2 * d; 0, 0, (d : ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem P_mul (x y : ℚ × ℚ) (B C : GL (Fin 2) ℚ) (d e : ℚˣ) :
    P x B d * P y C e = P (x + (d⁻¹ : ℚˣ).val • bmul B.val y) (B * C) (d * e) := by
  have hd : (d : ℚ) ≠ 0 := d.ne_zero
  apply Units.ext
  rw [Units.val_mul, P_val, P_val, P_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, bmul, Units.val_inv_eq_inv_val] <;>
    field_simp <;> ring

theorem P_one : P 0 1 1 = 1 := by
  apply Units.ext
  rw [P_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem P_inv (x : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    (P x B d)⁻¹ = P (-(d : ℚ) • bmul (B⁻¹ : GL (Fin 2) ℚ).val x) B⁻¹ d⁻¹ := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [P_mul, inv_mul_cancel, inv_mul_cancel, ← P_one]
  congr 1
  rw [inv_inv, neg_smul, neg_add_cancel]

theorem P_injective {x y : ℚ × ℚ} {B C : GL (Fin 2) ℚ} {d e : ℚˣ} (h : P x B d = P y C e) :
    x = y ∧ B = C ∧ d = e := by
  have hv := congrArg Units.val h
  rw [P_val, P_val] at hv
  have e22 := congrFun (congrFun hv 2) 2
  simp at e22
  have hde : d = e := Units.ext e22
  subst hde
  have hd : (d : ℚ) ≠ 0 := d.ne_zero
  refine ⟨?_, ?_, rfl⟩
  · have e02 := congrFun (congrFun hv 0) 2
    have e12 := congrFun (congrFun hv 1) 2
    simp at e02 e12
    ext
    · exact e02
    · exact e12
  · apply Units.ext
    ext i j
    have := congrFun (congrFun hv (Fin.castSucc i)) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;> simpa using this

/-- The arithmetic stabilizer of the identity plane. -/
abbrev Λ₀ : Subgroup RationalGL3 :=
  flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))

/-- The integral elements `P(b, m, 1)`. -/
def Pint (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) : RationalGL3 :=
  P ((b.1 : ℚ), (b.2 : ℚ)) (GeneralLinearGroup.map (Int.castRingHom ℚ) m) 1

theorem map_blocks (b₁ b₂ : ℤ) (m : GL (Fin 2) ℤ) :
    GeneralLinearGroup.map (Int.castRingHom ℚ) (planeUnipotent b₁ b₂ * planeLevi m 1) =
      Pint (b₁, b₂) m := by
  apply Units.ext
  rw [Pint, P_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem Pint_mem (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) : Pint b m ∈ Λ₀ := by
  rw [← map_blocks]
  exact (identityPlane_stabilizer_blocks_iff _).mpr ⟨b.1, b.2, m, rfl⟩

theorem mem_Λ₀_iff (g : RationalGL3) : g ∈ Λ₀ ↔ ∃ b m, g = Pint b m := by
  rw [identityPlane_stabilizer_blocks_iff]
  constructor
  · rintro ⟨b₁, b₂, m, rfl⟩
    exact ⟨(b₁, b₂), m, map_blocks b₁ b₂ m⟩
  · rintro ⟨b, m, rfl⟩
    exact ⟨b.1, b.2, m, (map_blocks b.1 b.2 m).symm⟩

/-- **Membership in `Λ₀` in coordinates.** -/
theorem P_mem_iff (x : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    P x B d ∈ Λ₀ ↔ d = 1 ∧ (∃ b : ℤ × ℤ, x = ((b.1 : ℚ), (b.2 : ℚ))) ∧
      ∃ m : GL (Fin 2) ℤ, B = GeneralLinearGroup.map (Int.castRingHom ℚ) m := by
  rw [mem_Λ₀_iff]
  constructor
  · rintro ⟨b, m, h⟩
    obtain ⟨h1, h2, h3⟩ := P_injective h
    exact ⟨h3, ⟨b, h1⟩, ⟨m, h2⟩⟩
  · rintro ⟨rfl, ⟨b, rfl⟩, ⟨m, rfl⟩⟩
    exact ⟨b, m, rfl⟩

end TernaryPeriodPolynomials.Spectral.PlaneCoordinates
