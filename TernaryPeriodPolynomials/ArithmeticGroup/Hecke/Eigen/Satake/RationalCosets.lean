module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.LatticeIndex
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.FiberCount
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.LineVectors
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.LineFactorization
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegerReduction

@[expose] public section


/-!
# Rational parabolic coordinates of `GL₃(ℚ)` modulo `GL₃(ℤ)`

Radical coordinates for the plane and line parabolics, conjugation by the Levi factors, the
transposition `τ(x) = w xᵀ w⁻¹` exchanging them, and the rational Iwasawa decompositions
`GL₃(ℚ) = N M GL₃(ℤ)` for both parabolics.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

/-- `GL₃(ℤ)` inside `GL₃(ℚ)`. -/
def Γ : Subgroup RationalGL3 := integralRational.range

/-- Plane radical coordinates. -/
def pU (v : ℚ × ℚ) : RationalGL3 := planeUnipotent v.1 v.2

/-- Line radical coordinates. -/
def lU (v : ℚ × ℚ) : RationalGL3 := lineUnipotent v.1 v.2

theorem pU_add (v w : ℚ × ℚ) : pU (v + w) = pU v * pU w := planeUnipotent_add _ _ _ _

theorem lU_add (v w : ℚ × ℚ) : lU (v + w) = lU v * lU w := lineUnipotent_add _ _ _ _

theorem pU_zero : pU 0 = 1 := by
  have := pU_add 0 0
  simpa using this

theorem lU_zero : lU 0 = 1 := by
  have := lU_add 0 0
  simpa using this

theorem pU_neg (v : ℚ × ℚ) : pU (-v) = (pU v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pU_add, neg_add_cancel, pU_zero]

theorem lU_neg (v : ℚ × ℚ) : lU (-v) = (lU v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← lU_add, neg_add_cancel, lU_zero]

theorem mem_Γ_iff (x : RationalGL3) :
    x ∈ Γ ↔ (∀ i j, ∃ z : ℤ, (z : ℚ) = x.val i j) ∧ ∀ i j, ∃ z : ℤ, (z : ℚ) = (x⁻¹).val i j := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun i j => ⟨k.val i j, rfl⟩, fun i j => ⟨(k⁻¹).val i j, ?_⟩⟩
    rw [← map_inv]; rfl
  · rintro ⟨h1, h2⟩
    choose a ha using h1
    choose b hb using h2
    have hab : Matrix.of a * Matrix.of b = 1 := by
      have : (Matrix.of a).map (Int.castRingHom ℚ) * (Matrix.of b).map (Int.castRingHom ℚ) = 1 := by
        have e1 : (Matrix.of a).map (Int.castRingHom ℚ) = x.val := by ext i j; exact ha i j
        have e2 : (Matrix.of b).map (Int.castRingHom ℚ) = (x⁻¹).val := by ext i j; exact hb i j
        rw [e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [← Matrix.map_mul] at this
      apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
      beta_reduce
      rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨Matrix.of a, Matrix.of b, hab, mul_eq_one_comm.mp hab⟩, ?_⟩
    apply Units.ext
    ext i j
    exact ha i j

theorem pU_mem_Γ (v : ℚ × ℚ) : pU v ∈ Γ ↔ v ∈ zLat := by
  rw [mem_Γ_iff, mem_zLat]
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨h1 0 2, h1 1 2⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hinv : (pU v)⁻¹ = pU (-v) := (pU_neg v).symm
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [pU, planeUnipotent, ← ha, ← hb]
    · rw [hinv]
      fin_cases i <;> fin_cases j <;> simp [pU, planeUnipotent, ← ha, ← hb]
      all_goals first | exact ⟨-a, Int.cast_neg a⟩ | exact ⟨-b, Int.cast_neg b⟩

theorem lU_mem_Γ (v : ℚ × ℚ) : lU v ∈ Γ ↔ v ∈ zLat := by
  rw [mem_Γ_iff, mem_zLat]
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨h1 0 1, h1 0 2⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hinv : (lU v)⁻¹ = lU (-v) := (lU_neg v).symm
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [lU, lineUnipotent, upperUnipotent, ← ha, ← hb]
    · rw [hinv]
      fin_cases i <;> fin_cases j <;> simp [lU, lineUnipotent, upperUnipotent, ← ha, ← hb]
      all_goals first | exact ⟨-a, Int.cast_neg a⟩ | exact ⟨-b, Int.cast_neg b⟩

/-! ### Levi conjugation -/

theorem planeLevi_pU (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) (w : ℚ × ℚ) :
    planeLevi B s * pU w = pU (matHom ((s⁻¹ : ℚˣ).val • B.val) w) * planeLevi B s := by
  have hs : (s : ℚ) ≠ 0 := s.ne_zero
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [pU, planeUnipotent, planeLevi, planeBlock, matHom_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Units.val_inv_eq_inv_val] <;>
    field_simp

theorem matHom_smul_inv (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) (v : ℚ × ℚ) :
    matHom ((s⁻¹ : ℚˣ).val • B.val) (matHom (s.val • (B⁻¹).val) v) = v := by
  rw [← AddMonoidHom.comp_apply, ← matHom_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, matHom_one]
  rfl

theorem matHom_inv_smul (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) (v : ℚ × ℚ) :
    matHom (s.val • (B⁻¹).val) (matHom ((s⁻¹ : ℚˣ).val • B.val) v) = v := by
  rw [← AddMonoidHom.comp_apply, ← matHom_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, matHom_one]
  rfl

/-- Conjugating the plane radical by the Levi. -/
theorem conj_pU (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) (v : ℚ × ℚ) :
    (planeLevi B s)⁻¹ * pU v * planeLevi B s = pU (matHom (s.val • (B⁻¹).val) v) := by
  have := planeLevi_pU B s (matHom (s.val • (B⁻¹).val) v)
  rw [matHom_smul_inv] at this
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  exact this.symm

/-- Line radical moved across the line Levi. -/
theorem lU_lineLevi (d : ℚˣ) (A : GeneralLinearGroup (Fin 2) ℚ) (w : ℚ × ℚ) :
    lU w * lineLevi d A = lineLevi d A * lU (matHom ((d⁻¹ : ℚˣ).val • A.valᵀ) w) := by
  have hd : (d : ℚ) ≠ 0 := d.ne_zero
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lineLevi_val]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [lU, lineUnipotent, upperUnipotent, matHom_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Units.val_inv_eq_inv_val] <;>
    field_simp

/-- Conjugating the line radical by the Levi. -/
theorem conj_lU (d : ℚˣ) (A : GeneralLinearGroup (Fin 2) ℚ) (w : ℚ × ℚ) :
    (lineLevi d A)⁻¹ * lU w * lineLevi d A = lU (matHom ((d⁻¹ : ℚˣ).val • A.valᵀ) w) := by
  rw [mul_assoc, lU_lineLevi, ← mul_assoc, inv_mul_cancel, one_mul]


/-! ### Transposition exchanging the parabolics -/

section Transpose

variable {R : Type*} [CommRing R]

/-- Transpose in `GL₃`. -/
def tr3 (x : GL3 R) : GL3 R :=
  ⟨x.valᵀ, (x⁻¹).valᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

theorem tr3_mul (x y : GL3 R) : tr3 (x * y) = tr3 y * tr3 x := by
  apply Units.ext
  simp [tr3, transpose_mul]

theorem tr3_one : tr3 (1 : GL3 R) = 1 := by
  apply Units.ext; simp [tr3]

/-- `τ(x) = w xᵀ w⁻¹`. -/
def τ (x : GL3 R) : GL3 R := weyl * tr3 x * weyl⁻¹

theorem τ_mul (x y : GL3 R) : τ (x * y) = τ y * τ x := by
  simp only [τ, tr3_mul]; group

theorem τ_one : τ (1 : GL3 R) = 1 := by simp [τ, tr3_one]

theorem τ_inv (x : GL3 R) : τ x⁻¹ = (τ x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← τ_mul, mul_inv_cancel, τ_one]

theorem weyl_map {S : Type*} [CommRing S] (φ : R →+* S) :
    GeneralLinearGroup.map φ (weyl : GL3 R) = weyl := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [weyl, GeneralLinearGroup.map_apply]

theorem τ_map {S : Type*} [CommRing S] (φ : R →+* S) (x : GL3 R) :
    GeneralLinearGroup.map φ (τ x) = τ (GeneralLinearGroup.map φ x) := by
  have htr : GeneralLinearGroup.map φ (tr3 x) = tr3 (GeneralLinearGroup.map φ x) := by
    apply Units.ext; rfl
  simp only [τ, map_mul, map_inv, weyl_map, htr]

theorem tr3_planeLevi (B : GeneralLinearGroup (Fin 2) R) (s : Rˣ) :
    tr3 (planeLevi B s) = planeLevi (RepresentationTheory.transposeGL B) s := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [tr3, planeLevi, planeBlock, RepresentationTheory.transposeGL]

theorem τ_planeLevi (B : GeneralLinearGroup (Fin 2) R) (s : Rˣ) :
    τ (planeLevi B s) = lineLevi s (RepresentationTheory.transposeGL B) := by
  rw [τ, tr3_planeLevi]; rfl

end Transpose

theorem τ_pU (v : ℚ × ℚ) : τ (pU v) = lU v := by
  apply Units.ext
  have hw : ((weyl : GL3 ℚ)⁻¹).val = !![0,1,0;0,0,1;1,0,0] := rfl
  simp only [τ, Units.val_mul, hw]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [tr3, weyl, pU, planeUnipotent, lU, lineUnipotent, upperUnipotent, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem τ_Γ {x : RationalGL3} (hx : x ∈ Γ) : τ x ∈ Γ := by
  obtain ⟨k, rfl⟩ := hx
  exact ⟨τ k, τ_map _ k⟩

/-- **Transposition of a plane coordinate.** -/
theorem τ_plane (v : ℚ × ℚ) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    τ (pU v * planeLevi B s) =
      lU (matHom (s.val • (B⁻¹).val) v) * lineLevi s (RepresentationTheory.transposeGL B) := by
  rw [τ_mul, τ_planeLevi, τ_pU, lU_lineLevi]
  congr 2
  have : (RepresentationTheory.transposeGL B).valᵀ = B.val := by
    simp [RepresentationTheory.transposeGL]
  rw [this, matHom_smul_inv]

/-! ### Rational Iwasawa decompositions -/

theorem plane_iwasawa (x : RationalGL3) :
    ∃ v : ℚ × ℚ, ∃ B : GeneralLinearGroup (Fin 2) ℚ, ∃ s : ℚˣ, ∃ γ ∈ Γ,
      x = pU v * planeLevi B s * γ := by
  obtain ⟨p, κ, hx⟩ := PlaneEisensteinContinuation.IntegerReduction.exists_rational_plane_integral x
  obtain ⟨a, b, s, B, hp⟩ := SphericalDetection.Helpers.planeParabolic_exists_decomposition p
  refine ⟨(a, b), B, s, integralRational κ, ⟨κ, rfl⟩, ?_⟩
  have hL : planeLevi (1 : GeneralLinearGroup (Fin 2) ℚ) s * planeLevi B 1 = planeLevi B s := by
    have := ((planeLeviHom ℚ).map_mul (1, s) (B, 1)).symm
    simp only [Prod.mk_mul_mk, one_mul, mul_one] at this
    exact this
  rw [hx, hp, hL]
  rfl

theorem line_iwasawa (x : RationalGL3) :
    ∃ w : ℚ × ℚ, ∃ d : ℚˣ, ∃ A : GeneralLinearGroup (Fin 2) ℚ, ∃ γ ∈ Γ,
      x = lU w * lineLevi d A * γ := by
  obtain ⟨p, κ, hx⟩ :=
    PlaneEisensteinContinuation.IntegerReduction.exists_rational_plane_integral (theta x)
  have hx' : x = theta p.val * theta (integralRational κ) := by
    rw [← theta_mul, ← hx, theta_theta]
  obtain ⟨a, b, d, A, hq⟩ := lineParabolic_exists_decomposition (theta p.val) (theta_plane p.property)
  refine ⟨(a, b), d, A, theta (integralRational κ), ⟨theta κ, theta_map _ κ⟩, ?_⟩
  rw [hx', hq, lineLevi_mul, mul_one, one_mul]
  rfl

/-! ### Integral Levi parts -/

/-- `GL₂(ℤ)` inside `GL₂(ℚ)`. -/
def Γ2 : Subgroup (GeneralLinearGroup (Fin 2) ℚ) :=
  (GeneralLinearGroup.map (Int.castRingHom ℚ) (n := Fin 2)).range

theorem mem_Γ2_iff (x : GeneralLinearGroup (Fin 2) ℚ) :
    x ∈ Γ2 ↔ (∀ i j, ∃ z : ℤ, (z : ℚ) = x.val i j) ∧ ∀ i j, ∃ z : ℤ, (z : ℚ) = (x⁻¹).val i j := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun i j => ⟨k.val i j, rfl⟩, fun i j => ⟨(k⁻¹).val i j, ?_⟩⟩
    rw [← map_inv]; rfl
  · rintro ⟨h1, h2⟩
    choose a ha using h1
    choose b hb using h2
    have hab : Matrix.of a * Matrix.of b = 1 := by
      have : (Matrix.of a).map (Int.castRingHom ℚ) * (Matrix.of b).map (Int.castRingHom ℚ) = 1 := by
        have e1 : (Matrix.of a).map (Int.castRingHom ℚ) = x.val := by ext i j; exact ha i j
        have e2 : (Matrix.of b).map (Int.castRingHom ℚ) = (x⁻¹).val := by ext i j; exact hb i j
        rw [e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [← Matrix.map_mul] at this
      apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
      beta_reduce
      rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨Matrix.of a, Matrix.of b, hab, mul_eq_one_comm.mp hab⟩, ?_⟩
    apply Units.ext
    ext i j
    exact ha i j

theorem int_unit_of_int_inv {s : ℚˣ} (h1 : ∃ z : ℤ, (z : ℚ) = s.val)
    (h2 : ∃ z : ℤ, (z : ℚ) = (s⁻¹ : ℚˣ).val) : s = 1 ∨ s = -1 := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hab : a * b = 1 := by
    have : (a : ℚ) * b = 1 := by rw [ha, hb, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h | h
  · left; apply Units.ext; rw [← ha, h]; simp
  · right; apply Units.ext; rw [← ha, h]; simp

/-- A plane-parabolic element of `GL₃(ℤ)` has integral Levi part. -/
theorem plane_levi_integral {v : ℚ × ℚ} {B : GeneralLinearGroup (Fin 2) ℚ} {s : ℚˣ}
    (h : pU v * planeLevi B s ∈ Γ) : B ∈ Γ2 ∧ (s = 1 ∨ s = -1) := by
  obtain ⟨h1, h2⟩ := (mem_Γ_iff _).mp h
  have hinv : (pU v * planeLevi B s)⁻¹ = planeLevi B⁻¹ s⁻¹ * pU (-v) := by
    rw [_root_.mul_inv_rev, pU_neg]
    congr 1
  rw [hinv] at h2
  refine ⟨(mem_Γ2_iff B).mpr ⟨fun i j => ?_, fun i j => ?_⟩, int_unit_of_int_inv ?_ ?_⟩
  · obtain ⟨z, hz⟩ := h1 i.castSucc j.castSucc
    refine ⟨z, ?_⟩
    rw [hz]
    fin_cases i <;> fin_cases j <;>
      simp [pU, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  · obtain ⟨z, hz⟩ := h2 i.castSucc j.castSucc
    refine ⟨z, ?_⟩
    rw [hz]
    fin_cases i <;> fin_cases j <;>
      simp [pU, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  · obtain ⟨z, hz⟩ := h1 2 2
    refine ⟨z, ?_⟩
    rw [hz]
    simp [pU, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  · obtain ⟨z, hz⟩ := h2 2 2
    refine ⟨z, ?_⟩
    rw [hz]
    simp [pU, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

end TernaryPeriodPolynomials.HeckeEigen.Satake
