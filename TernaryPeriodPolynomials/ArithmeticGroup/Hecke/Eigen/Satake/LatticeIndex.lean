module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.IntegerSmith
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.IntegerCartan

@[expose] public section


/-!
# Indices of rational lattices in `ℚ²`

For an invertible rational `2 × 2` matrix `A`, let `L = A ℤ²`. Then
`[L : L ∩ ℤ²] · |det A| = [ℤ² : L ∩ ℤ²]`. This is the modulus factor of the Satake comparison.
The proof reduces to diagonal matrices by the integer Smith normal form.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open Matrix

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

/-- The integer lattice `ℤ² ⊂ ℚ²`. -/
def zLat : AddSubgroup (ℚ × ℚ) :=
  (AddSubgroup.zmultiples (1 : ℚ)).prod (AddSubgroup.zmultiples (1 : ℚ))

theorem mem_zmultiples_one {x : ℚ} : x ∈ AddSubgroup.zmultiples (1 : ℚ) ↔ ∃ z : ℤ, (z : ℚ) = x := by
  rw [AddSubgroup.mem_zmultiples_iff]
  simp

theorem mem_zLat {v : ℚ × ℚ} : v ∈ zLat ↔ (∃ z : ℤ, (z : ℚ) = v.1) ∧ ∃ z : ℤ, (z : ℚ) = v.2 := by
  rw [zLat, AddSubgroup.mem_prod, mem_zmultiples_one, mem_zmultiples_one]

/-- The additive map of a rational `2 × 2` matrix. -/
def matHom (A : Matrix (Fin 2) (Fin 2) ℚ) : ℚ × ℚ →+ ℚ × ℚ where
  toFun v := (A 0 0 * v.1 + A 0 1 * v.2, A 1 0 * v.1 + A 1 1 * v.2)
  map_zero' := by simp
  map_add' v w := by ext <;> simp <;> ring

theorem matHom_apply (A : Matrix (Fin 2) (Fin 2) ℚ) (v : ℚ × ℚ) :
    matHom A v = (A 0 0 * v.1 + A 0 1 * v.2, A 1 0 * v.1 + A 1 1 * v.2) := rfl

theorem matHom_mul (X Y : Matrix (Fin 2) (Fin 2) ℚ) :
    matHom (X * Y) = (matHom X).comp (matHom Y) := by
  ext v <;> simp [matHom_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem matHom_one : matHom 1 = AddMonoidHom.id _ := by
  ext v <;> simp [matHom_apply]

/-- The lattice `A ℤ²`. -/
def lat (A : Matrix (Fin 2) (Fin 2) ℚ) : AddSubgroup (ℚ × ℚ) := zLat.map (matHom A)

theorem intMat_preserves (U : Matrix (Fin 2) (Fin 2) ℤ) :
    zLat.map (matHom (U.map (Int.cast : ℤ → ℚ))) ≤ zLat := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := mem_zLat.mp hv
  refine mem_zLat.mpr ⟨⟨U 0 0 * a + U 0 1 * b, ?_⟩, ⟨U 1 0 * a + U 1 1 * b, ?_⟩⟩ <;>
    simp [matHom_apply, ← ha, ← hb]

theorem intMat_map_eq (U U' : Matrix (Fin 2) (Fin 2) ℤ) (h : U * U' = 1) :
    zLat.map (matHom (U.map (Int.cast : ℤ → ℚ))) = zLat := by
  refine le_antisymm (intMat_preserves U) ?_
  intro v hv
  refine ⟨matHom (U'.map (Int.cast : ℤ → ℚ)) v, intMat_preserves U' ⟨v, hv, rfl⟩, ?_⟩
  have key : U.map (Int.cast : ℤ → ℚ) * U'.map (Int.cast : ℤ → ℚ) = 1 := by
    have := congrArg (fun M => M.map (Int.castRingHom ℚ)) h
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  rw [← AddMonoidHom.comp_apply, ← matHom_mul, key, matHom_one]
  rfl

theorem intMat_injective (U U' : Matrix (Fin 2) (Fin 2) ℤ) (h : U' * U = 1) :
    Function.Injective (matHom (U.map (Int.cast : ℤ → ℚ))) := by
  intro v w hvw
  have := congrArg (matHom (U'.map (Int.cast : ℤ → ℚ))) hvw
  have key : U'.map (Int.cast : ℤ → ℚ) * U.map (Int.cast : ℤ → ℚ) = 1 := by
    have := congrArg (fun M => M.map (Int.castRingHom ℚ)) h
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply, ← matHom_mul, key, matHom_one]
    at this
  exact this

/-! ### One-dimensional facts -/

theorem rat_mul_int_iff (d : ℚ) (x : ℤ) : (∃ z : ℤ, (z : ℚ) = d * x) ↔ (d.den : ℤ) ∣ x := by
  constructor
  · rintro ⟨z, hz⟩
    have hq : (d.den : ℚ) ≠ 0 := by exact_mod_cast d.den_nz
    have h1 : (d.num : ℚ) * x = z * d.den := by
      rw [hz]
      have := Rat.mul_den_eq_num d
      rw [← this]; ring
    have h2 : d.num * x = z * d.den := by exact_mod_cast h1
    have hcop : IsCoprime (d.den : ℤ) d.num := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      exact_mod_cast d.reduced
    exact hcop.dvd_of_dvd_mul_left ⟨z, by rw [h2]; ring⟩
  · rintro ⟨k, rfl⟩
    refine ⟨d.num * k, ?_⟩
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

theorem int_mem_rat_mul_iff (d : ℚ) (a : ℤ) :
    (∃ x : ℤ, d * x = a) ↔ d.num ∣ a := by
  constructor
  · rintro ⟨x, hx⟩
    have hq : (d.den : ℚ) ≠ 0 := by exact_mod_cast d.den_nz
    have h1 : (d.num : ℚ) * x = a * d.den := by
      rw [← Rat.mul_den_eq_num, ← hx]; ring
    have h2 : d.num * x = a * d.den := by exact_mod_cast h1
    have hcop : IsCoprime d.num (d.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact_mod_cast d.reduced
    exact hcop.dvd_of_dvd_mul_right ⟨x, by rw [← h2]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨d.den * k, ?_⟩
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

/-! ### Diagonal lattices -/

/-- `ℤ² → ℚ²`, `(a, b) ↦ (a d₁, b d₂)`. -/
def diagHom (d₁ d₂ : ℚ) : ℤ × ℤ →+ ℚ × ℚ where
  toFun x := ((x.1 : ℚ) * d₁, (x.2 : ℚ) * d₂)
  map_zero' := by simp
  map_add' x y := by ext <;> simp <;> ring

theorem diagHom_injective {d₁ d₂ : ℚ} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    Function.Injective (diagHom d₁ d₂) := by
  intro x y hxy
  simp only [diagHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  have e1 : (x.1 : ℚ) = y.1 := mul_right_cancel₀ h₁ h1
  have e2 : (x.2 : ℚ) = y.2 := mul_right_cancel₀ h₂ h2
  exact Prod.ext (by exact_mod_cast e1) (by exact_mod_cast e2)

theorem lat_diagonal (d₁ d₂ : ℚ) :
    lat (diagonal ![d₁, d₂]) = (⊤ : AddSubgroup (ℤ × ℤ)).map (diagHom d₁ d₂) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := mem_zLat.mp hw
    refine ⟨(a, b), trivial, ?_⟩
    simp [diagHom, matHom_apply, ← ha, ← hb, mul_comm]
  · rintro ⟨x, -, rfl⟩
    refine ⟨((x.1 : ℚ), (x.2 : ℚ)), mem_zLat.mpr ⟨⟨x.1, rfl⟩, ⟨x.2, rfl⟩⟩, ?_⟩
    simp [diagHom, matHom_apply, mul_comm]

/-- `ℤ² → ℚ²`, the inclusion. -/
def intHom : ℤ × ℤ →+ ℚ × ℚ := (Int.castAddHom ℚ).prodMap (Int.castAddHom ℚ)

theorem intHom_injective : Function.Injective intHom := by
  intro x y hxy
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  simp [intHom] at h1 h2
  exact Prod.ext h1 h2

theorem zLat_eq : zLat = (⊤ : AddSubgroup (ℤ × ℤ)).map intHom := by
  ext v
  rw [mem_zLat]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), trivial, by simp [intHom, ha, hb]⟩
  · rintro ⟨x, -, rfl⟩
    exact ⟨⟨x.1, rfl⟩, ⟨x.2, rfl⟩⟩

theorem diag_inf_eq_den {d₁ d₂ : ℚ} :
    lat (diagonal ![d₁, d₂]) ⊓ zLat = ((AddSubgroup.zmultiples (d₁.den : ℤ)).prod
      (AddSubgroup.zmultiples (d₂.den : ℤ))).map (diagHom d₁ d₂) := by
  rw [lat_diagonal]
  ext v
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and,
    AddSubgroup.mem_prod, Int.mem_zmultiples_iff]
  constructor
  · rintro ⟨⟨x, rfl⟩, hv⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := mem_zLat.mp hv
    refine ⟨x, ⟨(rat_mul_int_iff d₁ x.1).mp ⟨a, ?_⟩, (rat_mul_int_iff d₂ x.2).mp ⟨b, ?_⟩⟩, rfl⟩
    · rw [ha]; simp [diagHom, mul_comm]
    · rw [hb]; simp [diagHom, mul_comm]
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨x, rfl⟩, mem_zLat.mpr ⟨?_, ?_⟩⟩
    · obtain ⟨z, hz⟩ := (rat_mul_int_iff d₁ x.1).mpr h1
      exact ⟨z, by rw [hz]; simp [diagHom, mul_comm]⟩
    · obtain ⟨z, hz⟩ := (rat_mul_int_iff d₂ x.2).mpr h2
      exact ⟨z, by rw [hz]; simp [diagHom, mul_comm]⟩

theorem diag_inf_eq_num {d₁ d₂ : ℚ} :
    lat (diagonal ![d₁, d₂]) ⊓ zLat = ((AddSubgroup.zmultiples d₁.num).prod
      (AddSubgroup.zmultiples d₂.num)).map intHom := by
  rw [lat_diagonal]
  ext v
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and,
    AddSubgroup.mem_prod, Int.mem_zmultiples_iff]
  constructor
  · rintro ⟨⟨x, rfl⟩, hv⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := mem_zLat.mp hv
    refine ⟨(a, b), ⟨(int_mem_rat_mul_iff d₁ a).mp ⟨x.1, ?_⟩,
      (int_mem_rat_mul_iff d₂ b).mp ⟨x.2, ?_⟩⟩, ?_⟩
    · rw [ha]; simp [diagHom, mul_comm]
    · rw [hb]; simp [diagHom, mul_comm]
    · simp [intHom, diagHom, ha, hb]
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    obtain ⟨a, ha⟩ := (int_mem_rat_mul_iff d₁ x.1).mpr h1
    obtain ⟨b, hb⟩ := (int_mem_rat_mul_iff d₂ x.2).mpr h2
    refine ⟨⟨(a, b), ?_⟩, ?_⟩
    · exact Prod.ext (by change (a : ℚ) * d₁ = x.1; rw [mul_comm]; exact ha)
        (by change (b : ℚ) * d₂ = x.2; rw [mul_comm]; exact hb)
    · rw [zLat_eq]; exact ⟨x, trivial, rfl⟩

theorem diag_relIndex_lat {d₁ d₂ : ℚ} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    (lat (diagonal ![d₁, d₂]) ⊓ zLat).relIndex (lat (diagonal ![d₁, d₂])) = d₁.den * d₂.den := by
  rw [diag_inf_eq_den, lat_diagonal,
    AddSubgroup.relIndex_map_map_of_injective _ _ (diagHom_injective h₁ h₂),
    AddSubgroup.relIndex_top_right, AddSubgroup.index_prod, Int.index_zmultiples,
    Int.index_zmultiples]
  simp

theorem diag_relIndex_zLat {d₁ d₂ : ℚ} :
    (lat (diagonal ![d₁, d₂]) ⊓ zLat).relIndex zLat = d₁.num.natAbs * d₂.num.natAbs := by
  rw [diag_inf_eq_num, zLat_eq,
    AddSubgroup.relIndex_map_map_of_injective _ _ intHom_injective,
    AddSubgroup.relIndex_top_right, AddSubgroup.index_prod, Int.index_zmultiples,
    Int.index_zmultiples]

theorem diag_index_identity {d₁ d₂ : ℚ} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    ((lat (diagonal ![d₁, d₂]) ⊓ zLat).relIndex (lat (diagonal ![d₁, d₂])) : ℚ) *
      |(diagonal ![d₁, d₂]).det| = (lat (diagonal ![d₁, d₂]) ⊓ zLat).relIndex zLat := by
  rw [diag_relIndex_lat h₁ h₂, diag_relIndex_zLat, det_diagonal, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_mul]
  have hq1 : (d₁.den : ℚ) ≠ 0 := by exact_mod_cast d₁.den_nz
  have hq2 : (d₂.den : ℚ) ≠ 0 := by exact_mod_cast d₂.den_nz
  have hd1 : |d₁| = |(d₁.num : ℚ)| / d₁.den := by
    conv_lhs => rw [← Rat.num_div_den d₁]
    rw [abs_div, Nat.abs_cast]
  have hd2 : |d₂| = |(d₂.num : ℚ)| / d₂.den := by
    conv_lhs => rw [← Rat.num_div_den d₂]
    rw [abs_div, Nat.abs_cast]
  have e1 : ((d₁.num.natAbs : ℕ) : ℚ) = |(d₁.num : ℚ)| := by simp
  have e2 : ((d₂.num.natAbs : ℕ) : ℚ) = |(d₂.num : ℚ)| := by simp
  rw [hd1, hd2]
  push_cast
  rw [e1, e2]
  field_simp

/-! ### General rational lattices -/

theorem lat_mul_int (A : Matrix (Fin 2) (Fin 2) ℚ) (V V' : Matrix (Fin 2) (Fin 2) ℤ) (h : V * V' = 1) :
    lat (A * V.map (Int.cast : ℤ → ℚ)) = lat A := by
  rw [lat, lat, matHom_mul, ← AddSubgroup.map_map, intMat_map_eq V V' h]

theorem int_mul_lat (A : Matrix (Fin 2) (Fin 2) ℚ) (U : Matrix (Fin 2) (Fin 2) ℤ) :
    lat (U.map (Int.cast : ℤ → ℚ) * A) = (lat A).map (matHom (U.map (Int.cast : ℤ → ℚ))) := by
  rw [lat, lat, matHom_mul, ← AddSubgroup.map_map]

theorem det_int_abs (U U' : Matrix (Fin 2) (Fin 2) ℤ) (h : U * U' = 1) :
    |(U.map (Int.cast : ℤ → ℚ)).det| = 1 := by
  have hd : U.det * U'.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  have habs : |U.det| = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with h1 | h1 <;> simp [h1]
  have hmap : (U.map (Int.cast : ℤ → ℚ)).det = (U.det : ℚ) := by
    rw [show (Int.cast : ℤ → ℚ) = ⇑(Int.castRingHom ℚ) from rfl, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
  rw [hmap, ← Int.cast_abs, habs, Int.cast_one]

/-- **The lattice index identity** `[L : L ∩ ℤ²] · |det A| = [ℤ² : L ∩ ℤ²]` for `L = A ℤ²`. -/
theorem lat_index (A : Matrix (Fin 2) (Fin 2) ℚ) (hA : A.det ≠ 0) :
    ((lat A ⊓ zLat).relIndex (lat A) : ℚ) * |A.det| = (lat A ⊓ zLat).relIndex zLat := by
  obtain ⟨N, hN, M, hM⟩ := RepresentationTheory.IntegerCartan.exists_clear_denominators A
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hMdet : M.det ≠ 0 := by
    intro h0
    have : (M.map (Int.cast : ℤ → ℚ)).det = 0 := by
      rw [show (Int.cast : ℤ → ℚ) = ⇑(Int.castRingHom ℚ) from rfl, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, h0, map_zero]
    rw [hM, Matrix.det_smul] at this
    exact hA ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hNq))
  obtain ⟨U, V, U', V', a, hUU', hU'U, hVV', hV'V, hMeq⟩ :=
    HeckeCommutativity.exists_eq_mul_diagonal_mul M hMdet
  set Uq := U.map (Int.cast : ℤ → ℚ)
  set Vq := V.map (Int.cast : ℤ → ℚ)
  set D : Matrix (Fin 2) (Fin 2) ℚ := diagonal ![(a 0 : ℚ) / N, (a 1 : ℚ) / N]
  have hAeq : A = Uq * D * Vq := by
    have h1 : M.map (Int.cast : ℤ → ℚ) = Uq * (diagonal fun i => (a i : ℚ)) * Vq := by
      rw [hMeq, show (Int.cast : ℤ → ℚ) = ⇑(Int.castRingHom ℚ) from rfl, Matrix.map_mul,
        Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
      rfl
    have hND : (N : ℚ) • D = diagonal fun i => (a i : ℚ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [D] <;> field_simp
    have h2 : (N : ℚ) • A = (N : ℚ) • (Uq * D * Vq) := by
      rw [← hM, h1, ← Matrix.smul_mul, ← Matrix.mul_smul, hND]
    exact smul_right_injective _ hNq h2
  have hDdet : D.det ≠ 0 := by
    intro h0
    apply hA
    rw [hAeq, Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]
  have hd0 : (a 0 : ℚ) / N ≠ 0 := by
    intro h0; apply hDdet; simp [D, det_diagonal, Fin.prod_univ_two, h0]
  have hd1 : (a 1 : ℚ) / N ≠ 0 := by
    intro h0; apply hDdet; simp [D, det_diagonal, Fin.prod_univ_two, h0]
  have hlat : lat A = (lat D).map (matHom Uq) := by
    rw [hAeq, lat_mul_int _ V V' hVV', int_mul_lat]
  have hz : zLat = zLat.map (matHom Uq) := (intMat_map_eq U U' hUU').symm
  have hinj := intMat_injective U U' hU'U
  have hinter : lat A ⊓ zLat = (lat D ⊓ zLat).map (matHom Uq) := by
    rw [AddSubgroup.map_inf_eq _ _ _ hinj, ← hlat, ← hz]
  have hdet : |A.det| = |D.det| := by
    rw [hAeq, Matrix.det_mul, Matrix.det_mul, abs_mul, abs_mul, det_int_abs U U' hUU',
      det_int_abs V V' hVV', one_mul, mul_one]
  have e1 : (lat A ⊓ zLat).relIndex (lat A) = (lat D ⊓ zLat).relIndex (lat D) := by
    rw [hinter, hlat, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  have e2 : (lat A ⊓ zLat).relIndex zLat = (lat D ⊓ zLat).relIndex zLat := by
    have := AddSubgroup.relIndex_map_map_of_injective (lat D ⊓ zLat) zLat hinj
    rw [← hz] at this
    rw [hinter]
    exact this
  rw [e1, e2, hdet]
  exact diag_index_identity hd0 hd1

end TernaryPeriodPolynomials.HeckeEigen.Satake
