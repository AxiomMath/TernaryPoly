module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.Data
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.AwayParts
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AwayGood

@[expose] public section


/-!
# Representatives of an away-from-three correspondence as `GL₃(ℤ)`-cosets

For `t` away from three, the representatives of `t` are also right coset representatives of the
`GL₃(ℤ)` double coset `D = GL₃(ℤ) g GL₃(ℤ)`, which is stable under `τ(x) = w xᵀ w⁻¹`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.HeckeEigen

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

theorem rationalLevel_le_Γ : rationalLevel ≤ Γ := by
  rintro _ ⟨a, rfl⟩
  exact ⟨a.val, rfl⟩

/-- The `GL₃(ℤ)` double coset of `g`. -/
def DZ (g : RationalGL3) : Set RationalGL3 := {x | ∃ a ∈ Γ, ∃ b ∈ Γ, x = a * g * b}

theorem DZ_right {g x : RationalGL3} (hx : x ∈ DZ g) {γ : RationalGL3} (hγ : γ ∈ Γ) :
    x * γ ∈ DZ g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨a, ha, b * γ, Γ.mul_mem hb hγ, by group⟩

theorem DZ_left {g x : RationalGL3} (hx : x ∈ DZ g) {γ : RationalGL3} (hγ : γ ∈ Γ) :
    γ * x ∈ DZ g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨γ * a, Γ.mul_mem hγ ha, b, hb, by group⟩

theorem inLocal_inv {x : LocalThreeGL} (h : InLocalThreeLevel x) : InLocalThreeLevel x⁻¹ := by
  obtain ⟨k, hrow, rfl⟩ := h
  refine ⟨k⁻¹, ?_, by rw [map_inv]⟩
  conv_lhs => rw [← hrow]
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.vecMul_one]

theorem inLocal_one : InLocalThreeLevel 1 := ⟨1, by simp, by simp⟩

theorem finiteLevel_le_integral : finiteLevel ≤ finiteIntegralGLLevel 3 := by
  rintro _ ⟨y, _, rfl⟩
  exact ⟨y, rfl⟩

/-- A rational matrix which is finite-adelically integral is integral. -/
theorem mem_Γ_of_integral {x : RationalGL3} (hx : rationalFinite x ∈ finiteIntegralGLLevel 3) :
    x ∈ Γ := by
  obtain ⟨h1, h2⟩ := (finiteIntegralGLLevel_mem_iff _).mp hx
  rw [mem_Γ_iff]
  constructor
  · intro i j
    obtain ⟨z, hz⟩ :=
      (PlaneEisensteinContinuation.IntegralRationals.integral_iff_integer _).mp (h1 i j)
    exact ⟨z, hz.symm⟩
  · intro i j
    have := h2 i j
    rw [← map_inv] at this
    obtain ⟨z, hz⟩ :=
      (PlaneEisensteinContinuation.IntegralRationals.integral_iff_integer _).mp this
    exact ⟨z, hz.symm⟩

/-- **Disjointness modulo `GL₃(ℤ)`.** -/
theorem rep_disj {t : HeckeCorrespondence} (ht : AwayThree t) :
    ∀ r ∈ t.representatives, ∀ r' ∈ t.representatives, r⁻¹ * r' ∈ Γ → r = r' := by
  intro r hr r' hr' h
  apply t.disjoint r hr r' hr'
  apply (HeckeStability.rationalFinite_mem_finiteLevel_iff _).mp
  obtain ⟨γ₀, hγ⟩ := h
  apply finiteLevel_of_integral_of_three
  · rw [← hγ]; exact rationalFinite_integral γ₀
  · rw [map_mul, map_inv, map_mul, map_inv]
    exact InLocalThreeLevel_mul (inLocal_inv (rep_local_level ht hr)) (rep_local_level ht hr')

theorem glAway3_level_of_integral (γ₀ : IntegralGL) :
    glAway3 (rationalFinite (integralRational γ₀)) ∈ finiteLevel := by
  have hC : finiteAtThree (GeneralLinearGroup.map finiteThree (rationalFinite (integralRational γ₀)))
      ∈ finiteIntegralGLLevel 3 := by
    rw [← three_integral_map]
    exact finiteAtThree_integral _
  apply finiteLevel_of_integral_of_three
  · exact mul_mem (rationalFinite_integral γ₀) (inv_mem hC)
  · rw [glAway3, map_mul, map_inv, finiteAtThree_three, mul_inv_cancel]
    exact inLocal_one

/-- Conjugating an element supported at three by `g` stays supported at three. -/
theorem conj_finiteAtThree (y : FiniteGL) (X : LocalThreeGL) :
    y⁻¹ * finiteAtThree X * y =
      finiteAtThree ((GeneralLinearGroup.map finiteThree y)⁻¹ * X * GeneralLinearGroup.map finiteThree y) := by
  apply Units.ext
  apply finiteMatrix_eq_of_three_and_away
  · change (GeneralLinearGroup.map finiteThree (y⁻¹ * finiteAtThree X * y)).val =
      (GeneralLinearGroup.map finiteThree (finiteAtThree _)).val
    rw [finiteAtThree_three, map_mul, map_mul, map_inv, finiteAtThree_three]
  · intro place away
    change (GeneralLinearGroup.map (finiteEvaluation place) (y⁻¹ * finiteAtThree X * y)).val =
      (GeneralLinearGroup.map (finiteEvaluation place) (finiteAtThree _)).val
    rw [finiteAtThree_away _ _ away, map_mul, map_mul, finiteAtThree_away _ _ away, mul_one,
      map_inv, inv_mul_cancel]

/-- **Covering modulo `GL₃(ℤ)`.** -/
theorem rep_cover {t : HeckeCorrespondence} (ht : AwayThree t) :
    ∀ x ∈ DZ t.g, ∃ r ∈ t.representatives, r⁻¹ * x ∈ Γ := by
  rintro x ⟨a, ⟨a₀, rfl⟩, b, hb, rfl⟩
  set af := rationalFinite (integralRational a₀) with haf
  set C := finiteAtThree (GeneralLinearGroup.map finiteThree af) with hCdef
  have hCint : C ∈ finiteIntegralGLLevel 3 := by
    rw [hCdef, ← three_integral_map]
    exact finiteAtThree_integral _
  have hk := glAway3_level_of_integral a₀
  obtain ⟨γ, hγ, h1, h2⟩ := HeckeStability.CosetDecomposition.cosetDecomposition_all t.g _ hk
  have hcf : rationalFinite (γ⁻¹ * integralRational a₀) =
      ((rationalFinite γ)⁻¹ * glAway3 af) * C := by
    rw [glAway3, map_mul, map_inv, ← hCdef, ← haf]; group
  have hc : γ⁻¹ * integralRational a₀ ∈ Γ := by
    apply mem_Γ_of_integral
    rw [hcf]
    exact mul_mem (finiteLevel_le_integral h1) hCint
  -- the local level at three of `g`
  have hg3 := awayThree_local_level ht
  obtain ⟨kg, _, hkg⟩ := hg3
  have hgc : t.g⁻¹ * (γ⁻¹ * integralRational a₀) * t.g ∈ Γ := by
    apply mem_Γ_of_integral
    have : rationalFinite (t.g⁻¹ * (γ⁻¹ * integralRational a₀) * t.g) =
        ((rationalFinite t.g)⁻¹ * ((rationalFinite γ)⁻¹ * glAway3 af) * rationalFinite t.g) *
          ((rationalFinite t.g)⁻¹ * C * rationalFinite t.g) := by
      rw [map_mul, map_mul, map_inv, hcf]; group
    rw [this]
    refine mul_mem (finiteLevel_le_integral h2) ?_
    rw [conj_finiteAtThree, rationalFinite_three, ← hkg, ← three_integral_map]
    change finiteAtThree (GeneralLinearGroup.map padicThreeEmbedding kg⁻¹ *
      GeneralLinearGroup.map padicThreeEmbedding (GeneralLinearGroup.map (Int.castRingHom ℤ_[3]) a₀) *
      GeneralLinearGroup.map padicThreeEmbedding kg) ∈ _
    rw [← map_mul, ← map_mul]
    exact finiteAtThree_integral _
  obtain ⟨r, hr, hrr⟩ := t.complete ⟨γ, hγ⟩ 1
  refine ⟨r, hr, ?_⟩
  have : r⁻¹ * (integralRational a₀ * t.g * b) =
      (r⁻¹ * ((⟨γ, hγ⟩ : rationalLevel).val * t.g * (1 : rationalLevel).val)) *
        (t.g⁻¹ * (γ⁻¹ * integralRational a₀) * t.g) * b := by
    simp only [OneMemClass.coe_one, mul_one]; group
  rw [this]
  exact Γ.mul_mem (Γ.mul_mem (rationalLevel_le_Γ hrr) hgc) hb

/-! ### Transposition -/

theorem tr3_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x : GL3 R) :
    GeneralLinearGroup.map φ (tr3 x) = tr3 (GeneralLinearGroup.map φ x) := by
  apply Units.ext; rfl

theorem tr3_Γ {x : RationalGL3} (hx : x ∈ Γ) : tr3 x ∈ Γ := by
  obtain ⟨k, rfl⟩ := hx
  exact ⟨tr3 k, tr3_map _ k⟩

theorem weyl_Γ : (weyl : RationalGL3) ∈ Γ := ⟨weyl, weyl_map _⟩

theorem tr3_DZ {t : HeckeCorrespondence} (ht : AwayThree t) : tr3 t.g ∈ DZ t.g := by
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, d, hd⟩ :=
    HeckeCommutativity.exists_level_diagonal (HeckeCommutativity.good_of_awayThree ht)
  have hδ : tr3 (γ₁⁻¹ * t.g * γ₂⁻¹) = γ₁⁻¹ * t.g * γ₂⁻¹ := by
    apply Units.ext
    change (γ₁⁻¹ * t.g * γ₂⁻¹).valᵀ = _
    rw [hd, diagonal_transpose]
  have hg : t.g = γ₁ * (γ₁⁻¹ * t.g * γ₂⁻¹) * γ₂ := by group
  have h1 := rationalLevel_le_Γ hγ₁
  have h2 := rationalLevel_le_Γ hγ₂
  refine ⟨tr3 γ₂ * γ₁⁻¹, Γ.mul_mem (tr3_Γ h2) (Γ.inv_mem h1), γ₂⁻¹ * tr3 γ₁,
    Γ.mul_mem (Γ.inv_mem h2) (tr3_Γ h1), ?_⟩
  conv_lhs => rw [hg, tr3_mul, tr3_mul, hδ]
  group

theorem τ_DZ {t : HeckeCorrespondence} (ht : AwayThree t) {x : RationalGL3} (hx : x ∈ DZ t.g) :
    τ x ∈ DZ t.g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨a', ha', b', hb', hab⟩ := tr3_DZ ht
  refine ⟨τ b * weyl * a', Γ.mul_mem (Γ.mul_mem (τ_Γ hb) weyl_Γ) ha',
    b' * weyl⁻¹ * τ a, Γ.mul_mem (Γ.mul_mem hb' (Γ.inv_mem weyl_Γ)) (τ_Γ ha), ?_⟩
  have hτg : τ t.g = weyl * (a' * t.g * b') * weyl⁻¹ := by rw [τ, hab]
  rw [τ_mul, τ_mul, hτg]
  group

theorem τ_τ (x : RationalGL3) : τ (τ x) = (weyl * weyl) * x * (weyl * weyl)⁻¹ := by
  have hw : tr3 (weyl : RationalGL3) = weyl⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    apply Units.ext
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [tr3, weyl, Matrix.mul_apply, Fin.sum_univ_three]
  have htt : ∀ y : RationalGL3, tr3 (tr3 y) = y := fun y => Units.ext (transpose_transpose _)
  have hwi : tr3 (weyl⁻¹ : RationalGL3) = weyl := by
    rw [← hw, htt]
  simp only [τ, tr3_mul, htt, hw, hwi]
  group

theorem τ_DZ_iff {t : HeckeCorrespondence} (ht : AwayThree t) (x : RationalGL3) :
    τ x ∈ DZ t.g ↔ x ∈ DZ t.g := by
  refine ⟨fun h => ?_, τ_DZ ht⟩
  have h2 := τ_DZ ht h
  rw [τ_τ] at h2
  have hc : (weyl * weyl : RationalGL3) ∈ Γ := Γ.mul_mem weyl_Γ weyl_Γ
  have := DZ_right (DZ_left h2 (Γ.inv_mem hc)) hc
  simpa [mul_assoc] using this

/-- **The representatives form a `GL₃(ℤ)` coset representative set of `D`.** -/
theorem repSet {t : HeckeCorrespondence} (ht : AwayThree t) :
    RepSet Γ t.representatives (DZ t.g) where
  sub r hr := by
    obtain ⟨a, b, rfl⟩ := t.inDoubleCoset r hr
    exact ⟨a.val, rationalLevel_le_Γ a.property, b.val, rationalLevel_le_Γ b.property, rfl⟩
  disj := rep_disj ht
  cover := rep_cover ht
  right x hx γ hγ := DZ_right hx hγ

end TernaryPeriodPolynomials.HeckeEigen.Satake
