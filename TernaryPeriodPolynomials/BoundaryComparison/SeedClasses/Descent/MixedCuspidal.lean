module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNSeed

@[expose] public section


/-!
# The mixed cuspidal group `𝒞_P(E)` of one plane cusp, and the seeds that span it

Paper: Lemma C.3 (`ar:lem:seed`),
last sentence: "the holomorphic and antiholomorphic seeds span `𝒞_P(E)` after
including all plane cusps and finite reflections", with `𝒞_R(E)` defined at the paper as the
direct sum over faces of type `R` of the subspaces of `H¹(L_R, H¹(N_R, E))` "whose restrictions at
all rational cusps of the binary Levi vanish", which "inject into degree-two face cohomology by
Hochschild--Serre, since `L_R` has rational cohomological dimension one".

## Contents

* `oneRestriction B A`: the restriction `H¹(G, A) → H¹(B, A)` to a subgroup (Mathlib's
  `groupCohomology.map` along the inclusion); `oneRestriction_π_eq_zero_iff`: a class `[c]` restricts
  to zero iff `c|_B` is the coboundary of one vector.
* `leviCuspStab Λ F`: the stabilizer in `Λ ⊆ SL₂(ℤ)` of the rational cusp of a frame
  `F ∈ GL₂(ℚ)` (`F⁻¹ γ F` upper triangular), the same notion as B's `binaryCuspLevel`.
* `cuspidalSubspace Λ V`: the classes of `H¹(Λ, V)` restricting to zero at every `leviCuspStab Λ F`.
* `gammaNCuspidal N n`, `levelCuspidal Λ n`: this subspace for `V = H¹(N_P, E_n)`, the radical
  cohomology (`splitRadicalH1Representation`) of the plane group `Γ(N) ∩ P(ℤ)` (radical `Nℤ²`, Levi
  `Γ₂(N)`), resp. `ℤ² ⋊ Λ`. These are the literal paper definitions of `𝒞_P(E)` for a single face
  `P`; they are not defined through the parabolic cohomology or through the seeds.
* `mem_cuspidalSubspace_binRep_iff`, `mem_gammaNCuspidal_iff`, `mem_levelCuspidal_iff`: for every
  `Λ ⊆ SL₂(ℤ)`, a class restricts to zero at all rational cusps iff its binary coordinate in
  `H¹(Λ, Sym^{n+1} ⊗ det⁻¹)` is a parabolic class (`parabolicH1`). The substance is the
  number-theoretic reduction `exists_cusp_basis` (every rational frame is `SL₂(ℤ)`-conjugate to a
  primitive integral one) and `cusp_gen` (a cusp stabilizer is generated, up to sign, by one
  parabolic element), and the treatment of `-1 ∈ Λ`, which acts on `Sym^{n+1} ⊗ det⁻¹` by
  `(-1)^{n+1}` (`cusp_coboundary_of_parabolic_neg_one`).
* `gammaNSeedKerSpan_map_edge_eq_cuspidal`, `gammaNSeedSpan_eq_cuspidalInH2`,
  `seedKerSpan_map_edge_eq_levelCuspidal`: the seeds span `𝒞_P(E)` (inside
  `H¹(L_P, H¹(N_P, E))`, resp. its image in `H²(Γ_P, E)`), under the hypothesis `ESSpan` (discharged
  in `Exports/MixedCuspidalC3`).

Scope: one plane `P`. For `Γ(N) ∩ P(ℤ)` this is the full stabilizer `Γ(N) ∩ P(ℚ)` of the rational
plane, with Levi block exactly `Γ₂(N)` and no finite reflection, only for `N ≥ 3`. Other plane cusps
are in `PlaneCusps`; the finite reflections and the comparison with the Borel--Serre face cohomology
of the paper's level-three group are not in this file.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open Matrix



theorem rat_lowerLeft_conj (F : GL (Fin 2) ℚ) (M : Matrix (Fin 2) (Fin 2) ℚ) :
    (((F⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) * M * (F : Matrix (Fin 2) (Fin 2) ℚ)) 1 0 *
      (F : Matrix (Fin 2) (Fin 2) ℚ).det =
    (F : Matrix (Fin 2) (Fin 2) ℚ) 0 0 ^ 2 * M 1 0 +
      (F : Matrix (Fin 2) (Fin 2) ℚ) 0 0 * (F : Matrix (Fin 2) (Fin 2) ℚ) 1 0 * (M 1 1 - M 0 0) -
      (F : Matrix (Fin 2) (Fin 2) ℚ) 1 0 ^ 2 * M 0 1 := by
  have hdet : (F : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := by
    have := F.det.ne_zero
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, smul_eq_mul]
  field_simp
  ring



theorem exists_primitive_rat_pair (a c : ℚ) (h : a ≠ 0 ∨ c ≠ 0) :
    ∃ (p q : ℤ) (μ : ℚ), IsCoprime p q ∧ μ ≠ 0 ∧ a = μ * p ∧ c = μ * q := by
  set x : ℤ := a.num * c.den with hx
  set y : ℤ := c.num * a.den with hy
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    rcases h with h | h
    · left
      simp [hx, Rat.num_ne_zero.mpr h, c.den_nz]
    · right
      simp [hy, Rat.num_ne_zero.mpr h, a.den_nz]
  have hpos : 0 < Int.gcd x y := by
    rcases hxy with h | h
    · exact Int.gcd_pos_of_ne_zero_left _ h
    · exact Int.gcd_pos_of_ne_zero_right _ h
  obtain ⟨g, p, q, hg, hpq, hxp, hyq⟩ := Int.exists_gcd_one' hpos
  have hD : (a.den : ℚ) * c.den ≠ 0 := by
    have := a.den_nz; have := c.den_nz; positivity
  have hxa : (x : ℚ) = a * (a.den * c.den) := by
    simp only [hx]; push_cast
    rw [← Rat.mul_den_eq_num a]; ring
  have hyc : (y : ℚ) = c * (a.den * c.den) := by
    simp only [hy]; push_cast
    rw [← Rat.mul_den_eq_num c]; ring
  refine ⟨p, q, (g : ℚ) / ((a.den : ℚ) * c.den), Int.isCoprime_iff_gcd_eq_one.mpr hpq, ?_, ?_, ?_⟩
  · have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    exact div_ne_zero hg' hD
  · have : (x : ℚ) = p * g := by rw [hxp]; push_cast; ring
    field_simp
    linarith
  · have : (y : ℚ) = q * g := by rw [hyq]; push_cast; ring
    field_simp
    linarith


theorem exists_cusp_basis (F : GL (Fin 2) ℚ) : ∃ g : SL(2, ℤ), ∀ γ : SL(2, ℤ),
    ((F⁻¹ * SpecialLinearGroup.mapGL ℚ γ * F : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 ↔
      ((g⁻¹ * γ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
  have hdet : (F : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := by
    have := F.det.ne_zero
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hne : (F : Matrix (Fin 2) (Fin 2) ℚ) 0 0 ≠ 0 ∨ (F : Matrix (Fin 2) (Fin 2) ℚ) 1 0 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply hdet
    rw [Matrix.det_fin_two, hcon.1, hcon.2]; ring
  obtain ⟨p, q, μ, hpq, hμ, hp, hq⟩ := exists_primitive_rat_pair _ _ hne
  obtain ⟨g, hg0, hg1⟩ := hpq.exists_SL2_col 0
  refine ⟨g, fun γ => ?_⟩
  have key1 := rat_lowerLeft_conj F ((SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
  have key2 := rat_lowerLeft_conj (SpecialLinearGroup.mapGL ℚ g)
    ((SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
  have e2 : (((SpecialLinearGroup.mapGL ℚ g)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      ((SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      ((SpecialLinearGroup.mapGL ℚ g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((SpecialLinearGroup.mapGL ℚ (g⁻¹ * γ * g) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
    rw [map_mul, map_mul, map_inv]; simp
  rw [e2] at key2
  have hdg : ((SpecialLinearGroup.mapGL ℚ g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    have := Matrix.SpecialLinearGroup.det_mapGL (S := ℚ) g
    rw [← Matrix.GeneralLinearGroup.val_det_apply, this]; rfl
  rw [hdg, mul_one] at key2
  have hX : ∀ (x : SL(2, ℤ)) (i j : Fin 2),
      ((SpecialLinearGroup.mapGL ℚ x : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j =
        ((x : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
    intro x i j; simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  simp only [hX, hg0, hg1] at key2
  rw [Units.val_mul, Units.val_mul]
  simp only [hX] at key1
  rw [hp, hq] at key1
  have key3 : (((F⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      ((SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      (F : Matrix (Fin 2) (Fin 2) ℚ)) 1 0 * (F : Matrix (Fin 2) (Fin 2) ℚ).det =
      μ ^ 2 * (((g⁻¹ * γ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ) := by
    rw [key1, key2]; ring
  constructor
  · intro h0
    rw [h0, zero_mul] at key3
    have : ((((g⁻¹ * γ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℚ) = 0 := by
      rcases mul_eq_zero.mp key3.symm with h1 | h1
      · exact absurd (pow_eq_zero_iff (two_ne_zero) |>.mp h1) hμ
      · exact h1
    exact_mod_cast this
  · intro h0
    have h0' : ((((g⁻¹ * γ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℚ) = 0 := by
      exact_mod_cast h0
    rw [h0', mul_zero] at key3
    rcases mul_eq_zero.mp key3 with h1 | h1
    · exact h1
    · exact absurd h1 hdet



theorem upper_unipotent_cases (δ : SL(2, ℤ)) (h : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    (∃ k : ℤ, δ = ModularGroup.T ^ k) ∨ (∃ k : ℤ, δ = -(ModularGroup.T ^ k)) := by
  have hdet := δ.det_coe
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨(δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h, h1, h2]
  · right
    refine ⟨-(δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h, h1, h2]


section Cusps

/-- The Borel subgroup `{x ∈ SL₂(ℤ) | x₁₀ = 0}`. -/
def borelInt : Subgroup SL(2, ℤ) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx, hy]; ring
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hx]

/-- **The stabilizer in `Λ` of the rational cusp of a frame `F ∈ GL₂(ℚ)`** (the cusp `F · ∞`): the
elements `γ ∈ Λ` such that `F⁻¹ γ F` is upper triangular. This is the cusp subgroup of the binary
Levi `Λ` at the rational point `F e₁` of `P¹(ℚ)`. -/
def leviCuspStab (Λ : Subgroup SL(2, ℤ)) (F : GL (Fin 2) ℚ) : Subgroup Λ where
  carrier := {γ | ((F⁻¹ * SpecialLinearGroup.mapGL ℚ γ.1 * F : GL (Fin 2) ℚ) :
    Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    obtain ⟨g, hg⟩ := exists_cusp_basis F
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, hg] at hx hy ⊢
    have h : g⁻¹ * ((x * y : Λ) : SL(2, ℤ)) * g = (g⁻¹ * (x : SL(2, ℤ)) * g) * (g⁻¹ * (y : SL(2, ℤ)) * g) := by
      simp [mul_assoc]
    rw [h]
    exact borelInt.mul_mem hx hy
  inv_mem' := by
    obtain ⟨g, hg⟩ := exists_cusp_basis F
    intro x hx
    simp only [Set.mem_ofPred_eq, hg] at hx ⊢
    have h : g⁻¹ * (((x⁻¹ : Λ)) : SL(2, ℤ)) * g = (g⁻¹ * (x : SL(2, ℤ)) * g)⁻¹ := by
      simp [mul_assoc]
    rw [h]
    exact borelInt.inv_mem hx

theorem mem_leviCuspStab_iff (Λ : Subgroup SL(2, ℤ)) (F : GL (Fin 2) ℚ) (γ : Λ) :
    γ ∈ leviCuspStab Λ F ↔ ((F⁻¹ * SpecialLinearGroup.mapGL ℚ γ.1 * F : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := Iff.rfl

end Cusps


section Cocycles

variable {G : Type} [Group G]

/-- The subgroup of `G` on which the cocycle `c` agrees with the coboundary of `u`. -/
def cobStab (A : Rep ℂ G) (c : groupCohomology.cocycles₁ A) (u : A) : Subgroup G where
  carrier := {γ | c.1 γ = A.ρ γ u - u}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one]
    simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have h := (groupCohomology.mem_cocycles₁_iff c.1).mp c.2 a b
    rw [h, hb, ha, map_mul]
    simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h := (groupCohomology.mem_cocycles₁_iff c.1).mp c.2 a a⁻¹
    have h1 : c.1 1 = 0 := groupCohomology.cocycles₁_map_one c
    rw [mul_inv_cancel, h1, ha] at h
    have h3 : A.ρ a (c.1 a⁻¹) = u - A.ρ a u := by
      calc A.ρ a (c.1 a⁻¹) = (A.ρ a (c.1 a⁻¹) + (A.ρ a u - u)) - (A.ρ a u - u) := by abel
        _ = 0 - (A.ρ a u - u) := by rw [← h]
        _ = u - A.ρ a u := by abel
    calc c.1 a⁻¹ = A.ρ a⁻¹ (A.ρ a (c.1 a⁻¹)) := (Representation.inv_self_apply A.ρ a _).symm
      _ = A.ρ a⁻¹ u - u := by
        rw [h3, map_sub, Representation.inv_self_apply]

end Cocycles


section ParabolicCusps

/-- The diagonal entries of an upper triangular element of `SL₂(ℤ)` are both `1` or both `-1`. -/
theorem upper_diag (x : SL(2, ℤ)) (h : (x : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    ((x : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 ∧ (x : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1) ∨
      ((x : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -1 ∧ (x : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -1) := by
  have hdet := x.det_coe
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  exact Int.eq_one_or_neg_one_of_mul_eq_one' hdet

/-- The translation parameter `±k` of an element `±T^k` of the upper triangular group. -/
def upperShift (x : SL(2, ℤ)) : ℤ :=
  (x : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (x : Matrix (Fin 2) (Fin 2) ℤ) 0 0

theorem upperShift_mul (x y : SL(2, ℤ)) (hx : (x : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0)
    (hy : (y : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    upperShift (x * y) = upperShift x + upperShift y := by
  unfold upperShift
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, hy]
  rcases upper_diag x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases upper_diag y hy with ⟨k1, k2⟩ | ⟨k1, k2⟩ <;>
    simp [h1, k1, k2] <;> ring

theorem upperShift_eq_zero (x : SL(2, ℤ)) (hx : (x : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0)
    (h0 : upperShift x = 0) : x = 1 ∨ x = -1 := by
  unfold upperShift at h0
  rcases upper_diag x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [h1, mul_one] at h0
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, hx]
  · right
    rw [h1] at h0
    have h3 : (x : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by linarith
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h3, h1, h2, hx]

variable {Λ : Subgroup SL(2, ℤ)}

/-- **Structure of a cusp stabilizer.** The stabilizer in `Λ ⊆ SL₂(ℤ)` of a rational cusp is
generated, up to the sign `±1`, by one parabolic element `γ₀ = ± g T^k g⁻¹`: every element is
`γ₀^j` or `-γ₀^j`. -/
theorem cusp_gen (F : GL (Fin 2) ℚ) :
    ∃ γ0 : leviCuspStab Λ F, IsParabolicSL (γ0 : Λ).1 ∧ ∀ γ : leviCuspStab Λ F, ∃ j : ℤ,
      (γ : Λ).1 = (γ0 : Λ).1 ^ j ∨ (γ : Λ).1 = -((γ0 : Λ).1 ^ j) := by
  obtain ⟨g, hg⟩ := exists_cusp_basis F
  have hb : ∀ γ : leviCuspStab Λ F,
      ((g⁻¹ * (γ : Λ).1 * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 :=
    fun γ => (hg (γ : Λ).1).mp γ.2
  let φ : leviCuspStab Λ F →* Subgroup.zpowers ModularGroup.T :=
    { toFun := fun γ => ⟨ModularGroup.T ^ upperShift (g⁻¹ * (γ : Λ).1 * g),
        Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _⟩
      map_one' := by
        apply Subtype.ext
        simp [upperShift]
      map_mul' := by
        intro x y
        apply Subtype.ext
        have e : g⁻¹ * ((x * y : leviCuspStab Λ F) : Λ).1 * g =
            (g⁻¹ * (x : Λ).1 * g) * (g⁻¹ * (y : Λ).1 * g) := by
          simp [mul_assoc]
        change ModularGroup.T ^ upperShift (g⁻¹ * ((x * y : leviCuspStab Λ F) : Λ).1 * g) =
          ModularGroup.T ^ upperShift (g⁻¹ * (x : Λ).1 * g) *
            ModularGroup.T ^ upperShift (g⁻¹ * (y : Λ).1 * g)
        rw [e, upperShift_mul _ _ (hb x) (hb y), _root_.zpow_add] }
  have hker : ∀ x : leviCuspStab Λ F, φ x = 1 → (x : Λ).1 = 1 ∨ (x : Λ).1 = -1 := by
    intro x hx
    have h1 := congrArg Subtype.val hx
    change ModularGroup.T ^ upperShift (g⁻¹ * (x : Λ).1 * g) = 1 at h1
    have h2 : upperShift (g⁻¹ * (x : Λ).1 * g) = 0 := by
      have h3 : ((ModularGroup.T ^ upperShift (g⁻¹ * (x : Λ).1 * g) : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) 0 1 = ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
        rw [h1]
      rw [ModularGroup.coe_T_zpow] at h3
      simpa using h3
    have h5 : (x : Λ).1 = g * (g⁻¹ * (x : Λ).1 * g) * g⁻¹ := by group
    rcases upperShift_eq_zero _ (hb x) h2 with h4 | h4
    · left; rw [h5, h4]; simp
    · right; rw [h5, h4]; simp
  have hcyc : IsCyclic φ.range := inferInstance
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := φ.range)
  obtain ⟨γ0, hγ0⟩ := r.2
  refine ⟨γ0, ?_, fun γ => ?_⟩
  · rcases upper_unipotent_cases _ (hb γ0) with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨g, k, Or.inl ?_⟩
      have : (γ0 : Λ).1 = g * (g⁻¹ * (γ0 : Λ).1 * g) * g⁻¹ := by group
      rw [this, hk]
    · refine ⟨g, k, Or.inr ?_⟩
      have : (γ0 : Λ).1 = g * (g⁻¹ * (γ0 : Λ).1 * g) * g⁻¹ := by group
      rw [this, hk]; simp [mul_assoc]
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hr ⟨φ γ, ⟨γ, rfl⟩⟩)
    have hφj : φ (γ * γ0⁻¹ ^ j) = 1 := by
      have h1 : φ γ = (r : Subgroup.zpowers ModularGroup.T) ^ j := by
        have := congrArg Subtype.val hj
        simpa using this.symm
      rw [map_mul, map_zpow, map_inv, hγ0, h1]
      simp
    refine ⟨j, ?_⟩
    have hc : ((γ * γ0⁻¹ ^ j : leviCuspStab Λ F) : Λ).1 = (γ : Λ).1 * ((γ0 : Λ).1 ^ j)⁻¹ := by
      simp
    rcases hker _ hφj with h | h
    · left
      rw [hc] at h
      exact mul_inv_eq_one.mp h
    · right
      rw [hc] at h
      have := mul_inv_eq_iff_eq_mul.mp h
      rw [this, neg_one_mul]

/-- Parabolic elements have a coboundary at every cusp stabilizer, provided `-1 ∉ Λ` (then every
cusp stabilizer is infinite cyclic, generated by a parabolic element). -/
theorem cusp_coboundary_of_parabolic (hneg : (-1 : SL(2, ℤ)) ∉ Λ) (A : Rep ℂ Λ)
    (c : groupCohomology.cocycles₁ A)
    (hpar : ∀ γ : Λ, IsParabolicSL γ.1 → ∃ u : A, c.1 γ = A.ρ γ u - u) (F : GL (Fin 2) ℚ) :
    ∃ u : A, ∀ γ : leviCuspStab Λ F, c.1 (γ : Λ) = A.ρ (γ : Λ) u - u := by
  obtain ⟨γ0, hγ0p, hγ0⟩ := cusp_gen (Λ := Λ) F
  obtain ⟨u, hu⟩ := hpar (γ0 : Λ) hγ0p
  refine ⟨u, fun γ => ?_⟩
  have hmem : ((γ0 : Λ)) ∈ cobStab A c u := hu
  obtain ⟨j, hj | hj⟩ := hγ0 γ
  · have hz : (γ : Λ) ∈ Subgroup.zpowers (γ0 : Λ) :=
      Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext (by simpa using hj.symm)⟩
    exact (Subgroup.zpowers_le.mpr hmem) hz
  · exfalso
    apply hneg
    have h1 : (γ0 : Λ).1 ^ j ∈ Λ := Λ.zpow_mem (γ0 : Λ).2 j
    have h2 : (γ : Λ).1 * ((γ0 : Λ).1 ^ j)⁻¹ ∈ Λ := Λ.mul_mem (γ : Λ).2 (Λ.inv_mem h1)
    have h3 : (γ : Λ).1 * ((γ0 : Λ).1 ^ j)⁻¹ = -1 := by
      rw [hj, neg_mul, mul_inv_cancel]
    rw [← h3]; exact h2

/-- **Parabolic elements have a coboundary at every cusp stabilizer when `-1 ∈ Λ` acts by `±1`.**
The stabilizer of a cusp is generated by one parabolic `γ₀` and `-1`. If `-1` acts trivially its
cocycle value vanishes and `γ₀` decides; if it acts by `-1` the class of the cocycle is already
trivial on the group generated by `γ₀` and `-1`, with `u = -(1/2) c(-1)`. -/
theorem cusp_coboundary_of_parabolic_neg_one (hz : (-1 : SL(2, ℤ)) ∈ Λ) (A : Rep ℂ Λ)
    (hε : A.ρ ⟨-1, hz⟩ = 1 ∨ A.ρ ⟨-1, hz⟩ = -1) (c : groupCohomology.cocycles₁ A)
    (hpar : ∀ γ : Λ, IsParabolicSL γ.1 → ∃ u : A, c.1 γ = A.ρ γ u - u) (F : GL (Fin 2) ℚ) :
    ∃ u : A, ∀ γ : leviCuspStab Λ F, c.1 (γ : Λ) = A.ρ (γ : Λ) u - u := by
  obtain ⟨γ0, hγ0p, hγ0⟩ := cusp_gen (Λ := Λ) F
  set z : Λ := ⟨-1, hz⟩ with hzdef
  have hzz : z * z = 1 := by
    apply Subtype.ext
    simp [hzdef]
  have hc1 : c.1 (z * z) = A.ρ z (c.1 z) + c.1 z :=
    (groupCohomology.mem_cocycles₁_iff c.1).mp c.2 z z
  have h1c : c.1 1 = 0 := groupCohomology.cocycles₁_map_one c
  rw [hzz, h1c] at hc1
  have hcomm : z * (γ0 : Λ) = (γ0 : Λ) * z := by
    apply Subtype.ext
    simp [hzdef]
  have hsplit : ∀ (u : A), (z ∈ cobStab A c u) → ((γ0 : Λ) ∈ cobStab A c u) →
      ∀ γ : leviCuspStab Λ F, c.1 (γ : Λ) = A.ρ (γ : Λ) u - u := by
    intro u hzu hγu γ
    obtain ⟨j, hj | hj⟩ := hγ0 γ
    · have hz' : (γ : Λ) ∈ Subgroup.zpowers (γ0 : Λ) :=
        Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext (by simpa using hj.symm)⟩
      exact (Subgroup.zpowers_le.mpr hγu) hz'
    · have hmem : (γ : Λ) = z * (γ0 : Λ) ^ j := by
        apply Subtype.ext
        simp [hzdef, hj]
      have : z * (γ0 : Λ) ^ j ∈ cobStab A c u :=
        (cobStab A c u).mul_mem hzu ((cobStab A c u).zpow_mem hγu j)
      rw [← hmem] at this
      exact this
  rcases hε with hε | hε
  · -- `-1` acts trivially: `c(-1) = 0`
    have hcz : c.1 z = 0 := by
      rw [hε, Module.End.one_apply] at hc1
      have h2 : (2 : ℂ) • c.1 z = 0 := by
        rw [two_smul]; exact hc1.symm
      exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
    obtain ⟨u, hu⟩ := hpar (γ0 : Λ) hγ0p
    refine ⟨u, hsplit u ?_ hu⟩
    change c.1 z = A.ρ z u - u
    rw [hcz, hε, Module.End.one_apply, sub_self]
  · -- `-1` acts by `-1`: `u = -(1/2) c(-1)`
    set u₀ : A := (-(1 / 2 : ℂ)) • c.1 z with hu₀
    refine ⟨u₀, hsplit u₀ ?_ ?_⟩
    · change c.1 z = A.ρ z u₀ - u₀
      rw [hε, LinearMap.neg_apply, Module.End.one_apply, hu₀]
      module
    · change c.1 (γ0 : Λ) = A.ρ (γ0 : Λ) u₀ - u₀
      have r1 := (groupCohomology.mem_cocycles₁_iff c.1).mp c.2 z (γ0 : Λ)
      have r2 := (groupCohomology.mem_cocycles₁_iff c.1).mp c.2 (γ0 : Λ) z
      rw [hcomm, r2, hε, LinearMap.neg_apply, Module.End.one_apply] at r1
      rw [hu₀, map_smul]
      linear_combination (norm := module) (1 / 2 : ℂ) • r1

theorem parabolic_of_cusp_coboundary (A : Rep ℂ Λ) (c : groupCohomology.cocycles₁ A)
    (hcusp : ∀ F : GL (Fin 2) ℚ, ∃ u : A, ∀ γ : leviCuspStab Λ F, c.1 (γ : Λ) = A.ρ (γ : Λ) u - u)
    (γ : Λ) (hγ : IsParabolicSL γ.1) : ∃ u : A, c.1 γ = A.ρ γ u - u := by
  obtain ⟨g, k, hk⟩ := hγ
  have hmem : γ ∈ leviCuspStab Λ (SpecialLinearGroup.mapGL ℚ g) := by
    rw [mem_leviCuspStab_iff]
    have e2 : (((SpecialLinearGroup.mapGL ℚ g)⁻¹ * SpecialLinearGroup.mapGL ℚ γ.1 *
        SpecialLinearGroup.mapGL ℚ g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
        ((SpecialLinearGroup.mapGL ℚ (g⁻¹ * γ.1 * g) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
      rw [map_mul, map_mul, map_inv]
    rw [e2, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    have h10 : ((g⁻¹ * γ.1 * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
      rcases hk with hk | hk
      · have : g⁻¹ * γ.1 * g = ModularGroup.T ^ k := by rw [hk]; group
        rw [this, ModularGroup.coe_T_zpow]; simp
      · have : g⁻¹ * γ.1 * g = -(ModularGroup.T ^ k) := by
          rw [hk]; simp [mul_assoc]
        rw [this, Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]; simp
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, h10, map_zero]
  obtain ⟨u, hu⟩ := hcusp (SpecialLinearGroup.mapGL ℚ g)
  exact ⟨u, hu ⟨γ, hmem⟩⟩

end ParabolicCusps

section Restriction

variable {G : Type} [Group G]

/-- Restriction `H¹(G, A) → H¹(B, A)` to a subgroup `B ≤ G` (Mathlib's `groupCohomology.map` along
the inclusion). -/
def oneRestriction (B : Subgroup G) (A : Rep ℂ G) :
    groupCohomology.H1 A →ₗ[ℂ] groupCohomology.H1 (Rep.res B.subtype A) :=
  (groupCohomology.map B.subtype (𝟙 (Rep.res B.subtype A)) 1).hom

theorem oneRestriction_π (B : Subgroup G) (A : Rep ℂ G) (c : groupCohomology.cocycles₁ A) :
    oneRestriction B A (groupCohomology.H1π A c) =
      groupCohomology.H1π (Rep.res B.subtype A)
        (groupCohomology.mapCocycles₁ B.subtype (𝟙 (Rep.res B.subtype A)) c) :=
  groupCohomology.H1π_comp_map_apply B.subtype (𝟙 (Rep.res B.subtype A)) c

theorem oneRestriction_π_eq_zero_iff (B : Subgroup G) (A : Rep ℂ G)
    (c : groupCohomology.cocycles₁ A) :
    oneRestriction B A (groupCohomology.H1π A c) = 0 ↔
      ∃ u : A, ∀ γ : B, c.1 (γ : G) = A.ρ (γ : G) u - u := by
  have hc : ∀ γ : B, ((ConcreteCategory.hom (groupCohomology.mapCocycles₁ B.subtype
      (𝟙 (Rep.res B.subtype A)))) c) γ = c.1 (γ : G) := fun γ => rfl
  rw [oneRestriction_π, groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun γ => ?_⟩
    have := congrFun hu γ
    simp only [groupCohomology.d₀₁_hom_apply] at this
    rw [← hc γ, ← this]
    rfl
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    funext γ
    simp only [groupCohomology.d₀₁_hom_apply]
    rw [hc γ, hu γ]
    rfl

end Restriction

section Cuspidal

variable (Λ : Subgroup SL(2, ℤ))

/-- **The cuspidal subspace of `H¹(Λ, V)`**: the classes whose restriction to the stabilizer in `Λ`
of every rational cusp (every frame `F ∈ GL₂(ℚ)`) vanishes. For `V = H¹(N_P, E)` this is the mixed
cuspidal group `𝒞_P(E)` of the paper: the subspace of
`H¹(L_P, H¹(N_P, E))` "whose restrictions at all rational cusps of the binary Levi vanish". -/
def cuspidalSubspace (V : Rep ℂ Λ) : Submodule ℂ (groupCohomology.H1 V) :=
  ⨅ F : GL (Fin 2) ℚ, LinearMap.ker (oneRestriction (leviCuspStab Λ F) V)

variable {Λ}

theorem mem_cuspidalSubspace_π (V : Rep ℂ Λ) (c : groupCohomology.cocycles₁ V) :
    groupCohomology.H1π V c ∈ cuspidalSubspace Λ V ↔
      ∀ F : GL (Fin 2) ℚ, ∃ u : V, ∀ γ : leviCuspStab Λ F, c.1 (γ : Λ) = V.ρ (γ : Λ) u - u := by
  unfold cuspidalSubspace
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  exact forall_congr' fun F => oneRestriction_π_eq_zero_iff _ V c

/-- The cuspidal condition is invariant under isomorphisms of `Λ`-representations. -/
theorem cuspidal_iso_iff {V W : Rep ℂ Λ} (e : V ≅ W) (x : groupCohomology.H1 V) :
    x ∈ cuspidalSubspace Λ V ↔
      ModuleCat.Hom.hom ((groupCohomology.functor ℂ Λ 1).mapIso e).hom x ∈ cuspidalSubspace Λ W := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    have himg : ModuleCat.Hom.hom ((groupCohomology.functor ℂ Λ 1).mapIso e).hom
        (groupCohomology.H1π V c) = groupCohomology.H1π W
          (groupCohomology.mapCocycles₁ (MonoidHom.id Λ) e.hom c) :=
      groupCohomology.H1π_comp_map_apply (MonoidHom.id Λ) e.hom c
    refine (mem_cuspidalSubspace_π V c).trans (Iff.trans ?_
      (Iff.of_eq (congrArg (fun x : groupCohomology.H1 W => x ∈ cuspidalSubspace Λ W) himg)).symm)
    refine Iff.trans ?_ (mem_cuspidalSubspace_π W (groupCohomology.mapCocycles₁ (MonoidHom.id Λ) e.hom c)).symm
    refine forall_congr' fun F => ?_
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨e.hom.hom u, fun γ => ?_⟩
      have h1 := hu γ
      have h2 : ((groupCohomology.mapCocycles₁ (MonoidHom.id Λ) e.hom c).1 (γ : Λ)) =
          e.hom.hom (c.1 (γ : Λ)) := rfl
      rw [h2, h1, map_sub]
      congr 1
      exact Rep.hom_comm_apply e.hom (γ : Λ) u
    · rintro ⟨u, hu⟩
      refine ⟨e.inv.hom u, fun γ => ?_⟩
      have h1 := hu γ
      have h2 : ((groupCohomology.mapCocycles₁ (MonoidHom.id Λ) e.hom c).1 (γ : Λ)) =
          e.hom.hom (c.1 (γ : Λ)) := rfl
      rw [h2] at h1
      have h3 : ∀ v : V, e.inv.hom (e.hom.hom v) = v := fun v => by simp
      have h4 : c.1 (γ : Λ) = e.inv.hom (e.hom.hom (c.1 (γ : Λ))) := (h3 _).symm
      rw [h4, h1, map_sub]
      congr 1
      exact (Rep.hom_comm_apply e.inv (γ : Λ) u)

end Cuspidal

section Binary

variable (Λ : Subgroup SL(2, ℤ)) (n : ℕ)

theorem mem_parabolicH1_π_iff (c : groupCohomology.cocycles₁ (binRep Λ n)) :
    groupCohomology.H1π (binRep Λ n) c ∈ parabolicH1 Λ n ↔ c ∈ parabolicCocycles Λ n := by
  constructor
  · rintro ⟨c', hc', hcc⟩
    have h := (groupCohomology.H1π_eq_iff c' c).mp hcc
    obtain ⟨w, hw⟩ := h
    intro γ hγ
    obtain ⟨u, hu⟩ := hc' γ hγ
    refine ⟨u - w, ?_⟩
    have hw' := congrFun hw γ
    simp only [groupCohomology.d₀₁_hom_apply, Pi.sub_apply] at hw'
    have : c γ = c' γ - ((binRep Λ n).ρ γ w - w) := by
      rw [hw']; abel
    rw [this, hu, map_sub]
    abel
  · intro hc
    exact ⟨c, hc, rfl⟩

variable {Λ n}

omit n in
/-- `-1` acts on `Sym^{d} ⊗ det^{twist}` (of `SL₂(ℤ)`) by `-1` when `d` is odd. -/
theorem modularBinaryRep_neg_one_odd (degree : ℕ) (twist : ℤ) (odd : Odd degree)
    (polynomial : Binary.HomogeneousPoly degree) :
    (modularBinaryRep degree twist).ρ (-1) polynomial = -polynomial := by
  apply Subtype.ext
  change ((arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL (-1)) polynomial).val = _
  rw [arithmeticBinaryRep_specialLinear_coe]
  have matrix_eq : (((-1 : SpecialLinearGroup (Fin 2) ℤ)⁻¹).val.map (Int.castRingHom ℂ)) =
      Matrix.scalar (Fin 2) (-1 : ℂ) := by
    rw [SpecialLinearGroup.SL2_inv_expl]
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.map]
  rw [matrix_eq, binary_substitute_scalar, odd.neg_one_pow, neg_smul, one_smul]
  rfl

/-- `-1` acts on `Sym^{n+1} ⊗ det⁻¹` by the scalar `(-1)^{n+1}`. -/
theorem binRep_neg_one (hz : (-1 : SL(2, ℤ)) ∈ Λ) (n : ℕ) :
    (binRep Λ n).ρ ⟨-1, hz⟩ = 1 ∨ (binRep Λ n).ρ ⟨-1, hz⟩ = -1 := by
  rcases Nat.even_or_odd (n + 1) with he | ho
  · left
    apply LinearMap.ext
    intro P
    exact modularBinaryRep_neg_one (n + 1) (-1) he P
  · right
    apply LinearMap.ext
    intro P
    exact modularBinaryRep_neg_one_odd (n + 1) (-1) ho P

/-- **Mixed cuspidal = parabolic, for the binary representation.** For every subgroup
`Λ ⊆ SL₂(ℤ)`, a class of `H¹(Λ, Sym^{n+1} ⊗ det⁻¹)` restricts to zero at the stabilizer of every
rational cusp iff it is parabolic (has a representative cocycle that is a coboundary on every
parabolic element). -/
theorem mem_cuspidalSubspace_binRep_iff
    (x : groupCohomology.H1 (binRep Λ n)) :
    x ∈ cuspidalSubspace Λ (binRep Λ n) ↔ x ∈ parabolicH1 Λ n := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    rw [mem_cuspidalSubspace_π, mem_parabolicH1_π_iff]
    constructor
    · intro h γ hγ
      exact parabolic_of_cusp_coboundary (binRep Λ n) c h γ hγ
    · intro h F
      by_cases hz : (-1 : SL(2, ℤ)) ∈ Λ
      · exact cusp_coboundary_of_parabolic_neg_one hz (binRep Λ n) (binRep_neg_one hz n) c h F
      · exact cusp_coboundary_of_parabolic hz (binRep Λ n) c h F

end Binary

section GammaN

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **The mixed cuspidal group `𝒞_P(E)` of the paper's plane group `Γ_P = Γ(N) ∩ P(ℤ)`**: the subspace of `H¹(L_P, H¹(N_P, E))`, `L_P = Γ₂(N)`, `N_P = Nℤ²`, whose
restrictions at all rational cusps of the binary Levi vanish. Here `H¹(N_P, E)` is the literal
radical cohomology as a `Γ₂(N)`-module (`splitRadicalH1Representation`), not its identification with
`Sym^{n+1} ⊗ det⁻¹`. -/
def gammaNCuspidal : Submodule ℂ
    (groupCohomology.H1 (splitRadicalH1Representation (gammaNSplitting N) (gammaNRep N n))) :=
  cuspidalSubspace (CongruenceSubgroup.Gamma N)
    (splitRadicalH1Representation (gammaNSplitting N) (gammaNRep N n))

/-- **Comparison (one plane cusp).** For `N ≥ 3`, a class of `H¹(Γ₂(N), H¹(Nℤ², E))` vanishes at all
rational cusps iff its binary coordinate in `H¹(Γ₂(N), Sym^{n+1} ⊗ det⁻¹)` is parabolic. -/
theorem mem_gammaNCuspidal_iff
    (x : groupCohomology.H1 (splitRadicalH1Representation (gammaNSplitting N) (gammaNRep N n))) :
    x ∈ gammaNCuspidal N n ↔
      ModuleCat.Hom.hom (gammaNLeviIso N n).hom x ∈ parabolicH1 (CongruenceSubgroup.Gamma N) n :=
  (cuspidal_iso_iff (gammaNCoordinateIso N n) x).trans
    (mem_cuspidalSubspace_binRep_iff _)

theorem gammaNEdge_mem_parabolic_iff
    (x : ↥(twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n)).ker) :
    gammaNEdge N n x ∈ parabolicH1 (CongruenceSubgroup.Gamma N) n ↔
      splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n) x ∈ gammaNCuspidal N n :=
  (mem_gammaNCuspidal_iff N n _).symm

/-- Under `ESSpan`, every parabolic class is the edge of a combination of seeds. -/
theorem parabolicH1_le_map_gammaNEdge (hES : ESSpan (CongruenceSubgroup.Gamma N) n) :
    parabolicH1 (CongruenceSubgroup.Gamma N) n ≤
      Submodule.map (gammaNEdge N n) (gammaNSeedKerSpan N n) := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  refine hES.trans (Submodule.span_le.2 ?_)
  rintro _ (⟨f, rfl⟩ | ⟨f, rfl⟩)
  · refine ⟨((n : ℂ) + 1) • gammaNSeedKerClass N n f, Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl ⟨f, rfl⟩)), ?_⟩
    rw [map_smul, gammaNSeedKerClass, gammaNSeedEdge, smul_smul, mul_inv_cancel₀ hn, one_smul]
  · refine ⟨((n : ℂ) + 1) • gammaNSeedConjKerClass N n f, Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨f, rfl⟩)), ?_⟩
    rw [map_smul, gammaNSeedConjKerClass, gammaNSeedConjEdge, smul_smul, mul_inv_cancel₀ hn,
      one_smul]

/-- The seeds have edges in the mixed cuspidal group (unconditional). -/
theorem gammaNSeedKerSpan_map_edge_le_cuspidal :
    Submodule.map (splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n))
        (gammaNSeedKerSpan N n) ≤ gammaNCuspidal N n := by
  rintro _ ⟨x, hx, rfl⟩
  exact (gammaNEdge_mem_parabolic_iff N n x).mp (gammaNSeedKerSpan_le_comap N n hx)

/-- **Lemma C.3, last sentence, at one plane cusp (conditional on `ESSpan (Γ(N))`).** For `N ≥ 3`
the images, under the Hochschild--Serre edge `H²(Γ_P, E) ⊇ ker(res to N_P) → H¹(L_P, H¹(N_P, E))`,
of the holomorphic and antiholomorphic seeds span exactly the mixed cuspidal group `𝒞_P(E)`. -/
theorem gammaNSeedKerSpan_map_edge_eq_cuspidal
    (hES : ESSpan (CongruenceSubgroup.Gamma N) n) :
    Submodule.map (splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n))
        (gammaNSeedKerSpan N n) = gammaNCuspidal N n := by
  apply le_antisymm
  · exact gammaNSeedKerSpan_map_edge_le_cuspidal N n
  · intro m hm
    have hm' := (mem_gammaNCuspidal_iff N n m).mp hm
    obtain ⟨x, hx, hxm⟩ := parabolicH1_le_map_gammaNEdge N n hES hm'
    refine ⟨x, hx, ?_⟩
    have hinj : Function.Injective (ModuleCat.Hom.hom (gammaNLeviIso N n).hom) := by
      intro a b hab
      have h' := congrArg (ModuleCat.Hom.hom (gammaNLeviIso N n).inv) hab
      have e : ∀ z, (ModuleCat.Hom.hom (gammaNLeviIso N n).inv)
          ((ModuleCat.Hom.hom (gammaNLeviIso N n).hom) z) = z := fun z =>
        congrArg (fun φ => ModuleCat.Hom.hom φ z) (gammaNLeviIso N n).hom_inv_id
      simpa [e] using h'
    apply hinj
    exact hxm


/-- The image of `𝒞_P(E)` in `H²(Γ_P, E_n)` under the inverse of the Hochschild--Serre edge: the
classes with zero restriction to the radical `N_P` whose mixed class lies in `𝒞_P(E)` (the
injection of the mixed cuspidal group into degree-two face cohomology). -/
def gammaNCuspidalInH2 : Submodule ℂ (groupCohomology.H2 (gammaNRep N n)) :=
  Submodule.map (LinearMap.ker (twoCohomologyRestriction (gammaNExt N).inl
    (gammaNRep N n))).subtype
    (Submodule.comap (splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n)) (gammaNCuspidal N n))

theorem mem_gammaNCuspidalInH2_iff (y : groupCohomology.H2 (gammaNRep N n)) :
    y ∈ gammaNCuspidalInH2 N n ↔
      ∃ hy : twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n) y = 0,
        splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n) ⟨y, hy⟩ ∈ gammaNCuspidal N n := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, h, rfl⟩

/-- The seed span lies in the image of the mixed cuspidal group (unconditional). -/
theorem gammaNSeedSpan_le_cuspidalInH2 :
    gammaNSeedSpan N n ≤ gammaNCuspidalInH2 N n := by
  rw [gammaNSeedSpan, Submodule.span_le]
  rintro _ (⟨f, rfl⟩ | ⟨f, rfl⟩)
  · refine ⟨gammaNSeedKerClass N n f, ?_, (complexifyG_cuspSeedClass f).symm⟩
    exact gammaNSeedKerSpan_map_edge_le_cuspidal N n ⟨_, Submodule.subset_span (Or.inl ⟨f, rfl⟩), rfl⟩
  · refine ⟨gammaNSeedConjKerClass N n f, ?_, (complexifyG_cuspSeedConjClass f).symm⟩
    exact gammaNSeedKerSpan_map_edge_le_cuspidal N n ⟨_, Submodule.subset_span (Or.inr ⟨f, rfl⟩), rfl⟩

/-- **Lemma C.3, last sentence, at one plane cusp, in `H²(Γ_P, E)` (conditional on
`ESSpan (Γ(N))`).** For `N ≥ 3` the span of the complexified de Rham classes of the holomorphic and
antiholomorphic seeds is exactly the image of the mixed cuspidal group `𝒞_P(E)` in degree-two
cohomology. -/
theorem gammaNSeedSpan_eq_cuspidalInH2 (hES : ESSpan (CongruenceSubgroup.Gamma N) n) :
    gammaNSeedSpan N n = gammaNCuspidalInH2 N n := by
  refine le_antisymm (gammaNSeedSpan_le_cuspidalInH2 N n) ?_
  intro y hy
  obtain ⟨hy0, h⟩ := (mem_gammaNCuspidalInH2_iff N n y).mp hy
  exact gammaN_seed_span_conditional N n hES y hy0
    ((gammaNEdge_mem_parabolic_iff N n ⟨y, hy0⟩).mpr h)

end GammaN





section Level

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (Λ : Subgroup SL(2, ℤ)) (n : ℕ)

/-- **The mixed cuspidal group `𝒞_P(E)` of the plane group `ℤ² ⋊ Λ`** (radical `ℤ²`, Levi `Λ`):
the classes of `H¹(Λ, H¹(ℤ², E_n))` restricting to zero at every rational cusp of `Λ`. -/
def levelCuspidal : Submodule ℂ
    (groupCohomology.H1 (splitRadicalH1Representation (levelSplitting Λ) (levelRep Λ n))) :=
  cuspidalSubspace Λ (splitRadicalH1Representation (levelSplitting Λ) (levelRep Λ n))

variable {Λ n}

/-- For `-1 ∉ Λ`, `𝒞_P(E)` of `ℤ² ⋊ Λ` consists of the classes with parabolic coordinate. -/
theorem mem_levelCuspidal_iff 
    (x : groupCohomology.H1 (splitRadicalH1Representation (levelSplitting Λ) (levelRep Λ n))) :
    x ∈ levelCuspidal Λ n ↔
      ModuleCat.Hom.hom (levelLeviIso Λ n).hom x ∈ parabolicH1 Λ n :=
  (cuspidal_iso_iff (levelCoordinateIso Λ n) x).trans
    (mem_cuspidalSubspace_binRep_iff _)

theorem levelEdge_mem_parabolic_iff
    (x : ↥(twoCohomologyRestriction (levelExt Λ).inl (levelRep Λ n)).ker) :
    levelEdge Λ n x ∈ parabolicH1 Λ n ↔
      splitCohomologyEdge (levelSplitting Λ) (levelRep Λ n) x ∈ levelCuspidal Λ n :=
  (mem_levelCuspidal_iff _).symm

/-- Under `ESSpan`, every parabolic class is the edge of a combination of seeds on `ℤ² ⋊ Λ`. -/
theorem parabolicH1_le_map_levelEdge (hES : ESSpan Λ n) :
    parabolicH1 Λ n ≤ Submodule.map (levelEdge Λ n) (seedKerSpan Λ n) := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  refine hES.trans (Submodule.span_le.2 ?_)
  rintro _ (⟨f, rfl⟩ | ⟨f, rfl⟩)
  · refine ⟨((n : ℂ) + 1) • seedKerClass f, Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl ⟨f, rfl⟩)), ?_⟩
    rw [map_smul, seedKerClass, levelSeedEdge, smul_smul, mul_inv_cancel₀ hn, one_smul]
  · refine ⟨((n : ℂ) + 1) • seedConjKerClass f, Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨f, rfl⟩)), ?_⟩
    rw [map_smul, seedConjKerClass, levelSeedConjEdge, smul_smul, mul_inv_cancel₀ hn, one_smul]

/-- The seeds on `ℤ² ⋊ Λ` have edges in the mixed cuspidal group (unconditional, `-1 ∉ Λ`). -/
theorem seedKerSpan_map_edge_le_levelCuspidal :
    Submodule.map (splitCohomologyEdge (levelSplitting Λ) (levelRep Λ n)) (seedKerSpan Λ n) ≤
      levelCuspidal Λ n := by
  rintro _ ⟨x, hx, rfl⟩
  exact (levelEdge_mem_parabolic_iff x).mp (seedKerSpan_le_comap hx)

/-- **Lemma C.3, last sentence, at the plane group `ℤ² ⋊ Λ` (conditional on `ESSpan Λ n`,
`-1 ∉ Λ`).** The Hochschild--Serre edges of the holomorphic and antiholomorphic seeds span the mixed
cuspidal group `𝒞_P(E)`. Instances: `Λ = Γ₂(N)` (`N ≥ 3`) and the level-three Levi block
`Λ = Γ₁(3)` (`ESSpan` by `esSpan_gam3`). -/
theorem seedKerSpan_map_edge_eq_levelCuspidal (hES : ESSpan Λ n) :
    Submodule.map (splitCohomologyEdge (levelSplitting Λ) (levelRep Λ n)) (seedKerSpan Λ n) =
      levelCuspidal Λ n := by
  apply le_antisymm seedKerSpan_map_edge_le_levelCuspidal
  intro m hm
  have hm' := (mem_levelCuspidal_iff m).mp hm
  obtain ⟨x, hx, hxm⟩ := parabolicH1_le_map_levelEdge hES hm'
  refine ⟨x, hx, ?_⟩
  have hinj : Function.Injective (ModuleCat.Hom.hom (levelLeviIso Λ n).hom) := by
    intro a b hab
    have h' := congrArg (ModuleCat.Hom.hom (levelLeviIso Λ n).inv) hab
    have e : ∀ z, (ModuleCat.Hom.hom (levelLeviIso Λ n).inv)
        ((ModuleCat.Hom.hom (levelLeviIso Λ n).hom) z) = z := fun z =>
      congrArg (fun φ => ModuleCat.Hom.hom φ z) (levelLeviIso Λ n).hom_inv_id
    simpa [e] using h'
  apply hinj
  exact hxm

end Level

end TernaryPeriodPolynomials.Argument.SeedC3S4c
