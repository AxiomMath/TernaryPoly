module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChiHom
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Prism
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2DoublePrism
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Torus
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Matrices
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.SquareResolution
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerResolution

@[expose] public section


/-!
# The boundary trace from the cusp cycles, up to the orientation comparisons

For each of the four vertices of the quotient graph `L₁ – e₂ – P₁ – e₁ – L₀ – e₀ – P₀` the unipotent
radical of the stabilizer contains a lattice `ℤ²`, embedded by explicit matrices; it has a free
resolution of length two (the square tiling), so `H³(ℤ², ℂ) = 0`, and the torus two-chain `σ` of its
two generators is a cycle modulo the lattice. Every Levi generator acts on the lattice by a matrix of
determinant one, so it is a Levi element in the sense of `ChiHom`, and the cusp cycles
`C(m) = P_m σ − ρ_m` are defined. The group relations `T = E L`, `E³ = 1` (at `L₀`), `T' = E' L'`,
`E'³ = 1` (at `P₁`) and `T₀ = U₆ g₄`, `U₆⁶ = g₄⁴ = 1` (at `P₀` and `L₁`) give the vertex relations
`C(T) ≡ C(L)`, `C(T') ≡ C(L')` and `C(T₀) ≡ 0` modulo boundaries.

The trace uses the line-side cycles `C_{e₀} = C_{L₀}(T)`, `C_{e₁} = −C_{L₀}(L)`,
`C_{e₂} = t₂ C_{L₁}(T₀)`. The plane vertex relations then need the comparison of the line-side and
plane-side cycles of each complete flag (the orientation of the Heisenberg nilmanifold of the edge,
seen from its two fibrations); these three comparisons are the hypotheses of
`traceData_of_comparisons`, which assembles the chain data of a boundary trace.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.L2Assembly

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing (homogeneousBoundary FreeResolution)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus
open TernaryPeriodPolynomials.BoundaryDuality.ChainDuality
open TernaryPeriodPolynomials.BoundaryDuality.LowVanishing
open TernaryPeriodPolynomials.BoundaryDuality.ChiHom
open TernaryPeriodPolynomials.BoundaryDuality.L2Prism
open TernaryPeriodPolynomials.BoundaryDuality.L2DoublePrism
open TernaryPeriodPolynomials.BoundaryDuality.L2Torus
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
open TernaryPeriodPolynomials.BoundaryDuality.SquareResolution
open TernaryPeriodPolynomials.BoundaryDuality.StabilizerResolution

/-- The prism and double prism operators of `L2Prism` and `L2DoublePrism`. -/
def prismData (G : Type) [Group G] : PrismData G where
  P1 := prism1
  P2 := prism2
  P3 := prism3
  Q1 := dprism1
  Q2 := dprism2
  prism_two := prism2_homotopy
  prism_three := prism3_homotopy
  dprism_two := dprism2_boundary
  P2_left := prism2_leftTranslate
  P1_null := fun _ h _ hc => prism1_mem_null h hc
  P2_null := fun _ h _ hc => prism2_mem_null h hc
  Q1_null := fun _ h k _ hc => dprism1_mem_null h k hc

section Lattice

/-- An embedded lattice `ℤ² → G`: an injective additive parametrization `(x, y) ↦ u x y`. -/
structure Lattice (G : Type) [Group G] where
  /-- The parametrization. -/
  u : ℤ → ℤ → G
  u_mul : ∀ x y x' y', u x y * u x' y' = u (x + x') (y + y')
  u_inj : ∀ x y x' y', u x y = u x' y' → x = x' ∧ y = y'

namespace Lattice

variable {G : Type} [Group G] (Ω : Lattice G)

theorem u_zero : Ω.u 0 0 = 1 := by
  have h := Ω.u_mul 0 0 0 0
  rw [add_zero] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

/-- The parametrization as a homomorphism. -/
def hom : Multiplicative (ℤ × ℤ) →* G where
  toFun p := Ω.u (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2
  map_one' := Ω.u_zero
  map_mul' _ _ := (Ω.u_mul _ _ _ _).symm

theorem hom_injective : Function.Injective Ω.hom := fun p q h => by
  obtain ⟨h1, h2⟩ := Ω.u_inj _ _ _ _ h
  exact Multiplicative.toAdd.injective (Prod.ext h1 h2)

/-- The lattice as a subgroup. -/
abbrev sub : Subgroup G := Ω.hom.range

theorem u_mem (x y : ℤ) : Ω.u x y ∈ Ω.sub := ⟨Multiplicative.ofAdd (x, y), rfl⟩

theorem commute : Commute (Ω.u 1 0) (Ω.u 0 1) := by
  show Ω.u 1 0 * Ω.u 0 1 = Ω.u 0 1 * Ω.u 1 0
  rw [Ω.u_mul, Ω.u_mul, add_comm (1 : ℤ) 0]

theorem u_eq_zpow (x y : ℤ) : Ω.u x y = Ω.u 1 0 ^ x * Ω.u 0 1 ^ y := by
  have hx : Ω.u x 0 = Ω.u 1 0 ^ x := by
    have e : (Multiplicative.ofAdd (x, (0 : ℤ)) : Multiplicative (ℤ × ℤ)) =
        Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ)) ^ x := by
      rw [← ofAdd_zsmul]
      simp
    have := congrArg Ω.hom e
    rw [map_zpow] at this
    exact this
  have hy : Ω.u 0 y = Ω.u 0 1 ^ y := by
    have e : (Multiplicative.ofAdd ((0 : ℤ), y) : Multiplicative (ℤ × ℤ)) =
        Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ)) ^ y := by
      rw [← ofAdd_zsmul]
      simp
    have := congrArg Ω.hom e
    rw [map_zpow] at this
    exact this
  rw [← hx, ← hy, Ω.u_mul, add_zero, zero_add]

/-- `H³` of the lattice vanishes: restriction of the square resolution. -/
theorem topVanishingThree : TopVanishingThree Ω.sub :=
  topVanishingThree_of_freeResolution (restrictResolution squareResolution
    (MonoidHom.ofInjective Ω.hom_injective).symm.toMonoidHom
    (MonoidHom.ofInjective Ω.hom_injective).symm.injective)

/-- The torus two-chain of the two generators. -/
def σ : Chains G 2 := sigma (Ω.u 1 0) (Ω.u 0 1)

theorem boundary_σ : homogeneousBoundary 2 Ω.σ ∈ NullChains Ω.sub 1 :=
  boundary_sigma_mem_null (Ω.u_mem 1 0) (Ω.u_mem 0 1) Ω.commute

end Lattice

variable {G : Type} [Group G]

/-- Conjugation of the torus chain. -/
theorem conjugate_sigma (m u v : G) :
    conjugate m 2 (sigma u v) = sigma (m⁻¹ * u * m) (m⁻¹ * v * m) := by
  simp only [sigma, bar2, map_sub, conjugate_single]
  congr 2 <;> (funext i; fin_cases i <;> simp; group)

/-- **Levi criterion.** An element of `Λ` acting on the lattice by an integral matrix of
determinant one is a Levi element for the torus chain. -/
theorem isLevi_of_conj (Ω : Lattice G) {Λ : Subgroup G} {m : G} (hm : m ∈ Λ) {p q r s : ℤ}
    (h1 : m⁻¹ * Ω.u 1 0 * m = Ω.u p q) (h2 : m⁻¹ * Ω.u 0 1 * m = Ω.u r s)
    (hdet : p * s - q * r = 1) : IsLevi Λ Ω.sub Ω.σ m := by
  have conj : ∀ g : G, m⁻¹ * g * m = MulAut.conj m⁻¹ g := fun g => by
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨hm, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    show m⁻¹ * Ω.u (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2 * m ∈ Ω.sub
    rw [Ω.u_eq_zpow, conj, map_mul, map_zpow, map_zpow, ← conj, ← conj, h1, h2]
    exact Ω.sub.mul_mem (Ω.sub.zpow_mem (Ω.u_mem p q) _) (Ω.sub.zpow_mem (Ω.u_mem r s) _)
  · rw [Lattice.σ, conjugate_sigma, h1, h2, Ω.u_eq_zpow p q, Ω.u_eq_zpow r s]
    have := sigma_word_mem_bdry (Ω.u_mem 1 0) (Ω.u_mem 0 1) Ω.commute p q r s
    rwa [hdet, one_smul] at this

end Lattice

section Concrete

/-- A small entrywise matrix computation. -/
local macro "entries" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring))

theorem zuL0_mul (x y x' y' : ℤ) : zuL0 x y * zuL0 x' y' = zuL0 (x + x') (y + y') := by
  apply Units.ext
  simp only [Units.val_mul, zuL0_val]
  entries

theorem zuL1_mul (x y x' y' : ℤ) : zuL1 x y * zuL1 x' y' = zuL1 (x + x') (y + y') := by
  apply Units.ext
  simp only [Units.val_mul, zuL1_val]
  entries

theorem zuP0_mul (x y x' y' : ℤ) : zuP0 x y * zuP0 x' y' = zuP0 (x + x') (y + y') := by
  apply Units.ext
  simp only [Units.val_mul, zuP0_val]
  entries

theorem zuP1_mul (x y x' y' : ℤ) : zuP1 x y * zuP1 x' y' = zuP1 (x + x') (y + y') := by
  apply Units.ext
  simp only [Units.val_mul, zuP1_val]
  entries

/-- The lattice of the line `L₀`. -/
def latL0 : Lattice RationalGL3 where
  u := uL0
  u_mul x y x' y' := by rw [uL0, uL0, uL0, ← map_mul, zuL0_mul]
  u_inj x y x' y' h := by
    have h1 : ((zuL0 x y).val 0 1 : ℚ) = (zuL0 x' y').val 0 1 :=
      congrArg (fun g : RationalGL3 => g.val 0 1) h
    have h2 : ((zuL0 x y).val 0 2 : ℚ) = (zuL0 x' y').val 0 2 :=
      congrArg (fun g : RationalGL3 => g.val 0 2) h
    simp only [zuL0_val] at h1 h2
    norm_num at h1 h2
    exact ⟨h1, h2⟩

/-- The lattice of the line `L₁`. -/
def latL1 : Lattice RationalGL3 where
  u := uL1
  u_mul x y x' y' := by rw [uL1, uL1, uL1, ← map_mul, zuL1_mul]
  u_inj x y x' y' h := by
    have h1 : ((zuL1 x y).val 2 0 : ℚ) = (zuL1 x' y').val 2 0 :=
      congrArg (fun g : RationalGL3 => g.val 2 0) h
    have h2 : ((zuL1 x y).val 2 1 : ℚ) = (zuL1 x' y').val 2 1 :=
      congrArg (fun g : RationalGL3 => g.val 2 1) h
    simp only [zuL1_val] at h1 h2
    simp at h1 h2
    exact ⟨h1, h2⟩

/-- The lattice of the plane `P₀`. -/
def latP0 : Lattice RationalGL3 where
  u := uP0
  u_mul x y x' y' := by rw [uP0, uP0, uP0, ← map_mul, zuP0_mul]
  u_inj x y x' y' h := by
    have h1 : ((zuP0 x y).val 0 2 : ℚ) = (zuP0 x' y').val 0 2 :=
      congrArg (fun g : RationalGL3 => g.val 0 2) h
    have h2 : ((zuP0 x y).val 1 2 : ℚ) = (zuP0 x' y').val 1 2 :=
      congrArg (fun g : RationalGL3 => g.val 1 2) h
    simp only [zuP0_val] at h1 h2
    norm_num at h1 h2
    exact ⟨h1, h2⟩

/-- The lattice of the plane `P₁`. -/
def latP1 : Lattice RationalGL3 where
  u := uP1
  u_mul x y x' y' := by rw [uP1, uP1, uP1, ← map_mul, zuP1_mul]
  u_inj x y x' y' h := by
    have h1 : ((zuP1 x y).val 0 1 : ℚ) = (zuP1 x' y').val 0 1 :=
      congrArg (fun g : RationalGL3 => g.val 0 1) h
    have h2 : ((zuP1 x y).val 2 1 : ℚ) = (zuP1 x' y').val 2 1 :=
      congrArg (fun g : RationalGL3 => g.val 2 1) h
    simp only [zuP1_val] at h1 h2
    simp at h1 h2
    exact ⟨h1, h2⟩

theorem latL0_le : latL0.sub ≤ levelStabilizer L₀ := by
  rintro _ ⟨t, rfl⟩
  exact uL0_mem_levelStabilizer_L₀ _ _

theorem latL1_le : latL1.sub ≤ levelStabilizer L₁ := by
  rintro _ ⟨t, rfl⟩
  exact uL1_mem_levelStabilizer_L₁ _ _

theorem latP0_le : latP0.sub ≤ levelStabilizer P₀ := by
  rintro _ ⟨t, rfl⟩
  exact uP0_mem_levelStabilizer_P₀ _ _

theorem latP1_le : latP1.sub ≤ levelStabilizer P₁ := by
  rintro _ ⟨t, rfl⟩
  exact uP1_mem_levelStabilizer_P₁ _ _

theorem uL0_mem_levelStabilizer_e₀ (x y : ℤ) : uL0 x y ∈ levelStabilizer e₀ :=
  mem_levelStabilizer_one (H := parabolic .plane ⊓ parabolic .line) (uL0_mem_level x y)
    (mem_edgeParabolic (zuL0 x y) (by simp [zuL0_val]) (by simp [zuL0_val]) (by simp [zuL0_val]))

theorem uL0_mem_levelStabilizer_e₁ (x y : ℤ) : uL0 x y ∈ levelStabilizer e₁ :=
  mem_levelStabilizer_edge (zg := zuL0 x y) (zr := zw₁) (uL0_mem_level x y)
    (by
      simp only [Units.val_mul, zw₁_inv_val, zuL0_val, zw₁_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by
      simp only [Units.val_mul, zw₁_inv_val, zuL0_val, zw₁_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by
      simp only [Units.val_mul, zw₁_inv_val, zuL0_val, zw₁_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three])

theorem uL1_mem_levelStabilizer_e₂ (x y : ℤ) : uL1 x y ∈ levelStabilizer e₂ :=
  mem_levelStabilizer_edge (zg := zuL1 x y) (zr := zg₂) (uL1_mem_level x y)
    (by
      simp only [Units.val_mul, zg₂_inv_val, zuL1_val, zg₂_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by
      simp only [Units.val_mul, zg₂_inv_val, zuL1_val, zg₂_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by
      simp only [Units.val_mul, zg₂_inv_val, zuL1_val, zg₂_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three])

theorem latL0_le_e₀ : latL0.sub ≤ levelStabilizer e₀ := by
  rintro _ ⟨t, rfl⟩
  exact uL0_mem_levelStabilizer_e₀ _ _

theorem latL0_le_e₁ : latL0.sub ≤ levelStabilizer e₁ := by
  rintro _ ⟨t, rfl⟩
  exact uL0_mem_levelStabilizer_e₁ _ _

theorem latL1_le_e₂ : latL1.sub ≤ levelStabilizer e₂ := by
  rintro _ ⟨t, rfl⟩
  exact uL1_mem_levelStabilizer_e₂ _ _

/-! ### Levi elements -/

theorem isLevi_T : IsLevi (levelStabilizer L₀) latL0.sub latL0.σ T :=
  isLevi_of_conj latL0 T_mem_levelStabilizer_L₀ (p := 1) (q := 1) (r := 0) (s := 1)
    (by show T⁻¹ * uL0 1 0 * T = uL0 1 1; rw [T_conj_uL0]; norm_num)
    (by show T⁻¹ * uL0 0 1 * T = uL0 0 1; rw [T_conj_uL0]; norm_num) (by norm_num)

theorem isLevi_L : IsLevi (levelStabilizer L₀) latL0.sub latL0.σ L :=
  isLevi_of_conj latL0 L_mem_levelStabilizer_L₀ (p := 1) (q := 0) (r := 3) (s := 1)
    (by show L⁻¹ * uL0 1 0 * L = uL0 1 0; rw [L_conj_uL0]; norm_num)
    (by show L⁻¹ * uL0 0 1 * L = uL0 3 1; rw [L_conj_uL0]; norm_num) (by norm_num)

theorem isLevi_E : IsLevi (levelStabilizer L₀) latL0.sub latL0.σ E :=
  isLevi_of_conj latL0 E_mem_levelStabilizer_L₀ (p := -2) (q := 1) (r := -3) (s := 1)
    (by show E⁻¹ * uL0 1 0 * E = uL0 (-2) 1; rw [E_conj_uL0]; norm_num)
    (by show E⁻¹ * uL0 0 1 * E = uL0 (-3) 1; rw [E_conj_uL0]; norm_num) (by norm_num)

theorem isLevi_T₀_L₁ : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ T₀ :=
  isLevi_of_conj latL1 T₀_mem_levelStabilizer_L₁ (p := 1) (q := 1) (r := 0) (s := 1)
    (by show T₀⁻¹ * uL1 1 0 * T₀ = uL1 1 1; rw [T₀_conj_uL1]; norm_num)
    (by show T₀⁻¹ * uL1 0 1 * T₀ = uL1 0 1; rw [T₀_conj_uL1]; norm_num) (by norm_num)

theorem isLevi_U₆_L₁ : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ U₆ :=
  isLevi_of_conj latL1 U₆_mem_levelStabilizer_L₁ (p := 0) (q := -1) (r := 1) (s := 1)
    (by show U₆⁻¹ * uL1 1 0 * U₆ = uL1 0 (-1); rw [U₆_conj_uL1]; norm_num)
    (by show U₆⁻¹ * uL1 0 1 * U₆ = uL1 1 1; rw [U₆_conj_uL1]; norm_num) (by norm_num)

theorem isLevi_g₄_L₁ : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ g₄ :=
  isLevi_of_conj latL1 g₄_mem_levelStabilizer_L₁ (p := 1) (q := 2) (r := -1) (s := -1)
    (by show g₄⁻¹ * uL1 1 0 * g₄ = uL1 1 2; rw [g₄_conj_uL1]; norm_num)
    (by show g₄⁻¹ * uL1 0 1 * g₄ = uL1 (-1) (-1); rw [g₄_conj_uL1]; norm_num) (by norm_num)

theorem isLevi_T₀_P₀ : IsLevi (levelStabilizer P₀) latP0.sub latP0.σ T₀ :=
  isLevi_of_conj latP0 T₀_mem_levelStabilizer_P₀ (p := 1) (q := 0) (r := -1) (s := 1)
    (by show T₀⁻¹ * uP0 1 0 * T₀ = uP0 1 0; rw [T₀_conj_uP0]; norm_num)
    (by show T₀⁻¹ * uP0 0 1 * T₀ = uP0 (-1) 1; rw [T₀_conj_uP0]; norm_num) (by norm_num)

theorem isLevi_U₆_P₀ : IsLevi (levelStabilizer P₀) latP0.sub latP0.σ U₆ :=
  isLevi_of_conj latP0 U₆_mem_levelStabilizer_P₀ (p := 1) (q := -1) (r := 1) (s := 0)
    (by show U₆⁻¹ * uP0 1 0 * U₆ = uP0 1 (-1); rw [U₆_conj_uP0]; norm_num)
    (by show U₆⁻¹ * uP0 0 1 * U₆ = uP0 1 0; rw [U₆_conj_uP0]; norm_num) (by norm_num)

theorem isLevi_g₄_P₀ : IsLevi (levelStabilizer P₀) latP0.sub latP0.σ g₄ :=
  isLevi_of_conj latP0 g₄_mem_levelStabilizer_P₀ (p := -1) (q := 1) (r := -2) (s := 1)
    (by show g₄⁻¹ * uP0 1 0 * g₄ = uP0 (-1) 1; rw [g₄_conj_uP0]; norm_num)
    (by show g₄⁻¹ * uP0 0 1 * g₄ = uP0 (-2) 1; rw [g₄_conj_uP0]; norm_num) (by norm_num)

theorem isLevi_T' : IsLevi (levelStabilizer P₁) latP1.sub latP1.σ T' :=
  isLevi_of_conj latP1 T'_mem_levelStabilizer_P₁ (p := 1) (q := 0) (r := -3) (s := 1)
    (by show T'⁻¹ * uP1 1 0 * T' = uP1 1 0; rw [T'_conj_uP1]; norm_num)
    (by show T'⁻¹ * uP1 0 1 * T' = uP1 (-3) 1; rw [T'_conj_uP1]; norm_num) (by norm_num)

theorem isLevi_L' : IsLevi (levelStabilizer P₁) latP1.sub latP1.σ L' :=
  isLevi_of_conj latP1 L'_mem_levelStabilizer_P₁ (p := 1) (q := -1) (r := 0) (s := 1)
    (by show L'⁻¹ * uP1 1 0 * L' = uP1 1 (-1); rw [L'_conj_uP1]; norm_num)
    (by show L'⁻¹ * uP1 0 1 * L' = uP1 0 1; rw [L'_conj_uP1]; norm_num) (by norm_num)

theorem isLevi_E' : IsLevi (levelStabilizer P₁) latP1.sub latP1.σ E' :=
  isLevi_of_conj latP1 E'_mem_levelStabilizer_P₁ (p := 1) (q := 1) (r := -3) (s := -2)
    (by show E'⁻¹ * uP1 1 0 * E' = uP1 1 1; rw [E'_conj_uP1]; norm_num)
    (by show E'⁻¹ * uP1 0 1 * E' = uP1 (-3) (-2); rw [E'_conj_uP1]; norm_num) (by norm_num)

/-! ### The cusp cycles and the vertex relations -/

/-- The cusp cycle of `T` at the line `L₀` (complete flag `e₀`). -/
def cycleT : Chains RationalGL3 3 := cusp (prismData RationalGL3) latL0.σ isLevi_T

/-- The cusp cycle of `L` at the line `L₀` (complete flag `e₁`). -/
def cycleL : Chains RationalGL3 3 := cusp (prismData RationalGL3) latL0.σ isLevi_L

/-- The cusp cycle of `T₀` at the line `L₁` (complete flag `e₂`). -/
def cycleT₀L : Chains RationalGL3 3 := cusp (prismData RationalGL3) latL1.σ isLevi_T₀_L₁

/-- The cusp cycle of `T₀` at the plane `P₀` (complete flag `e₀`). -/
def cycleT₀P : Chains RationalGL3 3 := cusp (prismData RationalGL3) latP0.σ isLevi_T₀_P₀

/-- The cusp cycle of `T'` at the plane `P₁` (complete flag `e₁`). -/
def cycleT' : Chains RationalGL3 3 := cusp (prismData RationalGL3) latP1.σ isLevi_T'

/-- The cusp cycle of `L'` at the plane `P₁` (complete flag `e₂`). -/
def cycleL' : Chains RationalGL3 3 := cusp (prismData RationalGL3) latP1.σ isLevi_L'

/-- The vertex relation at `L₀`: `κ(C(T)) = κ(C(L))`. -/
theorem eval_L₀ (κ : (Fin 4 → RationalGL3) → ℂ)
    (hκ : ∀ (γ : levelStabilizer L₀) x, κ (fun i => γ.val * x i) = κ x)
    (closed : ∀ x, differentialThreeRaw κ x = 0) :
    Finsupp.linearCombination ℂ κ cycleT = Finsupp.linearCombination ℂ κ cycleL := by
  rw [cycleT, cycleL, cusp_congr (prismData RationalGL3) T_eq isLevi_T (isLevi_E.mul isLevi_L),
    eval_cusp_mul (prismData RationalGL3) latL0_le latL0.topVanishingThree latL0.boundary_σ κ hκ
      closed isLevi_E isLevi_L (isLevi_E.mul isLevi_L),
    eval_cusp_eq_zero_of_pow (prismData RationalGL3) latL0_le latL0.topVanishingThree
      latL0.boundary_σ κ hκ closed isLevi_E (by norm_num : 0 < 3) E_pow_three, zero_add]

/-- The vertex relation at `L₁`: `κ(C(T₀)) = 0`. -/
theorem eval_L₁ (κ : (Fin 4 → RationalGL3) → ℂ)
    (hκ : ∀ (γ : levelStabilizer L₁) x, κ (fun i => γ.val * x i) = κ x)
    (closed : ∀ x, differentialThreeRaw κ x = 0) :
    Finsupp.linearCombination ℂ κ cycleT₀L = 0 := by
  rw [cycleT₀L, cusp_congr (prismData RationalGL3) T₀_eq isLevi_T₀_L₁
      (isLevi_U₆_L₁.mul isLevi_g₄_L₁),
    eval_cusp_mul (prismData RationalGL3) latL1_le latL1.topVanishingThree latL1.boundary_σ κ hκ
      closed isLevi_U₆_L₁ isLevi_g₄_L₁ (isLevi_U₆_L₁.mul isLevi_g₄_L₁),
    eval_cusp_eq_zero_of_pow (prismData RationalGL3) latL1_le latL1.topVanishingThree
      latL1.boundary_σ κ hκ closed isLevi_U₆_L₁ (by norm_num : 0 < 6) U₆_pow_six,
    eval_cusp_eq_zero_of_pow (prismData RationalGL3) latL1_le latL1.topVanishingThree
      latL1.boundary_σ κ hκ closed isLevi_g₄_L₁ (by norm_num : 0 < 4) g₄_pow_four, add_zero]

/-- The vertex relation at `P₀`: `κ(C(T₀)) = 0`. -/
theorem eval_P₀ (κ : (Fin 4 → RationalGL3) → ℂ)
    (hκ : ∀ (γ : levelStabilizer P₀) x, κ (fun i => γ.val * x i) = κ x)
    (closed : ∀ x, differentialThreeRaw κ x = 0) :
    Finsupp.linearCombination ℂ κ cycleT₀P = 0 := by
  rw [cycleT₀P, cusp_congr (prismData RationalGL3) T₀_eq isLevi_T₀_P₀
      (isLevi_U₆_P₀.mul isLevi_g₄_P₀),
    eval_cusp_mul (prismData RationalGL3) latP0_le latP0.topVanishingThree latP0.boundary_σ κ hκ
      closed isLevi_U₆_P₀ isLevi_g₄_P₀ (isLevi_U₆_P₀.mul isLevi_g₄_P₀),
    eval_cusp_eq_zero_of_pow (prismData RationalGL3) latP0_le latP0.topVanishingThree
      latP0.boundary_σ κ hκ closed isLevi_U₆_P₀ (by norm_num : 0 < 6) U₆_pow_six,
    eval_cusp_eq_zero_of_pow (prismData RationalGL3) latP0_le latP0.topVanishingThree
      latP0.boundary_σ κ hκ closed isLevi_g₄_P₀ (by norm_num : 0 < 4) g₄_pow_four, add_zero]

/-- The vertex relation at `P₁`: `κ(C(T')) = κ(C(L'))`. -/
theorem eval_P₁ (κ : (Fin 4 → RationalGL3) → ℂ)
    (hκ : ∀ (γ : levelStabilizer P₁) x, κ (fun i => γ.val * x i) = κ x)
    (closed : ∀ x, differentialThreeRaw κ x = 0) :
    Finsupp.linearCombination ℂ κ cycleT' = Finsupp.linearCombination ℂ κ cycleL' := by
  rw [cycleT', cycleL', cusp_congr (prismData RationalGL3) T'_eq isLevi_T' (isLevi_E'.mul isLevi_L'),
    eval_cusp_mul (prismData RationalGL3) latP1_le latP1.topVanishingThree latP1.boundary_σ κ hκ
      closed isLevi_E' isLevi_L' (isLevi_E'.mul isLevi_L'),
    eval_cusp_eq_zero_of_pow (prismData RationalGL3) latP1_le latP1.topVanishingThree
      latP1.boundary_σ κ hκ closed isLevi_E' (by norm_num : 0 < 3) E'_pow_three, zero_add]

/-! ### Assembly -/

/-- The comparison of a line-side and a plane-side cusp cycle of a complete flag, for the
three-cocycles invariant under the stabilizer `Λ` of the plane endpoint: `κ(A) = s κ(B)`. -/
def Comparison (Λ : Subgroup RationalGL3) (A B : Chains RationalGL3 3) (s : ℂ) : Prop :=
  ∀ κ : (Fin 4 → RationalGL3) → ℂ, (∀ (γ : Λ) x, κ (fun i => γ.val * x i) = κ x) →
    (∀ x, differentialThreeRaw κ x = 0) →
      Finsupp.linearCombination ℂ κ A = s * Finsupp.linearCombination ℂ κ B

/-- **The chain data of the boundary trace**, given the three orientation comparisons
`κ(C_{L₀}(T)) = s₀ κ(C_{P₀}(T₀))`, `κ(C_{L₀}(L)) = s₁ κ(C_{P₁}(T'))`,
`κ(C_{L₁}(T₀)) = s₂ κ(C_{P₁}(L'))` with `s₂ ≠ 0`: the chains are `C_{L₀}(T)`, `−C_{L₀}(L)` and
`(s₁/s₂) C_{L₁}(T₀)` at the complete flags `e₀, e₁, e₂`. -/
def traceData_of_comparisons (s₀ s₁ s₂ : ℂ) (hs₂ : s₂ ≠ 0)
    (c₀ : Comparison (levelStabilizer P₀) cycleT cycleT₀P s₀)
    (c₁ : Comparison (levelStabilizer P₁) cycleL cycleT' s₁)
    (c₂ : Comparison (levelStabilizer P₁) cycleT₀L cycleL' s₂) :
    TraceData (Fin 3) (Fin 2) (Fin 2) :=
  TraceData.ofBdry ![e₀, e₁, e₂] ![cycleT, -cycleL, (s₁ / s₂) • cycleT₀L] ![L₀, L₁] ![0, 0, 1]
    (fun i => by
      fin_cases i
      exacts [endpoint_line_e₀, endpoint_line_e₁, endpoint_line_e₂])
    ![P₀, P₁] ![0, 1, 1]
    (fun i => by
      fin_cases i
      exacts [endpoint_plane_e₀, endpoint_plane_e₁, endpoint_plane_e₂])
    (fun i => by
      fin_cases i
      · exact boundary_cusp_mem_null (prismData RationalGL3) latL0.σ latL0_le_e₀ latL0.boundary_σ
          isLevi_T T_mem_levelStabilizer_e₀
      · show homogeneousBoundary 3 (-cycleL) ∈ NullChains (levelStabilizer e₁) 2
        rw [map_neg]
        exact neg_mem (boundary_cusp_mem_null (prismData RationalGL3) latL0.σ latL0_le_e₁
          latL0.boundary_σ isLevi_L L_mem_levelStabilizer_e₁)
      · show homogeneousBoundary 3 ((s₁ / s₂) • cycleT₀L) ∈ NullChains (levelStabilizer e₂) 2
        rw [map_smul]
        exact Submodule.smul_mem _ _ (boundary_cusp_mem_null (prismData RationalGL3) latL1.σ
          latL1_le_e₂ latL1.boundary_σ isLevi_T₀_L₁ T₀_mem_levelStabilizer_e₂))
    (Fin.forall_fin_two.mpr
      ⟨by
        show (∑ i ∈ Finset.univ.filter (fun i => (![0, 0, 1] : Fin 3 → Fin 2) i = 0),
          (![cycleT, -cycleL, (s₁ / s₂) • cycleT₀L] : Fin 3 → Chains RationalGL3 3) i) ∈
            BdryChains (levelStabilizer L₀) 3
        have hsum : (∑ i ∈ Finset.univ.filter (fun i => (![0, 0, 1] : Fin 3 → Fin 2) i = 0),
            (![cycleT, -cycleL, (s₁ / s₂) • cycleT₀L] : Fin 3 → Chains RationalGL3 3) i) =
            cycleT - cycleL := by
          rw [Finset.sum_filter, Fin.sum_univ_three]
          simp [sub_eq_add_neg]
        rw [hsum]
        refine (mem_bdryChains_iff _ _).mpr fun κ hκ closed => ?_
        rw [map_sub, eval_L₀ κ hκ closed, sub_self],
      by
        show (∑ i ∈ Finset.univ.filter (fun i => (![0, 0, 1] : Fin 3 → Fin 2) i = 1),
          (![cycleT, -cycleL, (s₁ / s₂) • cycleT₀L] : Fin 3 → Chains RationalGL3 3) i) ∈
            BdryChains (levelStabilizer L₁) 3
        have hsum : (∑ i ∈ Finset.univ.filter (fun i => (![0, 0, 1] : Fin 3 → Fin 2) i = 1),
            (![cycleT, -cycleL, (s₁ / s₂) • cycleT₀L] : Fin 3 → Chains RationalGL3 3) i) =
            (s₁ / s₂) • cycleT₀L := by
          rw [Finset.sum_filter, Fin.sum_univ_three]
          simp
        rw [hsum]
        refine (mem_bdryChains_iff _ _).mpr fun κ hκ closed => ?_
        rw [map_smul, eval_L₁ κ hκ closed, smul_zero]⟩)
    (Fin.forall_fin_two.mpr
      ⟨by
        show (∑ i ∈ Finset.univ.filter (fun i => (![0, 1, 1] : Fin 3 → Fin 2) i = 0),
          (![cycleT, -cycleL, (s₁ / s₂) • cycleT₀L] : Fin 3 → Chains RationalGL3 3) i) ∈
            BdryChains (levelStabilizer P₀) 3
        have hsum : (∑ i ∈ Finset.univ.filter (fun i => (![0, 1, 1] : Fin 3 → Fin 2) i = 0),
            (![cycleT, -cycleL, (s₁ / s₂) • cycleT₀L] : Fin 3 → Chains RationalGL3 3) i) =
            cycleT := by
          rw [Finset.sum_filter, Fin.sum_univ_three]
          simp
        rw [hsum]
        refine (mem_bdryChains_iff _ _).mpr fun κ hκ closed => ?_
        rw [c₀ κ hκ closed, eval_P₀ κ hκ closed, mul_zero],
      by
        show (∑ i ∈ Finset.univ.filter (fun i => (![0, 1, 1] : Fin 3 → Fin 2) i = 1),
          (![cycleT, -cycleL, (s₁ / s₂) • cycleT₀L] : Fin 3 → Chains RationalGL3 3) i) ∈
            BdryChains (levelStabilizer P₁) 3
        have hsum : (∑ i ∈ Finset.univ.filter (fun i => (![0, 1, 1] : Fin 3 → Fin 2) i = 1),
            (![cycleT, -cycleL, (s₁ / s₂) • cycleT₀L] : Fin 3 → Chains RationalGL3 3) i) =
            -cycleL + (s₁ / s₂) • cycleT₀L := by
          rw [Finset.sum_filter, Fin.sum_univ_three]
          simp
        rw [hsum]
        refine (mem_bdryChains_iff _ _).mpr fun κ hκ closed => ?_
        rw [map_add, map_neg, map_smul, c₁ κ hκ closed, c₂ κ hκ closed, eval_P₁ κ hκ closed,
          smul_eq_mul, ← mul_assoc, div_mul_cancel₀ s₁ hs₂]
        ring⟩)

/-- **A boundary trace from the three orientation comparisons.** -/
theorem isBoundaryTrace_of_comparisons (s₀ s₁ s₂ : ℂ) (hs₂ : s₂ ≠ 0)
    (c₀ : Comparison (levelStabilizer P₀) cycleT cycleT₀P s₀)
    (c₁ : Comparison (levelStabilizer P₁) cycleL cycleT' s₁)
    (c₂ : Comparison (levelStabilizer P₁) cycleT₀L cycleL' s₂) :
    TraceReduction.IsBoundaryTrace
      (traceData_of_comparisons s₀ s₁ s₂ hs₂ c₀ c₁ c₂).trace.toAddMonoidHom :=
  (traceData_of_comparisons s₀ s₁ s₂ hs₂ c₀ c₁ c₂).isBoundaryTrace_trace

end Concrete

end TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
