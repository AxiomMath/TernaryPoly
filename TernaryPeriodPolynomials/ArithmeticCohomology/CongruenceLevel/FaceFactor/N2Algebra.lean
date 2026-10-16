module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.LineTree
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CupProduct
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.CupEval

@[expose] public section


/-!
# Pure algebra of `N = ℤ²` with rational cochains: the pairing, the torus homotopy, `cd ≤ 2` at cochain level, normalization

Formalized by Claude Sonnet 5.5.

* (N1) `commPair`, `commPair_mul_left/right`, `commPair_zpow_*`, **`commPair_det`**, **`commPair_det_one`**: for a 2-cocycle `θ` of `ℤ²` the antisymmetrisation `A(a,b) = θ(a,b) - θ(b,a)` is
  biadditive, alternating, and `A(σ e₁, σ e₂) = det σ · A(e₁, e₂)` (`σ e₁ = e₁^a e₂^c`, `σ e₂ = e₁^b e₂^d`);
* (N2) `BarCh n B = ℚ[Bⁿ]` (`(Fin n → B) →₀ ℚ`, as `FlagH3.chainEval`), `bdry3 : C₃ → C₂` (`∂[g₁|g₂|g₃] = [g₂|g₃] - [g₁g₂|g₃] + [g₁|g₂g₃] - [g₁|g₂]`, dual to `dd2T`), `ev2 θ` the pairing with a 2-cochain,
  `exists_bdry_of_killed`: a 2-chain killed by every 2-cocycle is a boundary, **`torus_homotopy`**: `∃ m, ∂ m = ν^σ - ν` for `σ` of determinant one (`torus_homotopy_hom` for a hom `σ`);
* (N3) **`cd_two_cochain`**: every rational 3-cocycle of `ℤ²` is `dd2T` of a 2-cochain (from `cdLe_int2`);
* (N4) **`normalize_on_radical`**: for `inl : ℤ² →* Q` injective and `γ` with `dd3T γ = 0` on `inl(ℤ²)⁴` there is `ε` with `γ - dd2T ε = 0` on all triples in `inl(ℤ²)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FlagH3

section N1

variable {N : Type} [CommGroup N]

/-- The antisymmetrisation `A(a, b) = θ(a, b) - θ(b, a)` of a rational 2-cochain. -/
def commPair (θ : N → N → ℚ) (a b : N) : ℚ := θ a b - θ b a

theorem commPair_mul_left (θ : N → N → ℚ) (hθ : ∀ g h l, dd2T θ g h l = 0) (a b c : N) :
    commPair θ (a * b) c = commPair θ a c + commPair θ b c := by
  have h1 := hθ a b c
  have h2 := hθ a c b
  have h3 := hθ c a b
  simp only [dd2T] at h1 h2 h3
  simp only [commPair]
  rw [mul_comm c b] at h2
  rw [mul_comm c a] at h3
  linear_combination -h1 + h2 - h3

omit [CommGroup N] in
theorem commPair_neg (θ : N → N → ℚ) (a b : N) : commPair θ b a = - commPair θ a b := by
  simp [commPair]

omit [CommGroup N] in
theorem commPair_self (θ : N → N → ℚ) (a : N) : commPair θ a a = 0 := by simp [commPair]

theorem commPair_mul_right (θ : N → N → ℚ) (hθ : ∀ g h l, dd2T θ g h l = 0) (a b c : N) :
    commPair θ a (b * c) = commPair θ a b + commPair θ a c := by
  have e1 := commPair_neg θ (b * c) a
  have e2 := commPair_neg θ b a
  have e3 := commPair_neg θ c a
  have e4 := commPair_mul_left θ hθ b c a
  linear_combination e1 - e4 - e2 - e3

theorem commPair_one_left (θ : N → N → ℚ) (hθ : ∀ g h l, dd2T θ g h l = 0) (y : N) : commPair θ 1 y = 0 := by
  have := commPair_mul_left θ hθ 1 1 y
  rw [mul_one] at this
  linarith

theorem commPair_zpow_left (θ : N → N → ℚ) (hθ : ∀ g h l, dd2T θ g h l = 0) (x y : N) (n : ℤ) :
    commPair θ (x ^ n) y = n * commPair θ x y := by
  induction n using Int.induction_on with
  | zero => simp [commPair_one_left θ hθ]
  | succ i ih =>
    rw [zpow_add_one, commPair_mul_left θ hθ, ih]
    push_cast; ring
  | pred i ih =>
    have h := commPair_mul_left θ hθ (x ^ (-(i : ℤ) - 1)) x y
    rw [zpow_sub_one, ← zpow_sub_one, show x ^ (-(i : ℤ) - 1) * x = x ^ (-(i : ℤ)) by
      rw [zpow_sub_one]; group] at h
    rw [ih] at h
    push_cast at h ⊢
    linarith

theorem commPair_zpow_right (θ : N → N → ℚ) (hθ : ∀ g h l, dd2T θ g h l = 0) (x y : N) (n : ℤ) :
    commPair θ x (y ^ n) = n * commPair θ x y := by
  have hneg1 := commPair_neg θ x (y ^ n)
  have hneg2 := commPair_neg θ x y
  have hl := commPair_zpow_left θ hθ y x n
  linear_combination hneg1 - hl - (n : ℚ) * hneg2

end N1

section Lattice

/-- The first basis element `(1, 0)` of `ℤ²` (written multiplicatively, as `RadicalLattice`). -/
def latE1 : Multiplicative (ℤ × ℤ) := Multiplicative.ofAdd ((1, 0) : ℤ × ℤ)

/-- The second basis element `(0, 1)`. -/
def latE2 : Multiplicative (ℤ × ℤ) := Multiplicative.ofAdd ((0, 1) : ℤ × ℤ)

/-- **(N1)**: for a 2-cocycle `θ` of `ℤ²` (rational coefficients) the antisymmetrisation is multiplied by the determinant:
`A(e1^a e2^c, e1^b e2^d) = (a d - b c) A(e1, e2)`. -/
theorem commPair_det (θ : Multiplicative (ℤ × ℤ) → Multiplicative (ℤ × ℤ) → ℚ) (hθ : ∀ g h l, dd2T θ g h l = 0)
    (a b c d : ℤ) :
    commPair θ (latE1 ^ a * latE2 ^ c) (latE1 ^ b * latE2 ^ d) = ((a * d - b * c : ℤ) : ℚ) * commPair θ latE1 latE2 := by
  simp only [commPair_mul_left θ hθ, commPair_mul_right θ hθ, commPair_zpow_left θ hθ, commPair_zpow_right θ hθ,
    commPair_self, commPair_neg θ latE1 latE2]
  push_cast
  ring

/-- **(N1), determinant one**: `A(σ e1, σ e2) = A(e1, e2)` for `σ e1 = e1^a e2^c`, `σ e2 = e1^b e2^d`, `a d - b c = 1`. -/
theorem commPair_det_one (θ : Multiplicative (ℤ × ℤ) → Multiplicative (ℤ × ℤ) → ℚ) (hθ : ∀ g h l, dd2T θ g h l = 0)
    (a b c d : ℤ) (hdet : a * d - b * c = 1) :
    commPair θ (latE1 ^ a * latE2 ^ c) (latE1 ^ b * latE2 ^ d) = commPair θ latE1 latE2 := by
  rw [commPair_det θ hθ, hdet]
  simp

end Lattice

section Chains

variable {B : Type} [Group B]

/-- Chains of the bar complex with rational coefficients: `C_n(B) = ℚ[Bⁿ]`. -/
abbrev BarCh (n : ℕ) (B : Type) := (Fin n → B) →₀ ℚ

/-- The boundary `C₃ → C₂`: `∂[g₁|g₂|g₃] = [g₂|g₃] - [g₁g₂|g₃] + [g₁|g₂g₃] - [g₁|g₂]` (dual to `dd2T`). -/
def bdry3 : BarCh 3 B →ₗ[ℚ] BarCh 2 B :=
  Finsupp.linearCombination ℚ (fun x : Fin 3 → B =>
    Finsupp.single ![x 1, x 2] (1 : ℚ) - Finsupp.single ![x 0 * x 1, x 2] 1 + Finsupp.single ![x 0, x 1 * x 2] 1 -
      Finsupp.single ![x 0, x 1] 1)

/-- The pairing `⟨θ, z⟩` of a rational 2-cochain with a 2-chain. -/
def ev2 (θ : B → B → ℚ) : BarCh 2 B →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (fun g : Fin 2 → B => θ (g 0) (g 1))

omit [Group B] in
theorem ev2_single (θ : B → B → ℚ) (a b : B) : ev2 θ (Finsupp.single ![a, b] (1 : ℚ)) = θ a b := by
  simp [ev2]

theorem ev2_bdry3_single (θ : B → B → ℚ) (g h l : B) :
    ev2 θ (bdry3 (Finsupp.single ![g, h, l] (1 : ℚ))) = dd2T θ g h l := by
  simp [bdry3, map_sub, map_add, ev2_single, dd2T]

/-- **A 2-chain killed by every 2-cocycle is a boundary** (duality over the field `ℚ`). -/
theorem exists_bdry_of_killed (z : BarCh 2 B) (h : ∀ θ : B → B → ℚ, (∀ g h l, dd2T θ g h l = 0) → ev2 θ z = 0) :
    ∃ m : BarCh 3 B, bdry3 m = z := by
  by_contra hne
  have hz : z ∉ LinearMap.range (bdry3 (B := B)) := fun hmem => hne hmem
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
  let θ : B → B → ℚ := fun a b => f (Finsupp.single ![a, b] 1)
  have hev : ev2 θ = f := by
    apply Finsupp.lhom_ext
    intro g r
    have hg : g = ![g 0, g 1] := by
      funext i; fin_cases i <;> rfl
    have h1 : (Finsupp.single g r : BarCh 2 B) = r • Finsupp.single ![g 0, g 1] (1 : ℚ) := by
      rw [← hg]; simp
    rw [h1, map_smul, map_smul, ev2_single]
  have hcoc : ∀ g h l, dd2T θ g h l = 0 := by
    intro g h l
    rw [← ev2_bdry3_single, hev]
    have : bdry3 (Finsupp.single ![g, h, l] (1 : ℚ)) ∈ LinearMap.range (bdry3 (B := B)) := ⟨_, rfl⟩
    have h2 := Submodule.mem_map_of_mem (f := f) this
    rw [hmap] at h2
    exact (Submodule.mem_bot ℚ).1 h2
  have := h θ hcoc
  rw [hev] at this
  exact hf this

end Chains

section Torus

/-- The fundamental 2-chain `ν = [e₁|e₂] - [e₂|e₁]` of `ℤ²`. -/
def torusNu : BarCh 2 (Multiplicative (ℤ × ℤ)) :=
  Finsupp.single ![latE1, latE2] 1 - Finsupp.single ![latE2, latE1] 1

/-- The chain `ν^σ = [u|v] - [v|u]` for the images `u = σ e₁`, `v = σ e₂` of the basis. -/
def torusNuOf (u v : Multiplicative (ℤ × ℤ)) : BarCh 2 (Multiplicative (ℤ × ℤ)) :=
  Finsupp.single ![u, v] 1 - Finsupp.single ![v, u] 1

/-- **(N2) The torus homotopy**: for an automorphism `σ` of `ℤ²` of determinant one (`σ e₁ = e₁^a e₂^c`, `σ e₂ = e₁^b e₂^d`, `a d - b c = 1`) there is a 3-chain `m`
with `∂ m = ν^σ - ν`. -/
theorem torus_homotopy (a b c d : ℤ) (hdet : a * d - b * c = 1) :
    ∃ m : BarCh 3 (Multiplicative (ℤ × ℤ)),
      bdry3 m = torusNuOf (latE1 ^ a * latE2 ^ c) (latE1 ^ b * latE2 ^ d) - torusNu := by
  apply exists_bdry_of_killed
  intro θ hθ
  have h := commPair_det_one θ hθ a b c d hdet
  simp only [commPair] at h
  simp only [torusNuOf, torusNu, map_sub, ev2_single]
  linarith

/-- The same for an arbitrary endomorphism `σ` of `ℤ²` given by images of the basis. -/
theorem torus_homotopy_hom (σ : Multiplicative (ℤ × ℤ) →* Multiplicative (ℤ × ℤ)) (a b c d : ℤ)
    (h1 : σ latE1 = latE1 ^ a * latE2 ^ c) (h2 : σ latE2 = latE1 ^ b * latE2 ^ d) (hdet : a * d - b * c = 1) :
    ∃ m : BarCh 3 (Multiplicative (ℤ × ℤ)), bdry3 m = torusNuOf (σ latE1) (σ latE2) - torusNu := by
  rw [h1, h2]
  exact torus_homotopy a b c d hdet

end Torus

section CdTwo

open CategoryTheory CategoryTheory.Limits groupCohomology

/-- **(N3) `cd ℤ² ≤ 2` at cochain level**: every rational 3-cocycle of `ℤ²` is the coboundary of a 2-cochain. -/
theorem cd_two_cochain (Ψ : Multiplicative (ℤ × ℤ) → Multiplicative (ℤ × ℤ) → Multiplicative (ℤ × ℤ) → ℚ)
    (hΨ : ∀ g1 g2 g3 g4, dd3T Ψ g1 g2 g3 g4 = 0) :
    ∃ ε : Multiplicative (ℤ × ℤ) → Multiplicative (ℤ × ℤ) → ℚ, ∀ a b c, Ψ a b c = dd2T ε a b c := by
  have H0 : IsZero (groupCohomology (Rep.trivial ℚ (Multiplicative (ℤ × ℤ)) ℚ) 3) :=
    cdLe_int2 (k := ℚ) ℚ 3 (by norm_num)
  have hex : ((inhomogeneousCochains (Rep.trivial ℚ (Multiplicative (ℤ × ℤ)) ℚ)).sc' 2 3 4).Exact := by
    rw [← HomologicalComplex.exactAt_iff' _ 2 3 4 (by simp) (by simp), HomologicalComplex.exactAt_iff_isZero_homology]
    exact H0
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have h0 : dThree (fun g : Fin 3 → Multiplicative (ℤ × ℤ) => Ψ (g 0) (g 1) (g 2)) = 0 := by
    rw [dThree_eq_dd3T]
    funext g
    exact hΨ _ _ _ _
  obtain ⟨ε, hε⟩ := hex (fun g : Fin 3 → Multiplicative (ℤ × ℤ) => Ψ (g 0) (g 1) (g 2)) h0
  refine ⟨fun a b => ε ![a, b], fun a b c => ?_⟩
  have h1 : dTwo ε = fun g : Fin 3 → Multiplicative (ℤ × ℤ) => Ψ (g 0) (g 1) (g 2) := hε
  have h2 := congrFun h1 ![a, b, c]
  have e := dTwo_apply (B := Multiplicative (ℤ × ℤ)) ε ![a, b, c]
  simp at e h2
  simp only [dd2T]
  linarith

end CdTwo

section Normalize

open Classical in
/-- **(N4) Normalization**: for a group `Q ⊇ ℤ²` (`inl` injective) and a rational 3-cochain `γ` of `Q` whose differential vanishes on `inl(ℤ²)⁴`, there is a 2-cochain `ε`
of `Q` with `γ - dε` vanishing on all triples with all letters in `inl(ℤ²)`. -/
theorem normalize_on_radical {Q : Type} [Group Q] (inl : Multiplicative (ℤ × ℤ) →* Q) (hinj : Function.Injective inl)
    (γ : Q → Q → Q → ℚ)
    (hγ : ∀ a b c d : Multiplicative (ℤ × ℤ), dd3T γ (inl a) (inl b) (inl c) (inl d) = 0) :
    ∃ ε : Q → Q → ℚ, ∀ a b c : Multiplicative (ℤ × ℤ),
      γ (inl a) (inl b) (inl c) - dd2T ε (inl a) (inl b) (inl c) = 0 := by
  obtain ⟨ε₀, hε₀⟩ := cd_two_cochain (fun a b c => γ (inl a) (inl b) (inl c)) (fun g1 g2 g3 g4 => by
    have := hγ g1 g2 g3 g4
    simpa [dd3T, map_mul] using this)
  let ε : Q → Q → ℚ := fun q q' =>
    if h : (q ∈ Set.range inl ∧ q' ∈ Set.range inl) then ε₀ (Function.invFun inl q) (Function.invFun inl q') else 0
  have hε : ∀ a b, ε (inl a) (inl b) = ε₀ a b := by
    intro a b
    have hr : inl a ∈ Set.range inl ∧ inl b ∈ Set.range inl := ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    simp only [ε, dite_eq_left hr]
    rw [Function.leftInverse_invFun hinj a, Function.leftInverse_invFun hinj b]
  refine ⟨ε, fun a b c => ?_⟩
  have := hε₀ a b c
  simp only [dd2T, ← map_mul, hε]
  simp only [dd2T] at this
  linarith

end Normalize

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
