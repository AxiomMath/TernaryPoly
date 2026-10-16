module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.HeisCycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.DimBound

@[expose] public section


/-!
# One-dimensionality of `H³` of a flag group, the evaluation functional and the generator `G_F`

Formalized by Claude Sonnet 5.5.

`FlagCohomDatum B` packages: a bar `3`-cycle `z`, `dim H³(B, ℚ) = 1`, and the nonvanishing of the evaluation functional `λ = cycleFunctional z` (explicitly `λ[θ] = ∑ z(g) θ(g)` on cocycles,
`FlagCohomDatum.lam_cocycle`).  `FlagCohomDatum.gen` is the class `G_F` with `λ G_F = 1` (`lam_gen`), unique (`gen_unique`), and every class is `λ x • G_F` (`eq_smul_gen`).
`HeisCoords.flagData` constructs the datum for any extension of `ℤ` by `ℤ²` with Heisenberg coordinates and elements `X`, `Y` of coordinates `(p,0,0)`, `(0,q,0)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

variable {B : Type} [Group B]


/-- **The one-dimensionality datum of `H³(B, ℚ)` for a flag group `B`**: a finite bar `3`-cycle `z` whose evaluation functional `λ` on
`H³(B, ℚ)` is nonzero, and `dim H³(B, ℚ) = 1`. -/
structure FlagCohomDatum (B : Type) [Group B] where
  z : (Fin 3 → B) →₀ ℚ
  isCycle : IsCycle z
  finite : Module.Finite ℚ (groupCohomology (Rep.trivial ℚ B ℚ) 3)
  finrank_eq_one : Module.finrank ℚ (groupCohomology (Rep.trivial ℚ B ℚ) 3) = 1
  lam_ne_zero : cycleFunctional z isCycle ≠ 0

namespace FlagCohomDatum

variable (D : FlagCohomDatum B)

/-- The evaluation functional `λ_F` on `H³(B, ℚ)`. -/
def lam : groupCohomology (Rep.trivial ℚ B ℚ) 3 →ₗ[ℚ] ℚ := cycleFunctional D.z D.isCycle

theorem lam_cocycle (θ : (Fin 3 → B) → ℚ) (hθ : dThree θ = 0) : D.lam (cocycleClass θ hθ) = chainEval D.z θ :=
  cycleFunctional_cocycle D.z D.isCycle θ hθ

theorem exists_gen : ∃ G : groupCohomology (Rep.trivial ℚ B ℚ) 3, D.lam G = 1 := by
  have := D.finite
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp D.finrank_eq_one
  have hne : D.lam v ≠ 0 := by
    intro h0
    apply D.lam_ne_zero
    ext w
    obtain ⟨c, rfl⟩ := hv w
    show D.lam (c • v) = 0
    rw [map_smul, h0, smul_zero]
  exact ⟨(D.lam v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]⟩

theorem lam_injective : Function.Injective D.lam := by
  have := D.finite
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp D.finrank_eq_one
  have hne : D.lam v ≠ 0 := by
    intro h0
    apply D.lam_ne_zero
    ext w
    obtain ⟨c, rfl⟩ := hv w
    show D.lam (c • v) = 0
    rw [map_smul, h0, smul_zero]
  intro x y hxy
  obtain ⟨c, rfl⟩ := hv x
  obtain ⟨c', rfl⟩ := hv y
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hxy
  rw [mul_right_cancel₀ hne hxy]

theorem gen_unique {G G' : groupCohomology (Rep.trivial ℚ B ℚ) 3} (h : D.lam G = 1) (h' : D.lam G' = 1) : G = G' :=
  D.lam_injective (h.trans h'.symm)

/-- **The class `G_F`**: the unique class in `H³(B, ℚ)` with `λ(G_F) = 1`. -/
def gen : groupCohomology (Rep.trivial ℚ B ℚ) 3 := Classical.choose D.exists_gen

theorem lam_gen : D.lam D.gen = 1 := Classical.choose_spec D.exists_gen

theorem eq_smul_gen (x : groupCohomology (Rep.trivial ℚ B ℚ) 3) : x = D.lam x • D.gen :=
  D.lam_injective (by rw [map_smul, D.lam_gen, smul_eq_mul, mul_one])

end FlagCohomDatum


namespace HeisCoords

variable (H : HeisCoords B)

theorem lam_ne_zero (X Y : B) (p q : ℤ) (hp : p ≠ 0) (hq : q ≠ 0) (hXa : H.a X = p) (hXb : H.b X = 0)
    (hXc : H.c X = 0) (hYa : H.a Y = 0) (hYb : H.b Y = q) (hYc : H.c Y = 0) :
    cycleFunctional (heisCycle X Y) (H.cycle_isCycle X Y p q hXa hXb hXc hYa hYb hYc) ≠ 0 := by
  intro h
  have h1 := cycleFunctional_cocycleClass (heisCycle X Y) (H.cycle_isCycle X Y p q hXa hXb hXc hYa hYb hYc) H.theta
    H.theta_cocycle
  rw [h, LinearMap.zero_apply, H.cycle_theta X Y p q hXa hXb hXc hYa hYb hYc] at h1
  have : (-2 * (p : ℚ) ^ 2 * (q : ℚ) ^ 2) ≠ 0 := by
    have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
    positivity
  exact this h1.symm

/-- **`H³` of an extension of `ℤ` by `ℤ²` with Heisenberg coordinates is one-dimensional**, with the explicit evaluation functional. -/
def flagData (E : GroupExtension (Multiplicative (ℤ × ℤ)) B (Multiplicative ℤ)) (X Y : B) (p q : ℤ) (hp : p ≠ 0)
    (hq : q ≠ 0) (hXa : H.a X = p) (hXb : H.b X = 0) (hXc : H.c X = 0) (hYa : H.a Y = 0) (hYb : H.b Y = q)
    (hYc : H.c Y = 0) : FlagCohomDatum B where
  z := heisCycle X Y
  isCycle := H.cycle_isCycle X Y p q hXa hXb hXc hYa hYb hYc
  finite := (H3_ext_le E).1
  finrank_eq_one := by
    have hle := (H3_ext_le E).2
    have hne := H.lam_ne_zero X Y p q hp hq hXa hXb hXc hYa hYb hYc
    have := (H3_ext_le E).1
    obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hne
    have hw0 : w ≠ 0 := fun h => hw (by rw [h]; simp)
    have : Nontrivial (groupCohomology (Rep.trivial ℚ B ℚ) 3) := ⟨⟨w, 0, hw0⟩⟩
    exact le_antisymm hle (Module.finrank_pos_iff.2 inferInstance)
  lam_ne_zero := H.lam_ne_zero X Y p q hp hq hXa hXb hXc hYa hYb hYc

end HeisCoords


/-- **Cup product of a `1`-cocycle and a `2`-cocycle with trivial rational coefficients is a `3`-cocycle**: `(u ∪ β)(g₁,g₂,g₃) = u(g₁) β(g₂,g₃)`
 (the case `e = ·`, trivial actions). -/
theorem dThree_cup (u : B → ℚ) (β : B → B → ℚ) (hu : ∀ g h, u (g * h) = u g + u h)
    (hβ : ∀ g h k, β h k - β (g * h) k + β g (h * k) - β g h = 0) :
    dThree (fun g : Fin 3 → B => u (g 0) * β (g 1) (g 2)) = 0 := by
  funext g
  rw [dThree_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Pi.zero_apply]
  have h1 := hu (g 0) (g 1)
  have h2 := hβ (g 1) (g 2) (g 3)
  rw [h1]
  linear_combination (-(u (g 0))) * h2

namespace FlagCohomDatum

/-- **Evaluation of the functional on a cup product `u ∪ β`**: `λ[u ∪ β] = ∑ z(g₁,g₂,g₃) u(g₁) β(g₂,g₃)`. -/
theorem lam_cup (D : FlagCohomDatum B) (u : B → ℚ) (β : B → B → ℚ) (hu : ∀ g h, u (g * h) = u g + u h)
    (hβ : ∀ g h k, β h k - β (g * h) k + β g (h * k) - β g h = 0) :
    D.lam (cocycleClass (fun g : Fin 3 → B => u (g 0) * β (g 1) (g 2)) (dThree_cup u β hu hβ)) =
      D.z.sum fun g c => c * (u (g 0) * β (g 1) (g 2)) :=
  D.lam_cocycle _ _

end FlagCohomDatum

end TernaryPeriodPolynomials.Argument.FlagH3
