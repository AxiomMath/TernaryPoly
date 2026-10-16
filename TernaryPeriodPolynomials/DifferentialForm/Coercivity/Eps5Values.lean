module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeStar

@[expose] public section



/-! Concrete values of `eps5` on literal `Fin 5` arguments, made computable-by-`simp`:

* `epsFive_id`, `eps5_perm`: bridge `eps5` to `Equiv.Perm.sign` for a permutation built from
  `id`, so that a concretely-built `Equiv.Perm (Fin 5)` pins down `eps5`'s value at any injective 5-tuple.

* `eps5_eq_zero_01` .. `eps5_eq_zero_34`: the ten "repeated entry" vanishing lemmas, one per pair
  of argument positions, from `epsFive_eq_zero_of_not_injective`.

The 120 permutation-value lemmas themselves live in `Eps5ValuesA.lean` / `Eps5ValuesB.lean`
(60 each). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

/-- `epsFive` of the identity function is `1`: its indicator matrix is the identity matrix. -/
theorem epsFive_id : epsFive id = 1 := by
  have h1 : (Matrix.of fun i j => if (id i : Fin 5) = j then (1 : ℝ) else 0)
      = (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
    ext i j
    simp [Matrix.one_apply]
  show Matrix.det (Matrix.of fun i j => if (id i : Fin 5) = j then (1 : ℝ) else 0) = 1
  rw [h1, Matrix.det_one]

/-- `eps5` evaluated at a permutation's images, in order, is that permutation's sign. Combined
with a concretely-built `σ : Equiv.Perm (Fin 5)`, this
pins down `eps5`'s value at any injective tuple of literal `Fin 5` arguments. -/
theorem eps5_perm (σ : Equiv.Perm (Fin 5)) :
    eps5 (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) = (Equiv.Perm.sign σ : ℝ) := by
  show epsFive ![σ 0, σ 1, σ 2, σ 3, σ 4] = (Equiv.Perm.sign σ : ℝ)
  have h : (![σ 0, σ 1, σ 2, σ 3, σ 4] : Fin 5 → Fin 5) = id ∘ σ := by
    funext w; fin_cases w <;> rfl
  rw [h, epsFive_comp_perm id σ, epsFive_id, mul_one]

/-! The ten "repeated entry" vanishing lemmas: whenever two of the five argument positions carry
the same value, `eps5` is zero (its underlying 5-tuple is not injective). Each hypothesis is a
plain equation between two of the five bound variables.

-/

@[simp] theorem eps5_eq_zero_01 {a b c d e : Fin 5} (h : a = b) : eps5 a b c d e = 0 := by
  show epsFive ![a, b, c, d, e] = 0
  exact epsFive_eq_zero_of_not_injective (Function.not_injective_iff.mpr ⟨0, 1, h, by decide⟩)

@[simp] theorem eps5_eq_zero_02 {a b c d e : Fin 5} (h : a = c) : eps5 a b c d e = 0 := by
  show epsFive ![a, b, c, d, e] = 0
  exact epsFive_eq_zero_of_not_injective (Function.not_injective_iff.mpr ⟨0, 2, h, by decide⟩)

@[simp] theorem eps5_eq_zero_03 {a b c d e : Fin 5} (h : a = d) : eps5 a b c d e = 0 := by
  show epsFive ![a, b, c, d, e] = 0
  exact epsFive_eq_zero_of_not_injective (Function.not_injective_iff.mpr ⟨0, 3, h, by decide⟩)

@[simp] theorem eps5_eq_zero_04 {a b c d e : Fin 5} (h : a = e) : eps5 a b c d e = 0 := by
  show epsFive ![a, b, c, d, e] = 0
  exact epsFive_eq_zero_of_not_injective (Function.not_injective_iff.mpr ⟨0, 4, h, by decide⟩)

@[simp] theorem eps5_eq_zero_12 {a b c d e : Fin 5} (h : b = c) : eps5 a b c d e = 0 := by
  show epsFive ![a, b, c, d, e] = 0
  exact epsFive_eq_zero_of_not_injective (Function.not_injective_iff.mpr ⟨1, 2, h, by decide⟩)

@[simp] theorem eps5_eq_zero_13 {a b c d e : Fin 5} (h : b = d) : eps5 a b c d e = 0 := by
  show epsFive ![a, b, c, d, e] = 0
  exact epsFive_eq_zero_of_not_injective (Function.not_injective_iff.mpr ⟨1, 3, h, by decide⟩)

@[simp] theorem eps5_eq_zero_14 {a b c d e : Fin 5} (h : b = e) : eps5 a b c d e = 0 := by
  show epsFive ![a, b, c, d, e] = 0
  exact epsFive_eq_zero_of_not_injective (Function.not_injective_iff.mpr ⟨1, 4, h, by decide⟩)

@[simp] theorem eps5_eq_zero_23 {a b c d e : Fin 5} (h : c = d) : eps5 a b c d e = 0 := by
  show epsFive ![a, b, c, d, e] = 0
  exact epsFive_eq_zero_of_not_injective (Function.not_injective_iff.mpr ⟨2, 3, h, by decide⟩)

@[simp] theorem eps5_eq_zero_24 {a b c d e : Fin 5} (h : c = e) : eps5 a b c d e = 0 := by
  show epsFive ![a, b, c, d, e] = 0
  exact epsFive_eq_zero_of_not_injective (Function.not_injective_iff.mpr ⟨2, 4, h, by decide⟩)

@[simp] theorem eps5_eq_zero_34 {a b c d e : Fin 5} (h : d = e) : eps5 a b c d e = 0 := by
  show epsFive ![a, b, c, d, e] = 0
  exact epsFive_eq_zero_of_not_injective (Function.not_injective_iff.mpr ⟨3, 4, h, by decide⟩)

end TernaryPeriodPolynomials.Argument.Coercivity
