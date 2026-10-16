module

public import Mathlib

@[expose] public section


/-!
# Cusps of `Γ(6) ⊂ SL₂(ℤ)` and their positive parabolic generators

Formalized by Claude Sonnet 5.5.

`Prim2` is the set of primitive integer column vectors, `CuspRel` the equivalence `v ~ ±γ v`, `γ ∈ Γ(6)`; `Cusp6` its quotient (the cusps of `Γ(6)`).  `posPar v = 1 + 6 v ⊗ (-v₁, v₀)` is the
positive generator of the stabilizer of `v` of width six (`= g T⁶ g⁻¹` for any `g ∈ SL₂(ℤ)` with `g e₁ = v`); `posParSL v` is it as an element of `Γ(6)`.
`BaseSumZero` is the statement that the cusp values `φ(posParSL v)` of homomorphisms `φ : Γ(6) → ℚ` fill the whole sum-zero hyperplane (the residue theorem together with the surjectivity of
`Hom(Γ(6), ℚ) → ℚ^{cusps}` onto it); it is used as a hypothesis in `GammaNStokes/BLine`.
-/

open CongruenceSubgroup Matrix
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

/-- Primitive integer column vectors. -/
def Prim2 : Type := {v : Fin 2 → ℤ // IsCoprime (v 0) (v 1)}

/-- Two primitive vectors give the same cusp of `Γ(6)`: `γ v = ± w` with `γ ∈ Γ(6)`. -/
def CuspRel (v w : Prim2) : Prop :=
  ∃ (γ : SL(2, ℤ)), γ ∈ Gamma 6 ∧ ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v.1 = s • w.1

theorem cuspRel_refl (v : Prim2) : CuspRel v v := ⟨1, Subgroup.one_mem _, 1, Or.inl rfl, by simp⟩

theorem cuspRel_symm {v w : Prim2} (h : CuspRel v w) : CuspRel w v := by
  obtain ⟨γ, hγ, s, hs, e⟩ := h
  refine ⟨γ⁻¹, Subgroup.inv_mem _ hγ, s, hs, ?_⟩
  have h1 : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ((γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v.1) = v.1 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    simp
  rw [e, Matrix.mulVec_smul] at h1
  rw [← h1, smul_smul]
  rcases hs with rfl | rfl <;> simp

theorem cuspRel_trans {u v w : Prim2} (h1 : CuspRel u v) (h2 : CuspRel v w) : CuspRel u w := by
  obtain ⟨γ, hγ, s, hs, e⟩ := h1
  obtain ⟨δ, hδ, t, ht, f⟩ := h2
  refine ⟨δ * γ, Subgroup.mul_mem _ hδ hγ, t * s, ?_, ?_⟩
  · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul, f, smul_smul]
    ring_nf

/-- The setoid of cusps. -/
def cuspSetoid : Setoid Prim2 where
  r := CuspRel
  iseqv := ⟨cuspRel_refl, cuspRel_symm, cuspRel_trans⟩

/-- The cusps of `Γ(6)`. -/
def Cusp6 : Type := Quotient cuspSetoid

/-- The positive parabolic generator of width six fixing the vector `v`. -/
def posPar (v : Fin 2 → ℤ) : SL(2, ℤ) :=
  ⟨!![1 - 6 * v 0 * v 1, 6 * v 0 ^ 2; -6 * v 1 ^ 2, 1 + 6 * v 0 * v 1], by
    simp [Matrix.det_fin_two]; ring⟩

theorem posPar_mem (v : Fin 2 → ℤ) : posPar v ∈ Gamma 6 := by
  rw [Gamma_mem]
  have h6 : (6 : ZMod 6) = 0 := by decide
  simp only [posPar]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h6]

/-- The positive parabolic generator as an element of `Γ(6)`. -/
def posParSL (v : Fin 2 → ℤ) : Gamma 6 := ⟨posPar v, posPar_mem v⟩

/-- **The cusp values of homomorphisms `Γ(6) → ℚ` fill the sum-zero hyperplane.** -/
def BaseSumZero : Prop :=
  ∀ {I : Type} [Fintype I] (c : I → Prim2),
    Function.Bijective (fun i => (Quotient.mk cuspSetoid (c i) : Cusp6)) →
    ∀ x : I → ℚ, ∑ i, x i = 0 →
      ∃ φ : Gamma 6 → ℚ, (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ i, φ (posParSL (c i).1) = x i

end TernaryPeriodPolynomials.Argument.GammaNStokes
