module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPlane4
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Faces

@[expose] public section


/-!
# Plane geometry package, part 1: reflection of cusps, conjugation of the positive parabolic, block-diagonal elements

Formalized by Claude Sonnet 5.5.

* `Dref v = (v₀, -v₁)` and `cuspRel_Dref`: the cusp relation of `Γ(6)` is invariant under the reflection `diag(1, -1)`;
* `posPar_conj`: `γ posPar(v) γ⁻¹ = posPar(γ v)` for `γ ∈ SL₂(ℤ)`;
* `colSL w`: an element of `SL₂(ℤ)` with first column the primitive vector `w`; `colSL_inv_apply : (colSL w)⁻¹ w = e₁`.
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

/-- The reflection `v ↦ (v₀, -v₁)`. -/
def Dref (v : Fin 2 → ℤ) : Fin 2 → ℤ := ![v 0, -v 1]

theorem Dref_Dref (v : Fin 2 → ℤ) : Dref (Dref v) = v := by
  ext i; fin_cases i <;> simp [Dref]

/-- The reflection of a primitive vector. -/
def DrefP (v : Prim2) : Prim2 :=
  ⟨Dref v.1, by
    obtain ⟨x, y, h⟩ := v.2
    exact ⟨x, -y, by simpa [Dref] using h⟩⟩

/-- Conjugation by `diag(1, -1)` as an element of `SL₂(ℤ)`. -/
def reflSL (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, -(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
    -(γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    linear_combination h⟩

theorem reflSL_mem {γ : SL(2, ℤ)} (h : γ ∈ Gamma 6) : reflSL γ ∈ Gamma 6 := by
  rw [Gamma_mem] at h ⊢
  obtain ⟨a, b, c, d⟩ := h
  have h6 : (6 : ZMod 6) = 0 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [reflSL, a, b, c, d]

theorem reflSL_mulVec (γ : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    (reflSL γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ Dref v = Dref ((γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) := by
  ext i; fin_cases i <;> simp [reflSL, Dref, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring

/-- **The cusp relation is invariant under the reflection.** -/
theorem cuspRel_Dref {v w : Prim2} (h : CuspRel v w) : CuspRel (DrefP v) (DrefP w) := by
  obtain ⟨γ, hγ, s, hs, e⟩ := h
  refine ⟨reflSL γ, reflSL_mem hγ, s, hs, ?_⟩
  show (reflSL γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ Dref v.1 = s • Dref w.1
  rw [reflSL_mulVec, e]
  ext i; fin_cases i <;> simp [Dref]

theorem DrefP_DrefP (v : Prim2) : DrefP (DrefP v) = v := Subtype.ext (Dref_Dref v.1)

theorem cuspRel_Dref_iff {v w : Prim2} : CuspRel (DrefP v) (DrefP w) ↔ CuspRel v w :=
  ⟨fun h => by simpa [DrefP_DrefP] using cuspRel_Dref h, cuspRel_Dref⟩

/-- Conjugation of the positive parabolic. -/
theorem posPar_conj (γ : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    γ * posPar v * γ⁻¹ = posPar ((γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have key : γ * posPar v = posPar ((γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) * γ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [posPar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
    · linear_combination (6 * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * v 0 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * v 1) * v 1) * hdet
    · linear_combination (-6 * v 0 * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * v 0 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * v 1)) * hdet
    · linear_combination (6 * v 1 * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * v 0 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * v 1)) * hdet
    · linear_combination (-6 * v 0 * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * v 0 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * v 1)) * hdet
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

/-- An element of `SL₂(ℤ)` whose first column is the primitive vector `w`. -/
def colSL (w : Prim2) : SL(2, ℤ) :=
  ⟨!![w.1 0, -(Classical.choose (Classical.choose_spec w.2)); w.1 1, Classical.choose w.2], by
    have h := Classical.choose_spec (Classical.choose_spec w.2)
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    linear_combination h⟩

theorem colSL_mulVec (w : Prim2) : (colSL w : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![1, 0] = w.1 := by
  ext i; fin_cases i <;> simp [colSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem colSL_inv_mulVec (w : Prim2) : ((colSL w)⁻¹ : SL(2, ℤ)) *ᵥ w.1 = ![1, 0] := by
  rw [← colSL_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
  simp

end TernaryPeriodPolynomials.Argument.GammaNStokes
