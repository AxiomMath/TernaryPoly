module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Term
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Lattice

@[expose] public section


/-!
# The coset space `Γ_P \ Γ` and the bottom-row injection (Appendix C.3)

Right cosets `Γ_P γ` of the plane stabilizer inject into primitive integral bottom rows `e₃ᵀ γ ∈ ℤ³`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### The coset space `Γ_P \ Γ` and the bottom-row injection -/

section Cosets

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))

/-- The right coset space `Γ_P \ Γ`, with `Γ_P = Γ ∩ planeStab`. -/
abbrev PlaneCoset := Quotient (QuotientGroup.rightRel (planeStab.subgroupOf Γ))

/-- The bottom row `e₃ᵀ γ ∈ ℤ³`. -/
def bottomRowZ (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Fin 3 → ℤ :=
  fun j => (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 j

theorem bottomRowZ_stab_mul {l γ : Matrix.SpecialLinearGroup (Fin 3) ℤ} (hl : l ∈ planeStab) :
    bottomRowZ (l * γ) = bottomRowZ γ := by
  obtain ⟨h0, h1, h2⟩ := hl
  funext j
  simp [bottomRowZ, Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2]

theorem mem_planeStab_of_row {a b : Matrix.SpecialLinearGroup (Fin 3) ℤ}
    (h : bottomRowZ a = bottomRowZ b) : b * a⁻¹ ∈ planeStab := by
  have key : ∀ j, ((b * a⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℤ) 2 j := by
    intro j
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [bottomRowZ] at h0 h1 h2
    have e : ((b * a⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 2 j =
        ((a * a⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 2 j := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three]
      rw [← h0, ← h1, ← h2]
    rw [e, mul_inv_cancel]; rfl
  exact ⟨by simpa using key 0, by simpa using key 1, by simpa using key 2⟩

/-- The bottom row of a coset. -/
def cosetRow : PlaneCoset Γ → (Fin 3 → ℤ) :=
  Quotient.lift (fun a : Γ => bottomRowZ a.1) (by
    intro a b hab
    have hH : b.1 * a.1⁻¹ ∈ planeStab := by
      have := QuotientGroup.rightRel_apply.1 hab
      simpa using Subgroup.mem_subgroupOf.1 this
    have e : b.1 = (b.1 * a.1⁻¹) * a.1 := by simp
    show bottomRowZ a.1 = bottomRowZ b.1
    rw [e, bottomRowZ_stab_mul hH])

theorem cosetRow_injective : Function.Injective (cosetRow Γ) := by
  intro x y
  induction x using Quotient.inductionOn with | _ a => ?_
  induction y using Quotient.inductionOn with | _ b => ?_
  intro h
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_)
  simpa using mem_planeStab_of_row (a := a.1) (b := b.1) h

theorem bottomRowZ_ne_zero (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : bottomRowZ γ ≠ 0 := by
  intro h
  have := Matrix.det_eq_zero_of_row_eq_zero (A := (γ : Matrix (Fin 3) (Fin 3) ℤ)) 2
    (fun j => congrFun h j)
  rw [Matrix.SpecialLinearGroup.det_coe] at this
  exact one_ne_zero this

end Cosets

end TernaryPeriodPolynomials.Argument.ConvergenceC4
