module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ReflectionLevel
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Cusp
public import TernaryPeriodPolynomials.EisensteinSeries.Class.FaceK

@[expose] public section


/-!
# Slashing a cusp form of `Γ₂(N)` by an element of `SL₂(ℤ)`

(the identity cell of a non-standard cusp is the seed of `f|A`, `A ∈ SL₂(ℤ)`).

`Γ₂(N)` is normal in `SL₂(ℤ)`, so `f ↦ f ∣[k] A` preserves `S_k(Γ₂(N))`
(`cuspSlash`, from Mathlib's `CuspForm.translate` and the equality `A⁻¹ Γ₂(N) A = Γ₂(N)`);
`slashTwisted_cuspSlash`: its extension to `ℂ` is `slashTwisted (n + 3) A (f ∘ ofComplex)`, so the seed
of `f|A` is the seed with `h` replaced by `h|A`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise ConjAct
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument

section Level

variable (N : ℕ)

theorem conj_mem_leviGroup (A : SL(2, ℤ)) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ leviGroup N) :
    (mapGL ℝ A : GL (Fin 2) ℝ) * γ * (mapGL ℝ A : GL (Fin 2) ℝ)⁻¹ ∈ leviGroup N := by
  obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.1 hγ
  refine Subgroup.mem_map.2 ⟨A * B * A⁻¹, ?_, by simp [map_mul, map_inv]⟩
  exact (CongruenceSubgroup.Gamma_normal N).conj_mem B hB A

theorem conjAct_leviGroup (A : SL(2, ℤ)) :
    ConjAct.toConjAct (mapGL ℝ A : GL (Fin 2) ℝ)⁻¹ • leviGroup N = leviGroup N := by
  ext γ
  have key : ∀ (g : GL (Fin 2) ℝ) (Λ : Subgroup (GL (Fin 2) ℝ)) (γ : GL (Fin 2) ℝ),
      γ ∈ ConjAct.toConjAct g⁻¹ • Λ ↔ g * γ * g⁻¹ ∈ Λ := by
    intro g Λ γ
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [ConjAct.smul_def]
  rw [key]
  constructor
  · intro h
    have := conj_mem_leviGroup N A⁻¹ h
    simpa [map_inv, mul_assoc] using this
  · intro h
    exact conj_mem_leviGroup N A h

/-- Casting a cusp form along an equality of levels. -/
def castLevel {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ = Γ') (f : CuspForm Γ k) :
    CuspForm Γ' k := h ▸ f

theorem coe_castLevel {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ = Γ') (f : CuspForm Γ k) :
    ⇑(castLevel h f) = ⇑f := by
  subst h; rfl

variable (n : ℕ)

/-- **The slash `f ∣[n+3] A` of a cusp form of `Γ₂(N)` by `A ∈ SL₂(ℤ)`** (a cusp form of the same
level, by normality). -/
def cuspSlash (A : SL(2, ℤ)) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ) :=
  castLevel (conjAct_leviGroup N A) (CuspForm.translate f (mapGL ℝ A : GL (Fin 2) ℝ))

theorem coe_cuspSlash (A : SL(2, ℤ)) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    ⇑(cuspSlash N n A f) = ⇑f ∣[((n + 3 : ℕ) : ℤ)] A := by
  unfold cuspSlash
  rw [coe_castLevel]
  exact CuspForm.coe_translate f A

/-- **The extension of the slash is the twisted slash**: `(f|A) ∘ ofComplex = slashTwisted (n+3) A (f ∘
ofComplex)` on the upper half-plane. -/
theorem slashTwisted_cuspSlash (A : SL(2, ℤ)) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    {z : ℂ} (hz : 0 < z.im) :
    slashTwisted (n + 3) ((mapGL ℝ A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        (fun w => f (ofComplex w)) z =
      cuspSlash N n A f (ofComplex z) := by
  set τ : ℍ := ⟨z, hz⟩ with hτ
  have e2 : ofComplex z = τ := ofComplex_apply_of_im_pos hz
  rw [e2, coe_cuspSlash, SL_slash_def]
  have hdet : ((mapGL ℝ A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; simp
  have hpos : 0 < (mapGL ℝ A : GL (Fin 2) ℝ).det.val := by
    simp
  have hsm : (((mapGL ℝ A : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) =
      (((mapGL ℝ A : GL (Fin 2) ℝ) 0 0 : ℝ) * z + (mapGL ℝ A : GL (Fin 2) ℝ) 0 1) /
        (((mapGL ℝ A : GL (Fin 2) ℝ) 1 0 : ℝ) * z + (mapGL ℝ A : GL (Fin 2) ℝ) 1 1) :=
    coe_smul_of_det_pos hpos τ
  unfold slashTwisted
  rw [hdet]
  simp only [Complex.ofReal_one, one_pow, one_mul]
  rw [← hsm]
  have e1 : (ofComplex ((((mapGL ℝ A : GL (Fin 2) ℝ)) • τ : ℍ) : ℂ) : ℍ) =
      (mapGL ℝ A : GL (Fin 2) ℝ) • τ := ofComplex_apply _
  rw [e1]
  have e3 : (A • τ : ℍ) = (mapGL ℝ A : GL (Fin 2) ℝ) • τ := rfl
  rw [e3, mul_comm]
  rfl

end Level

end TernaryPeriodPolynomials.Argument.EisensteinClass
