module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.PrimeKappa
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ZetaMap

@[expose] public section


/-!
# Matrix entries of the `σ`-correspondence `f₁ : P_H ∩ σ⁻¹ S_p σ → P_H`

Formalized by Claude Sonnet 5.5.
The second family of representatives
has binary block `C_∞ = diag(p, 1)`, the parameter lying in the unipotent direction.

For `h ∈ P_H ∩ σ⁻¹ S_p σ` (that is `p ∣ h₁₀` and `p ∣ h₁₂`), the matrix `f₁(h)` has the entries

`λ ↦ λ`, `u₀ ↦ u₀ / p`, `u₁ ↦ u₁`, `D = (d₀₀ d₀₁; d₁₀ d₁₁) ↦ (d₀₀, d₀₁/p; p d₁₀, d₁₁)`

(`f1_val_ij`); in particular `f₁` is injective, maps `S ∩ U` into `U`, and its Levi part is the binary Hecke map.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPeriodPolynomials.Argument.AppendixBResidue

variable {p : ℕ} [Fact p.Prime]

/-- The subgroup `P_H ∩ σ⁻¹ S_p σ`. -/
abbrev Psig (p : ℕ) [Fact p.Prime] : Subgroup PH := Sx PH (primeDatum p).S sigma

theorem mX_val (h : ↥(Psig p)) :
    (((mX PH (primeDatum p).S sigma h : ↥(primeDatum p).S) : IntegralGL).val) = (sigma * h.1.1 * sigma).val := by
  have hs : ((mX PH (primeDatum p).S sigma h : ↥(primeDatum p).S) : IntegralGL) =
      sigma * h.1.1 * sigma⁻¹ := rfl
  rw [hs, sigma_inv]

theorem f1_val (h : ↥(Psig p)) :
    ((f1 (p := p) h : PH) : IntegralGL).val =
      (sigma * ((primeDatum p).f (mX PH (primeDatum p).S sigma h) : IntegralGL) * sigma).val := by
  have e : ((f1 (p := p) h : PH) : IntegralGL) =
      sigma⁻¹ * ((primeDatum p).f (mX PH (primeDatum p).S sigma h) : IntegralGL) * sigma⁻¹⁻¹ := rfl
  rw [e, inv_inv, sigma_inv]

section Entries

variable (h : ↥(Psig p))

private theorem mXe (i j : Fin 3) :
    (((mX PH (primeDatum p).S sigma h : ↥(primeDatum p).S) : IntegralGL).val i j) =
      (sigma * h.1.1 * sigma).val i j := by
  rw [mX_val]

theorem f1_val_00 : ((f1 (p := p) h : PH) : IntegralGL).val 0 0 = h.1.1.val 0 0 := by
  have h1 := f_val_11 (p := p) (mX PH (primeDatum p).S sigma h)
  rw [f1_val, sigma_conj_val]
  simp
  rw [h1, mXe, sigma_conj_val]
  simp

theorem f1_val_01 : ((f1 (p := p) h : PH) : IntegralGL).val 0 1 = p * h.1.1.val 0 1 := by
  have h1 := f_val_10 (p := p) (mX PH (primeDatum p).S sigma h)
  rw [f1_val, sigma_conj_val]
  simp
  rw [h1, mXe, sigma_conj_val]
  simp

theorem f1_val_02 : ((f1 (p := p) h : PH) : IntegralGL).val 0 2 = h.1.1.val 0 2 := by
  have h1 := f_val_12 (p := p) (mX PH (primeDatum p).S sigma h)
  rw [f1_val, sigma_conj_val]
  simp
  rw [h1, mXe, sigma_conj_val]
  simp

theorem f1_val_10 : ((f1 (p := p) h : PH) : IntegralGL).val 1 0 * p = h.1.1.val 1 0 := by
  have h1 := f_val_01 (p := p) (mX PH (primeDatum p).S sigma h)
  rw [f1_val, sigma_conj_val]
  simp
  rw [h1, mXe, sigma_conj_val]
  simp

theorem f1_val_11 : ((f1 (p := p) h : PH) : IntegralGL).val 1 1 = h.1.1.val 1 1 := by
  have h1 := f_val_00 (p := p) (mX PH (primeDatum p).S sigma h)
  rw [f1_val, sigma_conj_val]
  simp
  rw [h1, mXe, sigma_conj_val]
  simp

theorem f1_val_12 : ((f1 (p := p) h : PH) : IntegralGL).val 1 2 * p = h.1.1.val 1 2 := by
  have h1 := f_val_02 (p := p) (mX PH (primeDatum p).S sigma h)
  rw [f1_val, sigma_conj_val]
  simp
  rw [h1, mXe, sigma_conj_val]
  simp

theorem f1_val_20 : ((f1 (p := p) h : PH) : IntegralGL).val 2 0 = h.1.1.val 2 0 := by
  have h1 := f_val_21 (p := p) (mX PH (primeDatum p).S sigma h)
  rw [f1_val, sigma_conj_val]
  simp
  rw [h1, mXe, sigma_conj_val]
  simp

theorem f1_val_21 : ((f1 (p := p) h : PH) : IntegralGL).val 2 1 = p * h.1.1.val 2 1 := by
  have h1 := f_val_20 (p := p) (mX PH (primeDatum p).S sigma h)
  rw [f1_val, sigma_conj_val]
  simp
  rw [h1, mXe, sigma_conj_val]
  simp

theorem f1_val_22 : ((f1 (p := p) h : PH) : IntegralGL).val 2 2 = h.1.1.val 2 2 := by
  have h1 := f_val_22 (p := p) (mX PH (primeDatum p).S sigma h)
  rw [f1_val, sigma_conj_val]
  simp
  rw [h1, mXe, sigma_conj_val]
  simp

end Entries

/-- `f₁` is injective. -/
theorem f1_injective : Function.Injective (f1 (p := p)) := by
  intro h h' he
  have e := congrArg (fun x : PH => OrdinaryFullAction.integral (x : IntegralGL)) he
  simp only [f1_hf] at e
  have e2 : OrdinaryFullAction.integral (h.1.1 : IntegralGL) = OrdinaryFullAction.integral (h'.1.1 : IntegralGL) := by
    have := mul_left_cancel (mul_right_cancel e)
    exact this
  have e3 := integral_injective' e2
  exact Subtype.ext (Subtype.ext e3)

end TernaryPeriodPolynomials.Argument.HeckeHomology
