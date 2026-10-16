module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Tangent
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RhoAction

@[expose] public section


/-!
# The transported coefficient of the real entry

In Appendix C.5 (`ar:sec:real`) of the paper the
paper states that for `L = w₀⁻¹ u(s,t)` and the Gram matrix `L Lᵀ`, the seed's linear
coefficient `𝓑 = τY − X + (u₁ − τu₂)Z` (`ar:eq:seed`), transported by `ρ(L)⁻¹`, is
`aX + bY + (i/r)Z` with `a = (s − it/r)/(1 + s²)` and `b = −(1 + ist/r)/(1 + s²)`. The definitions take `b` as the given formula `entryCoefficient`. Here it is derived: at plane
coordinates equal to those of `L Lᵀ` (`real_entry_tangent`), `ρ(L)⁻¹ 𝓑 = aX + bY + (i/r)Z`, where
`ρ(g) q = det(g)⁻¹ q(g⁻¹𝐗)` is the paper's action (`SeedC3.rho`).

Written by Claude Opus 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.RealEntryCoefficient

open TernaryPeriodPolynomials.Argument

/-- `a = (s − it/r)/(1 + s²)`. -/
def entryCoefficientA (st : ℝ × ℝ) : ℂ :=
  ((st.1 : ℂ) - Complex.I * ((st.2 / entryRadius st : ℝ) : ℂ)) / ((1 + st.1 ^ 2 : ℝ) : ℂ)

private theorem entryFrame_det (s t : ℝ) : (entryFrame s t).det = 1 := by
  simp [entryFrame, Matrix.det_fin_three]

private theorem entryFrame_inv_inv (s t : ℝ) : ((entryFrame s t)⁻¹)⁻¹ = entryFrame s t := by
  apply Matrix.nonsing_inv_nonsing_inv
  rw [entryFrame_det]
  exact isUnit_one

private theorem entryFrame_inv_det (s t : ℝ) : ((entryFrame s t)⁻¹).det = 1 := by
  rw [Matrix.det_nonsing_inv, entryFrame_det, Ring.inverse_one]

/-- `ρ(L)⁻¹` is the substitution `𝐗 ↦ L𝐗 = (Y, Z, X + sY + tZ)`. -/
theorem rho_entryFrame_inv (s t : ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho (entryFrame s t)⁻¹ q =
      bind₁ (![X 1, X 2, X 0 + C (s : ℂ) * X 1 + C (t : ℂ) * X 2] :
        Fin 3 → MvPolynomial (Fin 3) ℂ) q := by
  unfold SeedC3.rho
  rw [entryFrame_inv_inv, entryFrame_inv_det]
  simp only [inv_one, Complex.ofReal_one, map_one, one_mul]
  have hφ : (fun i : Fin 3 => ∑ j : Fin 3, C (((entryFrame s t) i j : ℝ) : ℂ) * X j) =
      (![X 1, X 2, X 0 + C (s : ℂ) * X 1 + C (t : ℂ) * X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) := by
    funext i
    fin_cases i <;> simp [entryFrame, Fin.sum_univ_three]
  rw [hφ]

/-- **The transported real-entry coefficient.** If the plane coordinates `(u, τ)` of `p` are those
of `L Lᵀ`, then `ρ(L)⁻¹ 𝓑_p = aX + bY + (i/r)Z`, with `b = entryCoefficient (s, t)`. -/
theorem rho_entryFrame_inv_seedLinear (s t : ℝ) (p : Fin 5 → ℝ)
    (hu : (p 0, p 1) = gramPlaneU (entryCurve s t 0 0))
    (hτ : seedTau p = gramPlaneTau (entryCurve s t 0 0)) :
    SeedC3.rho (entryFrame s t)⁻¹ (seedLinear p) =
      C (entryCoefficientA (s, t)) * X 0 + C (entryCoefficient (s, t)) * X 1 +
        C (Complex.I / (entryRadius (s, t) : ℂ)) * X 2 := by
  obtain ⟨hU, hT, -⟩ := real_entry_tangent s t
  rw [hU] at hu
  rw [hT] at hτ
  have h0 : p 0 = s / entryRadius (s, t) ^ 2 := (Prod.ext_iff.mp hu).1
  have h1 : p 1 = t / entryRadius (s, t) ^ 2 := (Prod.ext_iff.mp hu).2
  set τ := entryTau (s, t) with hτdef
  set c : ℂ := ((s / entryRadius (s, t) ^ 2 : ℝ) : ℂ) - τ * ((t / entryRadius (s, t) ^ 2 : ℝ) : ℂ)
    with hcdef
  have hshape : SeedC3.rho (entryFrame s t)⁻¹ (seedLinear p) =
      C c * X 0 + C (c * s - 1) * X 1 + C (τ + c * t) * X 2 := by
    rw [rho_entryFrame_inv, seedLinear, hτ, h0, h1]
    simp only [map_add, map_sub, map_mul, map_one, bind₁_C_right, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    have hCc : (C c : MvPolynomial (Fin 3) ℂ) = C ((s / entryRadius (s, t) ^ 2 : ℝ) : ℂ) -
        C τ * C ((t / entryRadius (s, t) ^ 2 : ℝ) : ℂ) := by
      rw [hcdef, map_sub, map_mul]
    linear_combination (-(X 0 + X 1 * C (s : ℂ) + X 2 * C (t : ℂ))) * hCc
  rw [hshape]
  set r := entryRadius (s, t) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = 1 + s ^ 2 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hr2C : (r : ℂ) ^ 2 = 1 + (s : ℂ) ^ 2 + (t : ℂ) ^ 2 := by exact_mod_cast hr2
  have hsC : (1 + (s : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + s ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hτv : τ = ((-(s * t) : ℂ) + Complex.I * r) / (1 + s ^ 2) := by
    rw [hτdef, entryTau]; push_cast; ring
  have hcv : c = (s : ℂ) / r ^ 2 - τ * ((t : ℂ) / r ^ 2) := by
    rw [hcdef]; push_cast; ring
  have ha : c = entryCoefficientA (s, t) := by
    rw [hcv, hτv, entryCoefficientA, ← hr]
    push_cast
    field_simp
    linear_combination (-(s : ℂ)) * hr2C
  have hb : c * s - 1 = entryCoefficient (s, t) := by
    rw [hcv, hτv, entryCoefficient, ← hr]
    push_cast
    field_simp
    linear_combination (-(s : ℂ) ^ 2) * hr2C
  have hc : τ + c * t = Complex.I / (r : ℂ) := by
    rw [hcv, hτv]
    field_simp
    linear_combination (Complex.I * r - (s : ℂ) * t) * hr2C
  rw [hb, hc, ha]

end TernaryPeriodPolynomials.Argument.Statements.RealEntryCoefficient
