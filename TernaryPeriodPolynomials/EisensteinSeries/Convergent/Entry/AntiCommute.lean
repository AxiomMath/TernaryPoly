module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.SourceAnti
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.TCommute

@[expose] public section


/-!
# The reflected half commutes with the real intertwining integral

`ε = diag(-1,1,1)` and the entry frame satisfy `ε L_{s,t} = L_{-s,t} Λ` with `Λ = diag(1,-1,1)`, the reflection of the
line Levi.  Hence, by the measure-preserving substitution `(s,t) ↦ (-s,t)` and `tcommute` at `Λ g`, the real integral of
the plane integral cochain at the reflected group element `ε L_{s,t} g` is `c_∞` times the line integral cochain at `Λ g`
(`tcommute_anti`).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem epsJ_val : (epsJ.val : Mat3) = !![-1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsJ, GeneralEisenstein.Adelic.planeLevi, planeBlock, UpperHalfPlane.J]

/-- The reflection of the line Levi, `Λ = diag(1,-1,1)`. -/
def lamM : Mat3 := !![1, 0, 0; 0, -1, 0; 0, 0, 1]

theorem epsJ_mul_entryFrame (s t : ℝ) :
    epsJ.val * entryFrame s t = entryFrame (-s) t * lamM := by
  rw [epsJ_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [entryFrame, lamM, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_lamM : lamM.det = -1 := by
  simp [lamM, Matrix.det_fin_three]

/-- **The reflected half commutes with the real intertwining integral.** -/
theorem tcommute_anti (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (M : ℝ) (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (g : Mat3) (hg : g.det ≠ 0) (Γ₀ Γ₁ Γ₂ : Mat3) (hΓ₀ : Γ₀.PosDef) (hΓ₁ : Γ₁.PosDef) (hΓ₂ : Γ₂.PosDef)
    (κ : Fin 3 →₀ ℕ) :
    Integrable (fun u : ℝ × ℝ => planeIntG n h (epsJ.val * (entryFrame u.1 u.2 * g)) Γ₀ Γ₁ Γ₂ κ) ∧
    (∫ u : ℝ × ℝ, planeIntG n h (epsJ.val * (entryFrame u.1 u.2 * g)) Γ₀ Γ₁ Γ₂ κ) =
      (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) * lineIntG n h (lamM * g) Γ₀ Γ₁ Γ₂ κ := by
  have hg' : (lamM * g).det ≠ 0 := by
    rw [Matrix.det_mul, det_lamM]; simpa using hg
  obtain ⟨hI, hE⟩ := tcommute n hn h hh M hM (lamM * g) hg' Γ₀ Γ₁ Γ₂ hΓ₀ hΓ₁ hΓ₂ κ
  set Φ : ℝ × ℝ → ℂ := fun u => planeIntG n h (entryFrame u.1 u.2 * (lamM * g)) Γ₀ Γ₁ Γ₂ κ with hΦ
  set e : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ) with he
  have hmp : MeasurePreserving e (volume : Measure (ℝ × ℝ)) volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id volume)
  have hfun : (fun u : ℝ × ℝ => planeIntG n h (epsJ.val * (entryFrame u.1 u.2 * g)) Γ₀ Γ₁ Γ₂ κ) =
      fun u => Φ (e u) := by
    funext u
    have : epsJ.val * (entryFrame u.1 u.2 * g) = entryFrame (-u.1) u.2 * (lamM * g) := by
      rw [← Matrix.mul_assoc, epsJ_mul_entryFrame, Matrix.mul_assoc]
    rw [this]
    rfl
  rw [hfun]
  refine ⟨(hmp.integrable_comp_emb e.measurableEmbedding).mpr hI, ?_⟩
  exact (hmp.integral_comp' Φ).trans hE

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
