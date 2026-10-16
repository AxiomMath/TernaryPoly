module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PiecesK
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Shift
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBruhat

@[expose] public section


/-!
# Every cusp: integrability and absolute summability of the orbit integrals

Formalized by Claude Sonnet 5.5.
Paper: "The unfolding is absolutely convergent".

The analogues of `phiO_integrable`, `phiO_norm_summable`, `integral_phiO` for the cusp `k` (`PhiQ0 N k`, `FreeOrbK N k`).
-/

open MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The summand of `lineA1K N k` attached to a free orbit. -/
abbrev phiOK (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrbK N k) : (Fin 2 → ℝ) → ℂ :=
  PhiQ0 N k n f x p q m (orbCosetK N k o)

theorem phiOK_data (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    (∀ ℓ c v, PhiQ0 N k n f x p q m ((qActK N k).act ℓ c) v = PhiQ0 N k n f x p q m c ((N : ℝ) • intVec ℓ + v)) ∧
    (∀ c, Continuous (PhiQ0 N k n f x p q m c)) ∧
    ∀ R : ℝ, ∃ B : Ck N k → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖PhiQ0 N k n f x p q m c v‖ ≤ B c := by
  obtain ⟨hc, hb⟩ := PhiQ0_continuous_bound N k n f hn hx p q m
  exact ⟨fun ℓ c v => PhiQ0_latQ N k n f hx p q m ℓ c v, hc, hb⟩

theorem phiOK_integrable (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrbK N k) :
    Integrable (phiOK N k n f x p q m o) := by
  obtain ⟨h1, hc, hb⟩ := phiOK_data N k n f hn hx p q m
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have h := QAct.orbit_integrable (qActK N k) (fun c w => PhiQ0 N k n f x p q m c w) h1 hc hb o.1 o.2
  have := h.comp_smul (inv_ne_zero hN)
  have e : phiOK N k n f x p q m o = fun v => PhiQ0 N k n f x p q m (Quotient.out o.1) v := rfl
  rw [e]
  simpa [smul_smul, hN] using this

theorem phiOK_norm_summable (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    Summable fun o : FreeOrbK N k => ∫ v : Fin 2 → ℝ, ‖phiOK N k n f x p q m o ((N : ℝ) • v)‖ := by
  obtain ⟨h1, hc, hb⟩ := phiOK_data N k n f hn hx p q m
  have h := QAct.orbit_summable (qActK N k) (fun c w => ((‖PhiQ0 N k n f x p q m c w‖ : ℝ) : ℂ))
    (fun ℓ c v => by simp only [h1 ℓ c v])
    (fun c => Complex.continuous_ofReal.comp (continuous_norm.comp (hc c)))
    (fun R => by
      obtain ⟨B, hBs, hBb⟩ := hb R
      exact ⟨B, hBs, fun c v hv => by simpa using hBb c v hv⟩)
  have e : ∀ o : FreeOrbK N k, ∫ v : Fin 2 → ℝ,
      (((‖PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)‖ : ℝ)) : ℂ) =
      ((∫ v : Fin 2 → ℝ, ‖phiOK N k n f x p q m o ((N : ℝ) • v)‖ : ℝ) : ℂ) := fun o => integral_ofReal
  simp_rw [e] at h
  exact Complex.summable_ofReal.1 h

theorem integral_phiOK (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrbK N k) :
    ∫ v : Fin 2 → ℝ, phiOK N k n f x p q m o ((N : ℝ) • v) = ((N : ℂ) ^ 2)⁻¹ * ∫ v, phiOK N k n f x p q m o v :=
  integral_comp_smul_N N _

theorem integral_norm_phiOK (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrbK N k) :
    ∫ v : Fin 2 → ℝ, ‖phiOK N k n f x p q m o ((N : ℝ) • v)‖ =
      ((N : ℝ) ^ 2)⁻¹ * ∫ v, ‖phiOK N k n f x p q m o v‖ := by
  have := integral_comp_smul_N N (fun v => (((‖phiOK N k n f x p q m o v‖ : ℝ)) : ℂ))
  simp_rw [integral_complex_ofReal] at this
  apply Complex.ofReal_injective
  simpa using this

end TernaryPeriodPolynomials.Argument.FormClassK
