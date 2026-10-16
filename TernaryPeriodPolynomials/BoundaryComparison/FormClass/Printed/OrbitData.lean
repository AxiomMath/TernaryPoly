module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Integrand
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Shift
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBruhat

@[expose] public section


/-!
# (C), step 9: integrability and absolute summability of the orbit integrals

Formalized by Claude Sonnet 5.5.
Paper: "The unfolding is absolutely convergent".

For `3 ≤ N`, `4 ≤ n`, `x` in the face and the free orbit `o` of the line radical lattice:
* `phiO_integrable`: `v ↦ PhiQ0 (coset of o) v` is integrable over `ℝ²`;
* `phiO_norm_summable`: `o ↦ ∫ ‖PhiQ0 (coset of o) (N v)‖ dv` is summable (the absolute convergence of the unfolded integral);
* `integral_phiO`: `∫ PhiQ0 (N v) dv = N⁻² ∫ PhiQ0 v dv`.
-/

open MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The summand of `lineA1K` at the standard cusp attached to a free orbit. -/
abbrev phiO (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrb N) : (Fin 2 → ℝ) → ℂ :=
  PhiQ0 N 1 n f x p q m (orbCoset N o)

theorem phiO_data (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    (∀ ℓ c v, PhiQ0 N 1 n f x p q m ((qActK N 1).act ℓ c) v = PhiQ0 N 1 n f x p q m c ((N : ℝ) • intVec ℓ + v)) ∧
    (∀ c, Continuous (PhiQ0 N 1 n f x p q m c)) ∧
    ∀ R : ℝ, ∃ B : Ck N 1 → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖PhiQ0 N 1 n f x p q m c v‖ ≤ B c := by
  obtain ⟨hc, hb⟩ := PhiQ0_continuous_bound N 1 n f hn hx p q m
  exact ⟨fun ℓ c v => PhiQ0_latQ N 1 n f hx p q m ℓ c v, hc, hb⟩

theorem phiO_integrable_N (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrb N) :
    Integrable (fun v : Fin 2 → ℝ => phiO N n f x p q m o ((N : ℝ) • v)) := by
  obtain ⟨h1, hc, hb⟩ := phiO_data N n f hn hx p q m
  exact QAct.orbit_integrable (qActK N 1) (fun c w => PhiQ0 N 1 n f x p q m c w) h1 hc hb o.1 o.2

theorem phiO_integrable (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrb N) :
    Integrable (phiO N n f x p q m o) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have := (phiO_integrable_N N n f hn hx p q m o).comp_smul (inv_ne_zero hN)
  simpa [smul_smul, hN] using this

theorem phiO_norm_summable (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    Summable fun o : FreeOrb N => ∫ v : Fin 2 → ℝ, ‖phiO N n f x p q m o ((N : ℝ) • v)‖ := by
  obtain ⟨h1, hc, hb⟩ := phiO_data N n f hn hx p q m
  have h := QAct.orbit_summable (qActK N 1) (fun c w => ((‖PhiQ0 N 1 n f x p q m c w‖ : ℝ) : ℂ))
    (fun ℓ c v => by simp only [h1 ℓ c v])
    (fun c => Complex.continuous_ofReal.comp (continuous_norm.comp (hc c)))
    (fun R => by
      obtain ⟨B, hBs, hBb⟩ := hb R
      exact ⟨B, hBs, fun c v hv => by simpa using hBb c v hv⟩)
  have e : ∀ o : FreeOrb N, ∫ v : Fin 2 → ℝ, (((‖PhiQ0 N 1 n f x p q m (Quotient.out o.1) ((N : ℝ) • v)‖ : ℝ)) : ℂ) =
      ((∫ v : Fin 2 → ℝ, ‖phiO N n f x p q m o ((N : ℝ) • v)‖ : ℝ) : ℂ) := fun o => integral_ofReal
  simp_rw [e] at h
  exact Complex.summable_ofReal.1 h

theorem integral_phiO {x : Face} (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrb N) :
    ∫ v : Fin 2 → ℝ, phiO N n f x p q m o ((N : ℝ) • v) = ((N : ℂ) ^ 2)⁻¹ * ∫ v, phiO N n f x p q m o v :=
  integral_comp_smul_N N _

theorem integral_norm_phiO {x : Face} (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrb N) :
    ∫ v : Fin 2 → ℝ, ‖phiO N n f x p q m o ((N : ℝ) • v)‖ = ((N : ℝ) ^ 2)⁻¹ * ∫ v, ‖phiO N n f x p q m o v‖ := by
  have := integral_comp_smul_N N (fun v => (((‖phiO N n f x p q m o v‖ : ℝ)) : ℂ))
  simp_rw [integral_complex_ofReal] at this
  apply Complex.ofReal_injective
  simpa using this

end TernaryPeriodPolynomials.Argument.FormClassK
