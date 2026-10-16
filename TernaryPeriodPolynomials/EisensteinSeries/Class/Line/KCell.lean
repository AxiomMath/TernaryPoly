module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBig

@[expose] public section


/-!
# Cell analysis of the line row at the cusp `k⁻¹ P k`: which cosets lie in the big cell

Paper: "Two planes are either
equal or distinct. A line is either contained in or complementary to the source plane".

The bottom row of `k γ` for `γ ∈ Γ(N)` is congruent modulo `N` to the bottom row of `k`
(`cuspRow_modN`). Hence the first entry `r₀ = (k γ)₂₀` of every coset is congruent to `k₂₀` modulo `N`:

* if `N ∤ k₂₀`, then `r₀ ≠ 0` for every coset: the cell `Q, I` is empty and every orbit of the line
  radical lattice is free, i.e. the radical average of the series at this cusp is the sum over **all**
  orbits (`r0Q_ne_zero_of_not_dvd`);
* if `N ∣ k₂₀`, then `N ∣ r₀` for every coset: the cell `Q, I` can be non-empty (it is for `k = 1`)
  and the free orbits have `|r₀| ≥ N` (`N_dvd_r0_of_dvd`).

The unfolding of the free orbits involves no sign: the integrand is the same summand coefficient for every
orbit (`PhiQ0_eq_seed_mul_kernel`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

section Cells

variable (N : ℕ) (k : SL(3, ℤ))

/-- **The bottom row of `k γ` is congruent to the bottom row of `k` modulo `N`.** -/
theorem cuspRow_modN (c : Ck N k) (j : Fin 3) :
    (N : ℤ) ∣ cuspRow (gammaN N) (CuspData.ofSL k).r c j - (k : Matrix (Fin 3) (Fin 3) ℤ) 2 j := by
  induction c using Quotient.inductionOn with | _ a => ?_
  have hr : (CuspData.ofSL k).r = fun i => (k : Matrix (Fin 3) (Fin 3) ℤ) 2 i := by
    rw [ofSL_r]; ext i; simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  have ha := mem_gammaN.1 a.2
  have e : cuspRow (gammaN N) (CuspData.ofSL k).r (Quotient.mk _ a) j -
      (k : Matrix (Fin 3) (Fin 3) ℤ) 2 j = ∑ i : Fin 3, (k : Matrix (Fin 3) (Fin 3) ℤ) 2 i *
        ((a.1 : Matrix (Fin 3) (Fin 3) ℤ) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j) := by
    rw [cuspRow_mk, hr]
    simp [Matrix.vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib, Matrix.one_apply]
  rw [e]
  exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (ha i j) _

theorem N_dvd_r0_of_dvd (hk : (N : ℤ) ∣ (k : Matrix (Fin 3) (Fin 3) ℤ) 2 0) (c : Ck N k) :
    (N : ℤ) ∣ cuspRow (gammaN N) (CuspData.ofSL k).r c 0 := by
  have := cuspRow_modN N k c 0
  have h2 := dvd_add this hk
  simpa using h2

theorem r0_ne_zero_of_not_dvd (hk : ¬ (N : ℤ) ∣ (k : Matrix (Fin 3) (Fin 3) ℤ) 2 0) (c : Ck N k) :
    cuspRow (gammaN N) (CuspData.ofSL k).r c 0 ≠ 0 := by
  intro h0
  have := cuspRow_modN N k c 0
  rw [h0, zero_sub, dvd_neg] at this
  exact hk this

/-- If `N ∤ k₂₀`, the cell `Q, I` is empty: every orbit of the line radical lattice on the cosets of the
cusp `k⁻¹Pk` is free. -/
theorem r0Q_ne_zero_of_not_dvd [NeZero N]
    (hk : ¬ (N : ℤ) ∣ (k : Matrix (Fin 3) (Fin 3) ℤ) 2 0) (o : Quotient (qActK N k).orbSetoid) :
    (qActK N k).r0Q o ≠ 0 := by
  rw [QAct.r0Q_out]
  exact r0_ne_zero_of_not_dvd N k hk _

end Cells

end TernaryPeriodPolynomials.Argument.EisensteinClass
