module

public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.CochainLedger

@[expose] public section


/-!
# Cochain-level identity of the series and of the model cocycle at the vertices `(1, a, ab)`

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise MatrixGroups
open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeriesModel

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.FormCochainBridge TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- The rational vertex of an element of `Γ(N)`. -/
def ratVertex (N : ℕ) (h3 : 3 ∣ N) (a : gammaN N) : RationalGL3 := (toRationalLevel N h3 a).1

theorem ratVertex_mul (N : ℕ) (h3 : 3 ∣ N) (a b : gammaN N) :
    ratVertex N h3 (a * b) = ratVertex N h3 a * ratVertex N h3 b := by
  unfold ratVertex; rw [map_mul]; rfl

/-- **A cochain-level comparison hypothesis** (single `D`, single cusp, single scalar; NOT the paper's all-input linear comparison.  For `D, c, lam` the two homogeneous cocycles (the Gram-triangle cochain of the series on
real vertices and the model cocycle on rational vertices) agree, up to the scalar `lam`, on the vertices `(1, a, ab)`, `a, b ∈ Γ(N)`. -/
def CochainTarget (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (n : ℕ) (hn : 4 ≤ n)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (D : InducingData n)
    (c : SourceSpace.sourceCocycles D .plane) (lam : ℂ) : Prop :=
  ∀ a b : gammaN N,
    (gramCochain (gammaN N) n (planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))
        ![1, Matrix.SpecialLinearGroup.mapGL ℝ a.1, Matrix.SpecialLinearGroup.mapGL ℝ a.1 *
          Matrix.SpecialLinearGroup.mapGL ℝ b.1] : HomogeneousPoly n) =
      lam • (TernaryPeriodPolynomials.Argument.ConvergentEisenstein.EndpointEisensteinCocycle.globalCocycle D
        (TernaryPeriodPolynomials.Argument.ConvergentEisenstein.planeEisensteinConvergent hn D) hn c).val.val
        ![1, ratVertex N h3 a, ratVertex N h3 a * ratVertex N h3 b]

/-- **Reduction of a class identity to the cochain identity**: if the two cocycles agree up to `lam` on the vertices `(1, a, ab)` of `Γ(N)`, then the
literal class of the series is `lam` times the restriction of the model class. -/
theorem eisensteinClassC_eq_of_cochainTarget (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (n : ℕ) (hn : 4 ≤ n)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (D : InducingData n)
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1) (c : SourceSpace.sourceCocycles D .plane) (lam : ℂ)
    (H : CochainTarget N h3 n hn f D c lam) :
    eisensteinClassC_gammaN N n f hn =
      lam • (groupCohomology.map (toRationalLevel N h3) (repMor N h3 n D.chi hc) 2).hom
        (TernaryPeriodPolynomials.Argument.LevelTransfer.bridge (rationalCoefficientComponent n D.chi) rationalLevel
          (Submodule.Quotient.mk (TernaryPeriodPolynomials.Argument.ConvergentEisenstein.EndpointEisensteinCocycle.globalCocycle
            D (TernaryPeriodPolynomials.Argument.ConvergentEisenstein.planeEisensteinConvergent hn D) hn c))) := by
  change eisensteinClassC (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N) = _
  rw [← bridge_gramCocycle_eisenstein (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N)]
  rw [TernaryPeriodPolynomials.Argument.LevelTransfer.bridge_mk, TernaryPeriodPolynomials.Argument.LevelTransfer.bridge_mk,
    groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply, ← map_smul]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  refine Eq.trans ?_ (Eq.trans (H a b) ?_)
  · rfl
  · rw [Submodule.coe_smul, Pi.smul_apply]
    congr 1
    have := TernaryPeriodPolynomials.Argument.LevelTransfer.bridgeCocycle_apply
      (rationalCoefficientComponent n D.chi) rationalLevel
      (TernaryPeriodPolynomials.Argument.ConvergentEisenstein.EndpointEisensteinCocycle.globalCocycle
            D (TernaryPeriodPolynomials.Argument.ConvergentEisenstein.planeEisensteinConvergent hn D) hn c)
      (toRationalLevel N h3 a) (toRationalLevel N h3 b)
    refine Eq.trans ?_ (Eq.trans this.symm ?_)
    · rfl
    · rfl

end TernaryPeriodPolynomials.Argument.FormSeriesModel
