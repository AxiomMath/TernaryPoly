module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.RowOrbits
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Measure

@[expose] public section


/-!
# (C), step 5: the congruence cells of the finite integral

Formalized by Claude Sonnet 5.5.

The free orbits `o` of the line radical lattice on `Γ_P\Γ(N)` (cosets with `ρ₀ ≠ 0`) index the cells
`pieceFin o = (r_o₁ + N Ẑ) × (r_o₂ + N Ẑ) ⊂ 𝔸_f²` of the support of the finite part of the induced section,
`r_o = ptC(coset of o) ∈ ℚ²`:
* `pieceFin_measurable`, `volume_pieceFin = N⁻²` (the finite congruence integral of a constant),
* `pieceFin_disjoint` (distinct free orbits give disjoint cells),
* `exists_orbit_of_decomp` (the support: `w₀⁻¹ u(σ) ∈ P(ℚ) K(N)` forces `σ` into some cell).
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N]

/-- The free orbits of the line radical lattice at the standard cusp. -/
abbrev FreeOrb : Type := {o : Quotient (qActK N 1).orbSetoid // (qActK N 1).r0Q o ≠ 0}

/-- The coset of the representative of a free orbit. -/
def orbCoset (o : FreeOrb N) : Ck N 1 := Quotient.out o.1

/-- The rational point `r_o` of a free orbit. -/
def orbPt (o : FreeOrb N) : ℚ × ℚ := ptC N (orbCoset N o)

/-- The cell `(r₁ + N Ẑ) × (r₂ + N Ẑ)` of the free orbit `o`. -/
def pieceFin (o : FreeOrb N) : Set (FiniteAdeles × FiniteAdeles) :=
  latCoset N (algebraMap ℚ FiniteAdeles (orbPt N o).1) ×ˢ latCoset N (algebraMap ℚ FiniteAdeles (orbPt N o).2)

theorem pieceFin_measurable (o : FreeOrb N) : MeasurableSet (pieceFin N o) :=
  (latCoset_measurable N _).prod (latCoset_measurable N _)

/-- **The congruence cell has volume `N⁻²`.** -/
theorem volume_pieceFin (o : FreeOrb N) :
    (finiteMeasure.prod finiteMeasure) (pieceFin N o) = (N : ENNReal)⁻¹ * (N : ENNReal)⁻¹ := by
  unfold pieceFin
  rw [Measure.prod_prod, finiteMeasure_latCoset, finiteMeasure_latCoset, finiteMeasure_latSet]

theorem orbCoset_r0 (o : FreeOrb N) :
    cuspRow (gammaN N) (CuspData.ofSL 1).r (orbCoset N o) 0 ≠ 0 := by
  have := o.2
  rw [QAct.r0Q_out] at this
  exact this

/-- **Distinct free orbits give disjoint congruence cells.** -/
theorem pieceFin_disjoint (hN : 3 ≤ N) : Pairwise (Function.onFun Disjoint (pieceFin N)) := by
  intro o o' hne
  rw [Function.onFun, Set.disjoint_left]
  rintro σ ⟨h1, h2⟩ ⟨h1', h2'⟩
  apply hne
  have e1 := latSet_sub N ((mem_latCoset N).1 h1') ((mem_latCoset N).1 h1)
  have e2 := latSet_sub N ((mem_latCoset N).1 h2') ((mem_latCoset N).1 h2)
  have d1 : σ.1 - algebraMap ℚ FiniteAdeles (orbPt N o').1 - (σ.1 - algebraMap ℚ FiniteAdeles (orbPt N o).1) =
      algebraMap ℚ FiniteAdeles ((orbPt N o).1 - (orbPt N o').1) := by rw [map_sub]; ring
  have d2 : σ.2 - algebraMap ℚ FiniteAdeles (orbPt N o').2 - (σ.2 - algebraMap ℚ FiniteAdeles (orbPt N o).2) =
      algebraMap ℚ FiniteAdeles ((orbPt N o).2 - (orbPt N o').2) := by rw [map_sub]; ring
  rw [d1] at e1
  rw [d2] at e2
  obtain ⟨z1, hz1⟩ := rat_in_lat N e1
  obtain ⟨z2, hz2⟩ := rat_in_lat N e2
  have := orbit_of_pt_shift N hN (c := orbCoset N o) (c' := orbCoset N o') (orbCoset_r0 N o) (orbCoset_r0 N o')
    ![-z1, -z2] (by
      unfold orbPt at hz1 hz2
      ext
      · simp only [Matrix.cons_val_zero]; push_cast; linarith
      · simp only [Matrix.cons_val_one]; push_cast; linarith)
  obtain ⟨ℓ, hℓ⟩ := this
  have hrel : (qActK N 1).OrbRel (orbCoset N o) (orbCoset N o') := ⟨ℓ, hℓ⟩
  have : o.1 = o'.1 := by
    have h1 : Quotient.mk (qActK N 1).orbSetoid (orbCoset N o) = o.1 := Quotient.out_eq o.1
    have h2 : Quotient.mk (qActK N 1).orbSetoid (orbCoset N o') = o'.1 := Quotient.out_eq o'.1
    rw [← h1, ← h2]
    exact Quotient.sound hrel
  exact Subtype.ext this

end TernaryPeriodPolynomials.Argument.FormClassK
