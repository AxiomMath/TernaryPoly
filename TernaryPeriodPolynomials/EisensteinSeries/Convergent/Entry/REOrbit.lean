module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBadMain

@[expose] public section


/-!
# R-e: Orbit decomposition at the good-line cusp

`entry_orbit_decomposition`: splitting the spherical plane section at `3` along the two `P(ℚ₃)\GL₃(ℚ₃)/K₁` orbits, the bad-plane orbit contributes exactly `r_bad` and the complementary orbit `r_full - r_bad = (c₃ - 1/9)·∏_{p≠3} c_p` (a consequence of the two identities and integrability).

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- Integrability of one slice of the integrand of a `FiniteEntryIdentity` (from its first two clauses). -/
theorem integrable_of_finiteEntryIdentity {n : ℕ} {D : InducingData n} {ι ιL : AdelicGL → ℂ}
    {F : BinaryAdelicGL → ℂ → ℂ} {r : ℂ} (h : FiniteEntryIdentity D ι ιL F r) (g : AdelicGL)
    (hg : ιL g ≠ 0) (x : BinaryAdelicGL) (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun v : FiniteAdeles × FiniteAdeles =>
      ι (finiteEntryElement v g) * (cF D (finiteEntryElement v g) * F (x * bF (finiteEntryElement v g)) z))
      (finiteMeasure.prod finiteMeasure) := by
  obtain ⟨measurable, majorant, _⟩ := h g hg x
  obtain ⟨φ, hφ, bound⟩ := majorant {z} isCompact_singleton (by simpa using hz)
  refine hφ.mono' ?_ (Eventually.of_forall fun v => bound v z rfl)
  exact (measurable.comp (measurable_id.prodMk (measurable_const (a := (⟨z, hz⟩ : {z : ℂ // 0 < z.im}))))).aestronglyMeasurable

/-- **Orbit decomposition at the good-line cusp.**  Splitting the spherical plane section at `3` along the two
`P(ℚ₃)\GL₃(ℚ₃)/K₁` orbits, the bad-plane orbit contributes exactly `r_bad` and the complementary orbit
`r_full − r_bad = (c₃ − 1/9)·∏_{p≠3} c_p`. -/
theorem entry_orbit_decomposition {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) (g : AdelicGL)
    (hg : goodLineWeight g ≠ 0) (x : BinaryAdelicGL) (z : ℂ) (hz : 0 < z.im) :
    (∫ v : FiniteAdeles × FiniteAdeles, (1 - badPlaneWeight (finiteEntryElement v g)) *
        (cF D (finiteEntryElement v g) * S.F (x * bF (finiteEntryElement v g)) z)
        ∂(finiteMeasure.prod finiteMeasure)) =
      (S.rFull - S.rBad) * (cFLine D g * S.F (x * bFLine g) z) := by
  have h1 := finiteEntryIdentity_spherical S goodLineWeight
  have h2 := badPlaneEntryIdentity S
  have i1 := integrable_of_finiteEntryIdentity h1 g hg x z hz
  have i2 := integrable_of_finiteEntryIdentity h2 g hg x z hz
  have e1 := (h1 g hg x).2.2 z hz
  have e2 := (h2 g hg x).2.2 z hz
  have split : ∀ v : FiniteAdeles × FiniteAdeles, (1 - badPlaneWeight (finiteEntryElement v g)) *
      (cF D (finiteEntryElement v g) * S.F (x * bF (finiteEntryElement v g)) z) =
      (fun _ : AdelicGL => (1 : ℂ)) (finiteEntryElement v g) *
        (cF D (finiteEntryElement v g) * S.F (x * bF (finiteEntryElement v g)) z) -
      badPlaneWeight (finiteEntryElement v g) *
        (cF D (finiteEntryElement v g) * S.F (x * bF (finiteEntryElement v g)) z) := by
    intro v
    ring
  simp_rw [split]
  rw [integral_sub i1 i2, e1, e2]
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
