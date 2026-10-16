module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.FacePairingComparison
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Comparison

@[expose] public section


/-!
# A representative of the fundamental cycle of the model cone

`exists_fundamentalOmega` produces a degree-four chain `Ω` of the model cone `coneR` whose coinvariant class is a
cycle spanning all cycles of the coinvariant complex modulo boundaries.  These are exactly the hypotheses `hΩ` and
`hspan` of `facePairing_comparison`.  It follows from the `exists_fundamental_cycle` (the top cohomology of `coneR`
is one-dimensional, `coneR_H4`) and surjectivity of `Coinvariants.mk`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

theorem exists_fundamentalOmega : ∃ Ω : coneR.X 4,
    coinvD coneR 4 3 (Representation.Coinvariants.mk (coneR.X 4).ρ Ω) = 0 ∧
    ∀ z : (coneR.X 4).ρ.Coinvariants, coinvD coneR 4 3 z = 0 →
      ∃ c : ℚ, z - c • Representation.Coinvariants.mk (coneR.X 4).ρ Ω ∈ LinearMap.range (coinvD coneR 5 4) := by
  obtain ⟨ω, hω0, hspan, -⟩ := exists_fundamental_cycle coneR coneR_H4
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ ω
  exact ⟨v, hω0, hspan⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
