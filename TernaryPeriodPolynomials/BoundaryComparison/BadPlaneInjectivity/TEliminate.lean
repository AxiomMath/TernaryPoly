module

public import TernaryPeriodPolynomials.BoundaryComparison.BadPlaneInjectivity.EdgePullback

@[expose] public section


/-!
# Eliminating the abstract `T` from `bad_plane_data_injective` in favour of `line_constant_term_comparison`'s canonical map

`bad_plane_data_injective` quantifies over an *arbitrary* `T` satisfying the existence clause `hT`. `line_constant_term_comparison`
(`Targets/PropC5.lean`) supplies a *canonical* `T₀` satisfying both an existence clause and
a uniqueness clause: any global cocycle whose plane coordinate is `InnerBoundary` and whose line
coordinate is `InnerBoundary` has its line coordinate pinned to `T₀` applied to its plane
coordinate.

`line_innerBoundary_of_plane_innerBoundary` (`EdgePullback.lean`) shows the line-side
`InnerBoundary` hypothesis of the uniqueness clause is automatic for the coordinates of a global
cocycle once the plane side is `InnerBoundary`. Combining the two: *any* `T` satisfying `hT` must
agree with *any* `T₀` satisfying `line_constant_term_comparison`'s uniqueness clause, on every `InnerBoundary`-plane
class. This is proved here generically (`T₀` is just assumed to satisfy the uniqueness-clause
shape, as a hypothesis) so this file does not need to import `Targets/PropC5.lean` at all.

Consequence: `bad_plane_data_injective`'s `ξ = 0` goal depends on `T` only through `T ξ`, and `T ξ` is forced to
equal `T₀ ξ` for *any* fixed choice of a uniqueness-clause map `T₀` (e.g. `line_constant_term_comparison`'s own). So
`bad_plane_data_injective` reduces to a statement with no reference to an arbitrary `T`: for `ξ` with
`InnerBoundary .plane ξ`, `VanishesOnGood .plane ξ`, and `VanishesOnGood .line (T₀ ξ)` for *some*
fixed uniqueness-clause `T₀`, conclude `ξ = 0`. (`appendix_C6_of_core` below.)
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous


namespace TernaryPeriodPolynomials.Argument.BadPlaneInjectivity

/-- The shape of `line_constant_term_comparison`'s uniqueness clause, as a standalone hypothesis on a candidate `T₀`. -/
def IsUniquenessMap (n : ℕ) (χ : RankOneCharacter)
    (T₀ : StratumH2 n χ .plane →ₗ[ℂ] StratumH2 n χ .line) : Prop :=
  ∀ c : cocycles rationalLevel (rationalCoefficientComponent n χ),
    InnerBoundary n χ .plane (globalCoordinates n χ c).1 →
    InnerBoundary n χ .line (globalCoordinates n χ c).2 →
    (globalCoordinates n χ c).2 = T₀ (globalCoordinates n χ c).1

/-- **`T`-elimination.** Any `T` satisfying `bad_plane_data_injective`'s existence hypothesis `hT` agrees, on
every `InnerBoundary`-plane class, with any `T₀` satisfying the uniqueness-clause shape
`IsUniquenessMap` (in particular with `line_constant_term_comparison`'s canonical map). The line-side `InnerBoundary`
needed to invoke `IsUniquenessMap` comes for free from `line_innerBoundary_of_plane_innerBoundary`,
applied to the cocycle witnessing `hT`. -/
theorem T_eq_of_isUniquenessMap (n : ℕ) (χ : RankOneCharacter)
    (T T₀ : StratumH2 n χ .plane →ₗ[ℂ] StratumH2 n χ .line)
    (hT : ∀ ξ, InnerBoundary n χ .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n χ),
        globalCoordinates n χ c = (ξ, T ξ))
    (hT₀ : IsUniquenessMap n χ T₀)
    (ξ : StratumH2 n χ .plane) (hξ : InnerBoundary n χ .plane ξ) :
    T ξ = T₀ ξ := by
  obtain ⟨c, hc⟩ := hT ξ hξ
  have hplane : InnerBoundary n χ .plane (globalCoordinates n χ c).1 := by
    rw [hc]; exact hξ
  have hline' : InnerBoundary n χ .line (globalCoordinates n χ c).2 :=
    line_innerBoundary_of_plane_innerBoundary n χ c hplane
  have hres := hT₀ c hplane hline'
  rw [hc] at hres
  simpa using hres

/-- **Core-lemma reduction.** `bad_plane_data_injective`'s conclusion depends on the abstract `T` only through
`T ξ`, and `T ξ` is forced to equal `T₀ ξ` for any *fixed, caller-supplied* uniqueness-clause map
`T₀` (e.g. `line_constant_term_comparison`'s own canonical map, instantiated by whoever assembles the final proof). So
it suffices to prove the `T`-free `core` statement: `InnerBoundary .plane ξ`,
`VanishesOnGood .plane ξ`, and `VanishesOnGood .line (T₀ ξ)` imply `ξ = 0`, for that one `T₀`. -/
theorem appendix_C6_of_core (n : ℕ)
    (T₀ : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT₀ : IsUniquenessMap n trivialCharacter T₀)
    (core : ∀ ξ : StratumH2 n trivialCharacter .plane, InnerBoundary n trivialCharacter .plane ξ →
      VanishesOnGood n trivialCharacter .plane ξ → VanishesOnGood n trivialCharacter .line (T₀ ξ) →
        ξ = 0)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ))
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ)
    (hline : VanishesOnGood n trivialCharacter .line (T ξ)) : ξ = 0 := by
  have hTeq : T ξ = T₀ ξ := T_eq_of_isUniquenessMap n trivialCharacter T T₀ hT hT₀ ξ hξ
  exact core ξ hξ hgood (hTeq ▸ hline)

end TernaryPeriodPolynomials.Argument.BadPlaneInjectivity
