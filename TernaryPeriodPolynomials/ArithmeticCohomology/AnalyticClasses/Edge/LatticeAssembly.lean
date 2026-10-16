module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.LatticeComparisonLattice
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineMixedCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LowerRadicalEdgeFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RelativeTwoCocycleNormalization

@[expose] public section


/-!
# Mixed coordinates of coboundaries on the arithmetic good-line stabilizer

Let `β` be a one-cochain of the arithmetic good-line stabilizer `Γ_L = N(ℤ) ⋊ GL₂(ℤ)` whose
coboundary agrees on radical pairs with the coboundary of a function `ψ` on the radical lattice.
Then `κ = β|_N - ψ` is a lattice cocycle. The mixed coordinate of `δβ` at `γ` is the coordinate of
`γ ⋆ κ - κ` plus the coordinate of the Levi difference of `ψ`. Hence, if the mixed coordinate of
`δβ` is the coordinate of a family of lattice cocycles `G γ` plus the Levi difference of `ψ`, then
`γ ↦ coord (G γ)` is a one-coboundary of `GL₂(ℤ)` acting on `Sym^{n+1}` without twist.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- Radical and Levi elements of the arithmetic good-line stabilizer commute up to the Levi
input. -/
theorem goodLineLeviSection_mul_radical (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    goodLineLeviSection γ * goodLineRadicalInclusion (lowerLeviLatticeInput γ r) =
      goodLineRadicalInclusion r * goodLineLeviSection γ := by
  apply Subtype.ext
  exact (lowerLeviLatticeInput_conjugation γ r).symm

variable (n) in
/-- The lower radical coordinate of the inverse exponential averages of the values of a function
on the radical lattice at the two lattice generators. -/
def latticeCoordinate :
    (RadicalLattice → HomogeneousPoly n) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (lowerRadicalCoordinate n).comp (LinearMap.pi fun i =>
    (lowerRadicalAverageEquiv n i).symm.toLinearMap.comp
      (LinearMap.proj (R := ℂ) (φ := fun _ => HomogeneousPoly n) (radicalLatticeGenerator i)))

/-- The coordinate of a lattice cocycle is the lattice coordinate of its values. -/
theorem lowerRadicalCocycleCoordinate_eq_latticeCoordinate
    (κ : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n)) :
    lowerRadicalCocycleCoordinate n κ =
      latticeCoordinate n (fun r => goodLineCoefficientPolynomial n (κ r)) := rfl

/-- The lattice cocycle `r ↦ β (r) - ψ (r)`. -/
def latticeDifferenceCocycle
    (β : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →
      goodLineCoefficientRep n) (ψ : RadicalLattice → goodLineCoefficientRep n)
    (radical : ∀ r₁ r₂, twoBoundaryCycle (goodLineCoefficientRep n) β
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) =
        (goodLineCoefficientRep n).ρ (goodLineRadicalInclusion r₁) (ψ r₂) - ψ (r₁ * r₂) + ψ r₁) :
    groupCohomology.cocycles₁ (lowerRadicalLatticeRep n) :=
  ⟨fun r => goodLineCoefficientPolynomial n (β (goodLineRadicalInclusion r) - ψ r), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro r₁ r₂
    have relation := radical r₁ r₂
    rw [twoBoundaryCycle_apply, ← map_mul] at relation
    change β (goodLineRadicalInclusion (r₁ * r₂)) - ψ (r₁ * r₂) =
      (goodLineCoefficientRep n).ρ (goodLineRadicalInclusion r₁)
          (β (goodLineRadicalInclusion r₂) - ψ r₂) +
        (β (goodLineRadicalInclusion r₁) - ψ r₁)
    rw [map_sub]
    linear_combination (norm := abel) -relation⟩

/-- The Levi difference of a function on the radical lattice at `γ`, in lower coordinates. -/
def leviDifferenceCoordinate (ψ : RadicalLattice → goodLineCoefficientRep n)
    (γ : GeneralLinearGroup (Fin 2) ℤ) : Binary.HomogeneousPoly (n + 1) :=
  latticeCoordinate n fun r => goodLineCoefficientPolynomial n
    ((goodLineCoefficientRep n).ρ (goodLineLeviSection γ) (ψ (lowerLeviLatticeInput γ r)) - ψ r)

/-- The mixed coordinate of a two-cochain at `γ` is the lattice coordinate of its mixed
differences. -/
theorem goodLineMixedCoordinate_eq_latticeCoordinate (γ : GeneralLinearGroup (Fin 2) ℤ)
    (cochain : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) ×
      flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →
        goodLineCoefficientRep n) :
    goodLineMixedCoordinate n γ cochain = latticeCoordinate n fun r =>
      goodLineCoefficientPolynomial n
        (cochain (goodLineLeviSection γ, goodLineRadicalInclusion (lowerLeviLatticeInput γ r)) -
          cochain (goodLineRadicalInclusion r, goodLineLeviSection γ)) := rfl

/-- The mixed coordinate of a coboundary is the Levi difference of the restriction of the
primitive to the radical lattice. -/
theorem goodLineMixedCoordinate_twoBoundary
    (β : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →
      goodLineCoefficientRep n) (γ : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedCoordinate n γ (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) β pair) =
      leviDifferenceCoordinate (fun r => β (goodLineRadicalInclusion r)) γ := by
  set w : HomogeneousPoly n := goodLineCoefficientPolynomial n (β (goodLineLeviSection γ))
  have killed : latticeCoordinate n (fun r =>
      w - rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice r) w) = 0 :=
    lowerRadicalCoordinate_lattice_coboundary w
  have pointwise : (fun r => goodLineCoefficientPolynomial n
      (twoBoundaryCycle (goodLineCoefficientRep n) β
          (goodLineLeviSection γ, goodLineRadicalInclusion (lowerLeviLatticeInput γ r)) -
        twoBoundaryCycle (goodLineCoefficientRep n) β
          (goodLineRadicalInclusion r, goodLineLeviSection γ))) =
      (fun r => goodLineCoefficientPolynomial n
        ((goodLineCoefficientRep n).ρ (goodLineLeviSection γ)
            (β (goodLineRadicalInclusion (lowerLeviLatticeInput γ r))) -
          β (goodLineRadicalInclusion r))) +
      (fun r =>
        w - rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice r) w) := by
    funext r
    rw [twoBoundaryCycle_apply, twoBoundaryCycle_apply, goodLineLeviSection_mul_radical]
    change _ = goodLineCoefficientPolynomial n _ + (goodLineCoefficientPolynomial n
      (β (goodLineLeviSection γ)) - goodLineCoefficientPolynomial n
        ((goodLineCoefficientRep n).ρ (goodLineRadicalInclusion r) (β (goodLineLeviSection γ))))
    simp only [map_sub, map_add]
    abel
  rw [goodLineMixedCoordinate_eq_latticeCoordinate, pointwise, map_add, killed, add_zero]
  rfl

/-- **The lattice edge of a comparison is a coboundary.** If the coboundary of `β` agrees with the
coboundary of `ψ` on radical pairs, and the mixed coordinate of `δβ` is the coordinate of the
lattice cocycles `G γ` plus the Levi difference of `ψ`, then `γ ↦ coord (G γ)` is a one-coboundary
for the untwisted action of `GL₂(ℤ)` on `Sym^{n+1}`. -/
theorem latticeEdge_coboundary (_positive : 0 < n)
    (β : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →
      goodLineCoefficientRep n) (ψ : RadicalLattice → goodLineCoefficientRep n)
    (G : GeneralLinearGroup (Fin 2) ℤ → groupCohomology.cocycles₁ (lowerRadicalLatticeRep n))
    (radical : ∀ r₁ r₂, twoBoundaryCycle (goodLineCoefficientRep n) β
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) =
        (goodLineCoefficientRep n).ρ (goodLineRadicalInclusion r₁) (ψ r₂) - ψ (r₁ * r₂) + ψ r₁)
    (mixed : ∀ γ, goodLineMixedCoordinate n γ
      (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) β pair) =
        lowerRadicalCocycleCoordinate n (G γ) + leviDifferenceCoordinate ψ γ) :
    ∃ Q : Binary.HomogeneousPoly (n + 1), ∀ γ, lowerRadicalCocycleCoordinate n (G γ) =
      Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) Q - Q := by
  set κ := latticeDifferenceCocycle β ψ radical
  refine ⟨lowerRadicalCocycleCoordinate n κ, fun γ => ?_⟩
  have value := mixed γ
  rw [goodLineMixedCoordinate_twoBoundary] at value
  have levi : leviDifferenceCoordinate (fun r => β (goodLineRadicalInclusion r)) γ =
      leviDifferenceCoordinate ψ γ + (lowerRadicalCocycleCoordinate n
        (lowerRadicalCocycleLevi n γ κ) - lowerRadicalCocycleCoordinate n κ) := by
    rw [lowerRadicalCocycleCoordinate_eq_latticeCoordinate,
      lowerRadicalCocycleCoordinate_eq_latticeCoordinate, leviDifferenceCoordinate,
      leviDifferenceCoordinate, ← map_sub, ← map_add]
    congr 1
    funext r
    change _ = goodLineCoefficientPolynomial n _ + (goodLineCoefficientPolynomial n
      ((goodLineCoefficientRep n).ρ (goodLineLeviSection γ)
        (β (goodLineRadicalInclusion (lowerLeviLatticeInput γ r)) -
          ψ (lowerLeviLatticeInput γ r))) -
      goodLineCoefficientPolynomial n (β (goodLineRadicalInclusion r) - ψ r))
    simp only [map_sub]
    abel
  rw [levi, lowerRadicalCocycleCoordinate_equivariant] at value
  linear_combination (norm := abel) -value

end TernaryPeriodPolynomials.AnalyticClasses
