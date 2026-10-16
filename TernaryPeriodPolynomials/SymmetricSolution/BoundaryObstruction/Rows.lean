module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Normalization.Normalization
public import TernaryPeriodPolynomials.Building.BoundaryApartments.PathIndependence

@[expose] public section


/-!
# Lemma 4.1 (i) for the class `a_F`, independently of the cocycle

Formalized by Claude Sonnet 5.5.  And the proof at.

`Definitions/ManuscriptPolynomial.PureMixedBadLine c` is a property of one cocycle: its pure radical part `c(1,u,uu')` and its pure Levi part `c(1,l,ll')` vanish, which (for the split extension
`1 → U → P_L → L' → 1`, `U` the integral radical, `L'` the integral block-diagonal Levi) says that `c` is a representative with only the mixed Hochschild-Serre term.
`PureMixedClass a` states this for a *class*: some representative of `a` has vanishing pure radical and pure Levi parts.

* `lemma41_i_class`: for a polynomial functional `F`, every path family `τ` (the choice defining the cocycle `z_F`) and every cocycle `c` realizing `τ`, the class `a_F = [c]` is pure-mixed:
  there is a cohomologous cocycle with `PureMixedBadLine`.  So the property belongs to the class `a_F` (which is itself independent of `τ`: `pathCocycle_class_independent`), not to the chosen cocycle.
* `lemma41_i_independent`: any two realizing cocycles have the same class, which is pure-mixed.

The proof normalizes the paths (`τ(l) = s - l s` on the Levi, `τ(u) = 0` on the radical; `Paths.normalizedPaths`), observes that the normalized family is again a path family, and uses path independence of the class.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
open TernaryPeriodPolynomials.PolynomialBadLineNormalization

/-- **A class of `H²(K†, E_n)` is pure-mixed at the bad line** if some representative cocycle has vanishing pure radical and pure Levi parts. -/
def PureMixedClass {n : ℕ}
    (a : H2 rationalLevel (rationalCoefficientComponent n trivialCharacter)) : Prop :=
  ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
    classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c = a ∧ PureMixedBadLine c

theorem pureMixedClass_iff {n : ℕ} (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    PureMixedClass (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) ↔
      ∃ c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c' =
          classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c ∧ PureMixedBadLine c' :=
  Iff.rfl

/-- **Lemma 4.1 (i), class level**: the restriction of `a_F` to the bad-line stabilizer has only the mixed Hochschild-Serre component, for every choice of paths and every
cocycle realizing them. -/
theorem lemma41_i_class {n : ℕ} {f : HomogeneousPoly n} {F : EdgeChains →ₗ[ℂ] HomogeneousPoly n}
    (hF : IsPolynomialFunctional f F) {τ : rationalLevel → EdgeChains} (hτ : IsPathFamily τ)
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hc : RealizesPathClass F τ c) :
    PureMixedClass (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) := by
  have hτ' : IsPathFamily (Paths.normalizedPaths τ) := Paths.normalizedPaths_isPathFamily τ hτ
  refine ⟨pathCocycle hF hτ', ?_, Normalization.normalized_pure (pathCocycle_realizes hF hτ')⟩
  exact realizesPathClass_class_independent hF hτ' hτ (pathCocycle_realizes hF hτ') hc

/-- Any two realizing cocycles define the same class, and that class is pure-mixed. -/
theorem lemma41_i_independent {n : ℕ} {f : HomogeneousPoly n} {F : EdgeChains →ₗ[ℂ] HomogeneousPoly n}
    (hF : IsPolynomialFunctional f F) {τ₁ τ₂ : rationalLevel → EdgeChains}
    (h₁ : IsPathFamily τ₁) (h₂ : IsPathFamily τ₂)
    {c₁ c₂ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hc₁ : RealizesPathClass F τ₁ c₁) (hc₂ : RealizesPathClass F τ₂ c₂) :
    classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c₁ =
        classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c₂ ∧
      PureMixedClass (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c₁) :=
  ⟨realizesPathClass_class_independent hF h₁ h₂ hc₁ hc₂, lemma41_i_class hF h₁ hc₁⟩

end TernaryPeriodPolynomials.Argument.Identities
