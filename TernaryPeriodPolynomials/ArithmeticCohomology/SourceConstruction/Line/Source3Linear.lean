module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Identity

@[expose] public section


/-!
# Linearity of the level-three line source in the Levi cocycle

`lineSource3 D E` depends on the Levi datum `E` only through `E.α`, and it is linear in it: the
finite factors `cFLine3, bFLine3` do not involve `E`, and the radical and the real action are
linear.  So if `E.α` is the sum (a scalar multiple) of `E₁.α` and `E₂.α` (of `E₁.α`), the sources add
(scale).  This allows the source of a linear combination of Levi cocycles to be computed from the
sources of the summands.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

section Linear3

variable {n : ℕ}

/-- `lineSource3` depends on the Levi datum only through `α`. -/
theorem lineSourceAt3_congr (D : InducingData n) (E E' : LineLeviCocycleData3 D.cusp n)
    (hα : ∀ h x, E.α h x = E'.α h x) (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) :
    lineSourceAt3 D E y g x = lineSourceAt3 D E' y g x := by
  unfold lineSourceAt3
  simp only [hα]

theorem lineSource3_congr (D : InducingData n) (E E' : LineLeviCocycleData3 D.cusp n)
    (hα : ∀ h x, E.α h x = E'.α h x) : lineSource3 D E = lineSource3 D E' := by
  funext y g
  exact lineSourceAt3_congr D E E' hα y g 1

/-- **Additivity** of the level-three line source at the `GL₂` adele `x`. -/
theorem lineSourceAt3_add (D : InducingData n) (E E₁ E₂ : LineLeviCocycleData3 D.cusp n)
    (hα : ∀ h x, E.α h x = E₁.α h x + E₂.α h x) (y : Fin 3 → RealGL3) (g : AdelicGL)
    (x : BinaryAdelicGL) :
    lineSourceAt3 D E y g x = lineSourceAt3 D E₁ y g x + lineSourceAt3 D E₂ y g x := by
  unfold lineSourceAt3
  simp only [hα, add_sub_add_comm, smul_add, map_add]

/-- **Additivity**: if `E.α = E₁.α + E₂.α` pointwise then
`lineSource3 D E = lineSource3 D E₁ + lineSource3 D E₂`. -/
theorem lineSource3_add (D : InducingData n) (E E₁ E₂ : LineLeviCocycleData3 D.cusp n)
    (hα : ∀ h x, E.α h x = E₁.α h x + E₂.α h x) :
    lineSource3 D E = lineSource3 D E₁ + lineSource3 D E₂ := by
  funext y g
  exact lineSourceAt3_add D E E₁ E₂ hα y g 1

/-- **Homogeneity** of the level-three line source at the `GL₂` adele `x`. -/
theorem lineSourceAt3_smul (D : InducingData n) (E E₁ : LineLeviCocycleData3 D.cusp n) (c : ℂ)
    (hα : ∀ h x, E.α h x = c • E₁.α h x) (y : Fin 3 → RealGL3) (g : AdelicGL)
    (x : BinaryAdelicGL) :
    lineSourceAt3 D E y g x = c • lineSourceAt3 D E₁ y g x := by
  unfold lineSourceAt3
  simp only [hα]
  erw [← smul_sub]
  simp only [map_smul]
  exact smul_comm (cFLine3 D g) c _

/-- **Homogeneity**: if `E.α = c • E₁.α` pointwise then `lineSource3 D E = c • lineSource3 D E₁`. -/
theorem lineSource3_smul (D : InducingData n) (E E₁ : LineLeviCocycleData3 D.cusp n) (c : ℂ)
    (hα : ∀ h x, E.α h x = c • E₁.α h x) : lineSource3 D E = c • lineSource3 D E₁ := by
  funext y g
  exact lineSourceAt3_smul D E E₁ c hα y g 1

end Linear3

end TernaryPeriodPolynomials.SourceConstruction

end
