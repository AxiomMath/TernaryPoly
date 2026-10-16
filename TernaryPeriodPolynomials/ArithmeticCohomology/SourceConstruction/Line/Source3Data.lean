module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerData

@[expose] public section


/-!
# The level-three line source cocycle: definitions

The bad-line analogue of `LineSourceData`.  The spherical finite line vector is replaced by the
identity-cell finite part `badLineVector` of `BadLineFinite`, and the Levi data is
`LineLeviCocycleData3` (lift values only fixed by the bad-line Levi level).

On the identity cell `P_line(𝔸_f) · K₁` the finite part of an adele is `c • π(b) v` for a scalar
`cFin3` and a `GL₂(𝔸_f)` translation `bFin3` (the finite line factor and the block of a chosen
parabolic factor), and it vanishes off the cell.  The level-three line source is then given by the
same formula as `lineSource` with `cFLine, bFLine` replaced by `cFLine3, bFLine3`:

`lineSource3 y g = ρ(g_∞)⁻¹ ((l(g_∞ y₂) - l(g_∞ y₁)) (c_f (α(A(g_∞ y₁)) - α(A(g_∞ y₀))) (b_f)))`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

section Defs

variable {n : ℕ}

open Classical in
/-- The finite scalar factor on the identity cell (`0` off the cell). -/
def cFin3 (D : InducingData n) (f : FiniteGL) : ℂ :=
  if h : InBadCell f then
    finiteLineFactor D.chi 2 (lineBeta n) (Classical.choose h) (inBadCell_choose_mem h)
  else 0

open Classical in
/-- The finite `GL₂` translation on the identity cell (`1` off the cell). -/
def bFin3 (f : FiniteGL) : BinaryAdelicGL :=
  if h : InBadCell f then
    atFinite (lineBlockGL (Classical.choose h) (inBadCell_choose_mem h))
  else 1

theorem cFin3_of_cell (D : InducingData n) {f : FiniteGL} (h : InBadCell f) :
    cFin3 D f =
      finiteLineFactor D.chi 2 (lineBeta n) (Classical.choose h) (inBadCell_choose_mem h) := by
  unfold cFin3
  exact dite_eq_left h

theorem cFin3_of_not_cell (D : InducingData n) {f : FiniteGL} (h : ¬ InBadCell f) :
    cFin3 D f = 0 := by
  unfold cFin3
  exact dite_eq_right h

theorem bFin3_of_cell {f : FiniteGL} (h : InBadCell f) :
    bFin3 f = atFinite (lineBlockGL (Classical.choose h) (inBadCell_choose_mem h)) := by
  unfold bFin3
  exact dite_eq_left h

theorem bFin3_of_not_cell {f : FiniteGL} (h : ¬ InBadCell f) : bFin3 f = 1 := by
  unfold bFin3
  exact dite_eq_right h

/-- The finite scalar factor attached to an adelic matrix. -/
def cFLine3 (D : InducingData n) (g : AdelicGL) : ℂ := cFin3 D (finiteGroup g)

/-- The finite `GL₂` translation attached to an adelic matrix. -/
def bFLine3 (g : AdelicGL) : BinaryAdelicGL := bFin3 (finiteGroup g)

/-- **The level-three line source cochain**, at the `GL₂` adele `x`. -/
def lineSourceAt3 (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (x : BinaryAdelicGL) : HomogeneousPoly n :=
  realCoefficientComponent n D.chi (realGroup g)⁻¹
    ((lineRadical n D.chi (iwPLine (realGroup g * y 2)) -
        lineRadical n D.chi (iwPLine (realGroup g * y 1)))
      (cFLine3 D g • (E.α (iwALine (realGroup g * y 1)) (x * bFLine3 g) -
        E.α (iwALine (realGroup g * y 0)) (x * bFLine3 g))))

/-- **The level-three line source cocycle** (bad-line cell finite part). -/
def lineSource3 (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : HomogeneousPoly n :=
  lineSourceAt3 D E y g 1

end Defs

end TernaryPeriodPolynomials.SourceConstruction

end
