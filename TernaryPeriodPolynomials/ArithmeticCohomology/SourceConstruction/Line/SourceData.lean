module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceHelpers
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.RadicalAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceSmooth

@[expose] public section


/-!
# The line source cocycle: definitions

From a sign-twisted analytic Levi cocycle `α` of the cuspidal representation (a cocycle for the
`sgn(det)`-twisted binary action, with smooth, spherical, scalar-analytic components, vanishing on the
orthogonal group), the real analytic Iwasawa decomposition, the radical cocycle of the real line
parabolic and the spherical finite line vector, the cochain

`lineSource y g = ρ(g_∞)⁻¹ ((l(g_∞ y₂) - l(g_∞ y₁)) (c_f (α(A(g_∞ y₁)) - α(A(g_∞ y₀))) (b_f)))`

is assembled, where `A` is the lower right block of the real Iwasawa factor and `l` is `lineRadical`
of the real Iwasawa factor.  The sign twist is forced by the line induction law: the standard
action `lineStar` carries the *signed* determinant `det A_p`, while the induction law has the modulus.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The abstract sign-twisted analytic Levi cocycle of a cuspidal representation: a cocycle for the
`sgn(det)`-twisted cohomological action of `GL₂(ℝ)`, vanishing on the orthogonal group, whose
coefficients are realizations of smooth spherical vectors depending analytically on the real
argument. -/
structure LineLeviCocycleData (σ : CuspidalRepresentation) (n : ℕ) where
  α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)
  cocycle : ∀ g h x,
    α (g * h) x = α g x + lineSgn g • binaryCohomologicalAction n g (α h) x
  orth : ∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, α k x = 0
  lift : (Fin 2 →₀ ℕ) → BinaryRealGL → σ.smooth
  lift_realize : ∀ μ g A, σ.realize (lift μ g) A = (α g A).val.coeff μ
  lift_smooth : ∀ μ, Smooth (fun x : Fin 1 → BinaryRealGL => (lift μ (x 0)).val)
  scalar_smooth : ∀ μ A, Smooth (fun x : Fin 1 → BinaryRealGL => (α (x 0) A).val.coeff μ)
  spherical : ∀ μ g, (lift μ g).val ∈ sphericalSubspace σ

section Defs

variable {n : ℕ}

/-- The parabolic Iwasawa factor `b(y)` as an element of the real line parabolic. -/
def iwPLine (y : RealGL3) : lineParabolic ℝ := ⟨iwasawaB y, iwasawaB_mem_lineParabolic y⟩

/-- The `GL₂` block of the Iwasawa factor in the line parabolic. -/
def iwALine (y : RealGL3) : BinaryRealGL := lineLeviBlock (iwPLine y)

theorem iwALine_val (y : RealGL3) (i j : Fin 2) :
    (iwALine y).val i j = (iwasawaB y).val i.succ j.succ := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The finite scalar factor attached to a finite adele matrix. -/
def cFinLine (D : InducingData n) (f : FiniteGL) : ℂ :=
  finiteLineFactor D.chi 2 (lineBeta n) (finiteLineParabolic f) (finiteLineParabolic_mem f)

/-- The finite `GL₂` translation attached to a finite adele matrix. -/
def bFinLine (f : FiniteGL) : BinaryAdelicGL :=
  atFinite (lineBlockGL (finiteLineParabolic f) (finiteLineParabolic_mem f))

/-- The finite scalar factor attached to an adelic matrix. -/
def cFLine (D : InducingData n) (g : AdelicGL) : ℂ := cFinLine D (finiteGroup g)

/-- The finite `GL₂` translation attached to an adelic matrix. -/
def bFLine (g : AdelicGL) : BinaryAdelicGL := bFinLine (finiteGroup g)

/-- **The line source cochain**, at the `GL₂` adele `x`. -/
def lineSourceAt (D : InducingData n) (E : LineLeviCocycleData D.cusp n) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (x : BinaryAdelicGL) : HomogeneousPoly n :=
  realCoefficientComponent n D.chi (realGroup g)⁻¹
    ((lineRadical n D.chi (iwPLine (realGroup g * y 2)) -
        lineRadical n D.chi (iwPLine (realGroup g * y 1)))
      (cFLine D g • (E.α (iwALine (realGroup g * y 1)) (x * bFLine g) -
        E.α (iwALine (realGroup g * y 0)) (x * bFLine g))))

/-- **The line source cocycle.** -/
def lineSource (D : InducingData n) (E : LineLeviCocycleData D.cusp n) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : HomogeneousPoly n :=
  lineSourceAt D E y g 1

end Defs

/-- Coefficientwise real analyticity of the line radical along the Iwasawa parabolic factor. -/
def RadicalAnalyticLine (n : ℕ) (χ : RankOneCharacter) : Prop :=
  ∀ (Q : Binary.HomogeneousPoly (n + 1)) (μ : Fin 3 →₀ ℕ),
    Smooth (fun x : Fin 1 → RealGL3 => (lineRadical n χ (iwPLine (x 0)) Q).val.coeff μ)

end TernaryPeriodPolynomials.SourceConstruction

end
