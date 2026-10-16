module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RadicalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.FiniteSphericalPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RealIwasawa
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.AdelicSplit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceSmooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceExpand

@[expose] public section


/-!
# The plane source cocycle: definitions

From an `O(2)`-normalized analytic Levi cocycle `α` of the cuspidal representation (a
`GL₂(ℝ)`-cocycle with smooth, spherical, scalar-analytic components, vanishing on the orthogonal
group), the real analytic Iwasawa decomposition, the radical cocycle of the real plane parabolic
and the spherical finite plane vector, the cochain

`planeSource y g = ρ(g_∞)⁻¹ ((l(g_∞ y₂) - l(g_∞ y₁)) (c_f (α(A(g_∞ y₁)) - α(A(g_∞ y₀))) (b_f)))`

is assembled, where `A = leviBlock ∘ iwasawaB` and `l = planeRadical ∘ iwasawaB`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The abstract `O(2)`-normalized analytic Levi cocycle of a cuspidal representation: a
`GL₂(ℝ)`-cocycle with values in binary forms, vanishing on the orthogonal group, whose coefficients
are realizations of smooth spherical vectors depending analytically on the real argument. -/
structure LeviCocycleData (σ : CuspidalRepresentation) (n : ℕ) where
  α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)
  cocycle : ∀ g h x, α (g * h) x = α g x + binaryCohomologicalAction n g (α h) x
  orth : ∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, α k x = 0
  lift : (Fin 2 →₀ ℕ) → BinaryRealGL → σ.smooth
  lift_realize : ∀ μ g A, σ.realize (lift μ g) A = (α g A).val.coeff μ
  lift_smooth : ∀ μ, Smooth (fun x : Fin 1 → BinaryRealGL => (lift μ (x 0)).val)
  scalar_smooth : ∀ μ A, Smooth (fun x : Fin 1 → BinaryRealGL => (α (x 0) A).val.coeff μ)
  spherical : ∀ μ g, (lift μ g).val ∈ sphericalSubspace σ

section Defs

variable {n : ℕ}

theorem iwasawaB_mem_plane (y : RealGL3) : iwasawaB y ∈ planeParabolic ℝ :=
  ⟨(iwasawaB_upper y).2.1, (iwasawaB_upper y).2.2.1⟩

/-- The parabolic Iwasawa factor `b(y)` as an element of the real plane parabolic. -/
def iwP (y : RealGL3) : planeParabolic ℝ := ⟨iwasawaB y, iwasawaB_mem_plane y⟩

/-- The `GL₂` block of the Iwasawa factor. -/
def iwA (y : RealGL3) : BinaryRealGL := leviBlock (iwP y)

theorem iwA_val (y : RealGL3) (i j : Fin 2) :
    (iwA y).val i j = (iwasawaB y).val i.castSucc j.castSucc := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The finite scalar factor attached to a finite adele matrix. -/
def cFin (D : InducingData n) (f : FiniteGL) : ℂ :=
  finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) (finitePlaneParabolic f) (finitePlaneParabolic_mem f)

/-- The finite `GL₂` translation attached to a finite adele matrix. -/
def bFin (f : FiniteGL) : BinaryAdelicGL :=
  atFinite (planeBlockGL (finitePlaneParabolic f) (finitePlaneParabolic_mem f))

/-- The finite scalar factor attached to an adelic matrix. -/
def cF (D : InducingData n) (g : AdelicGL) : ℂ := cFin D (finiteGroup g)

/-- The finite `GL₂` translation attached to an adelic matrix. -/
def bF (g : AdelicGL) : BinaryAdelicGL := bFin (finiteGroup g)

/-- **The plane source cochain**, at the `GL₂` adele `x`. -/
def planeSourceAt (D : InducingData n) (E : LeviCocycleData D.cusp n) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (x : BinaryAdelicGL) : HomogeneousPoly n :=
  realCoefficientComponent n D.chi (realGroup g)⁻¹
    ((planeRadical n D.chi (iwP (realGroup g * y 2)) - planeRadical n D.chi (iwP (realGroup g * y 1)))
      (cF D g • (E.α (iwA (realGroup g * y 1)) (x * bF g) -
        E.α (iwA (realGroup g * y 0)) (x * bF g))))

/-- **The plane source cocycle.** -/
def planeSource (D : InducingData n) (E : LeviCocycleData D.cusp n) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : HomogeneousPoly n :=
  planeSourceAt D E y g 1

end Defs

/-! ## The analytic inputs on the radical and the coefficient representation -/

/-- Coefficientwise real analyticity of the plane radical along the Iwasawa parabolic factor
(the radical is defined by exact division by `x₂`; this is the explicit-coefficient statement). -/
def RadicalAnalytic (n : ℕ) (χ : RankOneCharacter) : Prop :=
  ∀ (Q : Binary.HomogeneousPoly (n + 1)) (μ : Fin 3 →₀ ℕ),
    Smooth (fun x : Fin 1 → RealGL3 => (planeRadical n χ (iwP (x 0)) Q).val.coeff μ)

/-- Coefficientwise real analyticity of the matrix coefficients of the (full-polynomial) coefficient
representation, in the inverse of the group element. -/
def CoefficientAnalytic (χ : RankOneCharacter) : Prop :=
  ∀ κ μ : Fin 3 →₀ ℕ, Smooth (fun x : Fin 1 → RealGL3 =>
    (fullCoefficientComponent χ (x 0)⁻¹ (MvPolynomial.monomial κ (1 : ℂ))).coeff μ)

end TernaryPeriodPolynomials.SourceConstruction
