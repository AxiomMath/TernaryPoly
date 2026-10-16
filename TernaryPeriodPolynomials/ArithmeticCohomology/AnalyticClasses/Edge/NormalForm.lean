module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.Normal
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.DerivativeEdge

@[expose] public section


/-!
# The twisted Eichler normal form and its good-line transport

The pointwise Eichler normal form `N⁺ = ½ (Per + J Per)` splits into a holomorphic part
`N_hol(A) = ½ Per(A·i)` and an antiholomorphic part `N_anti(A) = ½ J · Per(refl(A·i))`. The
derivative edge of the good-line transfer of `N⁺` is a cocycle for the action twisted by the
determinant, and it is a multiple of the transport of the **twisted** normal form
`N⁻ = N_hol - N_anti` along the pivot conjugation and the swap of the two binary variables:
`edgeNormal F m = Sw (N⁻ (σ m σ))`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The holomorphic half `½ Per(A · i)` of the Eichler normal form. -/
def eichlerHolomorphic (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL)
    (h : BinaryAdelicGL) : Binary.HomogeneousPoly (n + 1) :=
  (2 : ℂ)⁻¹ • eichlerPeriod n F (basePoint A) h

/-- The antiholomorphic half `½ J · Per(refl(A · i))` of the Eichler normal form. -/
def eichlerAntiholomorphic (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL)
    (h : BinaryAdelicGL) : Binary.HomogeneousPoly (n + 1) :=
  (2 : ℂ)⁻¹ • binaryAmbientRepresentation n UpperHalfPlane.J
    (eichlerPeriod n F (binaryComplexReflection (basePoint A))) h

theorem eichlerNormal_eq_add (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL)
    (h : BinaryAdelicGL) :
    eichlerNormal n F A h = eichlerHolomorphic n F A h + eichlerAntiholomorphic n F A h := by
  rw [eichlerNormal_def, eichlerHolomorphic, eichlerAntiholomorphic, smul_add]

/-- **The twisted Eichler normal form** `N⁻ = N_hol - N_anti`. -/
def eichlerTwisted (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL)
    (h : BinaryAdelicGL) : Binary.HomogeneousPoly (n + 1) :=
  eichlerHolomorphic n F A h - eichlerAntiholomorphic n F A h

/-- The swap `X₀ ↔ X₁` of the two binary variables. -/
def binarySwap (n : ℕ) : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) where
  toFun P := ⟨MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P.val,
    (P.property.rename_isHomogeneous)⟩
  map_add' P Q := Subtype.ext (map_add _ _ _)
  map_smul' c P := Subtype.ext (by simp [MvPolynomial.smul_eq_C_mul])

/-- **The good-line transport of the twisted normal form.** -/
def edgeNormal (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (m : unimodularLevi) :
    BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  fun h => binarySwap n (eichlerTwisted n F (pivotConjugate (m : BinaryRealGL)) h)

end TernaryPeriodPolynomials.AnalyticClasses
