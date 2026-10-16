module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Test.Dual
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.SupportSub

@[expose] public section


/-! Intrinsic local test spaces consisting of the actual compact forms supported over a quotient set. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpaceCovering SmoothCoveringDeRham

/-- Actual global compact quotient forms whose genuine closed quotient support lies in U. -/
def supportedCompactCore (n k : ℕ) (U : Set OrbitSpace) : Submodule ℝ (Core n k) where
  carrier := {w | quotientSupport w.val ⊆ U}
  zero_mem' := by simp
  add_mem' hw hz := (quotientSupport_add _ _).trans (union_subset hw hz)
  smul_mem' c _ hw := (quotientSupport_smul c _).trans hw

/-- Actual inclusion of smaller-support test spaces. -/
def supportedCompactInclusion (n k : ℕ) {U V : Set OrbitSpace} (hVU : V ⊆ U) :
    supportedCompactCore n k V →ₗ[ℝ] supportedCompactCore n k U :=
  Submodule.inclusion (fun _ hw => hw.trans hVU)

/-- A local current is a genuine algebraic functional on the actual supported compact quotient tests. -/
abbrev IntrinsicCurrent (n k : ℕ) (U : Set OrbitSpace) :=
  Module.Dual ℝ (supportedCompactCore n k U)

/-- Restriction of actual local currents is transposed inclusion of actual supported tests. -/
def intrinsicCurrentRestriction (n k : ℕ) {U V : Set OrbitSpace} (hVU : V ⊆ U) :
    IntrinsicCurrent n k U →ₗ[ℝ] IntrinsicCurrent n k V :=
  (supportedCompactInclusion n k hVU).dualMap

/-- The actual Hilbert current on an actual quotient set pairs against its actual supported tests. -/
def intrinsicHilbertCurrent (n k : ℕ) (U : Set OrbitSpace) :
    Hilbert n k →ₗ[ℝ] IntrinsicCurrent n k U :=
  ((supportedCompactCore n k U).subtype.dualMap).comp (hilbertTest n k)

/-- Intrinsic restriction preserves identity. -/
theorem intrinsicCurrentRestriction_refl (n k : ℕ) (U : Set OrbitSpace)
    (T : IntrinsicCurrent n k U) : intrinsicCurrentRestriction n k (Subset.rfl : U ⊆ U) T = T := rfl

/-- Intrinsic restriction composes exactly, independently of all coordinate charts. -/
theorem intrinsicCurrentRestriction_trans (n k : ℕ) {U V W : Set OrbitSpace}
    (hVU : V ⊆ U) (hWV : W ⊆ V) (T : IntrinsicCurrent n k U) :
    intrinsicCurrentRestriction n k hWV (intrinsicCurrentRestriction n k hVU T) =
      intrinsicCurrentRestriction n k (hWV.trans hVU) T := rfl

/-- The actual Hilbert current restricts intrinsically. -/
theorem intrinsicHilbertCurrent_restriction (n k : ℕ) {U V : Set OrbitSpace}
    (hVU : V ⊆ U) (u : Hilbert n k) :
    intrinsicCurrentRestriction n k hVU (intrinsicHilbertCurrent n k U u) =
      intrinsicHilbertCurrent n k V u := rfl

end TernaryPoly.PolynomialFormWeakSmooth
