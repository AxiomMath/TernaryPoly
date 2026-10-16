module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspSeparation
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Trace
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Matrices
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel

@[expose] public section


/-!
# The cusp data of the boundary trace of the level

The boundary trace `traceDataL2` has two representative lines, `L₀ = ⟨e₁⟩` and `L₁ = ⟨e₃⟩`. The
line `L₁` contains the vector `e₃`, which is not annihilated by `e₃*`, so it is a good line, while
`L₀` is the bad line cusp. Together they meet both orbits of lines of the arithmetic level.

The dual plane of a line `g L` is `dualInvolution g · longWeyl` applied to the base plane.

* For `L₀` it is `longWeyl · ⟨e₁, e₂⟩ = ⟨e₃, e₂⟩`, a plane containing `e₃`, hence a good plane.
* For `L₁ = g₂ L₀` the matrix `dualInvolution g₂ · longWeyl` has columns `(0, 1/3, 0)`, `(1, 0, 0)`,
  `(0, 0, 3)`, so its last row is `(0, 0, 3)` and it lies in the plane parabolic: the dual plane is
  the base plane `⟨e₁, e₂⟩`, the bad plane cusp.

Hence the dual planes of the two representative lines lie in the two different plane cusp orbits,
and the separation of the line cusps (`CuspSeparation.associateDuality_of_cuspDuality`) reduces
boundary duality on the associate pair to duality at each of the two line cusps separately.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (L₀ L₁ g₂ embedZ embedZ_val zg₂ zg₂_val zg₂_inv_val embedZ_apply)
open TernaryPeriodPolynomials.Spectral.CuspOrbits
  (cuspFlag cuspFlag_transporter)

/-- The plane cusp of the dual plane of each representative line: the first line has a good dual
plane, the second a bad one. -/
def good : Fin 2 → Bool := ![true, false]

/-- The first representative line of the boundary trace is the base line `L₀`. -/
theorem lineRep_zero : traceDataL2.lineRep 0 = L₀ := rfl

/-- The second representative line of the boundary trace is the line `L₁ = ⟨e₃⟩`. -/
theorem lineRep_one : traceDataL2.lineRep 1 = L₁ := rfl

/-! ### The dual planes of the representative lines -/

/-- The plane `⟨e₃, e₂⟩ = longWeyl ⟨e₁, e₂⟩` contains the integral vector `e₃`, so it is good. -/
theorem goodFlag_longWeyl : GoodFlag .plane (QuotientGroup.mk longWeyl : Flags .plane) := by
  refine ⟨![0, 0, 1], ⟨longWeyl, rfl, ![1, 0, 0], rfl, ?_⟩, by decide⟩
  funext i
  fin_cases i <;>
    simp [longWeyl, longWeylMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The line `L₁ = ⟨e₃⟩` contains the integral vector `e₃`, so it is good. -/
theorem goodFlag_L₁ : GoodFlag .line L₁ := by
  refine ⟨![0, 0, 1], ⟨g₂, rfl, ![1, 0, 0], ⟨rfl, rfl⟩, ?_⟩, by decide⟩
  funext i
  fin_cases i <;>
    simp [g₂, embedZ_apply, zg₂_val, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The dual plane of the base line `L₀` is the plane `longWeyl ⟨e₁, e₂⟩`. -/
theorem dualFlag_L₀ : dualFlag L₀ = (QuotientGroup.mk longWeyl : Flags .plane) := by
  have h : dualFlag L₀ = QuotientGroup.mk (dualInvolution 1 * longWeyl) :=
    dualFlag_mk (1 : RationalGL3)
  rw [map_one, one_mul] at h
  exact h

/-- The matrix of the inverse of the permutation `g₂`. -/
theorem g₂_inv_val : (g₂⁻¹).val = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
  have h : g₂⁻¹ = embedZ (zg₂⁻¹) := (map_inv embedZ zg₂).symm
  rw [h, embedZ_val, zg₂_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The matrix of the dual involution of the permutation `g₂`. -/
theorem dualInvolution_g₂_val :
    (dualInvolution g₂).val = !![0, 1, 0; 0, 0, 1 / 3; 3, 0, 0] := by
  ext i j
  rw [dualInvolution_val_apply, g₂_inv_val]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The matrix `dualInvolution g₂ · longWeyl` has last row `(0, 0, 3)`, so it lies in the plane
parabolic. -/
theorem dualInvolution_g₂_mul_longWeyl_mem :
    dualInvolution g₂ * longWeyl ∈ parabolic .plane := by
  refine ⟨?_, ?_⟩ <;> rw [Units.val_mul, dualInvolution_g₂_val] <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, longWeyl, longWeylMatrix]

/-- The dual plane of the line `L₁ = ⟨e₃⟩` is the base plane `⟨e₁, e₂⟩`. -/
theorem dualFlag_L₁ : dualFlag L₁ = (QuotientGroup.mk 1 : Flags .plane) := by
  have h : dualFlag L₁ = QuotientGroup.mk (dualInvolution g₂ * longWeyl) := dualFlag_mk g₂
  rw [h, QuotientGroup.eq, mul_one]
  exact inv_mem dualInvolution_g₂_mul_longWeyl_mem

/-! ### The cusp hypotheses of the separation of the line cusps -/

/-- **The dual planes of the representative lines lie in the plane cusp orbits `good v`.** -/
theorem hdual_L2 (n : ℕ) (χ : RankOneCharacter) :
    ∀ v : Fin 2, ∃ γ : rationalLevel,
      γ.val • cuspFlag .plane (good v) = (dualityData n χ).dualFlag (traceDataL2.lineRep v) := by
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := cuspFlag_transporter .plane true (dualFlag L₀)
      (iff_of_true (by rw [dualFlag_L₀]; exact goodFlag_longWeyl) rfl)
    exact ⟨γ, hγ⟩
  · refine ⟨1, ?_⟩
    change _ = dualFlag L₁
    rw [dualFlag_L₁]
    exact one_smul RationalGL3 _

/-- **The two plane cusp orbits of the dual planes are different.** -/
theorem hgood_L2 : ∀ u v : Fin 2, u ≠ v → good u = !good v := by
  decide

/-- **The representative lines meet every orbit of lines of the level**: a good line is a
translate of `L₁` and a bad line is a translate of `L₀`. -/
theorem hlines_L2 :
    ∀ F : Flags .line, ∃ v : Fin 2, ∃ γ : rationalLevel, γ.val • traceDataL2.lineRep v = F := by
  intro F
  by_cases hF : GoodFlag .line F
  · obtain ⟨γ₁, h₁⟩ := cuspFlag_transporter .line true F (iff_of_true hF rfl)
    obtain ⟨γ₂, h₂⟩ := cuspFlag_transporter .line true L₁ (iff_of_true goodFlag_L₁ rfl)
    subst h₁
    refine ⟨1, ⟨γ₁.val * γ₂.val⁻¹, mul_mem γ₁.property (inv_mem γ₂.property)⟩, ?_⟩
    change (γ₁.val * γ₂.val⁻¹) • traceDataL2.lineRep 1 = _
    rw [lineRep_one, mul_smul, ← h₂, inv_smul_smul]
  · obtain ⟨γ, hγ⟩ := cuspFlag_transporter .line false F (iff_of_false hF (by decide))
    exact ⟨0, γ, hγ⟩

/-- **Boundary duality on the associate pair from duality at each of the two line cusps** of the
boundary trace of the level. -/
theorem associatePairDuality_of_cuspDualityL2 {n : ℕ} (D : InducingData n)
    (duality : ∀ v, CuspSeparation.CuspDuality traceDataL2 D (dualityData n D.chi) v) :
    AssociatePairDuality D :=
  CuspSeparation.associateDuality_of_cuspDuality traceDataL2 (dualityData n D.chi) good
    (hdual_L2 n D.chi) hgood_L2 hlines_L2 duality

end TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2

end
