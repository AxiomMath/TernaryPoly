module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenFace

@[expose] public section


/-!
# The conjugation `μ : Stab_S(uΔ) → K'` and its Mackey coordinate, for arbitrary subgroups

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section Mu

variable {M : ℕ} [NeZero M] (K K' : Subgroup SL(3, ℤ)) (u : ↥(gammaN 6))

/-- The stabilizer of `uΔ` in the face group `S`. -/
abbrev StabK : Subgroup ↥(SK K) := StabS (Δ6 M) (SK K) u

omit [NeZero M] in
theorem stab_cond (s : ↥(StabK (M := M) K u)) :
    (u : SL(3, ℤ))⁻¹ * (((s : ↥(SK K)) : ↥(gammaN 6)) : SL(3, ℤ)) * (u : SL(3, ℤ)) ∈ gammaN M := by
  have h := (mem_stabilizer_quot_iff (Δ6 M) (SK K) u (s : ↥(SK K))).mp s.2
  exact h

variable (hmem : ∀ s : ↥(SK K), (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaN M →
    (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ K')

/-- **`μ : Stab_S(uΔ) → K'`, `s ↦ u⁻¹ s u`.** -/
def muGen : ↥(StabK (M := M) K u) →* ↥K' where
  toFun s := ⟨(u : SL(3, ℤ))⁻¹ * (((s : ↥(SK K)) : ↥(gammaN 6)) : SL(3, ℤ)) * (u : SL(3, ℤ)), hmem s.1 (stab_cond K u s)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

variable {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)
  (hK' : K' ≤ gammaN M)

/-- The coefficient module of `K'`. -/
abbrev WK : Rep ℂ ↥K' := Rep.res (Subgroup.inclusion hK') (Rep.of ρM)

omit [NeZero M] in
include hρ in
theorem hTgen (s : ↥(StabK (M := M) K u)) (w : WK K' ρM hK') :
    ρ (u : ↥(gammaN 6)) ((WK K' ρM hK').ρ (muGen K K' u hmem s) w) =
      ρ (((s : ↥(SK K)) : ↥(gammaN 6))) (ρ (u : ↥(gammaN 6)) w) := by
  have e : (WK K' ρM hK').ρ (muGen K K' u hmem s) w =
      ρ (u⁻¹ * ((s : ↥(SK K)) : ↥(gammaN 6)) * u) w := by
    have := hρ ⟨u⁻¹ * ((s : ↥(SK K)) : ↥(gammaN 6)) * u, (mem_stabilizer_quot_iff (Δ6 M) (SK K) u (s : ↥(SK K))).mp s.2⟩
    exact congrArg (fun f => f w) this
  rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

end Mu

end TernaryPeriodPolynomials.Argument.RadicalInduction
