module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MackeyTheta
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel

@[expose] public section


/-!
# Flag stabilizers under the frame change `h₂ = q h₁ u`

Formalized by Claude Sonnet 5.5.

`lineFlagStab_iff_chain`: for `h₂ = q h₁ u` with `q ∈ Q(ℚ) ∩ SL₃(ℤ)` and `p = u⁻¹ s u`, `p` lies in the stabilizer of the flag of the frame `F` at `(N₂, h₂)` iff `s` lies in the stabilizer of the flag of the frame
`castGL (botRight q⁻¹) (botRight q) * F` at `(N₁, h₁)`.  (The Levi block of `h₂ p h₂⁻¹` is `botRight q · botRight (h₁ s h₁⁻¹) · botRight q⁻¹`.)
-/

open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4

section Chain

variable (N₁ N₂ : ℕ) [NeZero N₁] [NeZero N₂] (h₁ h₂ q u : SL(3, ℤ))

/-- The integral matrix `botRight q` of a lower-right block has an integral inverse. -/
theorem botRight_q_inv (hq : q ∈ lineBorel) :
    botRight q * botRight q⁻¹ = 1 ∧ botRight q⁻¹ * botRight q = 1 := botRight_inv_mul q hq

theorem lineFlagStab_iff_chain (hq : q ∈ lineBorel) (hrel : h₂ = q * h₁ * u) (p : SL(3, ℤ))
    (hp : p ∈ gammaNQAt N₂ h₂) (s : SL(3, ℤ)) (hs : s ∈ gammaNQAt N₁ h₁) (hps : s = u * p * u⁻¹) (F : GL (Fin 2) ℚ) :
    (⟨p, hp⟩ : gammaNQAt N₂ h₂) ∈ lineFlagStab N₂ h₂ F ↔
      (⟨s, hs⟩ : gammaNQAt N₁ h₁) ∈ lineFlagStab N₁ h₁
        (castGL (botRight q⁻¹) (botRight q) (botRight_q_inv q hq).2 (botRight_q_inv q hq).1 * F) := by
  rw [mem_lineFlagStab_iff, mem_lineFlagStab_iff]
  have hX : h₁ * s * h₁⁻¹ ∈ lineBorel := mem_lineBorel_of_mem_lineStab hs.2
  have e : h₂ * p * h₂⁻¹ = q * (h₁ * s * h₁⁻¹) * q⁻¹ := by
    rw [hrel, hps]; group
  rw [e, botRight_conj q _ hq hX]
  rw [cond_conj F (botRight q) (botRight q⁻¹) (botRight (h₁ * s * h₁⁻¹)) (botRight_q_inv q hq).1 (botRight_q_inv q hq).2]

end Chain

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
