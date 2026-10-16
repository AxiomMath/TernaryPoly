module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.Factorisation6Thm
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel

@[expose] public section


/-!
# The literal Lemma `ar:lem:stokes` at level `Γ(6)` with the canonical pairings

Formalized by Claude Sonnet 5.5.

For global classes `c`, `c'` of `Γ(6)` with zero flag restrictions, the Stokes relation `∑_Q B + ∑_P B = 0` for the geometric (cone) face pairings, together with the uniform factorisation
`B = c · can6` on the line faces and `B = -c · can6P` on the plane faces (`c = -3Λ ≠ 0`, `faceFactorisation6U`; the relative sign is `κ_P = -κ_L`), gives
`∑_Q can6 - ∑_P can6P = 0`: the orientations are `ε_Q = +1`, `ε_P = -1` (the sign `-1` of the plane faces comes from `κ_P = +3 = -κ_L`, `planeSum_final` against `lineSum_final`).
`stokes_gamma6_literal` is this for every coefficient module `ρ`; `stokes_gamma6_literal_En` for `E_n` and its contragredient, in the notation `canAtClass`, `canAtClassP` of `FrameLevel`.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.GammaNFaceFactor (faceFactorisation6U)

section General

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

/-- **The literal Stokes lemma at `Γ(6)`, for every coefficient module**: with the oriented sum `ε_Q = +1`, `ε_P = -1`. -/
theorem stokes_gamma6_literal
    (c : groupCohomology.H2 (Rep.of ρ)) (c' : groupCohomology.H2 (Rep.of ρ.dual))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of ρ) c = 0)
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of ρ.dual) c' = 0) :
    (1 : ℂ) * ∑ i : LineFaces 6, can6 ρ i
        ⟨twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ) c,
          lineMixedSub_of_zeroFlags ρ i c hz⟩
        ⟨twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual) c',
          lineMixedSub_of_zeroFlags ρ.dual i c' hz'⟩ +
      (-1 : ℂ) * ∑ i : PlaneFaces 6, can6P ρ i
        ⟨twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ) c,
          planeMixedSub_of_zeroFlags ρ i c hz⟩
        ⟨twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual) c',
          planeMixedSub_of_zeroFlags ρ.dual i c' hz'⟩ = 0 := by
  obtain ⟨cc, hcc, hfac⟩ := faceFactorisation6U
  obtain ⟨hl, hp⟩ := hfac V ρ
  have hS := gamma6_stokes_of_zeroFlags ρ c c' hz hz'
  have e1 : ∀ i : LineFaces 6, lineFacePairM ρ i
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ) c)
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual) c') =
      cc * can6 ρ i ⟨_, lineMixedSub_of_zeroFlags ρ i c hz⟩ ⟨_, lineMixedSub_of_zeroFlags ρ.dual i c' hz'⟩ :=
    fun i => hl i ⟨_, lineMixedSub_of_zeroFlags ρ i c hz⟩ ⟨_, lineMixedSub_of_zeroFlags ρ.dual i c' hz'⟩
  have e2 : ∀ i : PlaneFaces 6, planeFacePairM ρ i
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ) c)
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual) c') =
      -cc * can6P ρ i ⟨_, planeMixedSub_of_zeroFlags ρ i c hz⟩ ⟨_, planeMixedSub_of_zeroFlags ρ.dual i c' hz'⟩ :=
    fun i => hp i ⟨_, planeMixedSub_of_zeroFlags ρ i c hz⟩ ⟨_, planeMixedSub_of_zeroFlags ρ.dual i c' hz'⟩
  rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_congr rfl (fun i _ => e2 i), ← Finset.mul_sum] at hS
  simp only [neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum] at hS
  have : cc * (∑ i : LineFaces 6, can6 ρ i ⟨_, lineMixedSub_of_zeroFlags ρ i c hz⟩ ⟨_, lineMixedSub_of_zeroFlags ρ.dual i c' hz'⟩ -
      ∑ i : PlaneFaces 6, can6P ρ i ⟨_, planeMixedSub_of_zeroFlags ρ i c hz⟩ ⟨_, planeMixedSub_of_zeroFlags ρ.dual i c' hz'⟩) = 0 := by
    linear_combination hS
  have h2 := (mul_eq_zero.1 this).resolve_left hcc
  linear_combination h2

end General

section En

variable (n : ℕ)

/-- **The literal Stokes lemma at `Γ(6)` for `E_n` and its contragredient**, in the notation of `FrameLevel`: `∑_Q canAt - ∑_P canAtP = 0`, i.e. `ε_Q = +1`, `ε_P = -1`. -/
theorem stokes_gamma6_literal_En (c : groupCohomology.H2 (gammaNRepAll 6 n)) (hz : ZeroFlags 6 n c)
    (c' : groupCohomology.H2 (gammaNRepAllDual 6 n))
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN 6 g)) (gammaNRepAllDual 6 n) c' = 0) :
    (1 : ℂ) * ∑ i : LineFaces 6, canAtClass 6 i.rep n (by norm_num) c hz c' hz' +
      (-1 : ℂ) * ∑ i : PlaneFaces 6, canAtClassP 6 (planeFaceRepr i) n (by norm_num) c hz c' hz' = 0 := by
  have : FiniteDimensional ℂ (GeneralEisenstein.HomogeneousPoly n) :=
    TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.homogeneousPoly_finite n
  exact stokes_gamma6_literal (rhoEn n) c c' hz hz'

end En

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
