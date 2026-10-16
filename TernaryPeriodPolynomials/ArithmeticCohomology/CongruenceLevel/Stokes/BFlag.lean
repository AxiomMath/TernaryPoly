module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLocal
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.FrameIndep

@[expose] public section


/-!
# The value of `λ_F` on the class of a line cup cocycle on a flag stabilizer

Formalized by Claude Sonnet 5.5.

For a complete flag `F`, a frame `g` (`flagOf g = F`), a homomorphism `Mh` of line type from the stabilizer of `F` into `SL₃(ℤ)` which is conjugate to the frame homomorphism `s ↦ g ι(s) g⁻¹` by an element `q` of the
Borel of the line, and `u = c · b` with `b = (g ι(s) g⁻¹)₁₂`, the evaluation functional `λ_F` takes on the class of `u ∪ β_{Mh}` the value `q₀₀ · c · (-2 · 6⁴)` (`flagLam_cup_value`).
-/

open scoped MatrixGroups
open CategoryTheory MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open Matrix TernaryPeriodPolynomials.Argument.FlagH3 TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg (flagGroup flag_entries)

/-- The matrix homomorphism `s ↦ ι(s)` of a subgroup of `Γ(6)` into `SL₃(ℤ)`. -/
def iotaS (S : Subgroup Γ6) : ↥S →* SL(3, ℤ) :=
  ((gammaN 6).subtype.comp (gammaSixEquiv.symm : Γ6 ≃* gammaN 6).toMonoidHom).comp S.subtype

/-- The conjugated matrix homomorphism `s ↦ g ι(s) g⁻¹`. -/
def conjIota (S : Subgroup Γ6) (g : SL(3, ℤ)) : ↥S →* SL(3, ℤ) := (MulAut.conj g).toMonoidHom.comp (iotaS S)

theorem conjIota_apply (S : Subgroup Γ6) (g : SL(3, ℤ)) (s : ↥S) :
    conjIota S g s = g * (gammaSixEquiv.symm (s : Γ6)).1 * g⁻¹ := rfl

/-- The cup cocycle `u(x₀) β(x₁, x₂)` of a homomorphism of line type. -/
def cupCochain {K : Type} [Group K] (M : K →* SL(3, ℤ)) (hM : LineType M) (u : K → ℚ) : (Fin 3 → K) → ℚ :=
  fun x => u (x 0) * (matLineData M hM).beta (x 1) (x 2)

theorem cupCochain_cocycle {K : Type} [Group K] (M : K →* SL(3, ℤ)) (hM : LineType M) (u : K → ℚ)
    (hu : ∀ g h, u (g * h) = u g + u h) : dThree (cupCochain M hM u) = 0 :=
  dThree_cup u (matLineData M hM).beta hu (matLineData M hM).beta_cocycle

/-- **The value of `λ_F` on a line cup class.** -/
theorem flagLam_cup_value (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) (Mh : ↥(MulAction.stabilizer Γ6 F) →* SL(3, ℤ))
    (hh : LineType Mh) (q : SL(3, ℤ)) (hq : q ∈ lineBorel)
    (hrel : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * (Mh s : Matrix (Fin 3) (Fin 3) ℤ) =
      (conjIota (MulAction.stabilizer Γ6 F) g s : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ))
    (c : ℚ) (u : ↥(MulAction.stabilizer Γ6 F) → ℚ)
    (hu : ∀ s, u s = c * ((conjIota (MulAction.stabilizer Γ6 F) g s : Matrix (Fin 3) (Fin 3) ℤ) 1 2 : ℤ))
    (hT : dThree (cupCochain Mh hh u) = 0) :
    flagLam F (clsRes (MulAction.stabilizer Γ6 F) (cupCochain Mh hh u) hT) =
      ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ) * (c * (-2 * (6 : ℚ) ^ 2 * (6 : ℚ) ^ 2)) := by
  have hl := flagLam_frame F g hg
  have hfm : ∀ s, conjIota (MulAction.stabilizer Γ6 F) g s = frameMat F g s := fun s => rfl
  set H := (flagCoords g).ofMulEquiv (stabCongr F g hg) with hH
  have hmem : ∀ s, frameMat F g s ∈ flagGroup 6 := fun s => frameMat_mem F g hg s
  have hent : ∀ s, ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∧
      ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 1 = 1 ∧ ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 ∧
      ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧ ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
      ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := by
    intro s
    obtain ⟨e00, e11, e22, -⟩ := flag_entries (by norm_num : 3 ≤ 6) (hmem s)
    obtain ⟨-, e10, e20, e21⟩ := hmem s
    exact ⟨e00, e11, e22, e10, e20, e21⟩
  have hgl : LineType (conjIota (MulAction.stabilizer Γ6 F) g) := fun s => by
    rw [hfm]; exact ⟨(hent s).2.2.2.1, (hent s).2.2.2.2.1, (hent s).1⟩
  have hHeis : ∀ s, (matLineData (conjIota (MulAction.stabilizer Γ6 F) g) hgl).A s = (heisLineData H).A s ∧
      (matLineData (conjIota (MulAction.stabilizer Γ6 F) g) hgl).v s = (heisLineData H).v s := by
    intro s
    have hc : H.a s = _ ∧ H.b s = _ ∧ H.c s = _ := frameMat_coords F g hg s
    obtain ⟨e00, e11, e22, e10, e20, e21⟩ := hent s
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [matLineData, heisLineData, hfm, e11, e22, e21, ← hc.2.1]
    · ext j
      fin_cases j <;> simp [matLineData, heisLineData, hfm, ← hc.1, ← hc.2.2]
  have hu' : ∀ s, u s = c * (H.b s : ℚ) := fun s => by
    rw [hu s, (frameMat_coords F g hg s).2.1, hfm]
  rw [hl]
  simp only [LinearMap.comp_apply, clsRes, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [FlagCohomDatum.lam_cocycle]
  exact local_value H (conjIota (MulAction.stabilizer Γ6 F) g) Mh hgl hh hHeis q hq hrel
    (stabCongr F g hg (flagX g)) (stabCongr F g hg (flagY g)) 6 6
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagX_coords g).1)
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagX_coords g).2.1)
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagX_coords g).2.2)
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagY_coords g).1)
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagY_coords g).2.1)
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagY_coords g).2.2) c u hu'

end TernaryPeriodPolynomials.Argument.GammaNStokes
