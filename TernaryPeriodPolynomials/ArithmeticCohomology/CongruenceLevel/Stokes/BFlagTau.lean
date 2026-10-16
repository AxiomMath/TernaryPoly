module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BFlagGen

@[expose] public section


/-!
# The plane version of the value of `λ_F` on cup classes

Formalized by Claude Sonnet 5.5.

For a complete flag `F` with frame `g`, the image of the frame homomorphism `s ↦ g ι(s) g⁻¹` under `tau` has Heisenberg coordinates `(-b, -a, a b - c)` (`heisTwist`).  `flagLam_cup_value_tau`: if `M_h` is a homomorphism of line type
with `q M_h = tau(g ι g⁻¹) q`, `q ∈ lineBorel`, and `u = c · (-a)` then `λ_F[u ∪ β_{M_h}] = q₀₀ · c · (-2 · 6⁴)`.
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

/-- The inverse of a unipotent upper triangular matrix. -/
theorem unip_inv_entries (M : SL(3, ℤ)) (h00 : (M : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1) (h11 : (M : Matrix (Fin 3) (Fin 3) ℤ) 1 1 = 1)
    (h22 : (M : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1) (h10 : (M : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0)
    (h20 : (M : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0) (h21 : (M : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0) :
    ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∧ ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 1 = 1 ∧
    ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 ∧ ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧
    ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧ ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 ∧
    ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 1 = -(M : Matrix (Fin 3) (Fin 3) ℤ) 0 1 ∧
    ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 2 = -(M : Matrix (Fin 3) (Fin 3) ℤ) 1 2 ∧
    ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 2 =
      (M : Matrix (Fin 3) (Fin 3) ℤ) 0 1 * (M : Matrix (Fin 3) (Fin 3) ℤ) 1 2 - (M : Matrix (Fin 3) (Fin 3) ℤ) 0 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, h00, h11, h22, h10, h20, h21]

theorem frame_entries_all (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) (s : ↥(MulAction.stabilizer Γ6 F)) :
    ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∧
      ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 1 = 1 ∧ ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 ∧
      ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧ ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
      ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 ∧
      (6 : ℤ) ∣ ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 1 := by
  have hmem := frameMat_mem F g hg s
  obtain ⟨e00, e11, e22, d01, -, -⟩ := flag_entries (by norm_num : 3 ≤ 6) hmem
  obtain ⟨-, e10, e20, e21⟩ := hmem
  exact ⟨e00, e11, e22, e10, e20, e21, by exact_mod_cast d01⟩

/-- The frame homomorphism twisted by `tau` has line type. -/
theorem tauFrame_lineType (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) :
    LineType (tau.comp (conjIota (MulAction.stabilizer Γ6 F) g)) := fun s => by
  obtain ⟨e00, e11, e22, e10, e20, e21, -⟩ := frame_entries_all F g hg s
  obtain ⟨i00, i11, i22, i10, i20, i21, i01, i12, i02⟩ := unip_inv_entries (frameMat F g s) e00 e11 e22 e10 e20 e21
  show ((tau (conjIota (MulAction.stabilizer Γ6 F) g s) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧
    ((tau (conjIota (MulAction.stabilizer Γ6 F) g s) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
    ((tau (conjIota (MulAction.stabilizer Γ6 F) g s) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1
  rw [tau_apply, tau_apply, tau_apply]
  exact ⟨i21, i20, i22⟩

/-- The Levi block of the twisted frame homomorphism is `[[1, -a], [0, 1]]`. -/
theorem tauFrame_A (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) (s : ↥(MulAction.stabilizer Γ6 F)) :
    (matLineData (tau.comp (conjIota (MulAction.stabilizer Γ6 F) g)) (tauFrame_lineType F g hg)).A s =
      !![1, -((conjIota (MulAction.stabilizer Γ6 F) g s : Matrix (Fin 3) (Fin 3) ℤ) 0 1); 0, 1] := by
  obtain ⟨e00, e11, e22, e10, e20, e21, -⟩ := frame_entries_all F g hg s
  obtain ⟨i00, i11, i22, i10, i20, i21, i01, i12, i02⟩ := unip_inv_entries (frameMat F g s) e00 e11 e22 e10 e20 e21
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-Matrix.SpecialLinearGroup.coe_inv, matLineData, tau_apply, show conjIota (MulAction.stabilizer Γ6 F) g s = frameMat F g s from rfl,
      i11, i01, i00, i10]

/-- **The value of `λ_F` on a plane cup class** (relative to the frame homomorphism twisted by `tau`). -/
theorem flagLam_cup_value_tau (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F)
    (Mh : ↥(MulAction.stabilizer Γ6 F) →* SL(3, ℤ)) (hh : LineType Mh) (q : SL(3, ℤ)) (hq : q ∈ lineBorel)
    (hrel : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * (Mh s : Matrix (Fin 3) (Fin 3) ℤ) =
      (tau (conjIota (MulAction.stabilizer Γ6 F) g s) : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ))
    (c : ℚ) (u : ↥(MulAction.stabilizer Γ6 F) → ℚ)
    (hu : ∀ s, u s = c * ((-((conjIota (MulAction.stabilizer Γ6 F) g s : Matrix (Fin 3) (Fin 3) ℤ) 0 1) : ℤ) : ℚ))
    (hT : dThree (cupCochain Mh hh u) = 0) :
    flagLam F (clsRes (MulAction.stabilizer Γ6 F) (cupCochain Mh hh u) hT) =
      ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ) * (c * (-2 * (6 : ℚ) ^ 2 * (6 : ℚ) ^ 2)) := by
  set H := (flagCoords g).ofMulEquiv (stabCongr F g hg) with hH
  have hfm : ∀ s, conjIota (MulAction.stabilizer Γ6 F) g s = frameMat F g s := fun s => rfl
  have hent : ∀ s, ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∧
      ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 1 = 1 ∧ ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 ∧
      ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧ ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
      ((frameMat F g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := by
    intro s
    have hmem := frameMat_mem F g hg s
    obtain ⟨e00, e11, e22, -⟩ := flag_entries (by norm_num : 3 ≤ 6) hmem
    obtain ⟨-, e10, e20, e21⟩ := hmem
    exact ⟨e00, e11, e22, e10, e20, e21⟩
  let Mg : ↥(MulAction.stabilizer Γ6 F) →* SL(3, ℤ) := tau.comp (conjIota (MulAction.stabilizer Γ6 F) g)
  have hinv : ∀ s, _ := fun s => unip_inv_entries (frameMat F g s) (hent s).1 (hent s).2.1 (hent s).2.2.1 (hent s).2.2.2.1
    (hent s).2.2.2.2.1 (hent s).2.2.2.2.2
  have hgL : LineType Mg := fun s => by
    obtain ⟨i00, i11, i22, i10, i20, i21, i01, i12, i02⟩ := hinv s
    show ((tau (conjIota (MulAction.stabilizer Γ6 F) g s) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧
      ((tau (conjIota (MulAction.stabilizer Γ6 F) g s) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
      ((tau (conjIota (MulAction.stabilizer Γ6 F) g s) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1
    rw [tau_apply, tau_apply, tau_apply, hfm]
    exact ⟨i21, i20, i22⟩
  have hD : ∀ s, (matLineData Mg hgL).A s = (heisLineData (heisTwist H)).A s ∧
      (matLineData Mg hgL).v s = (heisLineData (heisTwist H)).v s := by
    intro s
    obtain ⟨i00, i11, i22, i10, i20, i21, i01, i12, i02⟩ := hinv s
    have hc : H.a s = _ ∧ H.b s = _ ∧ H.c s = _ := frameMat_coords F g hg s
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [-Matrix.SpecialLinearGroup.coe_inv, matLineData, heisLineData, heisTwist, Mg, tau_apply, hfm, i11, i01, i00, i10, ← hc.1]
    · ext j
      fin_cases j <;>
        simp [-Matrix.SpecialLinearGroup.coe_inv, matLineData, heisLineData, heisTwist, Mg, tau_apply, hfm, i12, i02, ← hc.1, ← hc.2.1, ← hc.2.2]
  have hrel' : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * (Mh s : Matrix (Fin 3) (Fin 3) ℤ) =
      (Mg s : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ) := hrel
  have hu' : ∀ s, u s = c * ((heisTwist H).b s : ℚ) := fun s => by
    rw [hu s]
    have hc : H.a s = _ ∧ H.b s = _ ∧ H.c s = _ := frameMat_coords F g hg s
    simp only [heisTwist, hc.1, hfm]
  have hval := heis_cycle_cup_twist H (stabCongr F g hg (flagX g)) (stabCongr F g hg (flagY g)) 6 6
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagX_coords g).1)
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagX_coords g).2.1)
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagX_coords g).2.2)
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagY_coords g).1)
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagY_coords g).2.1)
    (by simpa [HeisCoords.ofMulEquiv, H] using (flagY_coords g).2.2)
  exact flagLam_gen F g hg (heisLineData (heisTwist H)) (heisTwist H).b (heisTwist H).b_mul Mg Mh hgL hh hD q hq hrel' _ hval c u hu' hT

end TernaryPeriodPolynomials.Argument.GammaNStokes
