module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine4
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.BaseSumZeroBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Vanish
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.CuspGeometry

@[expose] public section

/-!
# Calibration: the value of `λ_F` on the line cup class, and the matrix data of the radical and Levi letters

Formalized by Claude Sonnet 5.5.

`flagLam_calib` (G-c): for an additive `φ` on `Γ(6)` and the flag `flagAt h w`, `λ` of the class of the line cup cocycle `u ∪ β_{M_h}` (`M_h s = h ι(s) h⁻¹`, `u = φ ∘ (lower right block of M_h)`) is `-432 φ(posPar w)`
(the `flagLam_cup_value` with the frame `q_w h`, `q_w` with first diagonal entry `1`).  `letter_inl`, `letter_split`: `A(ext.inl r) = 1`, `v(ext.inl r) = (6 r₁, 6 r₂)`, `A(s σ) = σ`, `v(s σ) = 0`.
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (RadicalLattice)

section Calibration

variable (h : SL(3, ℤ))

theorem stab_flagAt_fixes_line (w : Prim2) (s : ↥(MulAction.stabilizer Γ6 (flagAt h w))) :
    (s : Γ6) ∈ MulAction.stabilizer Γ6 (lineOf h) := by
  have h1 : (s : Γ6) • flagLineOf (flagAt h w) = flagLineOf (flagAt h w) := by
    have e := TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant (s : Γ6) (flagAt h w)
    rw [← e, s.2]
  rw [flagLineOf_flagAt] at h1
  exact h1

theorem lineType_flagAt (w : Prim2) : LineType (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) := fun s => by
  have := (stab_gammaNQ h (lineOf h) rfl ⟨s.1, stab_flagAt_fixes_line h w s⟩).2
  exact ⟨this.2.1, this.2.2, this.1⟩

theorem gammaN_flagAt (w : Prim2) (s : ↥(MulAction.stabilizer Γ6 (flagAt h w))) :
    conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h s ∈ gammaN 6 :=
  (stab_gammaNQ h (lineOf h) rfl ⟨s.1, stab_flagAt_fixes_line h w s⟩).1

open TernaryPeriodPolynomials.Argument.FlagH3 in
/-- **(G-c) Calibration.**  For a flag `flagAt h w` over the line of `h` and an additive `φ` on `Γ(6)`, `λ` of the class of the line cup cocycle `u ∪ β_{M_h}`
(`M_h s = h ι(s) h⁻¹`, `u s = φ(lower right block of M_h s)`) is `-432 φ(posPar w)`. -/
theorem flagLam_calib (w : Prim2) (φ : Gamma 6 → ℚ) (hφ : ∀ a b, φ (a * b) = φ a + φ b)
    (hh : LineType (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h))
    (hN : ∀ s, conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h s ∈ gammaN 6)
    (hT : dThree (cupCochain (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh
      (fun s => φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN s))) = 0) :
    flagLam (flagAt h w) (clsRes (MulAction.stabilizer Γ6 (flagAt h w)) (cupCochain (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh
      (fun s => φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN s))) hT) = -432 * φ (posParSL w.1) := by
  set S := MulAction.stabilizer Γ6 (flagAt h w) with hS
  set Mh := conjIota S h with hMh
  set q := qMat w with hqdef
  have hq : q ∈ lineBorel := qMat_mem w
  set g : SL(3, ℤ) := q * h with hg
  have hgF : flagOf g = flagAt h w := rfl
  have hMg : LineType (conjIota S g) := fun s => by
    obtain ⟨e00, -, -, e10, e20, -⟩ := frame_entries (flagAt h w) g hgF s
    exact ⟨e10, e20, e00⟩
  have hrel : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * (Mh s : Matrix (Fin 3) (Fin 3) ℤ) =
      (conjIota S g s : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ) := by
    intro s
    have : q * Mh s = conjIota S g s * q := by
      simp only [hMh, conjIota_apply, hg]
      group
    exact congrArg (fun x : SL(3, ℤ) => (x : Matrix (Fin 3) (Fin 3) ℤ)) this
  obtain ⟨-, -, -, hA, -⟩ := frame_relation (conjIota S g) Mh hMg hh q hq hrel
  set c : ℚ := φ (PK q hq 1) / 6 with hc
  have hu : ∀ s, φ (gammaOfM Mh hh hN s) = c * ((conjIota S g s : Matrix (Fin 3) (Fin 3) ℤ) 1 2 : ℤ) := by
    intro s
    obtain ⟨e00, e11, e22, e10, e20, e21, d12⟩ := frame_entries (flagAt h w) g hgF s
    obtain ⟨k, hk⟩ := d12
    replace e11 : ((conjIota S g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 1 = 1 := e11
    replace e22 : ((conjIota S g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 := e22
    replace e21 : ((conjIota S g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := e21
    replace hk : ((conjIota S g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 2 = 6 * k := hk
    have hG : gammaOfM Mh hh hN s = PK q hq k := by
      apply Subtype.ext
      apply Subtype.ext
      show (matLineData Mh hh).A s = PKmat q k
      rw [hA s, PKmat]
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp [matLineData, e11, e22, e21, hk]
    rw [hG, phi_PK φ hφ q hq k, hk, hc]
    push_cast
    ring
  have := flagLam_cup_value (flagAt h w) g hgF Mh hh q hq hrel c (fun s => φ (gammaOfM Mh hh hN s)) hu hT
  rw [this, show ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ) = 1 by rw [hqdef, qMat_00]; norm_cast]
  have e1 : φ (posParSL w.1) = φ (PK q hq 1) := by
    have := phi_posPar φ hφ q hq
    rw [qMat_vec] at this
    rw [this, qMat_00]; simp
  rw [e1, hc]
  ring

end Calibration

section LetterData

variable (h : SL(3, ℤ))

theorem conjIota_inl (w : Prim2) (r : RadicalLattice) :
    conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h ⟨_, lineEmb_inl_mem_stab h w r⟩ = radEltQ 6 r := by
  rw [conjIota_apply]
  have e : (gammaSixEquiv.symm (lineEmb h ((lineFaceExt 6 h).inl r))).1 = h⁻¹ * radEltQ 6 r * h := by
    rw [lineEmb_val]
    exact inl_val h r
  show h * (gammaSixEquiv.symm (lineEmb h ((lineFaceExt 6 h).inl r))).1 * h⁻¹ = _
  rw [e]
  group

theorem conjIota_split (w : Prim2) (A : Gamma 6) (hA : ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ w.1 = w.1) :
    conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h ⟨_, lineEmb_split_mem_stab h w A hA⟩ = blockDiagQ A.1 := by
  rw [conjIota_apply]
  have e : (gammaSixEquiv.symm (lineEmb h ((lineFaceSplitting 6 h) A))).1 = h⁻¹ * blockDiagQ A.1 * h := by
    rw [lineEmb_val]
    exact split_val h A
  show h * (gammaSixEquiv.symm (lineEmb h ((lineFaceSplitting 6 h) A))).1 * h⁻¹ = _
  rw [e]
  group

/-- **The matrix data of the radical letters**: `A(ext.inl r) = 1`, `v(ext.inl r) = (6 r₁, 6 r₂)`. -/
theorem letter_inl (w : Prim2) (r : RadicalLattice)
    (hh : LineType (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h)) :
    (matLineData (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh).A ⟨_, lineEmb_inl_mem_stab h w r⟩ = 1 ∧
      (matLineData (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh).v ⟨_, lineEmb_inl_mem_stab h w r⟩ =
        ![6 * (Multiplicative.toAdd r).1, 6 * (Multiplicative.toAdd r).2] := by
  have e := conjIota_inl h w r
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matLineData, e, radEltQ]
  · ext j
    fin_cases j <;> simp [matLineData, e, radEltQ]

/-- **The matrix data of the Levi letters**: `A(s σ) = σ`, `v(s σ) = 0`. -/
theorem letter_split (w : Prim2) (A : Gamma 6) (hA : ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ w.1 = w.1)
    (hh : LineType (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h)) :
    (matLineData (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh).A ⟨_, lineEmb_split_mem_stab h w A hA⟩ =
        ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ∧
      (matLineData (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh).v ⟨_, lineEmb_split_mem_stab h w A hA⟩ = 0 := by
  have e := conjIota_split h w A hA
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matLineData, e, blockDiagQ]
  · ext j
    fin_cases j <;> simp [matLineData, e, blockDiagQ]

end LetterData

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
