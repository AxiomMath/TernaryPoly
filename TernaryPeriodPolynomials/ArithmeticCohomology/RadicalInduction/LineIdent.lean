module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenIdent

@[expose] public section


/-!
# Step 2 for the line faces: `OrbitIdentLine`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

**`orbitIdentLine`**: for `3 ≤ M`, `6 ∣ M`, the level-6 canonical pairing `can6` of the orbit components `lineTermX`, `lineTermY` of the restrictions to the line group `K_i = Γ(6) ∩ i.rep⁻¹ Q i.rep` of induced
classes equals the level-`M` canonical pairing `canAtClass` at the frame `i.rep · u_O` of the restrictions of the level-`M` classes, with constant exactly `1`.  The geometric data is the conjugation
`p ↦ u p u⁻¹` (`line_hmem`, `line_hback`, `line_hinl`, `line_hspl`), the rest is `orbit_ident_gen`.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section LineData

variable {M : ℕ} (i : LineFaces 6) (u : ↥(gammaN 6))

theorem line_hK : gammaNQAt 6 i.rep ≤ gammaN 6 := fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp

theorem line_hK' (h : SL(3, ℤ)) : gammaNQAt M h ≤ gammaN M := fun _ hp => gammaNQAt_le_gammaN M h hp

theorem line_hmem (s : ↥(SK (gammaNQAt 6 i.rep)))
    (hs : (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaN M) :
    (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaNQAt M (i.rep * (u : SL(3, ℤ))) := by
  have hsK : ((s : ↥(gammaN 6)) : SL(3, ℤ)) ∈ gammaNQAt 6 i.rep := s.2
  have hsK' : i.rep * ((s : ↥(gammaN 6)) : SL(3, ℤ)) * i.rep⁻¹ ∈ gammaNQ 6 := hsK
  show (i.rep * (u : SL(3, ℤ))) * ((u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ))) *
    (i.rep * (u : SL(3, ℤ)))⁻¹ ∈ gammaNQ M
  have e : (i.rep * (u : SL(3, ℤ))) * ((u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ))) *
      (i.rep * (u : SL(3, ℤ)))⁻¹ = i.rep * ((s : ↥(gammaN 6)) : SL(3, ℤ)) * i.rep⁻¹ := by group
  refine ⟨(gammaN_normal M).conj_mem _ hs (i.rep * (u : SL(3, ℤ))), ?_⟩
  rw [e]
  exact hsK'.2

theorem line_hback (h6 : 6 ∣ M) (p : ↥(gammaNQAt M (i.rep * (u : SL(3, ℤ))))) :
    (u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ ∈ gammaNQAt 6 i.rep := by
  have hp : (i.rep * (u : SL(3, ℤ))) * (p : SL(3, ℤ)) * (i.rep * (u : SL(3, ℤ)))⁻¹ ∈ gammaNQ M := p.2
  show i.rep * ((u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹) * i.rep⁻¹ ∈ gammaNQ 6
  have e : i.rep * ((u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹) * i.rep⁻¹ =
      (i.rep * (u : SL(3, ℤ))) * (p : SL(3, ℤ)) * (i.rep * (u : SL(3, ℤ)))⁻¹ := by group
  rw [e]
  exact ⟨gammaN_mono h6 hp.1, hp.2⟩

theorem line_hinl [NeZero M] (h6 : 6 ∣ M) (r : RadicalLattice) :
    (u : SL(3, ℤ)) * (((lineFaceExt M (i.rep * (u : SL(3, ℤ)))).inl r : ↥(gammaNQAt M (i.rep * (u : SL(3, ℤ))))) : SL(3, ℤ)) *
        (u : SL(3, ℤ))⁻¹ = (((lineFaceExt 6 i.rep).inl (r ^ (M / 6)) : ↥(gammaNQAt 6 i.rep)) : SL(3, ℤ)) := by
  rw [lineFaceExt_inl_val, lineFaceExt_inl_val, radEltQ_div h6]
  group

theorem line_hspl [NeZero M] (h6 : 6 ∣ M) (m : ↥(CongruenceSubgroup.Gamma M)) :
    (u : SL(3, ℤ)) * (((lineFaceSplitting M (i.rep * (u : SL(3, ℤ)))) m : ↥(gammaNQAt M (i.rep * (u : SL(3, ℤ))))) : SL(3, ℤ)) *
        (u : SL(3, ℤ))⁻¹ =
      (((lineFaceSplitting 6 i.rep) (Subgroup.inclusion (gamma_le_of_dvd h6) m) : ↥(gammaNQAt 6 i.rep)) : SL(3, ℤ)) := by
  rw [lineFaceSplitting_val, lineFaceSplitting_val]
  change _ = _ * blockDiagQ (m.1 : SL(2, ℤ)) * _
  group

end LineData

section Main

variable (M n : ℕ) [NeZero M]

/-- **Step 2 for the line faces (`OrbitIdentLine`), with the constant exactly `1`.** -/
theorem orbitIdentLine (hM : 3 ≤ M) (h6 : 6 ∣ M) : OrbitIdentLine M n hM := by
  intro c₀ hz c₀' hz' cV cVd hcV hcVd i o
  have hu : ((uOLine M i o : ↥(gammaN 6)) : ↥(gammaN 6) ⧸ Δ6 M) = Quotient.out o := Quotient.out_eq' _
  exact orbit_ident_gen hM h6 (gammaNQAt 6 i.rep) (gammaNQAt M (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))))
    (line_hK i) (line_hK' (M := M) (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ)))) (uOLine M i o) (line_hmem i (uOLine M i o)) (line_hback i (uOLine M i o) h6)
    (lineFaceExt 6 i.rep) (lineFaceSplitting 6 i.rep) (lineFaceRadicalInput_det 6 i.rep)
    (lineFaceExt M (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))))
    (lineFaceSplitting M (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))))
    (lineFaceRadicalInput_det M (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))))
    (line_hinl i (uOLine M i o) h6) (line_hspl i (uOLine M i o) h6)
    (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) o hu c₀ cV hcV c₀' cVd hcVd
    (res_radical_of_lineMixedAt (lineTermX c₀ hz cV hcV i o)) (lineEdge_mem_cuspidal (lineTermX c₀ hz cV hcV i o))
    (res_radical_of_lineMixedAt (lineTermY c₀' hz' cVd hcVd i o)) (lineEdge_mem_cuspidal (lineTermY c₀' hz' cVd hcVd i o))
    (res_radical_of_lineMixedAt (lineClass M (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))) n hM c₀ hz))
    (lineEdge_mem_cuspidal (lineClass M (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))) n hM c₀ hz))
    (res_radical_of_lineMixedAt (lineClassDual M (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))) n hM c₀' hz'))
    (lineEdge_mem_cuspidal (lineClassDual M (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))) n hM c₀' hz'))

end Main

end TernaryPeriodPolynomials.Argument.RadicalInduction
