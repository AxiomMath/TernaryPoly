module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.LineRestrict

@[expose] public section


/-!
# The canonical pairing at a line face: restriction from level `N` to level `M`

Formalized by Claude Sonnet 5.5.

`canAtClass_restrict`: for `N ∣ M`, the canonical pairing at the line cusp `h⁻¹Qh` of the restrictions to `Γ(M)` of global classes of `Γ(N)` with zero flag
restrictions is `[Γ_h(N) : Γ_h(M)]` times their canonical pairing at level `N`.
-/

open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.LevelDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.FaceFibre
open TernaryPeriodPolynomials.Argument.RadicalInduction
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open scoped Classical

section LineCan

variable {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (h : SL(3, ℤ)) (n : ℕ)

omit [NeZero N] [NeZero M] in
theorem rLine_resLevel (c : groupCohomology.H2 (gammaNRepAll N n)) :
    rLine M n h (resLevel N M n hNM c) =
      twoCohomologyRestriction (lineIota hNM h) (lineFaceRep N h n) (rLine N n h c) :=
  eq_of_heq (res_res_heq (Subgroup.inclusion (gammaN_mono hNM))
    (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M h hp))
    (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp))
    (lineIota hNM h) (by ext; rfl) (gammaNRepAll N n) c)

omit [NeZero N] [NeZero M] in
theorem rLineDual_resLevel (c' : groupCohomology.H2 (gammaNRepAllDual N n)) :
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M h hp)) (gammaNRepAllDual M n)
        (resLevelDual n hNM c') =
      twoCohomologyRestriction (lineIota hNM h) (dualRepG (lineFaceRep N h n))
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp)) (gammaNRepAllDual N n) c') :=
  eq_of_heq (res_res_heq (Subgroup.inclusion (gammaN_mono hNM))
    (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M h hp))
    (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp))
    (lineIota hNM h) (by ext; rfl) (gammaNRepAllDual N n) c')

/-- The transport of the Levi modules of the line cusp from level `N` to level `M`. -/
def lineLevTr :=
  levTr (Gamma_le_of_dvd hNM) (lineFaceSplitting N h) (lineFaceSplitting M h) (lineIota hNM h) (radScale (M / N))
    (lineIota_inl hNM h) (lineIota_split hNM h) (lineFaceRep N h n) (lineFaceRep M h n) LinearMap.id (fun _ _ => rfl)

/-- The dual transport. -/
def lineLevTrDual :=
  levTr (Gamma_le_of_dvd hNM) (lineFaceSplitting N h) (lineFaceSplitting M h) (lineIota hNM h) (radScale (M / N))
    (lineIota_inl hNM h) (lineIota_split hNM h) (dualRepG (lineFaceRep N h n)) (dualRepG (lineFaceRep M h n)) LinearMap.id
    (fun _ _ => rfl)

theorem lineClass_edge [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c) :
    mixedEdgeAt M h (lineFaceRep M h n) (lineClass M h n hM (resLevel N M n hNM c) (zeroFlags_resLevel N M n hNM c hz)) =
      mapCusp (N := N) hM (Gamma_le_of_dvd hNM) (lineLevTr hNM h n)
        (mixedEdgeAt N h (lineFaceRep N h n) (lineClass N h n hN.out c hz)) := by
  apply Subtype.ext
  exact edge_restrict (Gamma_le_of_dvd hNM) (lineFaceSplitting N h) (lineFaceSplitting M h) (lineIota hNM h) (radScale (M / N))
    (lineIota_inl hNM h) (lineIota_split hNM h) (lineFaceRep N h n)
    ⟨rLine N n h c, res_radical_of_lineMixedAt (lineClass N h n hN.out c hz)⟩
    ⟨rLine M n h (resLevel N M n hNM c), res_radical_of_lineMixedAt (lineClass M h n hM _ (zeroFlags_resLevel N M n hNM c hz))⟩
    (rLine_resLevel hNM h n c)

theorem lineClassDual_edge [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (c' : groupCohomology.H2 (gammaNRepAllDual N n))
    (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c') :
    mixedEdgeAt M h (dualRepG (lineFaceRep M h n))
        (lineClassDual M h n hM (resLevelDual n hNM c') (zeroFlags_resLevelDual n hNM c' hz')) =
      mapCusp (N := N) hM (Gamma_le_of_dvd hNM) (lineLevTrDual hNM h n)
        (mixedEdgeAt N h (dualRepG (lineFaceRep N h n)) (lineClassDual N h n hN.out c' hz')) := by
  apply Subtype.ext
  exact edge_restrict (Gamma_le_of_dvd hNM) (lineFaceSplitting N h) (lineFaceSplitting M h) (lineIota hNM h) (radScale (M / N))
    (lineIota_inl hNM h) (lineIota_split hNM h) (dualRepG (lineFaceRep N h n))
    ⟨_, res_radical_of_lineMixedAt (lineClassDual N h n hN.out c' hz')⟩
    ⟨_, res_radical_of_lineMixedAt (lineClassDual M h n hM (resLevelDual n hNM c') (zeroFlags_resLevelDual n hNM c' hz'))⟩
    (rLineDual_resLevel hNM h n c')

/-- **Restriction of the canonical pairing at a line face from level `N` to level `M`**:
`B_M(res a, res' b) = (M/N)² [Γ(N):Γ(M)] B_N(a, b)`. -/
theorem canAtClass_restrict_card [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) [Fintype (Gamma N ⧸ subM N M)]
    (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (c' : groupCohomology.H2 (gammaNRepAllDual N n)) (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c') :
    canAtClass M h n hM (resLevel N M n hNM c) (zeroFlags_resLevel N M n hNM c hz)
        (resLevelDual n hNM c') (zeroFlags_resLevelDual n hNM c' hz') =
      (((M / N : ℕ) : ℂ) ^ 2 * (Fintype.card (Gamma N ⧸ subM N M) : ℂ)) * canAtClass N h n hN.out c hz c' hz' := by
  unfold canAtClass canAt
  rw [lineClass_edge hNM h n hM c hz, lineClassDual_edge hNM h n hM c' hz']
  have hD : radDet (radScale (M / N)) ≠ 0 := by
    rw [radDet_radScale]
    have : (M / N : ℕ) ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hNM)
      (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
    exact mul_ne_zero (by exact_mod_cast this) (by exact_mod_cast this)
  have key := facePairingCan_restrict (Gamma_le_of_dvd hNM) (lineFaceSplitting N h) (lineFaceSplitting M h) (lineIota hNM h)
    (radScale (M / N)) (lineIota_inl hNM h) (lineIota_split hNM h) (lineFaceRep N h n) (lineFaceRep M h n) LinearMap.id
    (fun _ _ => rfl) hM LinearMap.id (fun _ _ => rfl) (fun _ _ => rfl)
    (lineFaceRadicalInput_det N h) (lineFaceRadicalInput_det M h) hD
  refine key _ _ |>.trans ?_
  rw [radDet_radScale]
  simp only [Int.cast_mul, Int.cast_natCast]
  ring

omit [NeZero N] in
theorem finite_quot_subM (hN : 3 ≤ N) : Finite (Gamma N ⧸ subM N M) := by
  have : Fact (3 ≤ N) := ⟨hN⟩
  have : (Gamma M).FiniteIndex := inferInstance
  have h2 : (subM N M).FiniteIndex := inferInstanceAs (((Gamma M).subgroupOf (Gamma N)).FiniteIndex)
  exact Subgroup.finite_quotient_of_finiteIndex

/-- **The restriction identity at a line face**: `B_M(res a, res' b) = [Γ_h(N) : Γ_h(M)] B_N(a, b)`. -/
theorem canAtClass_restrict (hN : 3 ≤ N) (hM : 3 ≤ M)
    (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (c' : groupCohomology.H2 (gammaNRepAllDual N n)) (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c') :
    canAtClass M h n hM (resLevel N M n hNM c) (zeroFlags_resLevel N M n hNM c hz)
        (resLevelDual n hNM c') (zeroFlags_resLevelDual n hNM c' hz') =
      (((gammaNQAt M h).relIndex (gammaNQAt N h) : ℕ) : ℂ) * canAtClass N h n hN c hz c' hz' := by
  have : Fact (3 ≤ N) := ⟨hN⟩
  have := finite_quot_subM (N := N) (M := M) hN
  let : Fintype (Gamma N ⧸ subM N M) := Fintype.ofFinite _
  rw [canAtClass_restrict_card hNM h n hM c hz c' hz']
  congr 1
  rw [lineFace_relIndex_eq hN hNM h]
  have hc : Fintype.card (Gamma N ⧸ subM N M) = (Gamma M).relIndex (Gamma N) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hc]
  push_cast
  rfl

end LineCan

end TernaryPeriodPolynomials.Argument.LevelDescent
