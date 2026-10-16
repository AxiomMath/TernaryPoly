module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.LineRestrict
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.PlaneData
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.FibreIndexPlane

@[expose] public section


/-!
# The canonical pairing at a plane face: restriction from level `N` to level `M`

Formalized by Claude Sonnet 5.5.

`canAtClassP_restrict`: for `N ∣ M`, the canonical pairing at the plane cusp `h⁻¹Qh` of the restrictions to `Γ(M)` of global classes of `Γ(N)` with zero flag
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
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.RadicalInduction
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open scoped Classical

section LineCan

variable {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (h : SL(3, ℤ)) (n : ℕ)

omit [NeZero N] [NeZero M] in
theorem rPlane_resLevel (c : groupCohomology.H2 (gammaNRepAll N n)) :
    rPlane M n h (resLevel N M n hNM c) =
      twoCohomologyRestriction (planeIota hNM h) (faceRep N h n) (rPlane N n h c) :=
  eq_of_heq (res_res_heq (Subgroup.inclusion (gammaN_mono hNM))
    (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M h hp))
    (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp))
    (planeIota hNM h) (by ext; rfl) (gammaNRepAll N n) c)

omit [NeZero N] [NeZero M] in
theorem rPlaneDual_resLevel (c' : groupCohomology.H2 (gammaNRepAllDual N n)) :
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M h hp)) (gammaNRepAllDual M n)
        (resLevelDual n hNM c') =
      twoCohomologyRestriction (planeIota hNM h) (dualRepG (faceRep N h n))
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp)) (gammaNRepAllDual N n) c') :=
  eq_of_heq (res_res_heq (Subgroup.inclusion (gammaN_mono hNM))
    (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M h hp))
    (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp))
    (planeIota hNM h) (by ext; rfl) (gammaNRepAllDual N n) c')

/-- The transport of the Levi modules of the plane cusp from level `N` to level `M`. -/
def planeLevTr :=
  levTr (Gamma_le_of_dvd hNM) (faceSplitting N h) (faceSplitting M h) (planeIota hNM h) (radScale (M / N))
    (plane_hinl hNM h (M / N) (Nat.mul_div_cancel' hNM).symm) (plane_hsplit hNM h) (faceRep N h n) (faceRep M h n) LinearMap.id (fun _ _ => rfl)

/-- The dual transport. -/
def planeLevTrDual :=
  levTr (Gamma_le_of_dvd hNM) (faceSplitting N h) (faceSplitting M h) (planeIota hNM h) (radScale (M / N))
    (plane_hinl hNM h (M / N) (Nat.mul_div_cancel' hNM).symm) (plane_hsplit hNM h) (dualRepG (faceRep N h n)) (dualRepG (faceRep M h n)) LinearMap.id
    (fun _ _ => rfl)

theorem planeClass_edge [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c) :
    planeMixedEdgeAt M h (faceRep M h n) (planeClass M h n hM (resLevel N M n hNM c) (zeroFlags_resLevel N M n hNM c hz)) =
      mapCusp (N := N) hM (Gamma_le_of_dvd hNM) (planeLevTr hNM h n)
        (planeMixedEdgeAt N h (faceRep N h n) (planeClass N h n hN.out c hz)) := by
  apply Subtype.ext
  exact edge_restrict (Gamma_le_of_dvd hNM) (faceSplitting N h) (faceSplitting M h) (planeIota hNM h) (radScale (M / N))
    (plane_hinl hNM h (M / N) (Nat.mul_div_cancel' hNM).symm) (plane_hsplit hNM h) (faceRep N h n)
    ⟨rPlane N n h c, res_radical_of_planeMixedAt (planeClass N h n hN.out c hz)⟩
    ⟨rPlane M n h (resLevel N M n hNM c), res_radical_of_planeMixedAt (planeClass M h n hM _ (zeroFlags_resLevel N M n hNM c hz))⟩
    (rPlane_resLevel hNM h n c)

theorem planeClassDual_edge [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (c' : groupCohomology.H2 (gammaNRepAllDual N n))
    (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c') :
    planeMixedEdgeAt M h (dualRepG (faceRep M h n))
        (planeClassDual M h n hM (resLevelDual n hNM c') (zeroFlags_resLevelDual n hNM c' hz')) =
      mapCusp (N := N) hM (Gamma_le_of_dvd hNM) (planeLevTrDual hNM h n)
        (planeMixedEdgeAt N h (dualRepG (faceRep N h n)) (planeClassDual N h n hN.out c' hz')) := by
  apply Subtype.ext
  exact edge_restrict (Gamma_le_of_dvd hNM) (faceSplitting N h) (faceSplitting M h) (planeIota hNM h) (radScale (M / N))
    (plane_hinl hNM h (M / N) (Nat.mul_div_cancel' hNM).symm) (plane_hsplit hNM h) (dualRepG (faceRep N h n))
    ⟨_, res_radical_of_planeMixedAt (planeClassDual N h n hN.out c' hz')⟩
    ⟨_, res_radical_of_planeMixedAt (planeClassDual M h n hM (resLevelDual n hNM c') (zeroFlags_resLevelDual n hNM c' hz'))⟩
    (rPlaneDual_resLevel hNM h n c')

/-- **Restriction of the canonical pairing at a plane face from level `N` to level `M`**:
`B_M(res a, res' b) = (M/N)² [Γ(N):Γ(M)] B_N(a, b)`. -/
theorem canAtClassP_restrict_card [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) [Fintype (Gamma N ⧸ subM N M)]
    (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (c' : groupCohomology.H2 (gammaNRepAllDual N n)) (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c') :
    canAtClassP M h n hM (resLevel N M n hNM c) (zeroFlags_resLevel N M n hNM c hz)
        (resLevelDual n hNM c') (zeroFlags_resLevelDual n hNM c' hz') =
      (((M / N : ℕ) : ℂ) ^ 2 * (Fintype.card (Gamma N ⧸ subM N M) : ℂ)) * canAtClassP N h n hN.out c hz c' hz' := by
  unfold canAtClassP canAtP
  rw [planeClass_edge hNM h n hM c hz, planeClassDual_edge hNM h n hM c' hz']
  have hD : radDet (radScale (M / N)) ≠ 0 := by
    rw [radDet_radScale]
    have : (M / N : ℕ) ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hNM)
      (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
    exact mul_ne_zero (by exact_mod_cast this) (by exact_mod_cast this)
  have key := facePairingCan_restrict (Gamma_le_of_dvd hNM) (faceSplitting N h) (faceSplitting M h) (planeIota hNM h)
    (radScale (M / N)) (plane_hinl hNM h (M / N) (Nat.mul_div_cancel' hNM).symm) (plane_hsplit hNM h) (faceRep N h n) (faceRep M h n) LinearMap.id
    (fun _ _ => rfl) hM LinearMap.id (fun _ _ => rfl) (fun _ _ => rfl)
    (planeFaceRadicalInput_det N h) (planeFaceRadicalInput_det M h) hD
  refine key _ _ |>.trans ?_
  rw [radDet_radScale]
  simp only [Int.cast_mul, Int.cast_natCast]
  ring

omit [NeZero N] in
theorem finite_quot_subM_plane (hN : 3 ≤ N) : Finite (Gamma N ⧸ subM N M) := by
  have : Fact (3 ≤ N) := ⟨hN⟩
  have : (Gamma M).FiniteIndex := inferInstance
  have h2 : (subM N M).FiniteIndex := inferInstanceAs (((Gamma M).subgroupOf (Gamma N)).FiniteIndex)
  exact Subgroup.finite_quotient_of_finiteIndex

/-- **The restriction identity at a plane face**: `B_M(res a, res' b) = [Γ_h(N) : Γ_h(M)] B_N(a, b)`. -/
theorem canAtClassP_restrict (hN : 3 ≤ N) (hM : 3 ≤ M)
    (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (c' : groupCohomology.H2 (gammaNRepAllDual N n)) (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c') :
    canAtClassP M h n hM (resLevel N M n hNM c) (zeroFlags_resLevel N M n hNM c hz)
        (resLevelDual n hNM c') (zeroFlags_resLevelDual n hNM c' hz') =
      (((gammaNPAt M h).relIndex (gammaNPAt N h) : ℕ) : ℂ) * canAtClassP N h n hN c hz c' hz' := by
  have : Fact (3 ≤ N) := ⟨hN⟩
  have := finite_quot_subM_plane (N := N) (M := M) hN
  let : Fintype (Gamma N ⧸ subM N M) := Fintype.ofFinite _
  rw [canAtClassP_restrict_card hNM h n hM c hz c' hz']
  congr 1
  rw [planeFace_relIndex_eq hN hNM h]
  have hc : Fintype.card (Gamma N ⧸ subM N M) = (Gamma M).relIndex (Gamma N) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hc]
  push_cast
  rfl

end LineCan

end TernaryPeriodPolynomials.Argument.LevelDescent
