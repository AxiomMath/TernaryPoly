module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.PairingLifts
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Decomp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FaceCanonical
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FlagStabilizers
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FlagDictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.PropC5GammaN

@[expose] public section


/-!
# The Hochschild-Serre edge of a mixed class and the canonical pairing, at any frame of any level `Γ(N)`

Formalized by Claude Sonnet 5.5.

For `N ≥ 3`, a frame `h ∈ SL₃(ℤ)` and a representation `W` of the line group `Γ(N) ∩ h⁻¹Qh` (resp. plane group), `lineMixedAt N h W` (`planeMixedAt`) is the group of classes of `H²(·, W)` vanishing on the stabilizer of every
complete flag over the line (plane); `mixedEdgeAt` is its Hochschild-Serre edge in the cuspidal group of `H¹(N_R, W)` (the edge of a mixed class), and `canAt` the pairing of the `facePairingCan` on the edges.
`lineMixedAt_of_zeroFlags`: the restriction to the line group of a frame of a global class with zero flag restrictions is mixed (for every coefficient module).
`canAtClass` is the pairing of the restrictions to the frame `h` of a global class `c₀` of `H²(Γ(N), E_n)` and a global class `c₀'` of `H²(Γ(N), E_n^*)` with zero flag restrictions.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4

section Line

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ))

/-- **The mixed classes of the line cusp `h⁻¹Qh` of `Γ(N)`** with coefficients `W`: the classes vanishing on the stabilizer of every complete flag over the line. -/
def lineMixedAt (W : Rep ℂ ↥(gammaNQAt N h)) : Submodule ℂ (groupCohomology.H2 W) :=
  ⨅ F : GL (Fin 2) ℚ, LinearMap.ker (twoCohomologyRestriction (lineFlagStab N h F).subtype W)

variable {N h}

theorem lineMixedAt_apply {W : Rep ℂ ↥(gammaNQAt N h)} {x : groupCohomology.H2 W} (hx : x ∈ lineMixedAt N h W)
    (F : GL (Fin 2) ℚ) : twoCohomologyRestriction (lineFlagStab N h F).subtype W x = 0 :=
  LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hx F)

theorem res_radical_of_lineMixedAt {W : Rep ℂ ↥(gammaNQAt N h)} (x : lineMixedAt N h W) :
    twoCohomologyRestriction (lineFaceExt N h).inl W x.1 = 0 := by
  have h1 := lineMixedAt_apply x.2 1
  rw [lineFlagStab_contains_radical, FacePairing.twoCohomologyRestriction_comp, h1, map_zero]

theorem lineEdge_mem_cuspidal {W : Rep ℂ ↥(gammaNQAt N h)} (x : lineMixedAt N h W) :
    splitCohomologyEdge (lineFaceSplitting N h) W ⟨x.1, res_radical_of_lineMixedAt x⟩ ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma N) (splitRadicalH1Representation (lineFaceSplitting N h) W) := by
  have hB : ∀ (F : GL (Fin 2) ℚ) (V : Rep ℂ ↥(leviCuspStab (CongruenceSubgroup.Gamma N) F))
      (z : groupCohomology.H2 V), z = 0 := fun F V z =>
    LocallyInner.h2_zero_subgroup
      (fun A z => H2_vanish_level (CongruenceSubgroup.Gamma N) A z) _ V z
  exact (LocallyInner.edge_mem_cuspidalFamily_iff (lineFaceSplitting N h) W
    (leviCuspStab (CongruenceSubgroup.Gamma N)) hB x.1 (res_radical_of_lineMixedAt x)).mpr
      (fun F => lineMixedAt_apply x.2 F)

variable (N h)

/-- **The Hochschild-Serre edge of a mixed class of the line cusp `h⁻¹Qh`** (Step 3 of the factorisation of the cone pairing): `lineMixedAt N h W → 𝒞(H¹(N_{Q'}, W))`. -/
def mixedEdgeAt (W : Rep ℂ ↥(gammaNQAt N h)) : lineMixedAt N h W →ₗ[ℂ] cuspidalSubspace (CongruenceSubgroup.Gamma N)
    (splitRadicalH1Representation (lineFaceSplitting N h) W) where
  toFun x := ⟨splitCohomologyEdge (lineFaceSplitting N h) W ⟨x.1, res_radical_of_lineMixedAt x⟩, lineEdge_mem_cuspidal x⟩
  map_add' x y := Subtype.ext (by
    have := map_add (splitCohomologyEdge (lineFaceSplitting N h) W)
      ⟨x.1, res_radical_of_lineMixedAt x⟩ ⟨y.1, res_radical_of_lineMixedAt y⟩
    exact this)
  map_smul' a x := Subtype.ext (by
    have := map_smul (splitCohomologyEdge (lineFaceSplitting N h) W) a ⟨x.1, res_radical_of_lineMixedAt x⟩
    exact this)

theorem mixedEdgeAt_val (W : Rep ℂ ↥(gammaNQAt N h)) (x : lineMixedAt N h W) :
    ((mixedEdgeAt N h W x : cuspidalSubspace (CongruenceSubgroup.Gamma N)
      (splitRadicalH1Representation (lineFaceSplitting N h) W)) : groupCohomology.H1 (splitRadicalH1Representation (lineFaceSplitting N h) W)) =
      splitCohomologyEdge (lineFaceSplitting N h) W ⟨x.1, res_radical_of_lineMixedAt x⟩ := rfl

/-- **The canonical pairing of mixed classes of the line cusp `h⁻¹Qh`**: S2's `facePairingCan` on the Hochschild-Serre edges. -/
def canAt (hN : 3 ≤ N) (W : Rep ℂ ↥(gammaNQAt N h)) [FiniteDimensional ℂ W] (x : lineMixedAt N h W)
    (y : lineMixedAt N h (dualRepG W)) : ℂ :=
  facePairingCan hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) W (mixedEdgeAt N h W x) (mixedEdgeAt N h (dualRepG W) y)

/-- **A global class with zero flag restrictions restricts to a mixed class at every line cusp** (for every coefficient module). -/
theorem lineMixedAt_of_zeroFlags (hN : 3 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ ↥(gammaN N) V)
    (c : groupCohomology.H2 (Rep.of ρ))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (Rep.of ρ) c = 0) :
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp)) (Rep.of ρ) c ∈
      lineMixedAt N h (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp)) (Rep.of ρ)) := by
  refine (Submodule.mem_iInf _).2 (fun F => LinearMap.mem_ker.2 ?_)
  obtain ⟨g, hg⟩ := lineFlagStab_map_exists_gammaNBAt N hN h F
  have hmem : ∀ k : lineFlagStab N h F, ((k : gammaNQAt N h) : SL(3, ℤ)) ∈ gammaNBAt N (blockDiagQ g⁻¹ * h) := by
    intro k
    rw [← hg]
    exact ⟨k.1, k.2, rfl⟩
  let κ : lineFlagStab N h F →* gammaNBAt N (blockDiagQ g⁻¹ * h) :=
    ((gammaNQAt N h).subtype.comp (lineFlagStab N h F).subtype).codRestrict _ hmem
  exact res_res_eq_zero (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp))
    (lineFlagStab N h F).subtype (Subgroup.inclusion (gammaNBAt_le_gammaN N (blockDiagQ g⁻¹ * h))) κ
    (by ext; rfl) (Rep.of ρ) c (hz _)

variable (n : ℕ)

/-- The restriction to the line cusp `h⁻¹Qh` of a global class `c` of `H²(Γ(N), E_n)` with zero flag restrictions, as a mixed class. -/
def lineClass (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c) :
    lineMixedAt N h (lineFaceRep N h n) :=
  ⟨rLine N n h c, lineMixedAt_of_zeroFlags N h hN (gammaNRepAll N n).ρ c hz⟩

/-- The restriction to the line cusp `h⁻¹Qh` of a global class `c'` of `H²(Γ(N), E_n^*)` with zero flag restrictions, as a mixed class. -/
def lineClassDual (hN : 3 ≤ N) (c' : groupCohomology.H2 (gammaNRepAllDual N n))
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (gammaNRepAllDual N n) c' = 0) :
    lineMixedAt N h (dualRepG (lineFaceRep N h n)) :=
  ⟨twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp)) (gammaNRepAllDual N n) c',
    lineMixedAt_of_zeroFlags N h hN (gammaNRepAll N n).ρ.dual c' hz'⟩

/-- **The canonical pairing, at the frame `h`, of the line restrictions of global classes `c₀`, `c₀'` of `H²(Γ(N), E_n)`, `H²(Γ(N), E_n^*)` with zero flag restrictions.** -/
def canAtClass (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (c' : groupCohomology.H2 (gammaNRepAllDual N n))
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (gammaNRepAllDual N n) c' = 0) : ℂ :=
  canAt N h hN (lineFaceRep N h n) (lineClass N h n hN c hz) (lineClassDual N h n hN c' hz')

end Line


section Plane

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ))

/-- **The mixed classes of the plane cusp `h⁻¹Ph` of `Γ(N)`** with coefficients `W`. -/
def planeMixedAt (W : Rep ℂ ↥(gammaNPAt N h)) : Submodule ℂ (groupCohomology.H2 W) :=
  ⨅ F : GL (Fin 2) ℚ, LinearMap.ker (twoCohomologyRestriction (faceFlagStab N h F).subtype W)

variable {N h}

theorem planeMixedAt_apply {W : Rep ℂ ↥(gammaNPAt N h)} {x : groupCohomology.H2 W} (hx : x ∈ planeMixedAt N h W)
    (F : GL (Fin 2) ℚ) : twoCohomologyRestriction (faceFlagStab N h F).subtype W x = 0 :=
  LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hx F)

theorem res_radical_of_planeMixedAt {W : Rep ℂ ↥(gammaNPAt N h)} (x : planeMixedAt N h W) :
    twoCohomologyRestriction (faceExt N h).inl W x.1 = 0 := by
  have h1 := planeMixedAt_apply x.2 1
  have hcomp : (faceExt N h).inl = (faceFlagStab N h 1).subtype.comp (faceInlFlag N h 1) := rfl
  rw [hcomp, FacePairing.twoCohomologyRestriction_comp, h1, map_zero]

theorem planeEdge_mem_cuspidal {W : Rep ℂ ↥(gammaNPAt N h)} (x : planeMixedAt N h W) :
    splitCohomologyEdge (faceSplitting N h) W ⟨x.1, res_radical_of_planeMixedAt x⟩ ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma N) (splitRadicalH1Representation (faceSplitting N h) W) := by
  have hB : ∀ (F : GL (Fin 2) ℚ) (V : Rep ℂ ↥(leviCuspStab (CongruenceSubgroup.Gamma N) F))
      (z : groupCohomology.H2 V), z = 0 := fun F V z =>
    LocallyInner.h2_zero_subgroup
      (fun A z => H2_vanish_level (CongruenceSubgroup.Gamma N) A z) _ V z
  exact (LocallyInner.edge_mem_cuspidalFamily_iff (faceSplitting N h) W
    (leviCuspStab (CongruenceSubgroup.Gamma N)) hB x.1 (res_radical_of_planeMixedAt x)).mpr
      (fun F => planeMixedAt_apply x.2 F)

variable (N h)

/-- **The Hochschild-Serre edge of a mixed class of the plane cusp `h⁻¹Ph`.** -/
def planeMixedEdgeAt (W : Rep ℂ ↥(gammaNPAt N h)) : planeMixedAt N h W →ₗ[ℂ] cuspidalSubspace (CongruenceSubgroup.Gamma N)
    (splitRadicalH1Representation (faceSplitting N h) W) where
  toFun x := ⟨splitCohomologyEdge (faceSplitting N h) W ⟨x.1, res_radical_of_planeMixedAt x⟩, planeEdge_mem_cuspidal x⟩
  map_add' x y := Subtype.ext (by
    have := map_add (splitCohomologyEdge (faceSplitting N h) W)
      ⟨x.1, res_radical_of_planeMixedAt x⟩ ⟨y.1, res_radical_of_planeMixedAt y⟩
    exact this)
  map_smul' a x := Subtype.ext (by
    have := map_smul (splitCohomologyEdge (faceSplitting N h) W) a ⟨x.1, res_radical_of_planeMixedAt x⟩
    exact this)

theorem planeMixedEdgeAt_val (W : Rep ℂ ↥(gammaNPAt N h)) (x : planeMixedAt N h W) :
    ((planeMixedEdgeAt N h W x : cuspidalSubspace (CongruenceSubgroup.Gamma N)
      (splitRadicalH1Representation (faceSplitting N h) W)) : groupCohomology.H1 (splitRadicalH1Representation (faceSplitting N h) W)) =
      splitCohomologyEdge (faceSplitting N h) W ⟨x.1, res_radical_of_planeMixedAt x⟩ := rfl

/-- **The canonical pairing of mixed classes of the plane cusp `h⁻¹Ph`.** -/
def canAtP (hN : 3 ≤ N) (W : Rep ℂ ↥(gammaNPAt N h)) [FiniteDimensional ℂ W] (x : planeMixedAt N h W)
    (y : planeMixedAt N h (dualRepG W)) : ℂ :=
  facePairingCan hN (faceSplitting N h) (planeFaceRadicalInput_det N h) W (planeMixedEdgeAt N h W x) (planeMixedEdgeAt N h (dualRepG W) y)

/-- **A global class with zero flag restrictions restricts to a mixed class at every plane cusp.** -/
theorem planeMixedAt_of_zeroFlags (hN : 3 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ ↥(gammaN N) V)
    (c : groupCohomology.H2 (Rep.of ρ))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (Rep.of ρ) c = 0) :
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp)) (Rep.of ρ) c ∈
      planeMixedAt N h (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp)) (Rep.of ρ)) := by
  refine (Submodule.mem_iInf _).2 (fun F => LinearMap.mem_ker.2 ?_)
  obtain ⟨g, hg⟩ := faceFlagStab_map_exists_gammaNBAt N hN h F
  have hmem : ∀ k : faceFlagStab N h F, ((k : gammaNPAt N h) : SL(3, ℤ)) ∈ gammaNBAt N (blockDiag g⁻¹ * h) := by
    intro k
    rw [← hg]
    exact ⟨k.1, k.2, rfl⟩
  let κ : faceFlagStab N h F →* gammaNBAt N (blockDiag g⁻¹ * h) :=
    ((gammaNPAt N h).subtype.comp (faceFlagStab N h F).subtype).codRestrict _ hmem
  exact res_res_eq_zero (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp))
    (faceFlagStab N h F).subtype (Subgroup.inclusion (gammaNBAt_le_gammaN N (blockDiag g⁻¹ * h))) κ
    (by ext; rfl) (Rep.of ρ) c (hz _)

variable (n : ℕ)

/-- The restriction to the plane cusp `h⁻¹Ph` of a global class `c` of `H²(Γ(N), E_n)` with zero flag restrictions, as a mixed class. -/
def planeClass (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c) :
    planeMixedAt N h (faceRep N h n) :=
  ⟨rPlane N n h c, planeMixedAt_of_zeroFlags N h hN (gammaNRepAll N n).ρ c hz⟩

/-- The restriction to the plane cusp `h⁻¹Ph` of a global class `c'` of `H²(Γ(N), E_n^*)` with zero flag restrictions, as a mixed class. -/
def planeClassDual (hN : 3 ≤ N) (c' : groupCohomology.H2 (gammaNRepAllDual N n))
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (gammaNRepAllDual N n) c' = 0) :
    planeMixedAt N h (dualRepG (faceRep N h n)) :=
  ⟨twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp)) (gammaNRepAllDual N n) c',
    planeMixedAt_of_zeroFlags N h hN (gammaNRepAll N n).ρ.dual c' hz'⟩

/-- **The canonical pairing, at the plane frame `h`, of the plane restrictions of global classes `c`, `c'` with zero flag restrictions.** -/
def canAtClassP (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (c' : groupCohomology.H2 (gammaNRepAllDual N n))
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (gammaNRepAllDual N n) c' = 0) : ℂ :=
  canAtP N h hN (faceRep N h n) (planeClass N h n hN c hz) (planeClassDual N h n hN c' hz')

end Plane

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
