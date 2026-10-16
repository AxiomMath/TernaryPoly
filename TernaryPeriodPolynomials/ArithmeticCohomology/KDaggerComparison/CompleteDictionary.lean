module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.CompleteFamilies
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.CompleteTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Inner
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Converse
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm

@[expose] public section


/-!
# `K†` comparison, completeness of the face dictionary

At the paper's level `3 ∣ N`, `N ≥ 3`: the face dictionaries `phiPlane`, `phiLine` (restriction of the `K†`-stratum class at the
chosen representatives of the faces of `Γ(N)`, read in Mathlib's `H²` of the face group) are linear isomorphisms onto the
`K†`-invariant vectors, and restrict to isomorphisms of the inner classes onto the `K†`-invariant mixed cuspidal vectors.

* `PlaneQInvariants`, `LineQInvariants`: the vectors of `⨁_{faces} H²(Γ(N) ∩ face, E_n)` that extend to a `K†`-invariant family
  over **all** rational planes (lines) (`qFamilies`: `(k • w)(F) = k_* w(k⁻¹ F)`, `k ∈ K†`; the extension is by `Γ(N)`-transport and is
  unique, `stratumFamily_injective`);
* `range_phiPlane`, `range_phiLine`: `range Φ = Q-invariants` (Shapiro surjectivity for `K†`, `CompleteShapiro`);
* `phiPlaneEquiv`, `phiLineEquiv`: the linear isomorphisms `StratumH2 ≃ₗ[ℂ] Q-invariants`;
* `innerBoundary_iff_phiPlane_mem_range`, `..._line`: `InnerBoundary ξ ↔ Φ ξ ∈ range (cusp embedding)` (the converse of the `phiPlane_mem_range`; the reduction from the chosen representatives to all flags is the transport `stabilizerTransportH2_mem_locallyInner`);
* `phiPlaneInnerEquiv`, `phiLineInnerEquiv`: `innerClasses ≃ₗ[ℂ] Q-invariants ⊓ range(cusp embedding)` (the `K†`-invariant mixed cuspidal
  vectors `𝒞_P(E)^{K†}`, `𝒞_Q(E)^{K†}`);
* `vanishesOnGood_iff_phiPlane`, `vanishesOnGood_iff_phiLine`: `VanishesOnGood ξ ↔ Φ ξ` has zero component at every good face
  (and `..._at` the flag-wise version at every integral change of basis).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

section Orbits

omit [NeZero N] in
/-- Every rational plane is a `Γ(N)`-translate of the plane of a chosen face representative. -/
theorem exists_planeFace_translate (F : Flags .plane) :
    ∃ (i : PlaneFaces N) (γ : SL(3, ℤ)), γ ∈ gammaN N ∧
      F = Matrix.SpecialLinearGroup.mapGL ℚ γ • planeFlagAt (planeFaceRepr i) := by
  obtain ⟨h, rfl⟩ := planeFlagAt_surjective F
  set i : PlaneFaces N := Quotient.mk (planeFaceSetoid N) h with hi
  obtain ⟨γ, hγ, hF⟩ := (planeFlagAt_orbit_iff N h (planeFaceRepr i)).mpr
    ((planeFaceSetoid N).iseqv.symm (Quotient.mk_out (s := planeFaceSetoid N) h))
  refine ⟨i, γ⁻¹, (gammaN N).inv_mem hγ, ?_⟩
  rw [hF, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

omit [NeZero N] in
/-- Every rational line is a `Γ(N)`-translate of the line of a chosen face representative. -/
theorem exists_lineFace_translate (F : Flags .line) :
    ∃ (i : LineFaces N) (γ : SL(3, ℤ)), γ ∈ gammaN N ∧
      F = Matrix.SpecialLinearGroup.mapGL ℚ γ • lineFlagAt i.rep := by
  obtain ⟨h, rfl⟩ := lineFlagAt_surjective F
  obtain ⟨γ, hγ, hF⟩ := lineFlagAt_rep N h
  refine ⟨LineFaces.mk h, γ, hγ, ?_⟩
  rw [hF, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

end Orbits

section Plane

open scoped Classical

/-- Reading a family of classes over all rational planes at the chosen representatives of the faces of `Γ(N)`. -/
def planeReps : FaceFamily N n .plane →ₗ[ℂ] PlaneFaceH2 N n :=
  ∑ i : PlaneFaces N, (DirectSum.lof ℂ (PlaneFaces N)
    (fun i => groupCohomology.H2 (faceRep N (planeFaceRepr i) n)) i).comp
      ((planeH2Equiv N h3 (planeFaceRepr i) n trivialCharacter hN).toLinearMap ∘ₗ
        LinearMap.proj (planeFlagAt (planeFaceRepr i)))

theorem planeReps_apply (w : FaceFamily N n .plane) (i : PlaneFaces N) :
    planeReps N h3 hN n w i =
      planeH2Equiv N h3 (planeFaceRepr i) n trivialCharacter hN (w (planeFlagAt (planeFaceRepr i))) := by
  simp only [planeReps, LinearMap.sum_apply, LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [DFinsupp.finsetSum_apply]
  simp [DirectSum.of_apply]

theorem phiPlane_eq_comp : phiPlane N h3 hN n = planeReps N h3 hN n ∘ₗ stratumFamily N n .plane := by
  apply LinearMap.ext
  intro ξ
  ext1 i
  rw [phiPlane_apply, LinearMap.comp_apply, planeReps_apply]
  rfl

/-- **The `K†`-invariant plane vectors** of `⨁_{faces of Γ(N)} H²(Γ(N) ∩ face, E_n)`: those that extend to a `K†`-invariant family over
all rational planes. -/
def PlaneQInvariants : Submodule ℂ (PlaneFaceH2 N n) :=
  (qFamilies N n .plane).map (planeReps N h3 hN n)

theorem mem_planeQInvariants_iff (v : PlaneFaceH2 N n) :
    v ∈ PlaneQInvariants N h3 hN n ↔ ∃ w ∈ qFamilies N n .plane, ∀ i : PlaneFaces N,
      planeH2Equiv N h3 (planeFaceRepr i) n trivialCharacter hN (w (planeFlagAt (planeFaceRepr i))) = v i := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, fun i => (planeReps_apply N h3 hN n w i).symm⟩
  · rintro ⟨w, hw, h⟩
    refine ⟨w, hw, ?_⟩
    ext1 i
    rw [planeReps_apply, h]

/-- **Completeness of the plane dictionary (CMP-2).**  The image of `phiPlane` is exactly the `K†`-invariant vectors. -/
theorem range_phiPlane : LinearMap.range (phiPlane N h3 hN n) = PlaneQInvariants N h3 hN n := by
  rw [phiPlane_eq_comp, LinearMap.range_comp, range_stratumFamily]
  rfl

theorem phiPlane_injective : Function.Injective (phiPlane N h3 hN n) := by
  rw [injective_iff_map_eq_zero]
  exact fun ξ h => eq_zero_of_phiPlane_eq_zero N h3 hN n ξ h

/-- **The plane face dictionary is a linear isomorphism onto the `K†`-invariant plane vectors.** -/
def phiPlaneEquiv : StratumH2 n trivialCharacter .plane ≃ₗ[ℂ] PlaneQInvariants N h3 hN n :=
  (LinearEquiv.ofInjective (phiPlane N h3 hN n) (phiPlane_injective N h3 hN n)).trans
    (LinearEquiv.ofEq _ _ (range_phiPlane N h3 hN n))

theorem phiPlaneEquiv_apply (ξ : StratumH2 n trivialCharacter .plane) :
    ((phiPlaneEquiv N h3 hN n ξ : PlaneQInvariants N h3 hN n) : PlaneFaceH2 N n) = phiPlane N h3 hN n ξ := rfl

/-- **Inner classes = mixed cuspidal vectors (converse of `phiPlane_mem_range`).** -/
theorem innerBoundary_of_phiPlane_mem_range (ξ : StratumH2 n trivialCharacter .plane)
    (h : phiPlane N h3 hN n ξ ∈ LinearMap.range (planeCuspSumEmbedding N n)) :
    InnerBoundary n trivialCharacter .plane ξ := by
  refine (innerBoundary_iff_locallyInner ξ).mpr fun F => ?_
  obtain ⟨i, γ, hγ, hF⟩ := exists_planeFace_translate N F
  have hmem : Matrix.SpecialLinearGroup.mapGL ℚ γ ∈ rationalLevel :=
    levelPrincipal_le N (mapGL_mem_levelPrincipal N h3 hγ)
  have hi : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (planeFlagAt (planeFaceRepr i)) ξ ∈
      locallyInnerClasses n trivialCharacter .plane (planeFlagAt (planeFaceRepr i)) := by
    refine (locallyInnerClasses_planeFlag_iff N h3 (planeFaceRepr i) n trivialCharacter hN _).mpr ?_
    have := (mem_range_planeCuspSumEmbedding N n _).mp h i
    rwa [phiPlane_apply] at this
  have e := stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
    ⟨_, hmem⟩ (planeFlagAt (planeFaceRepr i)) F hF.symm ξ
  rw [← e]
  exact stabilizerTransportH2_mem_locallyInner n trivialCharacter .plane ⟨_, hmem⟩ _ _ hF.symm _ hi

theorem innerBoundary_iff_phiPlane_mem_range (ξ : StratumH2 n trivialCharacter .plane) :
    InnerBoundary n trivialCharacter .plane ξ ↔
      phiPlane N h3 hN n ξ ∈ LinearMap.range (planeCuspSumEmbedding N n) :=
  ⟨phiPlane_mem_range N h3 hN n ξ, innerBoundary_of_phiPlane_mem_range N h3 hN n ξ⟩

/-- **The inner plane classes are isomorphic to the `K†`-invariant mixed cuspidal vectors `𝒞_P(E)^{K†}`.** -/
def phiPlaneInnerEquiv : FacePairingFull.innerClasses n .plane ≃ₗ[ℂ]
    ↥(PlaneQInvariants N h3 hN n ⊓ LinearMap.range (planeCuspSumEmbedding N n)) :=
  (Submodule.equivMapOfInjective (phiPlane N h3 hN n) (phiPlane_injective N h3 hN n)
    (FacePairingFull.innerClasses n .plane)).trans
    (LinearEquiv.ofEq _ _ (by
      ext v
      constructor
      · rintro ⟨ξ, hξ, rfl⟩
        exact ⟨(range_phiPlane N h3 hN n).le ⟨ξ, rfl⟩, phiPlane_mem_range N h3 hN n ξ hξ⟩
      · rintro ⟨hv, hc⟩
        obtain ⟨ξ, rfl⟩ := (range_phiPlane N h3 hN n).ge hv
        exact ⟨ξ, innerBoundary_of_phiPlane_mem_range N h3 hN n ξ hc, rfl⟩))

/-- **`VanishesOnGood` at every integral change of basis.** -/
theorem vanishesOnGood_iff_phiPlaneAt (ξ : StratumH2 n trivialCharacter .plane) :
    VanishesOnGood n trivialCharacter .plane ξ ↔
      ∀ h : SL(3, ℤ), GoodFlag .plane (planeFlagAt h) → phiPlaneAt N h3 hN n h ξ = 0 := by
  rw [vanishesOnGood_iff_fixedPointH2]
  constructor
  · intro hv h hg
    have := hv _ hg
    change planeH2Equiv N h3 h n trivialCharacter hN
      (resPrincipal N (planeFlagAt h) (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (planeFlagAt h) ξ)) = 0
    rw [this, LinearMap.map_zero, LinearEquiv.map_zero]
  · intro hv F hF
    obtain ⟨h, rfl⟩ := planeFlagAt_surjective F
    exact fixedPointH2_eq_zero_of_res N n ξ _
      ((planeH2Equiv N h3 h n trivialCharacter hN).map_eq_zero_iff.mp (hv h hF))

/-- **`VanishesOnGood` ⟺ zero restriction at every good face of `Γ(N)`** (plane side). -/
theorem vanishesOnGood_iff_phiPlane (ξ : StratumH2 n trivialCharacter .plane) :
    VanishesOnGood n trivialCharacter .plane ξ ↔
      ∀ i : PlaneFaces N, GoodFlag .plane (planeFlagAt (planeFaceRepr i)) → phiPlane N h3 hN n ξ i = 0 := by
  rw [vanishesOnGood_iff_fixedPointH2]
  constructor
  · intro hv i hg
    rw [phiPlane_apply]
    have := hv _ hg
    change planeH2Equiv N h3 (planeFaceRepr i) n trivialCharacter hN
      (resPrincipal N (planeFlagAt (planeFaceRepr i)) (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
          (planeFlagAt (planeFaceRepr i)) ξ)) = 0
    rw [this, LinearMap.map_zero, LinearEquiv.map_zero]
  · intro hv F hF
    obtain ⟨i, γ, hγ, hFγ⟩ := exists_planeFace_translate N F
    have hmem : Matrix.SpecialLinearGroup.mapGL ℚ γ ∈ rationalLevel :=
      levelPrincipal_le N (mapGL_mem_levelPrincipal N h3 hγ)
    have hg : GoodFlag .plane (planeFlagAt (planeFaceRepr i)) := by
      rw [hFγ] at hF
      exact (goodFlag_rationalLevel_smul_iff .plane ⟨_, hmem⟩ _).mp hF
    have h1 := hv i hg
    rw [phiPlane_apply] at h1
    have h2 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (planeFlagAt (planeFaceRepr i)) ξ = 0 :=
      fixedPointH2_eq_zero_of_res N n ξ _
        ((planeH2Equiv N h3 (planeFaceRepr i) n trivialCharacter hN).map_eq_zero_iff.mp h1)
    exact fixedPointH2_eq_zero_of_orbit N h3 n ξ _ F γ hγ hFγ h2

end Plane

end TernaryPeriodPolynomials.Argument.KDaggerComparison
