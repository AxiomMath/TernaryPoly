module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.QDiAlignInst

@[expose] public section


/-!
# Bridging the frame-level pairing `canAtClass` and the pairing of `ConeFactorisation`

Formalized by Claude Sonnet 5.5.

For the representative `i.rep` of a line face of `Γ(N)`, `canAtClass N i.rep n hN c hz (toLiteralG c'.1) _ = pairQfaceCan n hN i (ξ_i) (qdiLitEquiv N n i ((dualRQ c') i))`
whenever `ξ_i ∈ 𝒞_{Q'_i}(E)` has `lineFaceCuspidalEmbedding ξ_i = rLine c` (`canAtClass_rep_eq_pairQ`).
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.EisensteinClass

section LineBridge

variable {N : ℕ} [NeZero N] (n : ℕ)

theorem mixedEdgeAt_lineClass (h : SL(3, ℤ)) (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (ξ : lineFaceCuspidal N h n) (hξ : lineFaceCuspidalEmbedding N h n ξ = rLine N n h c) :
    mixedEdgeAt N h (lineFaceRep N h n) (lineClass N h n hN c hz) = ξ := by
  have h1 : (lineFaceEdgeEquiv N h n).symm ξ.1 = ⟨rLine N n h c, res_radical_of_lineMixedAt (lineClass N h n hN c hz)⟩ :=
    Subtype.ext hξ
  have h2 := (lineFaceEdgeEquiv N h n).apply_symm_apply ξ.1
  rw [h1] at h2
  exact Subtype.ext h2

theorem edge_congr (h : SL(3, ℤ)) (W : Rep ℂ ↥(gammaNQAt N h)) {y y' : groupCohomology.H2 W} (hyy : y = y')
    (hy : twoCohomologyRestriction (lineFaceExt N h).inl W y = 0) (hy' : twoCohomologyRestriction (lineFaceExt N h).inl W y' = 0) :
    splitCohomologyEdge (lineFaceSplitting N h) W ⟨y, hy⟩ = splitCohomologyEdge (lineFaceSplitting N h) W ⟨y', hy'⟩ := by
  subst hyy; rfl

theorem mixedEdgeAt_lineClassDual (hN : 3 ≤ N) (hn : 4 ≤ n) (c' : Hd (N := N) (n := n) hn) (i : LineFaces N)
    (hz'' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (gammaNRepAllDual N n)
      (toLiteralG N n c'.1) = 0) :
    mixedEdgeAt N i.rep (dualRepG (lineFaceRep N i.rep n)) (lineClassDual N i.rep n hN (toLiteralG N n c'.1) hz'') =
      qdiLitEquiv N n i ((dualRQ hN hn c') i) := by
  have hmem : toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n (resLine i c'.1) ∈ dualCuspidalQLiteral N n i.rep :=
    Submodule.mem_map_of_mem (resLine_mem hN hn i c')
  apply Subtype.ext
  rw [qdiLitEquiv_dualRQ hN hn c' i hmem]
  refine edge_congr i.rep _ ?_ _ _
  exact (toLiteralG_res N n (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) c'.1).symm

end LineBridge

section Components

variable {N : ℕ} [NeZero N] (n : ℕ)

theorem lineEmb_component (c : groupCohomology.H2 (gammaNRepAll N n)) (ξQ : LineCuspSum N n)
    (hξQ : lineCuspSumEmbedding N n ξQ = lineBoundary N n c) (i : LineFaces N) :
    lineFaceCuspidalEmbedding N i.rep n (ξQ i) = rLine N n i.rep c := by
  have h1 := congrArg (fun x : LineFaceH2 N n => x i) hξQ
  simp only [lineCuspSumEmbedding, DirectSum.lmap_apply, lineBoundary_apply] at h1
  exact h1

theorem planeEmb_component (c : groupCohomology.H2 (gammaNRepAll N n)) (ξP : PlaneCuspSum N n)
    (hξP : planeCuspSumEmbedding N n ξP = planeBoundary N n c) (j : PlaneFaces N) :
    faceCuspidalEmbedding N n (planeFaceRepr j) (ξP j) = rPlane N n (planeFaceRepr j) c := by
  have h1 := congrArg (fun x : PlaneFaceH2 N n => x j) hξP
  simp only [planeCuspSumEmbedding, DirectSum.lmap_apply, planeBoundary_apply] at h1
  exact h1

theorem planeEdge_planeClass (h : SL(3, ℤ)) (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (ξ : faceCuspidal N h n) (hξ : faceCuspidalEmbedding N n h ξ = rPlane N n h c) :
    planeMixedEdgeAt N h (faceRep N h n) (planeClass N h n hN c hz) = ξ := by
  have h1 : (faceEdgeEquiv N n h).symm ξ.1 = ⟨rPlane N n h c, res_radical_of_planeMixedAt (planeClass N h n hN c hz)⟩ :=
    Subtype.ext hξ
  have h2 := (faceEdgeEquiv N n h).apply_symm_apply ξ.1
  rw [h1] at h2
  exact Subtype.ext h2

end Components

section Factor

variable {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]

/-- A linear map `Ψ` vanishing on the kernel of `R` factors through the whole target of `R`. -/
theorem exists_factor (R : X →ₗ[ℂ] Y) (Ψ : X →ₗ[ℂ] Z) (h : ∀ x, R x = 0 → Ψ x = 0) :
    ∃ ψ : Y →ₗ[ℂ] Z, ∀ x, ψ (R x) = Ψ x := by
  have hk : LinearMap.ker R ≤ LinearMap.ker Ψ := fun x hx => LinearMap.mem_ker.2 (h x (LinearMap.mem_ker.1 hx))
  let f : LinearMap.range R →ₗ[ℂ] Z := (Submodule.liftQ (LinearMap.ker R) Ψ hk) ∘ₗ (R.quotKerEquivRange.symm : LinearMap.range R →ₗ[ℂ] _)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨g, fun x => ?_⟩
  have : g (R x) = f ⟨R x, LinearMap.mem_range_self R x⟩ := by
    have := congrArg (fun φ => φ ⟨R x, LinearMap.mem_range_self R x⟩) hg
    exact this
  rw [this]
  have e : (R.quotKerEquivRange.symm ⟨R x, LinearMap.mem_range_self R x⟩) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  change Submodule.liftQ (LinearMap.ker R) Ψ hk (R.quotKerEquivRange.symm ⟨R x, _⟩) = _
  rw [e]; rfl

end Factor

section PlaneDual

variable {N : ℕ} [NeZero N] (n : ℕ)

theorem dualRP_apply_val (hn : 4 ≤ n) (c : Hd (N := N) (n := n) hn) (j : PlaneFaces N) :
    (dualRP hn c) j = resToC N n (ρ := dualRhoC N n) (gammaNPAt N (planeFaceRepr j)) (gammaNPAt_le N (planeFaceRepr j)) c.1 := by
  have e : (dualRP hn c) j = (∑ x : PlaneFaces N, DirectSum.lof ℂ (PlaneFaces N) (fun x => groupCohomology.H2 (Rep.of ((dualRhoC N n).comp
    (Subgroup.inclusion (gammaNPAt_le N (planeFaceRepr x)))))) x
      (resToC N n (ρ := dualRhoC N n) (gammaNPAt N (planeFaceRepr x)) (gammaNPAt_le N (planeFaceRepr x)) c.1)) j := by
    simp [dualRP]
  rw [e, DFinsupp.finsetSum_apply, Finset.sum_eq_single j]
  · simp [DirectSum.lof_apply]
  · intro x _ hx
    rw [DirectSum.lof_eq_of, DirectSum.of_apply, dite_eq_right hx]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem hdZero (hN : 3 ≤ N) (hn : 4 ≤ n) (c' : Hd (N := N) (n := n) hn) (g : SL(3, ℤ)) :
    twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (gammaNRepAllDual N n) (toLiteralG N n c'.1) = 0 := by
  obtain ⟨u, hu⟩ := c'.2
  exact HdLit_zeroFlags hN hn (toLiteralG N n c'.1) ⟨u, congrArg (toLiteralG N n) hu⟩ g

/-- The linear dual-plane pairing map: a linear map `ψ_j` from the `j`-th plane coordinate of `PDmod` to the cuspidal group of the literal Levi module, which on the plane restrictions of the classes
of `Hd` is the Hochschild-Serre edge of the literal dual class. -/
theorem exists_planeDualMap (hN : 3 ≤ N) (hn : 4 ≤ n) (j : PlaneFaces N) :
    ∃ ψ : groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNPAt_le N (planeFaceRepr j))))) →ₗ[ℂ]
        cuspidalSubspace (CongruenceSubgroup.Gamma N) (faceRadH1Lit N n (planeFaceRepr j)),
      ∀ c' : Hd (N := N) (n := n) hn, ψ ((dualRP hn c') j) =
        planeMixedEdgeAt N (planeFaceRepr j) (dualRepG (faceRep N (planeFaceRepr j) n))
          (planeClassDual N (planeFaceRepr j) n hN (toLiteralG N n c'.1) (hdZero n hN hn c')) := by
  let h := planeFaceRepr j
  let R : Hd (N := N) (n := n) hn →ₗ[ℂ] groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNPAt_le N h)))) :=
    (resToC N n (ρ := dualRhoC N n) (gammaNPAt N h) (gammaNPAt_le N h)).comp (Submodule.subtype _)
  let Ψ0 : Hd (N := N) (n := n) hn →ₗ[ℂ] groupCohomology.H2 (dualRepG (faceRep N h n)) :=
    (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp)) (gammaNRepAllDual N n)).comp
      ((toLiteralG N n).comp (Submodule.subtype _))
  have hmem : ∀ x, Ψ0 x ∈ planeMixedAt N h (dualRepG (faceRep N h n)) := fun x =>
    planeMixedAt_of_zeroFlags N h hN (gammaNRepAll N n).ρ.dual (toLiteralG N n x.1) (hdZero n hN hn x)
  let Ψ : Hd (N := N) (n := n) hn →ₗ[ℂ] cuspidalSubspace (CongruenceSubgroup.Gamma N) (faceRadH1Lit N n h) :=
    (planeMixedEdgeAt N h (dualRepG (faceRep N h n))).comp (Ψ0.codRestrict _ hmem)
  obtain ⟨ψ, hψ⟩ := exists_factor R Ψ (fun x hx => by
    have h1 : toLiteral (gammaNPAt N h) (gammaNPAt_le N h) n (resToC N n (ρ := dualRhoC N n) (gammaNPAt N h) (gammaNPAt_le N h) x.1) =
        Ψ0 x := (toLiteralG_res N n (gammaNPAt N h) (gammaNPAt_le N h) x.1)
    have h2 : Ψ0 x = 0 := by
      rw [← h1]
      have : resToC N n (ρ := dualRhoC N n) (gammaNPAt N h) (gammaNPAt_le N h) x.1 = 0 := hx
      rw [this, map_zero]
      rfl
    have : Ψ0.codRestrict _ hmem x = 0 := Subtype.ext h2
    change (planeMixedEdgeAt N h (dualRepG (faceRep N h n))) (Ψ0.codRestrict _ hmem x) = 0
    rw [this, map_zero])
  refine ⟨ψ, fun c' => ?_⟩
  have e : (dualRP hn c') j = R c' := dualRP_apply_val n hn c' j
  rw [e, hψ]
  rfl

end PlaneDual

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
