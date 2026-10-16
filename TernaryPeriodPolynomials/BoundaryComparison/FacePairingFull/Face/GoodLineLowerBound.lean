module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.GoodLineParabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneESDimension

@[expose] public section


/-!
# Lower bound for the locally inner classes at the good line

Every parabolic class of `H¹(GL₂(ℤ), Sym^{n+1})` is trivial at every rational cusp
(`Parabolic.vanishes_every_cusp_GL`), hence, through the Kostant isomorphism, a mixed cuspidal class of
the good line (`mem_faceCuspidal_goodLine_of`). This realizes the parabolic classes by locally inner
classes: `dim parabolicH1 (Sym^{n+1}) ≤ dim (locally inner classes at the good line)`
(`finrank_parabolic_le_goodLine_locallyInner`); this is the line-side realization needed for the
dimension count of the face pairing (the reverse inequality is the injectivity of the good-line edge).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep goodLineSplitting)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (parabolicH1 mem_parabolicH1_iff)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

variable (n : ℕ) (positive : 0 < n)

include positive in
theorem finiteDimensional_glAction :
    FiniteDimensional ℂ (CrossedH1 (glAction n)) := by
  have h1 : FiniteDimensional ℂ (groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) :=
    TernaryPeriodPolynomials.Spectral.LevelOneESDimension.arithmeticH1_finiteDimensional
      (n + 1) 0
  have h2 : FiniteDimensional ℂ (CrossedH1 (arithmeticBinaryRep (n + 1) 0).ρ) :=
    Module.Finite.equiv (h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)).symm
  exact Module.Finite.equiv (glPsi n positive).symm

theorem glTheta_symm_equivariant (l : GeneralLinearGroup (Fin 2) ℤ) (v : Binary.HomogeneousPoly (n + 1)) :
    (glTheta n positive).symm ((arithmeticBinaryRep (n + 1) 0).ρ l v) =
      glAction n l ((glTheta n positive).symm v) := by
  exact (glTheta n positive).symm_apply_eq.mpr
    ((congrArg ((arithmeticBinaryRep (n + 1) 0).ρ l)
      ((glTheta n positive).apply_symm_apply v).symm).trans
      (glTheta_equivariant n positive l _).symm)

/-- The crossed cocycle of the good line attached to a crossed cocycle of `Sym^{n+1}`. -/
def glLift (y : crossedCocycles (arithmeticBinaryRep (n + 1) 0).ρ) :
    crossedCocycles (glAction n) :=
  ⟨fun l => (glTheta n positive).symm (y.val l), fun a b => by
    have h : (glTheta n positive).symm (y.val (a * b)) =
        (glTheta n positive).symm (y.val a) +
          (glTheta n positive).symm ((arithmeticBinaryRep (n + 1) 0).ρ a (y.val b)) := by
      rw [y.property a b]
      exact map_add (glTheta n positive).symm _ _
    exact h.trans (congrArg _ (glTheta_symm_equivariant n positive a (y.val b)))⟩

theorem glPsi_glLift (y : crossedCocycles (arithmeticBinaryRep (n + 1) 0).ρ) :
    glPsi n positive ((crossedBoundaries (glAction n)).mkQ (glLift n positive y)) =
      (crossedBoundaries (arithmeticBinaryRep (n + 1) 0).ρ).mkQ y := by
  obtain ⟨y', hy', hΨ⟩ := glPsi_mk n positive (glLift n positive y)
  have hyy : y' = y := by
    apply Subtype.ext
    funext l
    rw [hy']
    exact (glTheta n positive).apply_symm_apply (y.val l)
  rw [hΨ, hyy]

/-- A cocycle trivial at `T` lifts to a mixed cuspidal class of the good line. -/
theorem glLift_mem_faceCuspidal (y : crossedCocycles (arithmeticBinaryRep (n + 1) 0).ρ)
    (hT : ∃ u, y.val Tgl = (arithmeticBinaryRep (n + 1) 0).ρ Tgl u - u) :
    (crossedBoundaries (glAction n)).mkQ (glLift n positive y) ∈
      (FaceCuspidal goodLineSplitting.conjAct n trivialCharacter goodLineFlag
        goodLineSemidirectEquivFixed : Submodule ℂ (CrossedH1 (glAction n))) := by
  apply mem_faceCuspidal_goodLine_of
  intro A
  rw [pullback_mk_eq_zero_iff]
  obtain ⟨w₀, hw₀⟩ := vanishes_every_cusp_GL (arithmeticBinaryRep (n + 1) 0).ρ y hT A
  refine ⟨(glTheta n positive).symm w₀, fun s => ?_⟩
  change (glTheta n positive).symm (y.val s.1) =
    glAction n s.1 ((glTheta n positive).symm w₀) - (glTheta n positive).symm w₀
  have e1 : (glTheta n positive).symm (y.val s.1) =
      (glTheta n positive).symm ((arithmeticBinaryRep (n + 1) 0).ρ s.1 w₀ - w₀) :=
    congrArg (glTheta n positive).symm (hw₀ s.1 s.2)
  refine e1.trans ((map_sub (glTheta n positive).symm _ _).trans ?_)
  exact congrArg (fun z => z - (glTheta n positive).symm w₀)
    (glTheta_symm_equivariant n positive s.1 w₀)

/-- A parabolic class gives a mixed cuspidal class of the good line. -/
theorem parabolic_mem_faceCuspidal (c : parabolicH1 (arithmeticBinaryRep (n + 1) 0)) :
    (glPsi n positive).symm ((h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)).symm c.val) ∈
      (FaceCuspidal goodLineSplitting.conjAct n trivialCharacter goodLineFlag
        goodLineSemidirectEquivFixed : Submodule ℂ (CrossedH1 (glAction n))) := by
  obtain ⟨x, ⟨u, hu⟩, hxc⟩ := (mem_parabolicH1_iff _ c.val).mp c.property
  have hmk : (glPsi n positive).symm ((h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)).symm c.val)
      = (crossedBoundaries (glAction n)).mkQ
        (glLift n positive (crossedOfCocycle (arithmeticBinaryRep (n + 1) 0) x)) := by
    rw [LinearEquiv.symm_apply_eq, glPsi_glLift]
    apply (h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hxc.symm
  rw [hmk]
  exact glLift_mem_faceCuspidal n positive _ ⟨u, hu⟩

/-- The realization of parabolic classes by locally inner classes of the good line. -/
def parabolicToGoodLine :
    parabolicH1 (arithmeticBinaryRep (n + 1) 0) →ₗ[ℂ]
      locallyInnerClasses n trivialCharacter .line goodLineFlag :=
  ((goodLineLocallyInnerEquiv n trivialCharacter).symm.toLinearMap).comp
    (LinearMap.codRestrict _
      (((glPsi n positive).symm.toLinearMap).comp
        ((h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)).symm.toLinearMap.comp
          (parabolicH1 (arithmeticBinaryRep (n + 1) 0)).subtype))
      (fun c => parabolic_mem_faceCuspidal n positive c))

theorem parabolicToGoodLine_injective : Function.Injective (parabolicToGoodLine n positive) := by
  intro c d h
  have h' := (goodLineLocallyInnerEquiv n trivialCharacter).symm.injective h
  have h'' := congrArg Subtype.val h'
  apply Subtype.ext
  exact (h1EquivCrossed _).symm.injective ((glPsi n positive).symm.injective h'')

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
