module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Edge
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.LinearFamilies
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceSmooth

@[expose] public section


/-!
# Finite weights of the plane section

`PlaneWeight ι`: a function `ι` on `G(A)` that depends only on the finite part, is right invariant under the finite
level and left invariant under the adelic plane parabolic (`ι = 1`: the spherical plane section; `ι` = indicator of
`P(ℚ₃) K₁(3)`: the bad-plane section, the library's `LocalThreePlaneSupport` set).  The plane source cocycle weighted
by `ι` is again a source cocycle (`isSourceCocycle_smul_weight`), and the class identification of the integral cochain
with the source (R-b) holds for the `ι`-weighted cochains (`sourceToSummand_cOmega_eq_planeSource_weight`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.AnalyticClasses

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- **A finite weight of the plane section**: depends only on the finite part, is right invariant under the finite
level and left invariant under the adelic plane parabolic (`1` for the spherical section, the indicator of
`P(ℚ₃) K₁(3)` for the bad-plane section). -/
structure PlaneWeight (ι : AdelicGL → ℂ) : Prop where
  finite : ∀ g g' : AdelicGL, finiteGroup g = finiteGroup g' → ι g = ι g'
  level : ∀ (k : finiteLevel) (g : AdelicGL), ι (g * atFinite k.val) = ι g
  parabolic : ∀ p : AdelicGL, p ∈ planeParabolic Adeles → ∀ g : AdelicGL, ι (p * g) = ι g

namespace PlaneWeight

variable {ι : AdelicGL → ℂ} (hι : PlaneWeight ι)

include hι

theorem atInfinity (g : AdelicGL) (z : RealGL3) : ι (g * atInfinity z) = ι g :=
  hι.finite _ _ (finiteGroup_mul_atInfinity g z)

theorem planeLevi_left (A : BinaryAdelicGL) (t : Adelesˣ) (g : AdelicGL) :
    ι (GeneralEisenstein.Adelic.planeLevi A t * g) = ι g :=
  hι.parabolic _ (GeneralEisenstein.Adelic.planeLevi_mem A t) g

theorem planeUnipotent_left (a b : Adeles) (g : AdelicGL) :
    ι (GeneralEisenstein.Adelic.planeUnipotent a b * g) = ι g :=
  hι.parabolic _ (planeUnipotent_mem' a b) g

end PlaneWeight

theorem hasSmoothCuspLift_weight {n k : ℕ} (D : InducingData n) {ι : AdelicGL → ℂ} (hι : PlaneWeight ι)
    (s : ℂ) (f : (Fin k → RealGL3) → AdelicGL → ℂ) (hf : HasSmoothCuspLift D .plane s f) :
    HasSmoothCuspLift D .plane s (fun x g => ι g * f x g) := by
  intro a
  obtain ⟨v, hv, hr⟩ := hf a
  refine ⟨fun x => ι a • v x, LinearFamilies.smooth_smul (ι a) _ hv, fun x A => ?_⟩
  have hlev : ι (binaryLevi .plane A * (a * atInfinity (x (Fin.last k)))) = ι a := by
    show ι (GeneralEisenstein.Adelic.planeLevi A 1 * (a * atInfinity (x (Fin.last k)))) = ι a
    rw [hι.planeLevi_left, hι.atInfinity]
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hr x A]
  show ι a * (_ * f _ _) = _ * (ι _ * f _ _)
  rw [hlev]
  ring

/-- **Multiplying a plane source cocycle by a finite plane weight keeps it a source cocycle.** -/
theorem isSourceCocycle_smul_weight {n : ℕ} (D : InducingData n) {ι : AdelicGL → ℂ} (hι : PlaneWeight ι)
    (c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n) (hc : IsSourceCocycle D .plane c) :
    IsSourceCocycle D .plane (fun y g => ι g • c y g) := by
  have coe : ∀ y g m, ((ι g • c y g : HomogeneousPoly n) : Poly).coeff m = ι g * ((c y g).val.coeff m) := by
    intro y g m
    rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  refine ⟨fun y m => ?_, fun m => ?_, fun h y g => ?_, fun y g => ?_⟩
  · obtain ⟨sm, lev, lift, unip, tor, cusp⟩ := hc.1 y m
    simp only [coe]
    simp only [] at sm lev lift unip tor cusp
    refine ⟨fun g => ?_, fun k g => ?_, hasSmoothCuspLift_weight D hι _ _ lift, fun a b g => ?_,
      fun t g => ?_, fun g => ?_⟩
    · refine HeckeTranslate.SmoothClosure.smooth_congr (f := fun x : Fin 1 → RealGL3 => ι g * (c y (g * atInfinity (x 0))).val.coeff m)
        (smooth_mul_complex (smooth_const_complex (ι g)) (sm g)) (fun x => ?_)
      dsimp only
      rw [hι.atInfinity]
    · dsimp only
      rw [hι.level, lev]
    · dsimp only
      rw [hι.planeUnipotent_left, unip]
    · dsimp only
      rw [hι.planeLevi_left, tor]; ring
    · have h := cusp g
      have : (fun A : BinaryAdelicGL =>
          normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2 + inductionExponent .plane cohomologicalPoint)) *
            (ι (GeneralEisenstein.Adelic.planeLevi A 1 * g) *
              (c y (GeneralEisenstein.Adelic.planeLevi A 1 * g)).val.coeff m)) =
          ι g • (fun A : BinaryAdelicGL =>
          normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2 + inductionExponent .plane cohomologicalPoint)) *
            (c y (GeneralEisenstein.Adelic.planeLevi A 1 * g)).val.coeff m) := by
        funext A
        rw [hι.planeLevi_left]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      show (fun A : BinaryAdelicGL =>
          normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2 + inductionExponent .plane cohomologicalPoint)) *
            (ι (GeneralEisenstein.Adelic.planeLevi A 1 * g) *
              (c y (GeneralEisenstein.Adelic.planeLevi A 1 * g)).val.coeff m)) ∈ cuspFunctions D.cusp
      rw [this]
      exact (cuspFunctions D.cusp).smul_mem _ h
  · simp only [coe]
    exact hasSmoothCuspLift_weight D hι _ _ (hc.2.1 m)
  · show ι g • c (fun i => h * y i) g =
      realCoefficientComponent n D.chi h (ι (g * atInfinity h) • c y (g * atInfinity h))
    rw [hc.2.2.1, hι.atInfinity, map_smul]
  · have := hc.2.2.2 y g
    show ι g • c ![y 1, y 2, y 3] g - ι g • c ![y 0, y 2, y 3] g + ι g • c ![y 0, y 1, y 3] g -
      ι g • c ![y 0, y 1, y 2] g = 0
    calc _ = ι g • (c ![y 1, y 2, y 3] g - c ![y 0, y 2, y 3] g + c ![y 0, y 1, y 3] g -
          c ![y 0, y 1, y 2] g) := by simp only [smul_sub, smul_add]
      _ = 0 := by rw [this, smul_zero]

theorem rationalGroup_mem_planeParabolic (p : RationalGL3) (hp : p ∈ parabolic Side.plane) :
    rationalGroup p ∈ planeParabolic Adeles :=
  SphericalDetection.Helpers.generalLinearGroup_map_plane rationalAdele ⟨p, hp⟩

section Weighted

variable {n : ℕ} (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
  (hol : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
  (E : LeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormal n F A)
  (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
  {ι : AdelicGL → ℂ} (hι : PlaneWeight ι)

include hol hE hc hχ hι

/-- **R-b with the finite weight `ι`**: `ι · cOmega` and `ι · planeSource` define the same class. -/
theorem sourceToSummand_cOmega_eq_planeSource_weight
    (hRa : IsSourceCocycle D Side.plane (fun y g => ι g • cOmega n D F y g)) :
    SourceQuotient.sourceToSummand D Side.plane ⟨fun y g => ι g • cOmega n D F y g, hRa⟩ =
      SourceQuotient.sourceToSummand D Side.plane
        ⟨fun y g => ι g • planeSource D E y g,
          isSourceCocycle_smul_weight D hι _ (planeSource_isSourceCocycle D E hχ)⟩ :=
  sourceToSummand_eq_of_edge D Side.plane _ _ hRa
    (isSourceCocycle_smul_weight D hι _ (planeSource_isSourceCocycle D E hχ))
    (fun y g => ι g • planeEdge D F hol y g)
    (fun y g => by
      show ι g • cOmega n D F y g - ι g • planeSource D E y g = _
      have h := congrArg (fun P : HomogeneousPoly n => ι g • P)
        (cOmega_sub_planeSource D F hol E hE hc hχ y g)
      simpa only [smul_sub, smul_add] using h)
    (fun h y g => by
      show ι g • planeEdge D F hol (fun i => h * y i) g =
        realCoefficientComponent n D.chi h (ι (g * atInfinity h) • planeEdge D F hol y (g * atInfinity h))
      rw [planeEdge_cov D F hol E hE hc hχ h y g, hι.atInfinity, map_smul])
    (fun k y g => by
      show ι (g * atFinite k.val) • planeEdge D F hol y (g * atFinite k.val) = ι g • planeEdge D F hol y g
      rw [hι.level, planeEdge_level D F hol E hE hc hχ k y g])
    (fun p hp y g => by
      show ι (rationalGroup p * g) • planeEdge D F hol y (rationalGroup p * g) = ι g • planeEdge D F hol y g
      rw [hι.parabolic _ (rationalGroup_mem_planeParabolic p hp), planeEdge_parabolic D F hol E hE hc hχ p hp y g])

end Weighted

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
