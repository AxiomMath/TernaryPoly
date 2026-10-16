module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Edge
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Weight

@[expose] public section


/-!
# Finite weights of the line section

`LineWeight ιL`: a function `ιL` on `G(A)` that depends only on the finite part, is right invariant under the finite
level and left invariant under the adelic line parabolic (`ιL = 1`: the whole spherical line section; `ιL` = indicator of
a union of `P_line(ℚ₃) g₀ K₁(3)` orbits: the good-line component).  The line source cocycle weighted by `ιL` is again a
source cocycle (`isSourceCocycle_smul_lineWeight`), and the class identification of the line integral cochain with the
line source (R-b) holds for the `ιL`-weighted cochains (`sourceToSummand_cSigma_eq_lineSource_weight`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- **A finite weight of the line section**: depends only on the finite part, is right invariant under the finite
level and left invariant under the adelic line parabolic. -/
structure LineWeight (ι : AdelicGL → ℂ) : Prop where
  finite : ∀ g g' : AdelicGL, finiteGroup g = finiteGroup g' → ι g = ι g'
  level : ∀ (k : finiteLevel) (g : AdelicGL), ι (g * atFinite k.val) = ι g
  parabolic : ∀ p : AdelicGL, p ∈ GeneralEisenstein.Adelic.lineParabolic Adeles → ∀ g : AdelicGL, ι (p * g) = ι g

namespace LineWeight

variable {ι : AdelicGL → ℂ} (hι : LineWeight ι)

include hι

theorem atInfinity (g : AdelicGL) (z : RealGL3) : ι (g * atInfinity z) = ι g :=
  hι.finite _ _ (finiteGroup_mul_atInfinity g z)

theorem lineLevi_left (t : Adelesˣ) (A : BinaryAdelicGL) (g : AdelicGL) :
    ι (GeneralEisenstein.Adelic.lineLevi t A * g) = ι g :=
  hι.parabolic _ (GeneralEisenstein.Adelic.lineLevi_mem t A) g

theorem lineUnipotent_left (a b : Adeles) (g : AdelicGL) :
    ι (GeneralEisenstein.Adelic.lineUnipotent a b * g) = ι g :=
  hι.parabolic _ (lineUnipotent_mem a b) g

end LineWeight

/-- The constant weight `1` is a plane weight and a line weight. -/
theorem lineWeight_one : LineWeight (fun _ => (1 : ℂ)) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem hasSmoothCuspLift_lineWeight {n k : ℕ} (D : InducingData n) {ι : AdelicGL → ℂ} (hι : LineWeight ι)
    (s : ℂ) (f : (Fin k → RealGL3) → AdelicGL → ℂ) (hf : HasSmoothCuspLift D .line s f) :
    HasSmoothCuspLift D .line s (fun x g => ι g * f x g) := by
  intro a
  obtain ⟨v, hv, hr⟩ := hf a
  refine ⟨fun x => ι a • v x, LinearFamilies.smooth_smul (ι a) _ hv, fun x A => ?_⟩
  have hlev : ι (binaryLevi .line A * (a * atInfinity (x (Fin.last k)))) = ι a := by
    show ι (GeneralEisenstein.Adelic.lineLevi 1 A * (a * atInfinity (x (Fin.last k)))) = ι a
    rw [hι.lineLevi_left, hι.atInfinity]
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hr x A]
  show ι a * (_ * f _ _) = _ * (ι _ * f _ _)
  rw [hlev]
  ring

/-- **Multiplying a line source cocycle by a finite line weight keeps it a source cocycle.** -/
theorem isSourceCocycle_smul_lineWeight {n : ℕ} (D : InducingData n) {ι : AdelicGL → ℂ} (hι : LineWeight ι)
    (c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n) (hc : IsSourceCocycle D .line c) :
    IsSourceCocycle D .line (fun y g => ι g • c y g) := by
  have coe : ∀ y g m, ((ι g • c y g : HomogeneousPoly n) : Poly).coeff m = ι g * ((c y g).val.coeff m) := by
    intro y g m
    rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  refine ⟨fun y m => ?_, fun m => ?_, fun h y g => ?_, fun y g => ?_⟩
  · obtain ⟨sm, lev, lift, unip, tor, cusp⟩ := hc.1 y m
    simp only [coe]
    simp only [] at sm lev lift unip tor cusp
    refine ⟨fun g => ?_, fun k g => ?_, hasSmoothCuspLift_lineWeight D hι _ _ lift, fun a b g => ?_,
      fun t g => ?_, fun g => ?_⟩
    · refine HeckeTranslate.SmoothClosure.smooth_congr (f := fun x : Fin 1 → RealGL3 => ι g * (c y (g * atInfinity (x 0))).val.coeff m)
        (smooth_mul_complex (smooth_const_complex (ι g)) (sm g)) (fun x => ?_)
      dsimp only
      rw [hι.atInfinity]
    · dsimp only
      rw [hι.level, lev]
    · dsimp only
      rw [hι.lineUnipotent_left, unip]
    · dsimp only
      rw [hι.lineLevi_left, tor]; ring
    · have h := cusp g
      have : (fun A : BinaryAdelicGL =>
          normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2 - inductionExponent .line cohomologicalPoint)) *
            (ι (GeneralEisenstein.Adelic.lineLevi 1 A * g) *
              (c y (GeneralEisenstein.Adelic.lineLevi 1 A * g)).val.coeff m)) =
          ι g • (fun A : BinaryAdelicGL =>
          normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2 - inductionExponent .line cohomologicalPoint)) *
            (c y (GeneralEisenstein.Adelic.lineLevi 1 A * g)).val.coeff m) := by
        funext A
        rw [hι.lineLevi_left]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      show (fun A : BinaryAdelicGL =>
          normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2 - inductionExponent .line cohomologicalPoint)) *
            (ι (GeneralEisenstein.Adelic.lineLevi 1 A * g) *
              (c y (GeneralEisenstein.Adelic.lineLevi 1 A * g)).val.coeff m)) ∈ cuspFunctions D.cusp
      rw [this]
      exact (cuspFunctions D.cusp).smul_mem _ h
  · simp only [coe]
    exact hasSmoothCuspLift_lineWeight D hι _ _ (hc.2.1 m)
  · show ι g • c (fun i => h * y i) g =
      realCoefficientComponent n D.chi h (ι (g * atInfinity h) • c y (g * atInfinity h))
    rw [hc.2.2.1, hι.atInfinity, map_smul]
  · have := hc.2.2.2 y g
    show ι g • c ![y 1, y 2, y 3] g - ι g • c ![y 0, y 2, y 3] g + ι g • c ![y 0, y 1, y 3] g -
      ι g • c ![y 0, y 1, y 2] g = 0
    calc _ = ι g • (c ![y 1, y 2, y 3] g - c ![y 0, y 2, y 3] g + c ![y 0, y 1, y 3] g -
          c ![y 0, y 1, y 2] g) := by simp only [smul_sub, smul_add]
      _ = 0 := by rw [this, smul_zero]

theorem rationalGroup_mem_lineParabolic (p : RationalGL3) (hp : p ∈ parabolic Side.line) :
    rationalGroup p ∈ GeneralEisenstein.Adelic.lineParabolic Adeles :=
  HeckeEigen.generalLinearGroup_map_line rationalAdele hp

section Weighted

variable {n : ℕ} (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
  (hol : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
  (E : LineLeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormalTw n F A)
  (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
  {ι : AdelicGL → ℂ} (hι : LineWeight ι)

include hol hE hc hχ hι

/-- **R-b with the finite weight `ιL`**: `ιL · cSigma` and `ιL · lineSource` define the same class. -/
theorem sourceToSummand_cSigma_eq_lineSource_weight
    (hSig : IsSourceCocycle D Side.line (fun y g => ι g • cSigma n D F y g)) :
    SourceQuotient.sourceToSummand D Side.line ⟨fun y g => ι g • cSigma n D F y g, hSig⟩ =
      SourceQuotient.sourceToSummand D Side.line
        ⟨fun y g => ι g • lineSource D E y g,
          isSourceCocycle_smul_lineWeight D hι _ (lineSource_isSourceCocycle D E hχ)⟩ :=
  sourceToSummand_eq_of_edge D Side.line _ _ hSig
    (isSourceCocycle_smul_lineWeight D hι _ (lineSource_isSourceCocycle D E hχ))
    (fun y g => ι g • lineEdge D F hol y g)
    (fun y g => by
      show ι g • cSigma n D F y g - ι g • lineSource D E y g = _
      have h := congrArg (fun P : HomogeneousPoly n => ι g • P)
        (cSigma_sub_lineSource D F hol E hE hc hχ y g)
      simpa only [smul_sub, smul_add] using h)
    (fun h y g => by
      show ι g • lineEdge D F hol (fun i => h * y i) g =
        realCoefficientComponent n D.chi h (ι (g * atInfinity h) • lineEdge D F hol y (g * atInfinity h))
      rw [lineEdge_cov D F hol E hE hc hχ h y g, hι.atInfinity, map_smul])
    (fun k y g => by
      show ι (g * atFinite k.val) • lineEdge D F hol y (g * atFinite k.val) = ι g • lineEdge D F hol y g
      rw [hι.level, lineEdge_level D F hol E hE hc hχ k y g])
    (fun p hp y g => by
      show ι (rationalGroup p * g) • lineEdge D F hol y (rationalGroup p * g) = ι g • lineEdge D F hol y g
      rw [hι.parabolic _ (rationalGroup_mem_lineParabolic p hp), lineEdge_parabolic D F hol E hE hc hχ p hp y g])

end Weighted

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
