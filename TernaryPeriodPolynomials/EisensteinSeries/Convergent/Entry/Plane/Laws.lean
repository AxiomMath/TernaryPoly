module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.EdgeX

@[expose] public section


/-!
# The induced-section laws of the plane integral cochain

From the translation law `cOmegaAt_translate` (Entry/PlaneEdgeX): the plane integral cochain `cOmegaAt` is invariant
under the adelic unipotent radical, transforms by the character `χ` under the rank-one Levi, and satisfies the `GL₂` Levi
law `cOmegaAt y (L(A) g) x = |det A|^{(n+3)/2} · cOmegaAt y g (x A)`, exactly as the plane source.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)
open GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

section Laws

variable {n : ℕ} (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
  (hol : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
  (E : LeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormal n F A)
  (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hol hE hc hχ

/-- **Unipotent invariance of the plane integral cochain.** -/
theorem cOmegaAt_unipotent (a b : Adeles) (g : AdelicGL) (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    cOmegaAt D F y (GeneralEisenstein.Adelic.planeUnipotent a b * g) x = cOmegaAt D F y g x := by
  have hr : realGroup (GeneralEisenstein.Adelic.planeUnipotent a b * g) =
      GeneralEisenstein.Adelic.planeUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b) *
        realGroup g := by
    rw [map_mul, realGroup_planeUnipotent]
  have hfin : finiteGroup (GeneralEisenstein.Adelic.planeUnipotent a b * g) =
      GeneralEisenstein.Adelic.planeUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b) *
        finiteGroup g := by
    rw [map_mul, finiteGroup_planeUnipotent]
  have h := cOmegaAt_translate D F hol E hE hc hχ y g (GeneralEisenstein.Adelic.planeUnipotent a b * g)
    ⟨GeneralEisenstein.Adelic.planeUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b),
      planeUnipotent_mem' _ _⟩
    (GeneralEisenstein.Adelic.planeUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b))
    (planeUnipotent_mem' _ _) hr hfin x
  rw [h, leviBlock_planeUnipotent, planeBlockGL_planeUnipotent, finitePlaneFactor_planeUnipotent]
  simp [ps_atFinite_one, ps_normPower_one]

/-- **The rank-one Levi character law of the plane integral cochain.** -/
theorem cOmegaAt_torus (t : Adelesˣ) (g : AdelicGL) (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    cOmegaAt D F y (GeneralEisenstein.Adelic.planeLevi 1 t * g) x = D.chi.toMonoidHom t • cOmegaAt D F y g x := by
  have hr : realGroup (GeneralEisenstein.Adelic.planeLevi 1 t * g) = GeneralEisenstein.Adelic.planeLevi 1 (realUnitPart t) * realGroup g := by
    rw [map_mul, realGroup_planeLevi, realPart_one']
  have hfin : finiteGroup (GeneralEisenstein.Adelic.planeLevi 1 t * g) = GeneralEisenstein.Adelic.planeLevi 1 (finiteUnitPart t) * finiteGroup g := by
    rw [map_mul, finiteGroup_planeLevi, finitePart_one']
  have h := cOmegaAt_translate D F hol E hE hc hχ y g (GeneralEisenstein.Adelic.planeLevi 1 t * g)
    ⟨GeneralEisenstein.Adelic.planeLevi 1 (realUnitPart t), planeLevi_mem _ _⟩ (GeneralEisenstein.Adelic.planeLevi 1 (finiteUnitPart t))
    (planeLevi_mem _ _) hr hfin x
  rw [character_split D.chi t, character_real_eq_one D.chi hχ,
    one_mul (D.chi.toMonoidHom (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.finiteAdeleUnit (finiteUnitPart t)))]
  rw [h, leviBlock_planeLevi, planeBlockGL_planeLevi', finitePlaneFactor_planeLevi]
  simp [ps_atFinite_one, ps_normPower_one, ps_normPower_zero, ps_finiteAdeleUnit_one]

/-- **The `GL₂` Levi law of the plane integral cochain.** -/
theorem cOmegaAt_levi (A : BinaryAdelicGL) (g : AdelicGL) (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    cOmegaAt D F y (GeneralEisenstein.Adelic.planeLevi A 1 * g) x =
      normPower (GeneralLinearGroup.det A) (((n : ℂ) + 3) / 2) • cOmegaAt D F y g (x * A) := by
  have hr : realGroup (GeneralEisenstein.Adelic.planeLevi A 1 * g) = GeneralEisenstein.Adelic.planeLevi (realPart A) 1 * realGroup g := by
    rw [map_mul, realGroup_planeLevi, realUnitPart_one']
  have hfin : finiteGroup (GeneralEisenstein.Adelic.planeLevi A 1 * g) = GeneralEisenstein.Adelic.planeLevi (finitePart A) 1 * finiteGroup g := by
    rw [map_mul, finiteGroup_planeLevi, finiteUnitPart_one']
  have h := cOmegaAt_translate D F hol E hE hc hχ y g (GeneralEisenstein.Adelic.planeLevi A 1 * g)
    ⟨GeneralEisenstein.Adelic.planeLevi (realPart A) 1, planeLevi_mem _ _⟩ (GeneralEisenstein.Adelic.planeLevi (finitePart A) 1)
    (planeLevi_mem _ _) hr hfin x
  have hA : atFinite (finitePart A) * atInfinity (realPart A) = A := by
    rw [atFinite_mul_atInfinity_comm, ← adelic_split]
  rw [h, leviBlock_planeLevi, planeBlockGL_planeLevi', finitePlaneFactor_planeLevi,
    ps_finiteAdeleUnit_one, map_one D.chi.toMonoidHom, ps_normPower_zero, hA]
  simp only [one_mul, mul_one]
  rw [← normPower_det_split]

end Laws

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
