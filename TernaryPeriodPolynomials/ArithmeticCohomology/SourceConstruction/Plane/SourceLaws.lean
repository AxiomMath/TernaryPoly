module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceAlgebra

@[expose] public section


/-!
# The induced-section laws of the plane source

The Levi, torus and unipotent generators of the adelic plane parabolic and the finite level act on
the plane source exactly as on a normalized plane-induced section.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)

namespace TernaryPeriodPolynomials.SourceConstruction

section Laws

variable {n : ℕ} (D : InducingData n) (E : LeviCocycleData D.cusp n)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hχ

/-- **Right invariance under the finite level.** -/
theorem planeSourceAt_level (g : AdelicGL) (k : finiteLevel) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    planeSourceAt D E y (g * atFinite k.val) x = planeSourceAt D E y g x := by
  have hcb : ∀ h : BinaryRealGL, cF D (g * atFinite k.val) • E.α h (x * bF (g * atFinite k.val)) =
      cF D g • E.α h (x * bF g) := by
    intro h
    have := twist_level D E hχ (finiteGroup g) k h x
    rw [← finiteGroup_mul_atFinite g k.val] at this
    exact this
  unfold planeSourceAt
  rw [realGroup_mul_atFinite]
  simp only [smul_sub]
  rw [hcb, hcb]

/-- **Unipotent invariance.** -/
theorem planeSourceAt_unipotent (a b : Adeles) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    planeSourceAt D E y (planeUnipotent a b * g) x = planeSourceAt D E y g x := by
  have hr : realGroup (planeUnipotent a b * g) =
      planeUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b) *
        realGroup g := by
    rw [map_mul, realGroup_planeUnipotent]
  have hfin : finiteGroup (planeUnipotent a b * g) =
      planeUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b) *
        finiteGroup g := by
    rw [map_mul, finiteGroup_planeUnipotent]
  have h := planeSourceAt_translate D E hχ g (planeUnipotent a b * g)
    ⟨planeUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b),
      planeUnipotent_mem' _ _⟩
    (planeUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b))
    (planeUnipotent_mem' _ _) hr hfin y x
  rw [h, leviBlock_planeUnipotent, planeBlockGL_planeUnipotent, finitePlaneFactor_planeUnipotent]
  simp [ps_atFinite_one, ps_normPower_one]

/-- **The rank-one Levi character.** -/
theorem planeSourceAt_torus (t : Adelesˣ) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    planeSourceAt D E y (planeLevi 1 t * g) x = D.chi.toMonoidHom t • planeSourceAt D E y g x := by
  have hr : realGroup (planeLevi 1 t * g) = planeLevi 1 (realUnitPart t) * realGroup g := by
    rw [map_mul, realGroup_planeLevi, realPart_one']
  have hfin : finiteGroup (planeLevi 1 t * g) = planeLevi 1 (finiteUnitPart t) * finiteGroup g := by
    rw [map_mul, finiteGroup_planeLevi, finitePart_one']
  have h := planeSourceAt_translate D E hχ g (planeLevi 1 t * g)
    ⟨planeLevi 1 (realUnitPart t), planeLevi_mem _ _⟩ (planeLevi 1 (finiteUnitPart t))
    (planeLevi_mem _ _) hr hfin y x
  rw [character_split D.chi t, character_real_eq_one D.chi hχ,
    one_mul (D.chi.toMonoidHom (finiteAdeleUnit (finiteUnitPart t)))]
  rw [h, leviBlock_planeLevi, planeBlockGL_planeLevi', finitePlaneFactor_planeLevi]
  simp [ps_atFinite_one, ps_normPower_one, ps_normPower_zero,
    ps_finiteAdeleUnit_one]

/-- **The `GL₂` Levi law.** -/
theorem planeSourceAt_levi (A : BinaryAdelicGL) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    planeSourceAt D E y (planeLevi A 1 * g) x =
      normPower (GeneralLinearGroup.det A) (((n : ℂ) + 3) / 2) • planeSourceAt D E y g (x * A) := by
  have hr : realGroup (planeLevi A 1 * g) = planeLevi (realPart A) 1 * realGroup g := by
    rw [map_mul, realGroup_planeLevi, realUnitPart_one']
  have hfin : finiteGroup (planeLevi A 1 * g) = planeLevi (finitePart A) 1 * finiteGroup g := by
    rw [map_mul, finiteGroup_planeLevi, finiteUnitPart_one']
  have h := planeSourceAt_translate D E hχ g (planeLevi A 1 * g)
    ⟨planeLevi (realPart A) 1, planeLevi_mem _ _⟩ (planeLevi (finitePart A) 1)
    (planeLevi_mem _ _) hr hfin y x
  have hA : atFinite (finitePart A) * atInfinity (realPart A) = A := by
    rw [atFinite_mul_atInfinity_comm, ← adelic_split]
  rw [h, leviBlock_planeLevi, planeBlockGL_planeLevi', finitePlaneFactor_planeLevi,
    ps_finiteAdeleUnit_one, map_one D.chi.toMonoidHom, ps_normPower_zero, hA]
  simp only [one_mul, mul_one]
  rw [← normPower_det_split]

end Laws

end TernaryPeriodPolynomials.SourceConstruction
