module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Algebra

@[expose] public section


/-!
# The induced-section laws of the level-three line source

The Levi, torus and unipotent generators of the adelic line parabolic and the finite level act on
the level-three line source exactly as on a normalized line-induced section at the cohomological
point: the unipotent radical acts trivially, the rank-one torus acts by `χ(t) |t|²`, the `GL₂` Levi
by `|det A|^{(n+1)/2} · A`, and the finite level acts trivially.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)

namespace TernaryPeriodPolynomials.SourceConstruction

section Laws3

variable {n : ℕ} (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hχ

/-- **Right invariance under the finite level.** -/
theorem lineSourceAt3_level (g : AdelicGL) (k : finiteLevel) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    lineSourceAt3 D E y (g * atFinite k.val) x = lineSourceAt3 D E y g x := by
  have hcb : ∀ h : BinaryRealGL,
      cFLine3 D (g * atFinite k.val) • E.α h (x * bFLine3 (g * atFinite k.val)) =
        cFLine3 D g • E.α h (x * bFLine3 g) := by
    intro h
    have := twist3_level D E hχ (finiteGroup g) k h x
    rw [← finiteGroup_mul_atFinite g k.val] at this
    exact this
  unfold lineSourceAt3
  rw [realGroup_mul_atFinite]
  simp only [smul_sub]
  rw [hcb, hcb]

/-- **Unipotent invariance.** -/
theorem lineSourceAt3_unipotent (a b : Adeles) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    lineSourceAt3 D E y (lineUnipotent a b * g) x = lineSourceAt3 D E y g x := by
  have hr : realGroup (lineUnipotent a b * g) =
      lineUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b) *
        realGroup g := by
    rw [map_mul, realGroup_lineUnipotent]
  have hfin : finiteGroup (lineUnipotent a b * g) =
      lineUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b) *
        finiteGroup g := by
    rw [map_mul, finiteGroup_lineUnipotent]
  have h := lineSourceAt3_translate D E hχ g (lineUnipotent a b * g)
    ⟨lineUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b),
      lineUnipotent_mem _ _⟩
    (lineUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b))
    (lineUnipotent_mem _ _) hr hfin y x
  rw [h, lsLeviBlock_unipotent, lineBlockGL_lineUnipotent, finiteLineFactor_lineUnipotent,
    lsCorner_unipotent]
  simp [ps_atFinite_one, ps_normPower_one]

/-- **The rank-one Levi character.** -/
theorem lineSourceAt3_torus (t : Adelesˣ) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    lineSourceAt3 D E y (lineLevi t 1 * g) x =
      (D.chi.toMonoidHom t * normPower t 2) • lineSourceAt3 D E y g x := by
  have hr : realGroup (lineLevi t 1 * g) = lineLevi (realUnitPart t) 1 * realGroup g := by
    rw [map_mul, realGroup_lineLevi, realPart_one]
  have hfin : finiteGroup (lineLevi t 1 * g) = lineLevi (finiteUnitPart t) 1 * finiteGroup g := by
    rw [map_mul, finiteGroup_lineLevi, finitePart_one]
  have h := lineSourceAt3_translate D E hχ g (lineLevi t 1 * g)
    ⟨lineLevi (realUnitPart t) 1, lineLevi_mem _ _⟩ (lineLevi (finiteUnitPart t) 1)
    (lineLevi_mem _ _) hr hfin y x
  have hs := lsTorus_scalar D.chi hχ t
  rw [h, lineLeviBlock_levi, lineBlockGL_lineLevi, finiteLineFactor_lineLevi, lsCorner_levi]
  simp only [ps_atInfinity_one, ps_atFinite_one, mul_one, map_one, ps_normPower_one,
    ps_finiteAdeleUnit_one]
  congr 1

/-- **The `GL₂` Levi law.** -/
theorem lineSourceAt3_levi (A : BinaryAdelicGL) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    lineSourceAt3 D E y (lineLevi 1 A * g) x =
      normPower (GeneralLinearGroup.det A) (lineBeta n) • lineSourceAt3 D E y g (x * A) := by
  have hr : realGroup (lineLevi 1 A * g) = lineLevi 1 (realPart A) * realGroup g := by
    rw [map_mul, realGroup_lineLevi, realUnitPart_one]
  have hfin : finiteGroup (lineLevi 1 A * g) = lineLevi 1 (finitePart A) * finiteGroup g := by
    rw [map_mul, finiteGroup_lineLevi, finiteUnitPart_one]
  have h := lineSourceAt3_translate D E hχ g (lineLevi 1 A * g)
    ⟨lineLevi 1 (realPart A), lineLevi_mem _ _⟩ (lineLevi 1 (finitePart A))
    (lineLevi_mem _ _) hr hfin y x
  have hA : atFinite (finitePart A) * atInfinity (realPart A) = A := by
    rw [atFinite_mul_atInfinity_comm, ← adelic_split]
  have hs := normPower_det_split A (lineBeta n)
  rw [h, lineLeviBlock_levi, lineBlockGL_lineLevi, finiteLineFactor_lineLevi, lsCorner_levi, hA]
  simp only [Units.val_one, Complex.ofReal_one, one_pow, ps_finiteAdeleUnit_one, map_one,
    ps_normPower_one, one_mul, mul_one]
  congr 1
  all_goals linear_combination (-1 : ℂ) * hs

end Laws3

end TernaryPeriodPolynomials.SourceConstruction

end
