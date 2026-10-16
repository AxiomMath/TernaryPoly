module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Norm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Norm
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section


/-!
# Splitting adelic matrices and ideles into archimedean and finite parts

`g = atInfinity g_∞ · atFinite g_f` in every dimension, `t = t_∞ · t_f` for ideles, the real and
finite parts of the line Levi and unipotent elements, and the triviality of `χ` on real units once
it is trivial on integral units.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance (combineGL_mul)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The archimedean part of an adelic matrix. -/
abbrev realPart {m : ℕ} (g : GeneralLinearGroup (Fin m) Adeles) : GeneralLinearGroup (Fin m) ℝ :=
  GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) g

/-- The finite part of an adelic matrix. -/
abbrev finitePart {m : ℕ} (g : GeneralLinearGroup (Fin m) Adeles) :
    GeneralLinearGroup (Fin m) FiniteAdeles :=
  GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) g

theorem adelic_split {m : ℕ} (g : GeneralLinearGroup (Fin m) Adeles) :
    g = atInfinity (realPart g) * atFinite (finitePart g) := by
  change g = combineGL (realPart g) 1 * combineGL 1 (finitePart g)
  rw [combineGL_mul, mul_one, one_mul]
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext rfl rfl

theorem realGroup_eq_realPart (g : AdelicGL) : realGroup g = realPart g := rfl

theorem finiteGroup_eq_finitePart (g : AdelicGL) : finiteGroup g = finitePart g := rfl

theorem realPart_atInfinity {m : ℕ} (r : GeneralLinearGroup (Fin m) ℝ) :
    realPart (atInfinity r) = r := by
  apply Units.ext
  ext i j
  rfl

theorem finitePart_atInfinity {m : ℕ} (r : GeneralLinearGroup (Fin m) ℝ) :
    finitePart (atInfinity r) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => rfl

theorem realPart_atFinite {m : ℕ} (f : GeneralLinearGroup (Fin m) FiniteAdeles) :
    realPart (atFinite f) = 1 := by
  apply Units.ext
  ext i j
  rfl

theorem finitePart_atFinite {m : ℕ} (f : GeneralLinearGroup (Fin m) FiniteAdeles) :
    finitePart (atFinite f) = f := by
  apply Units.ext
  refine Matrix.ext fun i j => rfl

/-- The archimedean part of an idele. -/
abbrev realUnitPart (t : Adelesˣ) : ℝˣ := Units.map (RingHom.fst ℝ FiniteAdeles).toMonoidHom t

/-- The finite part of an idele. -/
abbrev finiteUnitPart (t : Adelesˣ) : FiniteAdelesˣ :=
  Units.map (RingHom.snd ℝ FiniteAdeles).toMonoidHom t

theorem idele_split (t : Adelesˣ) :
    t = realAdeleUnit (realUnitPart t) * finiteAdeleUnit (finiteUnitPart t) := by
  apply Units.ext
  change t.val = ((t.val.1, (1 : FiniteAdeles)) * ((1 : ℝ), t.val.2))
  rw [Prod.mk_mul_mk, mul_one, one_mul]

theorem normPower_split (t : Adelesˣ) (z : ℂ) :
    normPower t z = normPower (realAdeleUnit (realUnitPart t)) z *
      normPower (finiteAdeleUnit (finiteUnitPart t)) z := by
  conv_lhs => rw [idele_split t]
  exact TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_mul _ _ z

theorem character_split (χ : RankOneCharacter) (t : Adelesˣ) :
    χ.toMonoidHom t = χ.toMonoidHom (realAdeleUnit (realUnitPart t)) *
      χ.toMonoidHom (finiteAdeleUnit (finiteUnitPart t)) := by
  conv_lhs => rw [idele_split t]
  exact map_mul _ _ _

/-- A character trivial on integral units is trivial on real units. -/
theorem character_real_eq_one (χ : RankOneCharacter)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1) (t : ℝˣ) :
    χ.toMonoidHom (realAdeleUnit t) = 1 := by
  have hmul : ∀ s r : ℝˣ, realAdeleUnit (s * r) = realAdeleUnit s * realAdeleUnit r := by
    intro s r
    apply Units.ext
    change ((s * r).val, (1 : FiniteAdeles)) = (s.val * r.val, (1 : FiniteAdeles) * 1)
    rw [Units.val_mul, mul_one]
  have hminus : χ.toMonoidHom (realAdeleUnit (-1)) = 1 := by
    have hrat := χ.rational (-1)
    have hsplit : Units.map rationalAdele (-1 : ℚˣ) =
        realAdeleUnit (-1) * integralAdeleUnit (-1) := by
      apply Units.ext
      change (rationalAdele (-1 : ℚ)) = ((-1 : ℝ) * 1, (1 : FiniteAdeles) * integralEmbedding (-1))
      rw [map_neg, map_one, mul_one, one_mul]
      apply Prod.ext
      · simp
      · simp
    rw [hsplit, map_mul, hχ, mul_one] at hrat
    exact hrat
  rcases lt_or_gt_of_ne t.ne_zero with hneg | hpos
  · have hdecomp : t = (-1) * (-t) := by rw [neg_mul, one_mul, neg_neg]
    have hpos' : 0 < (-t).val := by
      rw [Units.val_neg]
      exact neg_pos.mpr hneg
    rw [hdecomp, hmul, map_mul, hminus, χ.positiveReal _ hpos', one_mul]
  · exact χ.positiveReal t hpos

/-! ## Real and finite parts of the line Levi -/

theorem map_lineLevi {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d : Rˣ)
    (A : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.map φ (lineLevi d A) =
      lineLevi (Units.map φ.toMonoidHom d) (GeneralLinearGroup.map φ A) := by
  apply Units.ext
  change (lineLevi d A).val.map φ = (lineLevi (Units.map φ.toMonoidHom d) (GeneralLinearGroup.map φ A)).val
  rw [lineLevi_val, lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.map_apply]

theorem map_lineUnipotent' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R) :
    GeneralLinearGroup.map φ (lineUnipotent a b) = lineUnipotent (φ a) (φ b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply, lineUnipotent, upperUnipotent]

end TernaryPeriodPolynomials.SourceConstruction
