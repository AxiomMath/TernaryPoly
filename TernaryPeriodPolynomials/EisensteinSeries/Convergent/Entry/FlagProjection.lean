module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceQuotient
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.GoodFlags

@[expose] public section


/-!
# Component projections of the stratum cohomology

An *arithmetically invariant flag weight* `w : Flags s → ℂ` (`w(γ x) = w(x)` for `γ` in the arithmetic level
`rationalLevel`) acts on the flag coefficient module `Flags s → V` by pointwise multiplication, commuting with the
`rationalLevel`-action.  Hence it induces a chain map of the homogeneous cochains, and an endomorphism `flagProj w` of
`H²(rationalLevel, flags)` = `StratumH2` with `flagProj w [z] = [w·z]` (`flagProj_classOf`).  For the indicator of the
good flags (`GoodFlag`, invariant under `rationalLevel` by `goodFlag_rationalLevel_smul_iff`) this is the **good-flag
component projection** `goodComponent`, an idempotent (`flagProj_idem`).

`flagProj_sourceClass`: on classes of source cocycles, `flagProj w [c] = [ι·c]` whenever the adelic weight `ι` satisfies
`ι(ρ(q⁻¹)) = w(qP)`.  So multiplication by the (non-right-`G(ℚ)`-invariant) adelic weight `ι` does descend to the
arithmetic cohomology: only invariance under the arithmetic level is needed.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

section FlagProjection

variable {n : ℕ} (χ : RankOneCharacter) (s : Side)

/-- Multiplication of a function on flags by a weight. -/
def flagMul (w : Flags s → ℂ) : (Flags s → HomogeneousPoly n) →ₗ[ℂ] (Flags s → HomogeneousPoly n) where
  toFun f x := w x • f x
  map_add' f g := by funext x; exact smul_add _ _ _
  map_smul' c f := by funext x; exact smul_comm (w x) c (f x)

variable {χ s}
variable (w : Flags s → ℂ) (hw : ∀ (γ : rationalLevel) (x : Flags s), w (γ.val • x) = w x)

include hw in
theorem flagRep_flagMul (γ : rationalLevel) (f : Flags s → HomogeneousPoly n) :
    flagRepresentation (rationalCoefficientComponent n χ) s γ.val (flagMul s w f) =
      flagMul s w (flagRepresentation (rationalCoefficientComponent n χ) s γ.val f) := by
  funext x
  have h1 : w (γ.val⁻¹ • x) = w x := hw γ⁻¹ x
  change rationalCoefficientComponent n χ γ.val (w (γ.val⁻¹ • x) • f (γ.val⁻¹ • x)) =
    w x • rationalCoefficientComponent n χ γ.val (f (γ.val⁻¹ • x))
  rw [map_smul, h1]


/-- Multiplication by an arithmetically invariant flag weight, as a map of homogeneous cochains. -/
def flagCochMap (k : ℕ) : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) k →ₗ[ℂ]
    cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) k where
  toFun f := ⟨fun v => flagMul s w (f.val v), fun γ x => by
    have h := f.property γ x
    change flagMul s w (f.val (fun i => γ.val * x i)) = _
    rw [h, flagRep_flagMul w hw]⟩
  map_add' f g := by
    apply Subtype.ext; funext v
    show flagMul s w (f.val v + g.val v) = flagMul s w (f.val v) + flagMul s w (g.val v)
    exact (flagMul s w).map_add _ _
  map_smul' c f := by
    apply Subtype.ext; funext v
    show flagMul s w (c • f.val v) = c • flagMul s w (f.val v)
    exact (flagMul s w).map_smul _ _

theorem flagCochMap_apply (k : ℕ) (f : cochains rationalLevel
    (flagRepresentation (rationalCoefficientComponent n χ) s) k) (v : Fin (k + 1) → RationalGL3) :
    (flagCochMap w hw k f).val v = flagMul s w (f.val v) := rfl

theorem flagCochMap_differentialOne (f : cochains rationalLevel
    (flagRepresentation (rationalCoefficientComponent n χ) s) 1) :
    differentialOne rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)
        (flagCochMap w hw 1 f) =
      flagCochMap w hw 2 (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) s) f) := by
  apply Subtype.ext; funext x
  change flagMul s w (f.val ![x 1, x 2]) - flagMul s w (f.val ![x 0, x 2]) + flagMul s w (f.val ![x 0, x 1]) =
    flagMul s w (f.val ![x 1, x 2] - f.val ![x 0, x 2] + f.val ![x 0, x 1])
  simp only [map_add, map_sub]

theorem flagCochMap_differentialTwo (f : cochains rationalLevel
    (flagRepresentation (rationalCoefficientComponent n χ) s) 2) (x : Fin 4 → RationalGL3) :
    differentialTwo rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)
        (flagCochMap w hw 2 f) x =
      flagMul s w (differentialTwo rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) s) f x) := by
  change flagMul s w (f.val ![x 1, x 2, x 3]) - flagMul s w (f.val ![x 0, x 2, x 3]) +
      flagMul s w (f.val ![x 0, x 1, x 3]) - flagMul s w (f.val ![x 0, x 1, x 2]) =
    flagMul s w (f.val ![x 1, x 2, x 3] - f.val ![x 0, x 2, x 3] +
      f.val ![x 0, x 1, x 3] - f.val ![x 0, x 1, x 2])
  simp only [map_add, map_sub]

/-- The map on cocycles. -/
def flagCocMap : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) →ₗ[ℂ]
    cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) :=
  (flagCochMap w hw 2).restrict (p := cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s))
    (q := cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)) (by
      intro f hf
      change differentialTwo rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)
        (flagCochMap w hw 2 f) = 0
      funext x
      rw [flagCochMap_differentialTwo]
      have : differentialTwo rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) f = 0 := hf
      rw [this]
      exact map_zero (flagMul s w) |>.trans rfl)

theorem flagCocMap_val (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)) :
    (flagCocMap w hw z).val.val = fun v => flagMul s w (z.val.val v) := rfl

/-- **The component projection on `H²`**: multiplication of the flag coefficients by an arithmetically invariant weight
descends to an endomorphism of the stratum cohomology. -/
def flagProj : StratumH2 n χ s →ₗ[ℂ] StratumH2 n χ s :=
  Submodule.mapQ _ _ (flagCocMap w hw) (by
    rintro _ ⟨b, rfl⟩
    refine ⟨flagCochMap w hw 1 b, ?_⟩
    apply Subtype.ext
    exact flagCochMap_differentialOne w hw b)

theorem flagProj_classOf (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)) :
    flagProj w hw (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) z) =
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) (flagCocMap w hw z) :=
  rfl


theorem flagProj_idem (hidem : ∀ x, w x * w x = w x) (a : StratumH2 n χ s) :
    flagProj w hw (flagProj w hw a) = flagProj w hw a := by
  induction a using Submodule.Quotient.induction_on with
  | H z =>
    change flagProj w hw (flagProj w hw (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) z)) =
      flagProj w hw (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) z)
    rw [flagProj_classOf, flagProj_classOf]
    congr 1
    apply Subtype.ext; apply Subtype.ext
    funext v x
    change w x • (w x • z.val.val v x) = w x • z.val.val v x
    rw [smul_smul, hidem]

end FlagProjection

section Naturality

variable {n : ℕ} (D : InducingData n) (side : Side) (w : Flags side → ℂ)
  (hw : ∀ (γ : rationalLevel) (x : Flags side), w (γ.val • x) = w x)

/-- **The component projection of a weighted source is the class of the weighted source**:
`flagProj w [c] = [ι · c]` whenever `ι(ρ(q⁻¹)) = w(qP)` for all rational `q`. -/
theorem flagProj_sourceClass (ι : AdelicGL → ℂ)
    (hιw : ∀ q : RationalGL3, ι (rationalGroup q⁻¹) = w (QuotientGroup.mk q))
    (c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n) (hc : IsSourceCocycle D side c)
    (hc' : IsSourceCocycle D side (fun y g => ι g • c y g)) :
    flagProj (χ := D.chi) w hw (SourceSpace.sourceClass D side ⟨c, hc⟩) =
      SourceSpace.sourceClass D side ⟨fun y g => ι g • c y g, hc'⟩ := by
  have key : flagCocMap (χ := D.chi) w hw (SourceSpace.evaluatedSource D side ⟨c, hc⟩) =
      SourceSpace.evaluatedSource D side ⟨fun y g => ι g • c y g, hc'⟩ := by
    refine SourceSpace.evaluates_unique D side (fun y g => ι g • c y g) _ _ ?_
      (SourceSpace.evaluatedSource_realizes D side ⟨_, hc'⟩)
    intro x q
    have h := SourceSpace.evaluatedSource_realizes D side ⟨c, hc⟩ x q
    change w (QuotientGroup.mk q) • (SourceSpace.evaluatedSource D side ⟨c, hc⟩).val.val x
      (QuotientGroup.mk q) = _
    rw [h, ← hιw]
  exact congrArg (fun z => classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side) z) key

end Naturality

section GoodWeight

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

open Classical in
/-- The indicator of the good flags (`GoodFlag`: the saturated integral lattice of the flag has a vector not annihilated
by `e₃*` modulo `3`). -/
def goodWeight (s : Side) : Flags s → ℂ := fun x => if GoodFlag s x then 1 else 0

theorem goodWeight_invariant (s : Side) (γ : rationalLevel) (x : Flags s) :
    goodWeight s (γ.val • x) = goodWeight s x := by
  unfold goodWeight
  by_cases h : GoodFlag s x
  · rw [ite_eq_left h, ite_eq_left ((goodFlag_rationalLevel_smul_iff s γ x).mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((goodFlag_rationalLevel_smul_iff s γ x).mp h'))]

theorem goodWeight_idem (s : Side) (x : Flags s) : goodWeight s x * goodWeight s x = goodWeight s x := by
  unfold goodWeight
  split_ifs <;> simp

/-- **The good-flag component** of the stratum cohomology: restriction of the flag coefficients to the good flags. -/
def goodComponent (n : ℕ) (χ : RankOneCharacter) (s : Side) : StratumH2 n χ s →ₗ[ℂ] StratumH2 n χ s :=
  flagProj (goodWeight s) (goodWeight_invariant s)

end GoodWeight

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
