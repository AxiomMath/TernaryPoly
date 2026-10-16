module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceReal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceFinite

@[expose] public section


/-!
# The algebraic laws of the line source cocycle

For a character `χ` trivial on the integral units the line source `lineSourceAt` is
* a homogeneous two-cocycle (the cup product of the two potentials),
* equivariant for the real group, and
* transforms under the general real/finite translation along the line parabolic by the scalar
  `d² |det L|^{(n+1)/2}` times the finite line factor.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

section Cup

variable {n : ℕ}

theorem cFLine_mul_atInfinity (D : InducingData n) (g : AdelicGL) (z : RealGL3) :
    cFLine D (g * atInfinity z) = cFLine D g := by
  unfold cFLine
  rw [finiteGroup_mul_atInfinity]

theorem bFLine_mul_atInfinity (g : AdelicGL) (z : RealGL3) :
    bFLine (g * atInfinity z) = bFLine g := by
  unfold bFLine
  rw [finiteGroup_mul_atInfinity]

theorem lineSourceAt_eq_cup (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    lineSourceAt D E y g a =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        (psCup (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
          (fun u : RealGL3 => cFLine D g • E.α (iwALine (realGroup g * u)) (a * bFLine g))
          (fun u : RealGL3 => lineRadical n D.chi (iwPLine (realGroup g * u))) y) := by
  unfold lineSourceAt psCup
  rw [smul_sub]
  rfl

/-- **The cocycle condition of the line source.** -/
theorem lineSourceAt_cocycle (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (x : Fin 4 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    lineSourceAt D E ![x 1, x 2, x 3] g a - lineSourceAt D E ![x 0, x 2, x 3] g a +
      lineSourceAt D E ![x 0, x 1, x 3] g a - lineSourceAt D E ![x 0, x 1, x 2] g a = 0 := by
  have h := psCup_cocycle
    (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
    (fun u : RealGL3 => cFLine D g • E.α (iwALine (realGroup g * u)) (a * bFLine g))
    (fun u : RealGL3 => lineRadical n D.chi (iwPLine (realGroup g * u))) x
  have h2 := congrArg (realCoefficientComponent n D.chi (realGroup g)⁻¹) h
  simp only [map_sub, map_add, _root_.map_zero] at h2
  simp only [lineSourceAt_eq_cup]
  exact h2

/-- **Equivariance of the line source** for the real group. -/
theorem lineSourceAt_equivariant (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (h : RealGL3) (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    lineSourceAt D E (fun i => h * y i) g a =
      realCoefficientComponent n D.chi h (lineSourceAt D E y (g * atInfinity h) a) := by
  unfold lineSourceAt
  rw [realGroup_mul_atInfinity, cFLine_mul_atInfinity, bFLine_mul_atInfinity]
  simp only [mul_assoc]
  rw [rho_mul_inv_mul]

end Cup

/-! ## The finite twist in the adelic form -/

section Translate

variable {n : ℕ}

theorem twistLine_left_g (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (f : FiniteGL) (hf : f ∈ lineParabolic FiniteAdeles)
    (hfin : finiteGroup g' = f * finiteGroup g) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFLine D g' • E.α h (x * bFLine g') =
      finiteLineFactor D.chi 2 (lineBeta n) f hf •
        (cFLine D g • E.α h (x * atFinite (lineBlockGL f hf) * bFLine g)) :=
  twistLine_left D E hχ (finiteGroup g) (finiteGroup g') f hf hfin h x

theorem sub_twistLine (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (f : FiniteGL) (hf : f ∈ lineParabolic FiniteAdeles)
    (hfin : finiteGroup g' = f * finiteGroup g) (h1 h0 : BinaryRealGL) (x : BinaryAdelicGL) :
    cFLine D g' • (E.α h1 (x * bFLine g') - E.α h0 (x * bFLine g')) =
      (finiteLineFactor D.chi 2 (lineBeta n) f hf * cFLine D g) •
        (E.α h1 (x * atFinite (lineBlockGL f hf) * bFLine g) -
          E.α h0 (x * atFinite (lineBlockGL f hf) * bFLine g)) := by
  rw [smul_sub, twistLine_left_g D E hχ g g' f hf hfin h1 x,
    twistLine_left_g D E hχ g g' f hf hfin h0 x]
  simp only [smul_sub, smul_smul]

/-- **The general translation law of the line source.** -/
theorem lineSourceAt_translate (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (p : lineParabolic ℝ) (f : FiniteGL)
    (hf : f ∈ lineParabolic FiniteAdeles) (hr : realGroup g' = p.1 * realGroup g)
    (hfin : finiteGroup g' = f * finiteGroup g) (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    lineSourceAt D E y g' x =
      ((((p.1.val 0 0 : ℝ) : ℂ) ^ 2 *
            normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (lineBeta n)) *
          finiteLineFactor D.chi 2 (lineBeta n) f hf) •
        lineSourceAt D E y g
          (x * (atFinite (lineBlockGL f hf) * atInfinity (lineLeviBlock p))) := by
  have hc := componentCharacter_eq_one_of_integral D.chi hχ
  have hcomm : bFLine g * atInfinity (lineLeviBlock p) = atInfinity (lineLeviBlock p) * bFLine g :=
    atFinite_mul_atInfinity_comm _ _
  have ht : x * atFinite (lineBlockGL f hf) * bFLine g * atInfinity (lineLeviBlock p) =
      x * (atFinite (lineBlockGL f hf) * atInfinity (lineLeviBlock p)) * bFLine g := by
    simp only [mul_assoc, hcomm]
  have hu : ∀ i, p.1 * realGroup g * y i = p.1 * (realGroup g * y i) :=
    fun i => mul_assoc _ _ _
  unfold lineSourceAt
  rw [hr, hu 2, hu 1, hu 0, sub_twistLine D E hχ g g' f hf hfin,
    lineCore_w D.chi hc E p (realGroup g) y (x * atFinite (lineBlockGL f hf) * bFLine g)
      (finiteLineFactor D.chi 2 (lineBeta n) f hf * cFLine D g), ht]
  simp only [map_smul, rho_inv_mul_rho, smul_smul]
  congr 1
  all_goals ring

end Translate

end TernaryPeriodPolynomials.SourceConstruction

end
