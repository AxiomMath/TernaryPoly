module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Real
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Finite

@[expose] public section


/-!
# The algebraic laws of the level-three line source cocycle

For a character `χ` trivial on the integral units the level-three line source `lineSourceAt3` is
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

section Cup3

variable {n : ℕ}

theorem cFLine3_mul_atInfinity (D : InducingData n) (g : AdelicGL) (z : RealGL3) :
    cFLine3 D (g * atInfinity z) = cFLine3 D g := by
  unfold cFLine3
  rw [finiteGroup_mul_atInfinity]

theorem bFLine3_mul_atInfinity (g : AdelicGL) (z : RealGL3) :
    bFLine3 (g * atInfinity z) = bFLine3 g := by
  unfold bFLine3
  rw [finiteGroup_mul_atInfinity]

theorem lineSourceAt3_eq_cup (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    lineSourceAt3 D E y g a =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        (psCup (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
          (fun u : RealGL3 => cFLine3 D g • E.α (iwALine (realGroup g * u)) (a * bFLine3 g))
          (fun u : RealGL3 => lineRadical n D.chi (iwPLine (realGroup g * u))) y) := by
  unfold lineSourceAt3 psCup
  rw [smul_sub]
  rfl

/-- **The cocycle condition of the level-three line source.** -/
theorem lineSourceAt3_cocycle (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (x : Fin 4 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    lineSourceAt3 D E ![x 1, x 2, x 3] g a - lineSourceAt3 D E ![x 0, x 2, x 3] g a +
      lineSourceAt3 D E ![x 0, x 1, x 3] g a - lineSourceAt3 D E ![x 0, x 1, x 2] g a = 0 := by
  have h := psCup_cocycle
    (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
    (fun u : RealGL3 => cFLine3 D g • E.α (iwALine (realGroup g * u)) (a * bFLine3 g))
    (fun u : RealGL3 => lineRadical n D.chi (iwPLine (realGroup g * u))) x
  have h2 := congrArg (realCoefficientComponent n D.chi (realGroup g)⁻¹) h
  simp only [map_sub, map_add, _root_.map_zero] at h2
  simp only [lineSourceAt3_eq_cup]
  exact h2

/-- **Equivariance of the level-three line source** for the real group. -/
theorem lineSourceAt3_equivariant (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (h : RealGL3) (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    lineSourceAt3 D E (fun i => h * y i) g a =
      realCoefficientComponent n D.chi h (lineSourceAt3 D E y (g * atInfinity h) a) := by
  unfold lineSourceAt3
  rw [realGroup_mul_atInfinity, cFLine3_mul_atInfinity, bFLine3_mul_atInfinity]
  simp only [mul_assoc]
  rw [rho_mul_inv_mul]

end Cup3

/-! ## The finite twist in the adelic form -/

section Translate3

variable {n : ℕ}

theorem twist3_left_g (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (f : FiniteGL) (hf : f ∈ lineParabolic FiniteAdeles)
    (hfin : finiteGroup g' = f * finiteGroup g) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFLine3 D g' • E.α h (x * bFLine3 g') =
      finiteLineFactor D.chi 2 (lineBeta n) f hf •
        (cFLine3 D g • E.α h (x * atFinite (lineBlockGL f hf) * bFLine3 g)) :=
  twist3_left D E hχ (finiteGroup g) (finiteGroup g') f hf hfin h x

theorem sub_twist3 (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (f : FiniteGL) (hf : f ∈ lineParabolic FiniteAdeles)
    (hfin : finiteGroup g' = f * finiteGroup g) (h1 h0 : BinaryRealGL) (x : BinaryAdelicGL) :
    cFLine3 D g' • (E.α h1 (x * bFLine3 g') - E.α h0 (x * bFLine3 g')) =
      (finiteLineFactor D.chi 2 (lineBeta n) f hf * cFLine3 D g) •
        (E.α h1 (x * atFinite (lineBlockGL f hf) * bFLine3 g) -
          E.α h0 (x * atFinite (lineBlockGL f hf) * bFLine3 g)) := by
  rw [smul_sub, twist3_left_g D E hχ g g' f hf hfin h1 x,
    twist3_left_g D E hχ g g' f hf hfin h0 x]
  simp only [smul_sub, smul_smul]

/-- **The general translation law of the level-three line source.** -/
theorem lineSourceAt3_translate (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (p : lineParabolic ℝ) (f : FiniteGL)
    (hf : f ∈ lineParabolic FiniteAdeles) (hr : realGroup g' = p.1 * realGroup g)
    (hfin : finiteGroup g' = f * finiteGroup g) (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    lineSourceAt3 D E y g' x =
      ((((p.1.val 0 0 : ℝ) : ℂ) ^ 2 *
            normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (lineBeta n)) *
          finiteLineFactor D.chi 2 (lineBeta n) f hf) •
        lineSourceAt3 D E y g
          (x * (atFinite (lineBlockGL f hf) * atInfinity (lineLeviBlock p))) := by
  have hc := componentCharacter_eq_one_of_integral D.chi hχ
  have hcomm : bFLine3 g * atInfinity (lineLeviBlock p) =
      atInfinity (lineLeviBlock p) * bFLine3 g := bFin3_comm_atInfinity _ _
  have ht : x * atFinite (lineBlockGL f hf) * bFLine3 g * atInfinity (lineLeviBlock p) =
      x * (atFinite (lineBlockGL f hf) * atInfinity (lineLeviBlock p)) * bFLine3 g := by
    simp only [mul_assoc, hcomm]
  have hu : ∀ i, p.1 * realGroup g * y i = p.1 * (realGroup g * y i) :=
    fun i => mul_assoc _ _ _
  unfold lineSourceAt3
  rw [hr, hu 2, hu 1, hu 0, sub_twist3 D E hχ g g' f hf hfin,
    lineCore_w3 D.chi hc E p (realGroup g) y (x * atFinite (lineBlockGL f hf) * bFLine3 g)
      (finiteLineFactor D.chi 2 (lineBeta n) f hf * cFLine3 D g), ht]
  simp only [map_smul, rho_inv_mul_rho, smul_smul]
  congr 1
  all_goals ring

end Translate3

end TernaryPeriodPolynomials.SourceConstruction

end
