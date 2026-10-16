module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Data

@[expose] public section


/-!
# The real law of the level-three line source

The Levi cocycle laws along the Iwasawa factor only use the cocycle identity and the vanishing on
orthogonal matrices, so they hold verbatim for `LineLeviCocycleData3`.  The radical laws
(`lineRadical_iwPLine_mul`) do not involve the Levi data and are reused.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

section Real3

variable {n : ℕ}

/-- **The Levi cocycle along the Iwasawa factor** (sign-twisted). -/
theorem alpha_iwALine_mul3 {σ : CuspidalRepresentation} (E : LineLeviCocycleData3 σ n)
    (p : lineParabolic ℝ) (y : RealGL3) (x : BinaryAdelicGL) :
    E.α (iwALine (p.1 * y)) x =
      E.α (lineLeviBlock p) x +
        lineSgn (lineLeviBlock p) •
          binaryCohomologicalAction n (lineLeviBlock p) (E.α (iwALine y)) x := by
  obtain ⟨k, hk, he⟩ := lineLeviBlock_iwPLine_mul p y
  have h1 : E.α (iwALine (p.1 * y) * k) x = E.α (iwALine (p.1 * y)) x := by
    rw [E.cocycle]
    have h0 : E.α k = fun _ => 0 := funext (E.orth k hk)
    rw [h0]
    simp [binaryCohomologicalAction]
  rw [← h1, he, E.cocycle]

/-- **The transformation law of the differenced potentials.** -/
theorem lineCore3 {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (E : LineLeviCocycleData3 σ n)
    (p : lineParabolic ℝ) (u : Fin 3 → RealGL3) (t : BinaryAdelicGL) (c : ℂ) :
    (lineRadical n χ (iwPLine (p.1 * u 2)) - lineRadical n χ (iwPLine (p.1 * u 1)))
        (c • (E.α (iwALine (p.1 * u 1)) t - E.α (iwALine (p.1 * u 0)) t)) =
      realCoefficientComponent n χ p.1
        ((c * (((p.1.val 0 0 : ℝ) : ℂ) ^ 2 *
            normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (lineBeta n))) •
          (lineRadical n χ (iwPLine (u 2)) - lineRadical n χ (iwPLine (u 1)))
            (E.α (iwALine (u 1)) (t * atInfinity (lineLeviBlock p)) -
              E.α (iwALine (u 0)) (t * atInfinity (lineLeviBlock p)))) := by
  have e3 : ((n : ℂ) + 3) / 2 = lineBeta n + 1 := by
    unfold lineBeta
    ring
  have hsc := lsCore_scalar c p (lineBeta n)
  rw [← e3] at hsc
  have hdiff : E.α (iwALine (p.1 * u 1)) t - E.α (iwALine (p.1 * u 0)) t =
      (lineSgn (lineLeviBlock p) *
          normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (((n : ℂ) + 3) / 2)) •
        binaryCoefficient n (lineLeviBlock p)
          (E.α (iwALine (u 1)) (t * atInfinity (lineLeviBlock p)) -
            E.α (iwALine (u 0)) (t * atInfinity (lineLeviBlock p))) := by
    rw [alpha_iwALine_mul3 E p (u 1) t, alpha_iwALine_mul3 E p (u 0) t]
    simp only [binaryCohomologicalAction, map_sub, smul_sub, smul_smul]
    abel
  have hstar : lineStar χ (n + 1) p⁻¹
      (c • (lineSgn (lineLeviBlock p) *
          normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (((n : ℂ) + 3) / 2)) •
        binaryCoefficient n (lineLeviBlock p)
          (E.α (iwALine (u 1)) (t * atInfinity (lineLeviBlock p)) -
            E.α (iwALine (u 0)) (t * atInfinity (lineLeviBlock p)))) =
      (c * (((p.1.val 0 0 : ℝ) : ℂ) ^ 2 *
          normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (lineBeta n))) •
        (E.α (iwALine (u 1)) (t * atInfinity (lineLeviBlock p)) -
          E.α (iwALine (u 0)) (t * atInfinity (lineLeviBlock p))) := by
    rw [map_smul, map_smul, lsStar_inv_binaryCoefficient χ hc, smul_smul, smul_smul]
    congr 1
  rw [hdiff, LinearMap.sub_apply, lineRadical_iwPLine_mul χ p (u 2),
    lineRadical_iwPLine_mul χ p (u 1), hstar]
  simp only [map_smul, map_sub, LinearMap.sub_apply, smul_sub]
  abel

/-- `lineCore3` for the vertices `w * y i`. -/
theorem lineCore_w3 {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (E : LineLeviCocycleData3 σ n)
    (p : lineParabolic ℝ) (w : RealGL3) (y : Fin 3 → RealGL3) (t : BinaryAdelicGL) (c : ℂ) :
    (lineRadical n χ (iwPLine (p.1 * (w * y 2))) - lineRadical n χ (iwPLine (p.1 * (w * y 1))))
        (c • (E.α (iwALine (p.1 * (w * y 1))) t - E.α (iwALine (p.1 * (w * y 0))) t)) =
      realCoefficientComponent n χ p.1
        ((c * (((p.1.val 0 0 : ℝ) : ℂ) ^ 2 *
            normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (lineBeta n))) •
          (lineRadical n χ (iwPLine (w * y 2)) - lineRadical n χ (iwPLine (w * y 1)))
            (E.α (iwALine (w * y 1)) (t * atInfinity (lineLeviBlock p)) -
              E.α (iwALine (w * y 0)) (t * atInfinity (lineLeviBlock p)))) :=
  lineCore3 χ hc E p (fun i => w * y i) t c

end Real3

end TernaryPeriodPolynomials.SourceConstruction

end
