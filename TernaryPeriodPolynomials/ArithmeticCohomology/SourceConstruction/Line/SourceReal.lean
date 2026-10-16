module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceData

@[expose] public section


/-!
# The real law of the line source

For `p` in the real line parabolic, the Iwasawa factor satisfies `b(p y) m = p b(y)` with `m`
orthogonal and block diagonal.  Together with the sign-twisted cocycle law of the Levi cocycle (which
vanishes on the orthogonal group) and the cocycle law of the radical, this gives the transformation
law of the difference of the two potentials: the constant terms cancel and the potentials transform
linearly with the scalar `d_p² |det A_p|^{(n+1)/2}`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

section Real

variable {n : ℕ}

theorem iwPLine_mul_left (p : lineParabolic ℝ) (y : RealGL3) :
    ∃ m : lineParabolic ℝ, IsOrthogonalReal m.1 ∧ iwPLine (p.1 * y) * m = p * iwPLine y := by
  obtain ⟨m, hm, ho, -, hB⟩ := iwasawa_lineParabolic p.2 y
  refine ⟨⟨m, hm⟩, ho, ?_⟩
  apply Subtype.ext
  show iwasawaB (p.1 * y) * m = p.1 * iwasawaB y
  rw [hB, _root_.inv_mul_cancel_right]

theorem lineLeviBlock_iwPLine_mul (p : lineParabolic ℝ) (y : RealGL3) :
    ∃ k : BinaryRealGL, k.val.transpose * k.val = 1 ∧
      iwALine (p.1 * y) * k = lineLeviBlock p * iwALine y := by
  obtain ⟨m, ho, hm⟩ := iwPLine_mul_left p y
  refine ⟨lineLeviBlock m, lsLeviBlock_orth m ho, ?_⟩
  have h1 : lineLeviBlock (iwPLine (p.1 * y) * m) =
      lineLeviBlock (iwPLine (p.1 * y)) * lineLeviBlock m :=
    lineLeviBlockHom.map_mul _ _
  have h2 : lineLeviBlock (p * iwPLine y) = lineLeviBlock p * lineLeviBlock (iwPLine y) :=
    lineLeviBlockHom.map_mul _ _
  show lineLeviBlock (iwPLine (p.1 * y)) * lineLeviBlock m =
    lineLeviBlock p * lineLeviBlock (iwPLine y)
  rw [← h1, hm, h2]

/-- **The radical law along the Iwasawa factor.** -/
theorem lineRadical_iwPLine_mul (χ : RankOneCharacter) (p : lineParabolic ℝ) (y : RealGL3)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    lineRadical n χ (iwPLine (p.1 * y)) Q =
      lineRadical n χ p Q +
        realCoefficientComponent n χ p.1
          (lineRadical n χ (iwPLine y) (lineStar χ (n + 1) p⁻¹ Q)) := by
  obtain ⟨m, ho, hm⟩ := iwPLine_mul_left p y
  have h0 : lineRadical n χ m = 0 := lsRadical_orth χ ho
  have e := lineRadical_mul n χ (iwPLine (p.1 * y)) m Q
  rw [hm, h0, lineRadical_mul n χ p (iwPLine y) Q, LinearMap.zero_apply, _root_.map_zero,
    add_zero] at e
  exact e.symm

/-- **The Levi cocycle along the Iwasawa factor** (sign-twisted). -/
theorem alpha_iwALine_mul {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n)
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

/-- **The transformation law of the differenced potentials.** For `p` in the real line parabolic,
with corner `d` and `GL₂` block `L`, the scalar is `d² |det L|^{(n+1)/2}`. -/
theorem lineCore {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (E : LineLeviCocycleData σ n)
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
    rw [alpha_iwALine_mul E p (u 1) t, alpha_iwALine_mul E p (u 0) t]
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

/-- `lineCore` for the vertices `w * y i`. -/
theorem lineCore_w {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (E : LineLeviCocycleData σ n)
    (p : lineParabolic ℝ) (w : RealGL3) (y : Fin 3 → RealGL3) (t : BinaryAdelicGL) (c : ℂ) :
    (lineRadical n χ (iwPLine (p.1 * (w * y 2))) - lineRadical n χ (iwPLine (p.1 * (w * y 1))))
        (c • (E.α (iwALine (p.1 * (w * y 1))) t - E.α (iwALine (p.1 * (w * y 0))) t)) =
      realCoefficientComponent n χ p.1
        ((c * (((p.1.val 0 0 : ℝ) : ℂ) ^ 2 *
            normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (lineBeta n))) •
          (lineRadical n χ (iwPLine (w * y 2)) - lineRadical n χ (iwPLine (w * y 1)))
            (E.α (iwALine (w * y 1)) (t * atInfinity (lineLeviBlock p)) -
              E.α (iwALine (w * y 0)) (t * atInfinity (lineLeviBlock p)))) :=
  lineCore χ hc E p (fun i => w * y i) t c

end Real

end TernaryPeriodPolynomials.SourceConstruction

end
