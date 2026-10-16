module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceData

@[expose] public section


/-!
# The real law of the plane source

For `p` in the real plane parabolic, the Iwasawa factor satisfies `b(p y) m = p b(y)` with `m`
orthogonal and block diagonal. Together with the cocycle law of the Levi cocycle (which vanishes on
the orthogonal group) and the cocycle law of the radical, this gives the transformation law of the
difference of the two potentials: the constant terms cancel and the potentials transform linearly.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

section Real

variable {n : ℕ}

theorem planeUnipotentPart_eq_one_of_block (p : planeParabolic ℝ) (h02 : p.1.val 0 2 = 0)
    (h12 : p.1.val 1 2 = 0) : planeUnipotentPart p = 1 := by
  show planeUnipotent (p.1.val 0 2 / p.1.val 2 2) (p.1.val 1 2 / p.1.val 2 2) = 1
  rw [h02, h12, zero_div]
  exact planeUnipotent_zero

/-- The radical vanishes on the orthogonal elements of the plane parabolic. -/
theorem planeRadical_orth (χ : RankOneCharacter) {m : planeParabolic ℝ}
    (ho : IsOrthogonalReal m.1) : planeRadical n χ m = 0 := by
  obtain ⟨h02, h12⟩ := orth_planeParabolic_block m.2 ho
  apply LinearMap.ext
  intro Q
  apply Subtype.ext
  simp only [LinearMap.zero_apply, Submodule.coe_zero]
  apply mul_left_cancel₀ X2_ne_zero
  rw [X2_mul_planeRadical, planeUnipotentPart_eq_one_of_block m h02 h12]
  simp

theorem iwP_mul_left (p : planeParabolic ℝ) (y : RealGL3) :
    ∃ m : planeParabolic ℝ, IsOrthogonalReal m.1 ∧ iwP (p.1 * y) * m = p * iwP y := by
  obtain ⟨m, hm, ho, -, hB⟩ := iwasawa_planeParabolic p.2 y
  refine ⟨⟨m, hm⟩, ho, ?_⟩
  apply Subtype.ext
  show iwasawaB (p.1 * y) * m = p.1 * iwasawaB y
  rw [hB, _root_.inv_mul_cancel_right]

/-- The block of an orthogonal element of the plane parabolic is orthogonal. -/
theorem leviBlock_orth (m : planeParabolic ℝ) (hm : IsOrthogonalReal m.1) :
    (leviBlock m).val.transpose * (leviBlock m).val = 1 := by
  have h20 : m.1.val 2 0 = 0 := m.2.1
  have h21 : m.1.val 2 1 = 0 := m.2.2
  have hc : m.1.val.transpose * m.1.val = 1 := hm
  have c00 := congrFun (congrFun hc 0) 0
  have c01 := congrFun (congrFun hc 0) 1
  have c10 := congrFun (congrFun hc 1) 0
  have c11 := congrFun (congrFun hc 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21] at c00 c01 c10 c11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviBlock, blockP, blockOf, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

theorem leviBlock_iwP_mul (p : planeParabolic ℝ) (y : RealGL3) :
    ∃ k : BinaryRealGL, k.val.transpose * k.val = 1 ∧
      iwA (p.1 * y) * k = leviBlock p * iwA y := by
  obtain ⟨m, ho, hm⟩ := iwP_mul_left p y
  refine ⟨leviBlock m, leviBlock_orth m ho, ?_⟩
  have h1 : leviBlock (iwP (p.1 * y) * m) = leviBlock (iwP (p.1 * y)) * leviBlock m :=
    leviBlockHom.map_mul _ _
  have h2 : leviBlock (p * iwP y) = leviBlock p * leviBlock (iwP y) := leviBlockHom.map_mul _ _
  show leviBlock (iwP (p.1 * y)) * leviBlock m = leviBlock p * leviBlock (iwP y)
  rw [← h1, hm, h2]

/-- **The radical law along the Iwasawa factor.** -/
theorem planeRadical_iwP_mul (χ : RankOneCharacter) (p : planeParabolic ℝ) (y : RealGL3)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    planeRadical n χ (iwP (p.1 * y)) Q =
      planeRadical n χ p Q +
        realCoefficientComponent n χ p.1
          (planeRadical n χ (iwP y) (leviStar χ (n + 1) p⁻¹ Q)) := by
  obtain ⟨m, ho, hm⟩ := iwP_mul_left p y
  have h0 : planeRadical n χ m = 0 := planeRadical_orth χ ho
  have e := planeRadical_mul n χ (iwP (p.1 * y)) m Q
  rw [hm, h0, planeRadical_mul n χ p (iwP y) Q, LinearMap.zero_apply, _root_.map_zero,
    add_zero] at e
  exact e.symm

/-- **The Levi cocycle along the Iwasawa factor.** -/
theorem alpha_iwA_mul {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (p : planeParabolic ℝ) (y : RealGL3) (x : BinaryAdelicGL) :
    E.α (iwA (p.1 * y)) x =
      E.α (leviBlock p) x + binaryCohomologicalAction n (leviBlock p) (E.α (iwA y)) x := by
  obtain ⟨k, hk, he⟩ := leviBlock_iwP_mul p y
  have h1 : E.α (iwA (p.1 * y) * k) x = E.α (iwA (p.1 * y)) x := by
    rw [E.cocycle]
    have h0 : E.α k = fun _ => 0 := funext (E.orth k hk)
    rw [h0]
    simp [binaryCohomologicalAction]
  rw [← h1, he, E.cocycle]

theorem componentCharacter_eq_one_of_integral (χ : RankOneCharacter)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1) (g : RealGL3) :
    componentCharacter χ g = 1 :=
  character_real_eq_one χ hχ (GeneralLinearGroup.det g)

theorem leviStar_binaryCoefficient (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (p : planeParabolic ℝ)
    (v : Binary.HomogeneousPoly (n + 1)) :
    leviStar χ (n + 1) p⁻¹ (binaryCoefficient n (leviBlock p) v) = v := by
  have e : leviBlock p⁻¹ = (leviBlock p)⁻¹ := leviBlockHom.map_inv p
  show componentCharacter χ (p⁻¹).1 •
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock p⁻¹))
        (Binary.homogeneousAction (n + 1) (-1)
          (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock p)) v) = v
  rw [hc, one_smul, e, _root_.map_inv, ← Module.End.mul_apply, ← map_mul, _root_.inv_mul_cancel,
    map_one, Module.End.one_apply]

/-- **The transformation law of the differenced potentials.** For `p` in the real plane parabolic,
with `N = |det L|^β` for `L` the `GL₂` block of `p`. -/
theorem planeCore {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (E : LeviCocycleData σ n)
    (p : planeParabolic ℝ) (u : Fin 3 → RealGL3) (t : BinaryAdelicGL) (c : ℂ) :
    (planeRadical n χ (iwP (p.1 * u 2)) - planeRadical n χ (iwP (p.1 * u 1)))
        (c • (E.α (iwA (p.1 * u 1)) t - E.α (iwA (p.1 * u 0)) t)) =
      realCoefficientComponent n χ p.1
        ((c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2)) •
          (planeRadical n χ (iwP (u 2)) - planeRadical n χ (iwP (u 1)))
            (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
              E.α (iwA (u 0)) (t * atInfinity (leviBlock p)))) := by
  have hdiff : E.α (iwA (p.1 * u 1)) t - E.α (iwA (p.1 * u 0)) t =
      normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) •
        binaryCoefficient n (leviBlock p)
          (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
            E.α (iwA (u 0)) (t * atInfinity (leviBlock p))) := by
    rw [alpha_iwA_mul E p (u 1) t, alpha_iwA_mul E p (u 0) t]
    simp only [binaryCohomologicalAction, map_sub, smul_sub]
    abel
  have hstar : leviStar χ (n + 1) p⁻¹
      (c • normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) •
        binaryCoefficient n (leviBlock p)
          (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
            E.α (iwA (u 0)) (t * atInfinity (leviBlock p)))) =
      (c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2)) •
        (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
          E.α (iwA (u 0)) (t * atInfinity (leviBlock p))) := by
    rw [map_smul, map_smul, leviStar_binaryCoefficient χ hc, smul_smul]
  rw [hdiff, LinearMap.sub_apply, planeRadical_iwP_mul χ p (u 2),
    planeRadical_iwP_mul χ p (u 1), hstar]
  simp only [map_smul, map_sub, LinearMap.sub_apply, smul_sub]
  abel

/-- `planeCore` for the vertices `w * y i`. -/
theorem planeCore_w {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (E : LeviCocycleData σ n)
    (p : planeParabolic ℝ) (w : RealGL3) (y : Fin 3 → RealGL3) (t : BinaryAdelicGL) (c : ℂ) :
    (planeRadical n χ (iwP (p.1 * (w * y 2))) - planeRadical n χ (iwP (p.1 * (w * y 1))))
        (c • (E.α (iwA (p.1 * (w * y 1))) t - E.α (iwA (p.1 * (w * y 0))) t)) =
      realCoefficientComponent n χ p.1
        ((c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2)) •
          (planeRadical n χ (iwP (w * y 2)) - planeRadical n χ (iwP (w * y 1)))
            (E.α (iwA (w * y 1)) (t * atInfinity (leviBlock p)) -
              E.α (iwA (w * y 0)) (t * atInfinity (leviBlock p)))) :=
  planeCore χ hc E p (fun i => w * y i) t c

/-! ### Block of the generators -/

theorem planeUnipotent_mem' {R : Type*} [CommRing R] (s t : R) :
    planeUnipotent s t ∈ planeParabolic R := ⟨rfl, rfl⟩

theorem leviBlock_planeLevi (A : BinaryRealGL) (d : ℝˣ) :
    leviBlock ⟨planeLevi A d, planeLevi_mem A d⟩ = A := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem leviBlock_planeUnipotent (s t : ℝ) :
    leviBlock ⟨planeUnipotent s t, planeUnipotent_mem' s t⟩ = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Real

end TernaryPeriodPolynomials.SourceConstruction
