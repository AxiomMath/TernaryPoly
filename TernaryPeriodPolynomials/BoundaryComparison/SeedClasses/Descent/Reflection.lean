module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EichlerCompare
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.CocycleReflection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.ParityPrimitive
public import Mathlib.Analysis.Calculus.Deriv.Star

@[expose] public section


/-!
# The reflected holomorphic period cocycle is the conjugate period cocycle

The library's parity projections of period classes use the reflection
`(R c)(m) = Π(c(ε m ε))` (`modularCocycleReflection`, `ε = diag(1, -1)`, `Π : Y ↦ -Y`). For the
holomorphic period cocycle of a cusp form `f`, the reflected cocycle is, coefficientwise, minus the
complex conjugate of the Eichler cocycle of `f^*(τ) = \overline{f(-\bar τ)}`
(`modularCocycleReflection_classical`); this identifies the library's parity-projected period classes
with combinations of holomorphic and antiholomorphic seed classes (S4c, Lemma C.3).

Written by Claude Opus 5.5.
-/

open GeneralEisenstein Matrix MvPolynomial UpperHalfPlane ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3

/-- **Reflection of primitives.** If `G' = h z^j` and `G^*' = \overline{h(-\bar z)} z^j` on the
half plane, both vanishing at `i`, then `\overline{G(-\bar τ)} = -(-1)^j G^*(τ)`. -/
theorem conj_neg_conj_primitive (h : ℂ → ℂ) (j : ℕ) (G Gs : ℂ → ℂ)
    (hG0 : G Complex.I = 0) (hGs0 : Gs Complex.I = 0)
    (hG : ∀ z, 0 < z.im → HasDerivAt G (h z * z ^ j) z)
    (hGs : ∀ z, 0 < z.im → HasDerivAt Gs (conj (h (-conj z)) * z ^ j) z)
    {τ : ℂ} (hτ : 0 < τ.im) :
    conj (G (-conj τ)) = -(-1 : ℂ) ^ j * Gs τ := by
  have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_upperHalfPlaneSet
  have hconn : IsPreconnected {u : ℂ | 0 < u.im} := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have hF : ∀ z, 0 < z.im → HasDerivAt (fun w => conj (G (-conj w)))
      (-(-1 : ℂ) ^ j * (conj (h (-conj z)) * z ^ j)) z := by
    intro z hz
    have hmem : 0 < (-conj z).im := by simpa using hz
    have h1 : HasDerivAt (fun w => G (-w)) (-(h (-conj z) * (-conj z) ^ j)) (conj z) := by
      have := (hG (-conj z) hmem).comp (conj z) (hasDerivAt_neg (conj z))
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun w => conj (G (-conj w)))
        (conj (-(h (-conj z) * (-conj z) ^ j))) (conj (conj z)) := h1.conj_conj
    rw [Complex.conj_conj] at h2
    refine h2.congr_deriv ?_
    simp only [map_neg, map_mul, map_pow, Complex.conj_conj]
    rw [neg_pow z j]
    ring
  have heq : Set.EqOn (fun w => conj (G (-conj w))) (fun w => -(-1 : ℂ) ^ j * Gs w)
      {u : ℂ | 0 < u.im} := by
    refine hopen.eqOn_of_deriv_eq hconn
      (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => ((hGs w hw).const_mul _).differentiableAt.differentiableWithinAt)
      (fun w hw => ?_) (show (0 : ℝ) < Complex.I.im by simp) ?_
    · rw [(hF w hw).deriv, ((hGs w hw).const_mul _).deriv]
    · simp [hG0, hGs0, Complex.conj_I]
  exact heq hτ

private theorem substitute_C (c : ℂ) :
    Binary.substitute !![1, 0; 0, -1] (C c : MvPolynomial (Fin 2) ℂ) = C c :=
  (Binary.substitute !![1, 0; 0, -1]).commutes c

private theorem substitute_X0 :
    Binary.substitute !![1, 0; 0, -1] (X 0 : MvPolynomial (Fin 2) ℂ) = X 0 := by
  simp [Binary.substitute, Binary.linearForm, Fin.sum_univ_two]

private theorem substitute_X1 :
    Binary.substitute !![1, 0; 0, -1] (X 1 : MvPolynomial (Fin 2) ℂ) = -X 1 := by
  simp [Binary.substitute, Binary.linearForm, Fin.sum_univ_two]

/-- **Reflection of the Eichler primitive.** -/
theorem conj_parity_eichlerPoly (n : ℕ) (h : ℂ → ℂ) (G Gs : ℕ → ℂ → ℂ)
    (hG0 : ∀ j, G j Complex.I = 0) (hGs0 : ∀ j, Gs j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (h z * z ^ j) z)
    (hGs : ∀ j z, 0 < z.im → HasDerivAt (Gs j) (conj (h (-conj z)) * z ^ j) z)
    {τ : ℂ} (hτ : 0 < τ.im) :
    MvPolynomial.map (starRingEnd ℂ)
        (Binary.substitute !![1, 0; 0, -1] (eichlerPoly n G (-conj τ))) =
      -eichlerPoly n Gs τ := by
  have key : ∀ j, conj (G j (-conj τ)) = -(-1 : ℂ) ^ j * Gs j τ := fun j =>
    conj_neg_conj_primitive h j (G j) (Gs j) (hG0 j) (hGs0 j) (hG j) (hGs j) hτ
  have hs : ∀ j : ℕ, ((-1 : MvPolynomial (Fin 2) ℂ)) ^ j * (-1) ^ j = 1 := fun j => by
    rw [← mul_pow]
    norm_num
  unfold eichlerPoly
  rw [map_sum, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_pow, substitute_C, substitute_X0, substitute_X1]
  simp only [map_mul, map_pow, map_neg, MvPolynomial.map_C, MvPolynomial.map_X, map_one,
    map_natCast, key j]
  rw [neg_pow (X 1 : MvPolynomial (Fin 2) ℂ) j]
  linear_combination (-(C (Gs j τ) * ((n + 1).choose j : MvPolynomial (Fin 2) ℂ) * (-1) ^ (n + 1 - j) *
    X 1 ^ j * X 0 ^ (n + 1 - j) : MvPolynomial (Fin 2) ℂ)) * hs j

/-- `ε m ε · i = -\overline{m · i}` for `ε = diag(1, -1)`. -/
theorem modularReflection_smul_I (m : SpecialLinearGroup (Fin 2) ℤ) :
    ((modularReflection m • UpperHalfPlane.I : ℍ) : ℂ) = -conj ((m • UpperHalfPlane.I : ℍ) : ℂ) := by
  have h := modularReflection_upper m UpperHalfPlane.I
  have hI : UpperHalfPlane.ofComplex (binaryComplexReflection (UpperHalfPlane.I : ℂ)) =
      UpperHalfPlane.I := by
    rw [UpperHalfPlane.coe_I, binaryComplexReflection_basepoint]
    exact UpperHalfPlane.ofComplex_apply UpperHalfPlane.I
  rw [hI] at h
  have hb : binaryComplexReflection ((SpecialLinearGroup.mapGL ℝ m • UpperHalfPlane.I : ℍ) : ℂ) =
      -conj ((SpecialLinearGroup.mapGL ℝ m • UpperHalfPlane.I : ℍ) : ℂ) := by
    simp [binaryComplexReflection]
  change ((SpecialLinearGroup.mapGL ℝ (modularReflection m) • UpperHalfPlane.I : ℍ) : ℂ) =
    -conj ((SpecialLinearGroup.mapGL ℝ m • UpperHalfPlane.I : ℍ) : ℂ)
  rw [← h, hb]

private theorem map_conj_map_conj (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext z
    simp
  rw [this, MvPolynomial.map_id]

/-- **The reflected holomorphic period cocycle.** For a cusp form `f` and the `i`-normalized
primitives `G` of `f(z) z^j` and `G^*` of `\overline{f(-\bar z)} z^j`,
`(R c_f)(m) = -(-1)^{n+1} \overline{ε_{f^*}(m)}` coefficientwise, where `ε` is D's Eichler cocycle. -/
theorem modularCocycleReflection_classical {weight : ℤ}
    (f : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight) (n : ℕ)
    (weight_eq : weight = ((n + 1 : ℕ) : ℤ) + 2) (twist : ℤ) (G Gs : ℕ → ℂ → ℂ)
    (hG0 : ∀ j, G j Complex.I = 0) (hGs0 : ∀ j, Gs j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (ofComplex z) * z ^ j) z)
    (hGs : ∀ j z, 0 < z.im → HasDerivAt (Gs j) (conj (f (ofComplex (-conj z))) * z ^ j) z)
    (m : SpecialLinearGroup (Fin 2) ℤ) :
    (show Binary.HomogeneousPoly (n + 1) from
        modularCocycleReflection (n + 1) twist (classicalBinaryCocycle f (n + 1) weight_eq twist) m).val =
      -(C ((-1 : ℂ) ^ (n + 1)) *
        MvPolynomial.map (starRingEnd ℂ) (eichlerCocycle n Gs (SpecialLinearGroup.mapGL ℝ m))) := by
  set τ : ℂ := ((m • UpperHalfPlane.I : ℍ) : ℂ) with hτ
  have hτpos : 0 < τ.im := UpperHalfPlane.im_pos _
  have hmem : 0 < (-conj τ).im := by simpa using hτpos
  have hP := classicalBinaryPrimitive_eq_eichlerPoly f n G hG0 hG hmem
  have hpar := conj_parity_eichlerPoly n (fun z => f (ofComplex z)) G Gs hG0 hGs0 hG hGs hτpos
  have hsub : Binary.substitute !![1, 0; 0, -1] (eichlerPoly n G (-conj τ)) =
      MvPolynomial.map (starRingEnd ℂ) (-eichlerPoly n Gs τ) := by
    rw [← hpar, map_conj_map_conj]
  have hpos : 0 < (SpecialLinearGroup.mapGL ℝ m : GL (Fin 2) ℝ).det.val := by
    simp [SpecialLinearGroup.mapGL]
  have hmob : mob (SpecialLinearGroup.mapGL ℝ m) Complex.I = τ := by
    have := mob_eq_smul (SpecialLinearGroup.mapGL ℝ m) hpos UpperHalfPlane.I
    exact this
  change Binary.substitute !![1, 0; 0, -1]
      ((classicalBinaryPrimitive f (n + 1)
        ((modularReflection m • UpperHalfPlane.I : ℍ) : ℂ) : Binary.HomogeneousPoly (n + 1)) :
          MvPolynomial (Fin 2) ℂ) = _
  rw [modularReflection_smul_I, ← hτ, hP, map_mul, substitute_C, hsub, eichlerCocycle, hmob, map_neg]
  ring

end TernaryPeriodPolynomials.Argument.SeedC3S4c
