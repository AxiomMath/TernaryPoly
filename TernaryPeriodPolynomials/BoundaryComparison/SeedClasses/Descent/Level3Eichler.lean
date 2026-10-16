module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level3Bridge
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level3Crossed

@[expose] public section


/-!
# Level three, bridge III: period cocycles of `Γ₁(3)` are the Eichler cocycles of `Lemma C.3`

Paper: Lemma C.3
(`ar:lem:seed`), Eichler--Shimura at the level-three plane cusp.

For a library cusp form `f` of weight `n + 3` for `Γ₁(3)` (`liftL3 f` is the same function as a cusp
form for the image of `Gamma1 3`), the library's period cocycle is `(-1)^{n+1}` times the
holomorphic period cocycle `holCocycle (liftL3 f)` (`periodCocycle_eq`), and its reflection
`ι c (k) = ρ(ε) c(ε k ε)` by `ε = diag(-1, 1)` is `-(-1)^e` times the conjugate period cocycle of
the conjugate cusp form `f^*(τ) = \overline{f(-\bar τ)}` (`iotaVal_eq`, from the polynomial
identity `eichlerCocycle_reflect`; `Gamma1 3` is normalized by `J`, `gam3_J_stable`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups Manifold ModularForm
open GeneralEisenstein Matrix MvPolynomial ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3
open UpperHalfPlane
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwistSplitting
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive (V primitive)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (reflection)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel)

theorem map_conj_map_conj' (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext z
    simp
  rw [this, MvPolynomial.map_id]

/-- **Reflection of the Eichler cocycle** for any holomorphic datum: with `D = diag(1, -1)`,
`D · ε_G(ε s ε) = -\overline{ε_{G^*}(s)}`. -/
theorem eichlerCocycle_reflect (n : ℕ) (h : ℂ → ℂ) (G Gs : ℕ → ℂ → ℂ)
    (hG0 : ∀ j, G j Complex.I = 0) (hGs0 : ∀ j, Gs j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (h z * z ^ j) z)
    (hGs : ∀ j z, 0 < z.im → HasDerivAt (Gs j) (conj (h (-conj z)) * z ^ j) z)
    (s : SL(2, ℤ)) :
    Binary.substitute !![1, 0; 0, -1]
        (eichlerCocycle n G (SpecialLinearGroup.mapGL ℝ (modularReflection s))) =
      -MvPolynomial.map (starRingEnd ℂ) (eichlerCocycle n Gs (SpecialLinearGroup.mapGL ℝ s)) := by
  set τ : ℂ := ((s • UpperHalfPlane.I : ℍ) : ℂ) with hτ
  have hτpos : 0 < τ.im := UpperHalfPlane.im_pos _
  have hpar := conj_parity_eichlerPoly n h G Gs hG0 hGs0 hG hGs hτpos
  have hpos : 0 < (SpecialLinearGroup.mapGL ℝ (modularReflection s) : GL (Fin 2) ℝ).det.val := by
    simp [SpecialLinearGroup.mapGL]
  have hpos' : 0 < (SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ).det.val := by
    simp [SpecialLinearGroup.mapGL]
  have hmob : mob (SpecialLinearGroup.mapGL ℝ (modularReflection s)) Complex.I = -conj τ := by
    have := mob_eq_smul (SpecialLinearGroup.mapGL ℝ (modularReflection s)) hpos UpperHalfPlane.I
    exact this.trans (modularReflection_smul_I s)
  have hmob' : mob (SpecialLinearGroup.mapGL ℝ s) Complex.I = τ := by
    have := mob_eq_smul (SpecialLinearGroup.mapGL ℝ s) hpos' UpperHalfPlane.I
    exact this
  unfold eichlerCocycle
  rw [hmob, hmob']
  have := congrArg (MvPolynomial.map (starRingEnd ℂ)) hpar
  rw [map_conj_map_conj', map_neg] at this
  exact this

section Lift

variable {n : ℕ}

/-- A level-three cusp form of the library, as a cusp form for the image of `Gamma1 3`. -/
def liftL3 (f : S (n + 1)) : CuspForm (LamGL Gam3) ((n + 3 : ℕ) : ℤ) :=
  CuspForm.mcast (by simp only [weight]; push_cast; ring) f rfl

theorem liftL3_apply (f : S (n + 1)) (z : ℍ) : liftL3 f z = f z := rfl

/-- The image of `Gamma1 3` in `GL₂(ℝ)` is normalized by `J = diag(-1, 1)`. -/
theorem gam3_J_stable : ∀ γ ∈ LamGL Gam3, UpperHalfPlane.J * γ * UpperHalfPlane.J ∈ LamGL Gam3 := by
  rintro γ ⟨s, hs, rfl⟩
  refine ⟨jConj s, ?_, (J_mul_mapGL_mul_J s).symm⟩
  change s ∈ CongruenceSubgroup.Gamma1 3 at hs
  change jConj s ∈ CongruenceSubgroup.Gamma1 3
  rw [CongruenceSubgroup.Gamma1_mem] at hs ⊢
  obtain ⟨h00, h11, h10⟩ := hs
  simp only [jConj, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  refine ⟨h00, h11, ?_⟩
  simp [h10]

/-- **The library's period cocycle is `(-1)^{n+1}` times the holomorphic period cocycle.** -/
theorem periodCocycle_eq (e : ℤ) (f : S (n + 1)) (k : core) :
    ((periodCocycle (n + 1) e f).val k : MvPolynomial (Fin 2) ℂ) =
      C ((-1 : ℂ) ^ (n + 1)) *
        (eichlerForm (liftL3 f) (coreSL k) : Binary.HomogeneousPoly (n + 1)).val := by
  have hpos : 0 < (SpecialLinearGroup.mapGL ℝ (coreSL k) : GL (Fin 2) ℝ).det.val := by
    simp [SpecialLinearGroup.mapGL]
  have hmob : mob (SpecialLinearGroup.mapGL ℝ (coreSL k)) Complex.I =
      ((coreReal k • I : ℍ) : ℂ) := by
    have := mob_eq_smul (SpecialLinearGroup.mapGL ℝ (coreSL k)) hpos UpperHalfPlane.I
    rw [mapGL_coreSL] at this
    exact this
  rw [periodCocycle_apply]
  change ((primitive (n + 1) (⇑f) ((coreReal k • I : ℍ) : ℂ) : V (n + 1)) :
    MvPolynomial (Fin 2) ℂ) = C ((-1 : ℂ) ^ (n + 1)) *
      eichlerCocycle n (momentPrim (LamGL Gam3) n (liftL3 f))
        (SpecialLinearGroup.mapGL ℝ (coreSL k))
  rw [eichlerCocycle, hmob]
  exact primitive_eq_eichlerPoly n (form_holo f) (momentPrim (LamGL Gam3) n (liftL3 f))
    (momentPrim_zero (LamGL Gam3) n (liftL3 f))
    (fun j z hz => momentPrim_hasDerivAt (LamGL Gam3) n (liftL3 f) j z hz) (coreReal k • I).im_pos

end Lift

section Iota

variable {n : ℕ}

/-- The action of the reflection `ε = diag(-1, 1)` on the underlying polynomial. -/
theorem levelRep_reflection_val (m : ℕ) (e : ℤ) (P : V m) :
    ((levelRep m e reflection P : V m) : MvPolynomial (Fin 2) ℂ) =
      (-1 : ℂ) ^ e • Binary.substitute !![-1, 0; 0, 1] (P : MvPolynomial (Fin 2) ℂ) := by
  rw [SharpBounds.levelRep_ε, Binary.homogeneousAction_coe, Binary.action_apply]
  have hdet : Binary.determinantCharacter e SharpBounds.reflectionC = (-1 : ℂ) ^ e := by
    change ((GeneralLinearGroup.det SharpBounds.reflectionC : ℂˣ) : ℂ) ^ e = _
    rw [SharpBounds.reflectionC_det]
  rw [hdet]
  rfl

/-- `diag(-1, 1)` and `diag(1, -1)` differ by the scalar `(-1)^d` on forms of degree `d`. -/
theorem substitute_negDiag (d : ℕ) (q : Binary.Poly) (hq : q.IsHomogeneous d) :
    Binary.substitute !![-1, 0; 0, 1] q = (-1 : ℂ) ^ d • Binary.substitute !![1, 0; 0, -1] q := by
  have hM : (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.scalar (Fin 2) (-1 : ℂ) * !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  have h := Binary.substitute_comp (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)
    (Matrix.scalar (Fin 2) (-1 : ℂ))
  have h2 := congrArg (fun φ => φ q) h
  simp only [AlgHom.comp_apply] at h2
  rw [hM, ← h2]
  have h3 := binary_substitute_scalar (⟨q, (mem_homogeneousSubmodule _ _).mpr hq⟩ :
    Binary.HomogeneousPoly d) (-1 : ℂ)
  change Binary.substitute (Matrix.scalar (Fin 2) (-1 : ℂ)) q = _ at h3
  rw [h3, map_smul]

end Iota

section Iota2

variable {n : ℕ}

theorem coreSL_conjH (k : core) :
    coreSL (conjH (fun _ hk => conj_mem_core hk) k) = modularReflection (coreSL k) := by
  apply Subtype.ext
  rw [modularReflection_apply]
  ext i j
  rw [coreSL_val]
  change (((reflection : binaryArithmeticLevel).val * (k : binaryArithmeticLevel).val *
    (reflection : binaryArithmeticLevel).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Units.val_mul, Units.val_mul]
  have hk' : ((k : binaryArithmeticLevel).val : Matrix (Fin 2) (Fin 2) ℤ) =
      (coreSL k : Matrix _ _ ℤ) := rfl
  rw [hk']
  fin_cases i <;> fin_cases j <;>
    simp [reflection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

end Iota2

section Iota3

theorem substitute_C_const (M : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) :
    Binary.substitute M (C a) = C a := by
  simp [Binary.substitute]

variable {n : ℕ}

/-- **The reflected period cocycle is the conjugate period cocycle of `f^*`.** -/
theorem iotaVal_eq (e : ℤ) (f : S (n + 1)) (k : core) :
    ((iotaVal (n + 1) e (periodCocycle (n + 1) e f) k : V (n + 1)) :
        MvPolynomial (Fin 2) ℂ) =
      (-((-1 : ℂ) ^ e)) • MvPolynomial.map (starRingEnd ℂ)
        (eichlerForm (fStarGen (LamGL Gam3) gam3_J_stable (liftL3 f)) (coreSL k) :
          Binary.HomogeneousPoly (n + 1)).val := by
  unfold iotaVal
  rw [levelRep_reflection_val, periodCocycle_eq, coreSL_conjH]
  have hq := eichlerCocycle_isHomogeneous n (momentPrim (LamGL Gam3) n (liftL3 f))
    (SpecialLinearGroup.mapGL ℝ (modularReflection (coreSL k)))
  change (-1 : ℂ) ^ e • Binary.substitute !![-1, 0; 0, 1] (C ((-1 : ℂ) ^ (n + 1)) *
    eichlerCocycle n (momentPrim (LamGL Gam3) n (liftL3 f))
      (SpecialLinearGroup.mapGL ℝ (modularReflection (coreSL k)))) = _
  rw [map_mul, substitute_C_const, substitute_negDiag (n + 1) _ hq]
  have href := eichlerCocycle_reflect n (cuspH (LamGL Gam3) n (liftL3 f))
    (momentPrim (LamGL Gam3) n (liftL3 f))
    (momentPrim (LamGL Gam3) n (fStarGen (LamGL Gam3) gam3_J_stable (liftL3 f)))
    (momentPrim_zero _ n _) (momentPrim_zero _ n _) (momentPrim_hasDerivAt _ n _)
    (fun j z hz => by
      have := momentPrim_hasDerivAt (LamGL Gam3) n
        (fStarGen (LamGL Gam3) gam3_J_stable (liftL3 f)) j z hz
      rwa [fStarGen_cuspH (LamGL Gam3) gam3_J_stable (liftL3 f) hz] at this) (coreSL k)
  rw [href]
  change _ = (-((-1 : ℂ) ^ e)) • MvPolynomial.map (starRingEnd ℂ)
    (eichlerCocycle n (momentPrim (LamGL Gam3) n
      (fStarGen (LamGL Gam3) gam3_J_stable (liftL3 f))) (SpecialLinearGroup.mapGL ℝ (coreSL k)))
  have hs : ((-1 : ℂ) ^ (n + 1)) * ((-1 : ℂ) ^ (n + 1)) = 1 := by
    rw [← mul_pow]; norm_num
  simp only [smul_eq_C_mul, map_neg, mul_neg]
  have hC : (C ((-1 : ℂ) ^ (n + 1)) : MvPolynomial (Fin 2) ℂ) * C ((-1 : ℂ) ^ (n + 1)) = 1 := by
    rw [← map_mul, hs, map_one]
  rw [← mul_assoc (C ((-1 : ℂ) ^ (n + 1))) (C ((-1 : ℂ) ^ (n + 1))), hC, one_mul, neg_mul]

end Iota3

end TernaryPeriodPolynomials.Argument.SeedC3S4c
