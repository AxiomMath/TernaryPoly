module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3PeriodCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceData

@[expose] public section


/-!
# The parity-projected period cocycle of `Γ₁(3)` is the untwisted level-three Levi cocycle

Formalized by Claude Sonnet 5.5 (AxiomCode).

Plane twin of `L3PeriodCore`.  Let `E` be an untwisted level-three Levi cocycle datum whose values at
the identity adele are given by the classical formula

`E.α K 1 = ½ (P (K i) + J_* P (-conj (K i)))`,   `P = LevelThreePeriodPrimitive.primitive (n + 1) f`

(`L3PlanePeriodFormula`, with a plus sign) for a cusp form `f` for `Γ₁(3)`.  Since the coefficient
action of `J` is the determinant-twist `-1` action of the reflection, the parity projected and
extended period cocycle `levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f)` takes the value
`E.α (A_ℝ) 1` at every `A ∈ Γ₁'(3)` (`l3pp_levelPlus_eq_alpha`).  Consequently, if the values
`E.α(A_ℝ) 1` are a coboundary in `det⁻¹ Sym^{n+1}`, the period class of `f` vanishes
(`l3pp_levelPeriodMap_eq_zero`, `l3pp_levelPeriodMap_eq_zero_smul`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix UpperHalfPlane
open scoped Manifold ModularForm MatrixGroups
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.SharpBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.TwistSplitting
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity
open TernaryPeriodPolynomials.AnalyticClasses
  (basePoint basePoint_mul_J basePoint_J_mul)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (binaryComplexReflection)
open TernaryPeriodPolynomials.SourceConstruction
  (l3p_levelPlus_core_apply l3p_levelPlus_not_core l3p_reflection_real)
open TernaryPeriodPolynomials.LevelThreeSource (LevelLeviCocycleData)

namespace TernaryPeriodPolynomials.EvenLevelThree

/-- The coefficient action of the real reflection `J` is the determinant-twist `-1` action of the
complex reflection. -/
theorem l3pp_binaryCoefficient_J (n : ℕ) (p : Binary.HomogeneousPoly (n + 1)) :
    binaryCoefficient n UpperHalfPlane.J p =
      Binary.homogeneousAction (n + 1) (-1) reflectionC p := by
  have hmat : GeneralLinearGroup.map (algebraMap ℝ ℂ) UpperHalfPlane.J = reflectionC := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectionC, UpperHalfPlane.val_J, GeneralLinearGroup.map_apply]
  have h : binaryCoefficient n UpperHalfPlane.J =
      Binary.homogeneousAction (n + 1) (-1) reflectionC := by
    unfold binaryCoefficient
    rw [hmat]
  rw [h]

/-- The classical formula `α K 1 = ½ (P (K i) + J_* P (-conj (K i)))` for an untwisted Levi cocycle
datum. -/
def L3PlanePeriodFormula {σ : CuspidalRepresentation} {n : ℕ} (E : LevelLeviCocycleData σ n)
    (f : UpperHalfPlane → ℂ) : Prop :=
  ∀ K : BinaryRealGL, E.α K 1 = (2 : ℂ)⁻¹ •
    (LevelThreePeriodPrimitive.primitive (n + 1) f (basePoint K) +
      binaryCoefficient n UpperHalfPlane.J
        (LevelThreePeriodPrimitive.primitive (n + 1) f (binaryComplexReflection (basePoint K))))

/-- On `Γ₁(3)` the parity-projected period cocycle is the Levi cocycle. -/
theorem l3pp_core_eq {σ : CuspidalRepresentation} {n : ℕ} (E : LevelLeviCocycleData σ n)
    (f : S (n + 1)) (hα : L3PlanePeriodFormula E ⇑f) (k : core) :
    (levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f)).val k.val =
      E.α (coreReal k) 1 := by
  rw [l3p_levelPlus_core_apply (n + 1) (-1) f k, hα (coreReal k), l3pp_binaryCoefficient_J]

/-- The untwisted Levi cocycle does not change when its argument is multiplied by `J` on the
right. -/
theorem l3pp_alpha_mul_reflection {σ : CuspidalRepresentation} {n : ℕ}
    (E : LevelLeviCocycleData σ n) (K : BinaryRealGL) :
    E.α (K * UpperHalfPlane.J) 1 = E.α K 1 := by
  have hJ : (UpperHalfPlane.J : BinaryRealGL).val.transpose *
      (UpperHalfPlane.J : BinaryRealGL).val = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [UpperHalfPlane.val_J, Matrix.mul_apply, Fin.sum_univ_two]
  have h0 : binaryCohomologicalAction n K (E.α UpperHalfPlane.J) 1 = 0 := by
    unfold binaryCohomologicalAction
    rw [E.orth UpperHalfPlane.J hJ, map_zero, smul_zero]
  rw [E.cocycle K UpperHalfPlane.J 1, h0, add_zero]

/-- **The parity-projected, extended period cocycle of `f` is the untwisted Levi cocycle** at every
element of `Γ₁'(3)`. -/
theorem l3pp_levelPlus_eq_alpha {σ : CuspidalRepresentation} {n : ℕ}
    (E : LevelLeviCocycleData σ n) (f : S (n + 1)) (hα : L3PlanePeriodFormula E ⇑f)
    (A : binaryArithmeticLevel) :
    (levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f)).val A =
      E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 := by
  by_cases hA : A ∈ core
  · exact l3pp_core_eq E f hα ⟨A, hA⟩
  · have hA' : A * reflection ∈ core := (mem_core_or A).resolve_left hA
    have h1 : (levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f)).val A =
        (levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f)).val (A * reflection) :=
      (l3p_levelPlus_not_core (n + 1) (-1) (periodCocycle (n + 1) (-1) f) hA).trans
        (levelPlus_core (n + 1) (-1) (periodCocycle (n + 1) (-1) f)
          ⟨A * reflection, hA'⟩).symm
    have hmul : (A * reflection) * reflection = A := by
      rw [mul_assoc, reflection_mul_self, mul_one]
    have e : GeneralLinearGroup.map (Int.castRingHom ℝ) A.val =
        GeneralLinearGroup.map (Int.castRingHom ℝ) (A * reflection).val * UpperHalfPlane.J := by
      calc GeneralLinearGroup.map (Int.castRingHom ℝ) A.val
          = GeneralLinearGroup.map (Int.castRingHom ℝ) ((A * reflection) * reflection).val := by
            rw [hmul]
        _ = GeneralLinearGroup.map (Int.castRingHom ℝ) (A * reflection).val *
              UpperHalfPlane.J := by
            rw [Subgroup.coe_mul, map_mul, l3p_reflection_real]
    have e2 : E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) (A * reflection).val) 1 := by
      rw [e, l3pp_alpha_mul_reflection]
    rw [h1, e2]
    exact l3pp_core_eq E f hα ⟨A * reflection, hA'⟩

/-- **If the untwisted Levi values `E.α(A_ℝ) 1` form a coboundary of `Γ₁'(3)` in
`det⁻¹ Sym^{n+1}`, the period class of `f` vanishes.** -/
theorem l3pp_levelPeriodMap_eq_zero {σ : CuspidalRepresentation} {n : ℕ}
    (E : LevelLeviCocycleData σ n) (f : S (n + 1)) (hα : L3PlanePeriodFormula E ⇑f)
    (hcob : ∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        levelRep (n + 1) (-1) A w₀ - w₀) :
    levelPeriodMap (n + 1) (-1) f = 0 := by
  obtain ⟨w₀, hw₀⟩ := hcob
  rw [levelPeriodMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  show _ ∈ LinearMap.range (crossedBoundary (levelRep (n + 1) (-1)))
  rw [LinearMap.mem_range]
  refine ⟨w₀, ?_⟩
  apply Subtype.ext
  funext A
  show levelRep (n + 1) (-1) A w₀ - w₀ =
    (levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f)).val A
  rw [l3pp_levelPlus_eq_alpha E f hα A, hw₀ A]

/-- The same with a nonzero scalar multiple of the Levi values. -/
theorem l3pp_levelPeriodMap_eq_zero_smul {σ : CuspidalRepresentation} {n : ℕ}
    (E : LevelLeviCocycleData σ n) (f : S (n + 1)) (hα : L3PlanePeriodFormula E ⇑f)
    (c : ℂ) (hc : c ≠ 0)
    (hcob : ∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      c • E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        levelRep (n + 1) (-1) A w₀ - w₀) :
    levelPeriodMap (n + 1) (-1) f = 0 := by
  obtain ⟨w₀, hw₀⟩ := hcob
  refine l3pp_levelPeriodMap_eq_zero E f hα ⟨c⁻¹ • w₀, fun A => ?_⟩
  rw [map_smul]
  exact ((eq_inv_smul_iff₀ hc).mpr (hw₀ A)).trans (smul_sub _ _ _)

end TernaryPeriodPolynomials.EvenLevelThree

end
