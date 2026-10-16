module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Parity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerData
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.NormalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarNonvanishing

@[expose] public section


/-!
# The parity-projected period cocycle of `Γ₁(3)` is the level-three Levi cocycle

Let `E` be a sign-twisted level-three Levi cocycle datum whose values at the identity adele are given
by the classical formula

`E.α K 1 = ½ (P (K i) - J_* P (-conj (K i)))`,   `P = LevelThreePeriodPrimitive.primitive (n + 1) f`

(`L3PeriodFormula`) for a cusp form `f` for `Γ₁(3)`.  Then for every `A ∈ Γ₁'(3)` the parity projected
and extended period cocycle `levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 f)` takes the value
`E.α (A_ℝ) 1` at `A` (`l3p_levelPlus_eq_alpha`).  Consequently, if the values `(n + 1) E.α(A_ℝ) 1` are a
coboundary in `Sym^{n+1}`, the parity-projected period class of `f` vanishes
(`l3p_levelPeriodMap_eq_zero`).  Algebra only: the analytic identification of the formula is in
`L3PeriodAlpha`.

Original work by Claude Opus 5.5 (AxiomCode).
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

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## Generic evaluation lemmas -/

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {H : Subgroup G} {ε : G}

/-- The `ι`-symmetric part of a cocycle, evaluated. -/
theorem l3p_plusPart_apply (ρ : Representation ℂ G V) (hεε : ε * ε = 1)
    (normal : ∀ k ∈ H, ε * k * ε ∈ H) (z : crossedCocycles (ρ.comp H.subtype)) (k : H) :
    (plusPart ρ hεε normal z).val k = (2 : ℂ)⁻¹ • (z.val k + ρ ε (z.val (conjH normal k))) := by
  rfl

end Generic

/-- The parity-projected extension at an element outside `Γ₁(3)`: the value at `g` is the value of the
projection at `g ε`. -/
theorem l3p_levelPlus_not_core (m : ℕ) (e : ℤ) (z : crossedCocycles (coreRep m e))
    {g : binaryArithmeticLevel} (hg : g ∉ core) :
    (levelPlus m e z).val g =
      (plusPart (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk) z).val
        ⟨g * reflection, (mem_core_or g).resolve_left hg⟩ :=
  extendFun_not_mem (H := core) (ε := reflection) mem_core_or (levelRep m e)
    (plusPart (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk) z) hg

/-! ## The reflection in the coefficient representation -/

/-- The binary action with determinant twist `e` is `det ^ e` times the twist-zero action. -/
theorem l3p_homogeneousAction_twist (d : ℕ) (e : ℤ) (A : Binary.GL2) :
    Binary.homogeneousAction d e A =
      (((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ e) • Binary.homogeneousAction d 0 A := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, LinearMap.smul_apply, Submodule.coe_smul,
    Binary.homogeneousAction_coe, Binary.action_apply, Binary.action_apply, smul_smul]
  congr 1
  change ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ e =
    ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ e * ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ (0 : ℤ)
  rw [zpow_zero, mul_one]

/-- The twisted coefficient action of the real reflection is minus the untwisted one. -/
theorem l3p_binaryCoefficient_J (n : ℕ) (p : Binary.HomogeneousPoly (n + 1)) :
    binaryCoefficient n UpperHalfPlane.J p =
      -(Binary.homogeneousAction (n + 1) 0 reflectionC p) := by
  have hmat : GeneralLinearGroup.map (algebraMap ℝ ℂ) UpperHalfPlane.J = reflectionC := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectionC, UpperHalfPlane.val_J, GeneralLinearGroup.map_apply]
  have h : binaryCoefficient n UpperHalfPlane.J = Binary.homogeneousAction (n + 1) (-1) reflectionC := by
    unfold binaryCoefficient
    rw [hmat]
  rw [h, l3p_homogeneousAction_twist (n + 1) (-1) reflectionC, reflectionC_det,
    LinearMap.smul_apply]
  simp

/-! ## `Γ₁(3)` inside `GL₂(ℝ)` -/

theorem l3p_coreReal_eq (k : core) :
    coreReal k = GeneralLinearGroup.map (Int.castRingHom ℝ) (k : binaryArithmeticLevel).val := rfl

/-- The real image of the reflection `diag(-1, 1) ∈ Γ₁'(3)` is `J`. -/
theorem l3p_reflection_real :
    GeneralLinearGroup.map (Int.castRingHom ℝ) (reflection : binaryArithmeticLevel).val =
      UpperHalfPlane.J := by
  exact TernaryPeriodPolynomials.SphericalDetection.Helpers.binaryIntegerReflection_real

/-- Conjugation of `Γ₁(3)` by the reflection is conjugation by `J` in `GL₂(ℝ)`. -/
theorem l3p_coreReal_conj (k : core) :
    coreReal (conjH (H := core) (ε := reflection) (fun _ hk => conj_mem_core hk) k) =
      UpperHalfPlane.J * coreReal k * UpperHalfPlane.J := by
  rw [l3p_coreReal_eq (conjH (H := core) (ε := reflection) (fun _ hk => conj_mem_core hk) k),
    l3p_coreReal_eq k]
  change GeneralLinearGroup.map (Int.castRingHom ℝ)
    (((reflection : binaryArithmeticLevel) * (k : binaryArithmeticLevel) *
      (reflection : binaryArithmeticLevel) : binaryArithmeticLevel) :
        GeneralLinearGroup (Fin 2) ℤ) = _
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, l3p_reflection_real]

/-! ## The parity-projected period cocycle on `Γ₁(3)` -/

/-- **The parity projection of the period cocycle on `Γ₁(3)`**:
`½ (P (K i) + ε · P (-conj (K i)))`. -/
theorem l3p_levelPlus_core_apply (m : ℕ) (e : ℤ) (f : S m) (k : core) :
    (levelPlus m e (periodCocycle m e f)).val k.val =
      (2 : ℂ)⁻¹ • (LevelThreePeriodPrimitive.primitive m ⇑f (basePoint (coreReal k)) +
        Binary.homogeneousAction m e reflectionC
          (LevelThreePeriodPrimitive.primitive m ⇑f
            (binaryComplexReflection (basePoint (coreReal k))))) := by
  have h1 : (periodCocycle m e f).val k =
      LevelThreePeriodPrimitive.primitive m ⇑f (basePoint (coreReal k)) := rfl
  have h2 : (periodCocycle m e f).val
      (conjH (H := core) (ε := reflection) (fun _ hk => conj_mem_core hk) k) =
        LevelThreePeriodPrimitive.primitive m ⇑f
          (binaryComplexReflection (basePoint (coreReal k))) := by
    have hc := l3p_coreReal_conj k
    change LevelThreePeriodPrimitive.primitive m ⇑f (basePoint (coreReal
      (conjH (H := core) (ε := reflection) (fun _ hk => conj_mem_core hk) k))) = _
    rw [hc, basePoint_mul_J, basePoint_J_mul]
  rw [levelPlus_core, l3p_plusPart_apply, levelRep_ε]
  exact congrArg (fun x => (2 : ℂ)⁻¹ • x)
    (congrArg₂ (· + ·) h1
      (congrArg (fun p => Binary.homogeneousAction m e reflectionC p) h2))

/-! ## Comparison with a Levi cocycle -/

/-- The classical formula `α K 1 = ½ (P (K i) - J_* P (-conj (K i)))` for a Levi cocycle datum. -/
def L3PeriodFormula {σ : CuspidalRepresentation} {n : ℕ} (E : LineLeviCocycleData3 σ n)
    (f : UpperHalfPlane → ℂ) : Prop :=
  ∀ K : BinaryRealGL, E.α K 1 = (2 : ℂ)⁻¹ •
    (LevelThreePeriodPrimitive.primitive (n + 1) f (basePoint K) -
      binaryCoefficient n UpperHalfPlane.J
        (LevelThreePeriodPrimitive.primitive (n + 1) f (binaryComplexReflection (basePoint K))))

/-- On `Γ₁(3)` the parity-projected period cocycle is the Levi cocycle. -/
theorem l3p_core_eq {σ : CuspidalRepresentation} {n : ℕ} (E : LineLeviCocycleData3 σ n)
    (f : S (n + 1)) (hα : L3PeriodFormula E ⇑f) (k : core) :
    (levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 f)).val k.val = E.α (coreReal k) 1 := by
  rw [l3p_levelPlus_core_apply, hα (coreReal k), l3p_binaryCoefficient_J, sub_neg_eq_add]

/-- The Levi cocycle does not change when its argument is multiplied by `J` on the right. -/
theorem l3p_alpha_mul_reflection {σ : CuspidalRepresentation} {n : ℕ}
    (E : LineLeviCocycleData3 σ n) (K : BinaryRealGL) :
    E.α (K * UpperHalfPlane.J) 1 = E.α K 1 := by
  have hJ : (UpperHalfPlane.J : BinaryRealGL).val.transpose *
      (UpperHalfPlane.J : BinaryRealGL).val = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [UpperHalfPlane.val_J, Matrix.mul_apply, Fin.sum_univ_two]
  have h0 : binaryCohomologicalAction n K (E.α UpperHalfPlane.J) 1 = 0 := by
    unfold binaryCohomologicalAction
    rw [E.orth UpperHalfPlane.J hJ, map_zero, smul_zero]
  rw [E.cocycle K UpperHalfPlane.J 1, h0, smul_zero, add_zero]

/-- **The parity-projected, extended period cocycle of `f` is the Levi cocycle** at every element of
`Γ₁'(3)`. -/
theorem l3p_levelPlus_eq_alpha {σ : CuspidalRepresentation} {n : ℕ}
    (E : LineLeviCocycleData3 σ n) (f : S (n + 1)) (hα : L3PeriodFormula E ⇑f)
    (A : binaryArithmeticLevel) :
    (levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 f)).val A =
      E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 := by
  by_cases hA : A ∈ core
  · exact l3p_core_eq E f hα ⟨A, hA⟩
  · have hA' : A * reflection ∈ core := (mem_core_or A).resolve_left hA
    have h1 : (levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 f)).val A =
        (levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 f)).val (A * reflection) :=
      (l3p_levelPlus_not_core (n + 1) 0 (periodCocycle (n + 1) 0 f) hA).trans
        (levelPlus_core (n + 1) 0 (periodCocycle (n + 1) 0 f) ⟨A * reflection, hA'⟩).symm
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
      rw [e, l3p_alpha_mul_reflection]
    rw [h1, e2]
    exact l3p_core_eq E f hα ⟨A * reflection, hA'⟩

/-! ## A coboundary kills the period class -/

/-- **If the Levi values `(n + 1) E.α(A_ℝ) 1` form a coboundary of `Γ₁'(3)` in `Sym^{n+1}`, the
parity-projected period class of `f` vanishes.** -/
theorem l3p_levelPeriodMap_eq_zero {σ : CuspidalRepresentation} {n : ℕ}
    (E : LineLeviCocycleData3 σ n) (f : S (n + 1)) (hα : L3PeriodFormula E ⇑f)
    (hcob : ∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        binaryArithmeticRepresentation n A w₀ - w₀) :
    levelPeriodMap (n + 1) 0 f = 0 := by
  obtain ⟨w₀, hw₀⟩ := hcob
  have hw₁ : ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        levelRep (n + 1) 0 A w₀ - w₀ := hw₀
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [levelPeriodMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  show _ ∈ LinearMap.range (crossedBoundary (levelRep (n + 1) 0))
  rw [LinearMap.mem_range]
  refine ⟨((n + 1 : ℕ) : ℂ)⁻¹ • w₀, ?_⟩
  apply Subtype.ext
  funext A
  show levelRep (n + 1) 0 A (((n + 1 : ℕ) : ℂ)⁻¹ • w₀) - ((n + 1 : ℕ) : ℂ)⁻¹ • w₀ =
    (levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 f)).val A
  have key : E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
      ((n + 1 : ℕ) : ℂ)⁻¹ • (levelRep (n + 1) 0 A w₀ - w₀) := by
    rw [← hw₁ A, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [l3p_levelPlus_eq_alpha E f hα A, key, map_smul, smul_sub]

/-! ## Weights -/

/-- A cusp form for `Γ₁(3)` of weight `k = m + 2`, as an element of `S m`. -/
theorem l3p_exists_S_cast {k : ℤ} (m : ℕ) (h : k = (m : ℤ) + 2)
    (f : CuspForm TernaryPeriodPolynomials.EisensteinRegularization.Helpers.binaryRealGammaOneThree k) :
    ∃ g : S m, (g : UpperHalfPlane → ℂ) = f := by
  subst h
  exact ⟨f, rfl⟩

end TernaryPeriodPolynomials.SourceConstruction

end
