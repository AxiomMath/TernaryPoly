module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Primitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ExactLevel
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeBasic

@[expose] public section


/-!
# The Eichler–Shimura period cocycle of a cusp form for `Γ₁(3)`

`core = ⟨T, L⟩ ⊆ Γ₁'(3)` is `Γ₁(3)` (`coreSL` identifies it with Mathlib's
`CongruenceSubgroup.Gamma1 3`: `coreSL_mem`, `exists_core_of_mem`), and its image in `GL₂(ℝ)`
lies in `binaryRealGammaOneThree = Γ₁(3)`, the level of Mathlib's
`CuspForm binaryRealGammaOneThree k`. For a cusp form `f` of weight `m + 2` the holomorphic primitive `P` of `f(z) (X₀ - z X₁)^m dz` with
`P(i) = 0` (`LevelThreePeriodPrimitive.primitive`) satisfies `P(γ z) = P(γ i) + γ · P(z)`, so
`γ ↦ P(γ i)` is a crossed cocycle with values in `Sym^m ⊗ det^e` (`periodCocycle`), in exactly the
coefficient convention `coreRep m e` of the level-three dimension theorems (`ExactLevel`,
`Existence`). The cocycle is linear in `f` (`periodCocycleMap`), and its class defines

`levelThreePeriodMap m e : S_{m+2}(Γ₁(3)) →ₗ[ℂ] H¹(Γ₁(3), Sym^m ⊗ det^e)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix UpperHalfPlane
open scoped Manifold ModularForm MatrixGroups
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.ExactLevel
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle

/-! ### `Γ₁(3)` as a group of real matrices and as `Gamma1 3` -/

/-- `Γ₁(3) → GL₂(ℝ)`. -/
def coreReal : core →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map (Int.castRingHom ℝ)).comp
    (binaryArithmeticLevel.subtype.comp core.subtype)

theorem coreReal_val (k : core) :
    (coreReal k).val = (k : binaryArithmeticLevel).val.val.map (Int.castRingHom ℝ) := rfl

theorem core_det_val (k : core) : (k : binaryArithmeticLevel).val.val.det = 1 := by
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) (core_det k)
  simpa [GeneralLinearGroup.val_det_apply] using h

theorem coreReal_det (k : core) : (coreReal k).val.det = 1 := by
  rw [coreReal_val, show (k : binaryArithmeticLevel).val.val.map (Int.castRingHom ℝ) =
      (Int.castRingHom ℝ).mapMatrix (k : binaryArithmeticLevel).val.val from rfl,
    ← RingHom.map_det, core_det_val, map_one]

/-- `Γ₁(3) → SL₂(ℤ)`. -/
def coreSL : core →* SL(2, ℤ) where
  toFun k := ⟨(k : binaryArithmeticLevel).val.val, core_det_val k⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coreSL_val (k : core) : ((coreSL k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
    (k : binaryArithmeticLevel).val.val := rfl

theorem coreSL_injective : Function.Injective coreSL := by
  intro k l h
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun g : SL(2, ℤ) => (g : Matrix (Fin 2) (Fin 2) ℤ)) h

theorem coreSL_mem (k : core) : coreSL k ∈ CongruenceSubgroup.Gamma1 3 := by
  have level := (mem_binaryArithmeticLevel_iff (k : binaryArithmeticLevel).val).mp
    (k : binaryArithmeticLevel).property
  have h0 := level 0
  have h1 := level 1
  simp only [ite_eq_right (show (0 : Fin 2) ≠ 1 by decide)] at h0 h1
  have hdet := congrArg (fun x : ℤ => (x : ZMod 3)) (core_det_val k)
  simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one, h0, h1] at hdet
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, h1, h0⟩
  rw [coreSL_val]
  erw [mul_one, mul_zero, sub_zero] at hdet
  exact hdet

theorem mapGL_coreSL (k : core) : SpecialLinearGroup.mapGL ℝ (coreSL k) = coreReal k := by
  apply Units.ext
  ext i j
  simp [coreReal_val, coreSL_val, SpecialLinearGroup.mapGL]

theorem coreReal_mem (k : core) : coreReal k ∈ binaryRealGammaOneThree :=
  ⟨coreSL k, coreSL_mem k, mapGL_coreSL k⟩

/-- An element of `Gamma1 3`, as an element of `Γ₁'(3)`. -/
def levelOf (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 3) : binaryArithmeticLevel :=
  ⟨SpecialLinearGroup.toGL γ, by
    rw [CongruenceSubgroup.Gamma1_mem] at hγ
    apply (mem_binaryArithmeticLevel_iff _).mpr
    intro column
    fin_cases column
    · simpa using hγ.2.2
    · simpa using hγ.2.1⟩

/-- **`Gamma1 3 ⊆ Γ₁(3) = ⟨T, L⟩`.** -/
theorem exists_core_of_mem (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 3) :
    ∃ k : core, coreSL k = γ := by
  rcases mem_core_or (levelOf γ hγ) with h | h
  · refine ⟨⟨levelOf γ hγ, h⟩, ?_⟩
    ext i j
    rfl
  · exfalso
    have hdet := core_det ⟨_, h⟩
    have hval := congrArg (fun u : ℤˣ => (u : ℤ)) hdet
    simp only [Subgroup.coe_mul, Units.val_one] at hval
    rw [GeneralLinearGroup.val_det_apply] at hval
    change ((SpecialLinearGroup.toGL γ).val * reflection.val.val).det = 1 at hval
    rw [Matrix.det_mul] at hval
    have hγdet : (SpecialLinearGroup.toGL γ).val.det = 1 := γ.property
    have hr : (reflection : GL (Fin 2) ℤ).val.det = -1 := by
      simp [reflection, Matrix.det_fin_two]
    rw [hγdet, hr] at hval
    norm_num at hval

/-! ### Invariance and coefficient conventions -/

variable (m : ℕ) (e : ℤ)

/-- The weight. -/
abbrev weight : ℤ := (m : ℤ) + 2

/-- Level-three cusp forms of weight `m + 2`. -/
abbrev S := CuspForm binaryRealGammaOneThree (weight m)

variable {m}

theorem form_invariant (f : S m) (k : core) : (⇑f) ∣[weight m] coreReal k = ⇑f :=
  SlashInvariantFormClass.slash_action_eq f _ (coreReal_mem k)

theorem form_holo (f : S m) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f) := CuspFormClass.holo f

variable (m)

theorem complexify_coreReal (k : core) :
    complexify (coreReal k) = binaryIntegralComplex (k : binaryArithmeticLevel).val := by
  apply Units.ext
  ext i j
  simp [coreReal_val, binaryIntegralComplex]

/-- `coreRep m e` is `Sym^m ⊗ det^e` of the real matrix. -/
theorem coreRep_eq (k : core) :
    coreRep m e k = Binary.homogeneousAction m e (complexify (coreReal k)) := by
  rw [complexify_coreReal]
  rfl

/-! ### The period cocycle -/

/-- The primitive of a level-three cusp form. -/
abbrev periodPrimitive (f : S m) : ℂ → V m := primitive m ⇑f

/-- The period relation `P(γ z) = P(γ i) + γ · P(z)`. -/
theorem primitive_core (f : S m) (k : core) (z : ℍ) :
    periodPrimitive m f ((coreReal k • z : ℍ) : ℂ) =
      periodPrimitive m f ((coreReal k • I : ℍ) : ℂ) + coreRep m e k (periodPrimitive m f z) := by
  rw [coreRep_eq]
  exact primitive_modular m e (form_holo f) (coreReal k) (coreReal_det k) (form_invariant f k) z

/-- **The Eichler–Shimura period cocycle** `γ ↦ P(γ i)` on `Γ₁(3)`. -/
def periodCocycle (f : S m) : crossedCocycles (coreRep m e) :=
  ⟨fun k => periodPrimitive m f ((coreReal k • I : ℍ) : ℂ), by
    intro g h
    change periodPrimitive m f ((coreReal (g * h) • I : ℍ) : ℂ) =
      periodPrimitive m f ((coreReal g • I : ℍ) : ℂ) +
        coreRep m e g (periodPrimitive m f ((coreReal h • I : ℍ) : ℂ))
    rw [map_mul, mul_smul]
    exact primitive_core m e f g _⟩

theorem periodCocycle_apply (f : S m) (k : core) :
    (periodCocycle m e f).val k = periodPrimitive m f ((coreReal k • I : ℍ) : ℂ) := rfl

/-- The primitive is a primitive of the cocycle, at every base point. -/
theorem periodCocycle_primitive (f : S m) (k : core) (z : ℍ) :
    (periodCocycle m e f).val k =
      periodPrimitive m f ((coreReal k • z : ℍ) : ℂ) - coreRep m e k (periodPrimitive m f z) := by
  rw [periodCocycle_apply, primitive_core m e f k z, add_sub_cancel_right]

/-- The period cocycle as a linear map. -/
def periodCocycleMap : S m →ₗ[ℂ] crossedCocycles (coreRep m e) where
  toFun := periodCocycle m e
  map_add' f g := by
    apply Subtype.ext
    funext k
    change primitive m ⇑(f + g) _ = primitive m ⇑f _ + primitive m ⇑g _
    rw [FunLike.coe_add]
    exact primitive_add m (form_holo f) (form_holo g) _ (coreReal k • I).im_pos
  map_smul' c f := by
    apply Subtype.ext
    funext k
    change primitive m ⇑(c • f) _ = c • primitive m ⇑f _
    rw [FunLike.coe_smul]
    exact primitive_smul m c (form_holo f) _ (coreReal k • I).im_pos

theorem periodCocycleMap_apply (f : S m) : periodCocycleMap m e f = periodCocycle m e f := rfl

/-- The class map `X → H¹(ρ)` of a linear map into the cocycles, for a generic representation
(proved abstractly so that no unfolding of `coreRep` is attempted). -/
def classMap {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G V) (L : X →ₗ[ℂ] crossedCocycles ρ) : X →ₗ[ℂ] CrossedH1 ρ :=
  (crossedBoundaries ρ).mkQ ∘ₗ L

theorem classMap_apply {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X]
    [Module ℂ X] (ρ : Representation ℂ G V) (L : X →ₗ[ℂ] crossedCocycles ρ) (x : X) :
    classMap ρ L x = (crossedBoundaries ρ).mkQ (L x) := rfl

/-- **The level-three Eichler–Shimura period map**
`S_{m+2}(Γ₁(3)) → H¹(Γ₁(3), Sym^m ⊗ det^e)`. -/
def levelThreePeriodMap : S m →ₗ[ℂ] CrossedH1 (coreRep m e) :=
  classMap (coreRep m e) (periodCocycleMap m e)

theorem levelThreePeriodMap_apply (f : S m) :
    levelThreePeriodMap m e f = (crossedBoundaries (coreRep m e)).mkQ (periodCocycle m e f) :=
  classMap_apply (coreRep m e) (periodCocycleMap m e) f

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
