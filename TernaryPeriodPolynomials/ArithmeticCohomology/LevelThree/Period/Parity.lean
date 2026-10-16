module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Parabolic

@[expose] public section


/-!
# The parity-projected period map to `H¹(Γ₁'(3), Sym^m ⊗ det^e)`

`Γ₁'(3) = Γ₁(3) ⊔ Γ₁(3) ε` with `ε = diag(-1, 1)`. The involution `ι z (k) = ε · z(ε k ε)` of the
cocycles of `Γ₁(3)` splits them into `ι`-invariant ones, which extend to cocycles of `Γ₁'(3)` with
coefficients `Sym^m ⊗ det^e` (`TwistSplitting.extendCocycle`), and `ι`-anti-invariant ones, which
extend to cocycles with coefficients `Sym^m ⊗ det^{e+1}`.

* `extendLin`: the extension as a *linear* map, for any linear `P` landing in the compatible
  cocycles;
* `levelPeriodMap m e : S_{m+2}(Γ₁(3)) →ₗ H¹(Γ₁'(3), Sym^m ⊗ det^e)`, the class of the extension of
  `(c + ι c)/2` for the period cocycle `c` of a cusp form (the `+` parity projection);
* `levelPeriodMapMinus m e : S_{m+2}(Γ₁(3)) →ₗ H¹(Γ₁'(3), Sym^m ⊗ det^{e+1})`, the `-` projection;
* both take values in the parabolic classes (`levelPeriodMap_mem_parabolic`), and restrict on
  `Γ₁(3)` to the `±` parts of the period class (`restrict_levelPeriodMap`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix UpperHalfPlane
open scoped Manifold ModularForm MatrixGroups
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.TwistSplitting
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParabolic

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {H : Subgroup G} {ε : G}
variable (cover : ∀ g : G, g ∈ H ∨ g * ε ∈ H)
variable (ρ ρ' : Representation ℂ G V)

theorem extendFun_add (z w : crossedCocycles (ρ.comp H.subtype)) (g : G) :
    extendFun cover ρ (z + w) g = extendFun cover ρ z g + extendFun cover ρ w g := by
  by_cases h : g ∈ H
  · rw [extendFun_mem cover ρ _ h, extendFun_mem cover ρ _ h, extendFun_mem cover ρ _ h]
    rfl
  · rw [extendFun_not_mem cover ρ _ h, extendFun_not_mem cover ρ _ h,
      extendFun_not_mem cover ρ _ h]
    rfl

theorem extendFun_smul (a : ℂ) (z : crossedCocycles (ρ.comp H.subtype)) (g : G) :
    extendFun cover ρ (a • z) g = a • extendFun cover ρ z g := by
  by_cases h : g ∈ H
  · rw [extendFun_mem cover ρ _ h, extendFun_mem cover ρ _ h]
    rfl
  · rw [extendFun_not_mem cover ρ _ h, extendFun_not_mem cover ρ _ h]
    rfl

/-- **Linear extension.** A linear endomorphism `P` of the cocycles of `H` whose values satisfy the
compatibility `z(ε k ε) = ρ'(ε) z(k)` extends to a linear map into the `ρ'`-cocycles of `G`. -/
def extendLin (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (agree : ∀ k : H, ρ' k.val = ρ k.val)
    (P : crossedCocycles (ρ.comp H.subtype) →ₗ[ℂ] crossedCocycles (ρ.comp H.subtype))
    (hP : ∀ (z : crossedCocycles (ρ.comp H.subtype)) (k : H),
      (P z).val (conjH normal k) = ρ' ε ((P z).val k)) :
    crossedCocycles (ρ.comp H.subtype) →ₗ[ℂ] crossedCocycles ρ' where
  toFun z := extendCocycle cover ρ ρ' hεε normal agree (P z) (hP z)
  map_add' z w := by
    apply Subtype.ext
    funext g
    change extendFun cover ρ (P (z + w)) g =
      extendFun cover ρ (P z) g + extendFun cover ρ (P w) g
    rw [map_add, extendFun_add]
  map_smul' a z := by
    apply Subtype.ext
    funext g
    change extendFun cover ρ (P (a • z)) g = a • extendFun cover ρ (P z) g
    rw [map_smul, extendFun_smul]

theorem extendLin_apply (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (agree : ∀ k : H, ρ' k.val = ρ k.val)
    (P : crossedCocycles (ρ.comp H.subtype) →ₗ[ℂ] crossedCocycles (ρ.comp H.subtype))
    (hP : ∀ (z : crossedCocycles (ρ.comp H.subtype)) (k : H),
      (P z).val (conjH normal k) = ρ' ε ((P z).val k))
    (z : crossedCocycles (ρ.comp H.subtype)) (k : H) :
    (extendLin cover ρ ρ' hεε normal agree P hP z).val k.val = (P z).val k :=
  extendCocycle_mem cover ρ ρ' hεε normal agree (P z) (hP z) k

/-- The `ι`-symmetric projection as a linear map. -/
def plusLin (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H) :
    crossedCocycles (ρ.comp H.subtype) →ₗ[ℂ] crossedCocycles (ρ.comp H.subtype) :=
  (2 : ℂ)⁻¹ • (LinearMap.id + conjCocycle hεε normal ρ)

theorem plusLin_apply (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (z : crossedCocycles (ρ.comp H.subtype)) :
    plusLin ρ hεε normal z = plusPart ρ hεε normal z := rfl

/-- The `ι`-antisymmetric projection as a linear map. -/
def minusLin (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H) :
    crossedCocycles (ρ.comp H.subtype) →ₗ[ℂ] crossedCocycles (ρ.comp H.subtype) :=
  (2 : ℂ)⁻¹ • (LinearMap.id - conjCocycle hεε normal ρ)

theorem minusLin_apply (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (z : crossedCocycles (ρ.comp H.subtype)) :
    minusLin ρ hεε normal z = minusPart ρ hεε normal z := rfl

end Generic

/-! ### The two projections for `Γ₁'(3) ⊇ Γ₁(3)` -/

section Level

variable (m : ℕ) (e : ℤ)

/-- The `+` projection and extension to `Γ₁'(3)`, coefficients `Sym^m ⊗ det^e`. -/
def levelPlus : crossedCocycles (coreRep m e) →ₗ[ℂ] crossedCocycles (levelRep m e) :=
  extendLin (H := core) (ε := reflection) mem_core_or (levelRep m e) (levelRep m e)
    reflection_mul_self (fun _ hk => conj_mem_core hk) (fun _ => rfl)
    (plusLin (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk))
    (fun z k => plusPart_conj (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk)
      z k)

/-- The `-` projection and extension to `Γ₁'(3)`, coefficients `Sym^m ⊗ det^{e+1}`. -/
def levelMinus : crossedCocycles (coreRep m e) →ₗ[ℂ] crossedCocycles (levelRep m (e + 1)) :=
  extendLin (H := core) (ε := reflection) mem_core_or (levelRep m e) (levelRep m (e + 1))
    reflection_mul_self (fun _ hk => conj_mem_core hk) (fun k => ExactLevel.twist_agree m e k)
    (minusLin (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk))
    (fun z k => minusPart_conj (levelRep m e) (levelRep m (e + 1)) reflection_mul_self
      (fun _ hk => conj_mem_core hk) (ExactLevel.twist_anti m e) z k)

theorem levelPlus_core (z : crossedCocycles (coreRep m e)) (k : core) :
    (levelPlus m e z).val k.val = (plusPart (levelRep m e) reflection_mul_self
      (fun _ hk => conj_mem_core hk) z).val k :=
  extendLin_apply (H := core) (ε := reflection) mem_core_or (levelRep m e) (levelRep m e)
    reflection_mul_self (fun _ hk => conj_mem_core hk) (fun _ => rfl)
    (plusLin (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk))
    (fun z k => plusPart_conj (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk)
      z k) z k

theorem levelMinus_core (z : crossedCocycles (coreRep m e)) (k : core) :
    (levelMinus m e z).val k.val = (minusPart (levelRep m e) reflection_mul_self
      (fun _ hk => conj_mem_core hk) z).val k :=
  extendLin_apply (H := core) (ε := reflection) mem_core_or (levelRep m e) (levelRep m (e + 1))
    reflection_mul_self (fun _ hk => conj_mem_core hk) (fun k => ExactLevel.twist_agree m e k)
    (minusLin (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk))
    (fun z k => minusPart_conj (levelRep m e) (levelRep m (e + 1)) reflection_mul_self
      (fun _ hk => conj_mem_core hk) (ExactLevel.twist_anti m e) z k) z k

/-- **The parity-projected period map**
`S_{m+2}(Γ₁(3)) → H¹(Γ₁'(3), Sym^m ⊗ det^e)` (the `+` part of the period class). -/
def levelPeriodMap : S m →ₗ[ℂ] CrossedH1 (levelRep m e) :=
  classMap (levelRep m e) (levelPlus m e ∘ₗ periodCocycleMap m e)

/-- The `-` part of the period class, with coefficients `Sym^m ⊗ det^{e+1}`. -/
def levelPeriodMapMinus : S m →ₗ[ℂ] CrossedH1 (levelRep m (e + 1)) :=
  classMap (levelRep m (e + 1)) (levelMinus m e ∘ₗ periodCocycleMap m e)

theorem levelPeriodMap_apply (f : S m) :
    levelPeriodMap m e f =
      (crossedBoundaries (levelRep m e)).mkQ (levelPlus m e (periodCocycle m e f)) :=
  classMap_apply (levelRep m e) (levelPlus m e ∘ₗ periodCocycleMap m e) f

theorem levelPeriodMapMinus_apply (f : S m) :
    levelPeriodMapMinus m e f =
      (crossedBoundaries (levelRep m (e + 1))).mkQ (levelMinus m e (periodCocycle m e f)) :=
  classMap_apply (levelRep m (e + 1)) (levelMinus m e ∘ₗ periodCocycleMap m e) f

/-- **Parabolicity of the parity-projected classes.** -/
theorem levelPeriodMap_mem_parabolic (f : S m) :
    levelPeriodMap m e f ∈ parabolicH1 (levelRep m e) (upper 1) (lower 1) := by
  have hp := periodCocycle_mem_parabolic m e f
  have pp := plusPart_parabolic (levelRep m e) reflection_mul_self
    (fun _ hk => conj_mem_core hk) (upper 1) (lower 1) coreT.property coreL.property
    SharpBounds.hεT SharpBounds.hεL (periodCocycle m e f) hp
  refine ⟨levelPlus m e (periodCocycle m e f), ⟨?_, ?_⟩, rfl⟩
  · have e1 : (levelPlus m e (periodCocycle m e f)).val (upper 1) =
        (plusPart (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk)
          (periodCocycle m e f)).val coreT := levelPlus_core m e (periodCocycle m e f) coreT
    rw [e1]
    exact pp.1
  · have e1 : (levelPlus m e (periodCocycle m e f)).val (lower 1) =
        (plusPart (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk)
          (periodCocycle m e f)).val coreL := levelPlus_core m e (periodCocycle m e f) coreL
    rw [e1]
    exact pp.2

/-- **Parabolicity of the `-` projection.** -/
theorem levelPeriodMapMinus_mem_parabolic (f : S m) :
    levelPeriodMapMinus m e f ∈ parabolicH1 (levelRep m (e + 1)) (upper 1) (lower 1) := by
  have hp := periodCocycle_mem_parabolic m e f
  have pp := minusPart_parabolic (levelRep m e) reflection_mul_self
    (fun _ hk => conj_mem_core hk) (upper 1) (lower 1) coreT.property coreL.property
    SharpBounds.hεT SharpBounds.hεL (periodCocycle m e f) hp
  refine ⟨levelMinus m e (periodCocycle m e f), ⟨?_, ?_⟩, rfl⟩
  · have e1 : (levelMinus m e (periodCocycle m e f)).val (upper 1) =
        (minusPart (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk)
          (periodCocycle m e f)).val coreT := levelMinus_core m e (periodCocycle m e f) coreT
    rw [e1, moved_agree (levelRep m e) (levelRep m (e + 1)) (ExactLevel.twist_agree m e) (upper 1)
      coreT.property]
    exact pp.1
  · have e1 : (levelMinus m e (periodCocycle m e f)).val (lower 1) =
        (minusPart (levelRep m e) reflection_mul_self (fun _ hk => conj_mem_core hk)
          (periodCocycle m e f)).val coreL := levelMinus_core m e (periodCocycle m e f) coreL
    rw [e1, moved_agree (levelRep m e) (levelRep m (e + 1)) (ExactLevel.twist_agree m e) (lower 1)
      coreL.property]
    exact pp.2

end Level

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity
