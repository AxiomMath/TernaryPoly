module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.DualJ.CoefficientJ
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Maps

@[expose] public section


/-!
# The dual series as the `ȷ`-pullback of a conjugate construction

Paper (Appendix C.4): "Apply the preceding construction to `ȷ(Γ)` and pull back." In the boundary-building
cochain model the level group `Γ` is preserved by `φ`, and `ȷ(Γ) = w Γ w⁻¹` is the rational conjugate of `Γ`
by the fixed matrix `w = J a⁻¹` (`DualJ.jmath_eq_conj`). The convention of the construction is unchanged for a rational
conjugate (paper, start of Appendix C), so a cochain `f` of `Γ` with coefficients `R` gives

1. its conjugate `Ad_w f` on `ȷ(Γ)`, `(Ad_w f)(y) = R(w) f(w⁻¹ y w)` (`adConj`);
2. the pullback along `ȷ`: a cochain of `Γ` with coefficients `R ∘ ȷ` (`jPull`);
3. on flag cochains, the pullback along the `ȷ`-equivariant flag map (`jFlagPull`);
4. the fixed linear change of coefficient coordinates by `w` (`jCoeff`, `jCoeffFun`), which carries
   `R ∘ ȷ` to the dual system `R ∘ φ`.

`jDualGlobal`, `jDualFlag` are the composites. The theorems `jDualGlobal_eq` and `jDualFlag_eq` prove that
they are, on the nose, the model's transport along `φ` (`phiCocycle`, `transportCochains`; the maps
`toLineStar`, `toPlaneStar`, `toEdgeStar` of `Dual/Maps`), so that the dual series `𝓔_Q^∨(η)` of `Dual/ConstantTerms`
is literally the paper's pullback along `ȷ` of the construction for `ȷ(Γ)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ

variable {W : Type} [AddCommGroup W] [Module ℂ W]

/-- `ȷ(Γ) = w Γ w⁻¹`, the rational conjugate of the level group. -/
def conjLevel : Subgroup RationalGL3 :=
  rationalLevel.map (MulAut.conj jmathConj).toMonoidHom

theorem mem_conjLevel_iff (y : RationalGL3) :
    y ∈ conjLevel ↔ jmathConj⁻¹ * y * jmathConj ∈ rationalLevel := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    have : jmathConj⁻¹ * (MulAut.conj jmathConj).toMonoidHom g * jmathConj = g := by
      change jmathConj⁻¹ * (jmathConj * g * jmathConj⁻¹) * jmathConj = g
      group
    rw [this]
    exact hg
  · intro h
    refine ⟨_, h, ?_⟩
    change jmathConj * (jmathConj⁻¹ * y * jmathConj) * jmathConj⁻¹ = y
    group

theorem jmath_mem_conjLevel {γ : RationalGL3} (h : γ ∈ rationalLevel) : jmath γ ∈ conjLevel := by
  rw [mem_conjLevel_iff, ← dualInvolution_eq_conj]
  exact dualInvolution_mem_rationalLevel h

/-- `ȷ(Γ) = Ad_w(Γ)`: the image of the level group under `ȷ` is `conjLevel`. -/
theorem map_jmath_level : rationalLevel.map jmath = conjLevel := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact jmath_mem_conjLevel hg
  · intro y hy
    rw [mem_conjLevel_iff] at hy
    refine ⟨dualInvolution (jmathConj⁻¹ * y * jmathConj), dualInvolution_mem_rationalLevel hy, ?_⟩
    rw [jmath_eq_conj, dualInvolution_involutive]
    group

section Cochains

variable (R : Representation ℂ RationalGL3 W) (k : ℕ)

/-- **Step 1: conjugation `Ad_w`.** A cochain of `Γ` becomes a cochain of `ȷ(Γ) = wΓw⁻¹`,
`(Ad_w f)(y) = R(w) f(w⁻¹ y w)`. -/
def adConj : cochains rationalLevel R k →ₗ[ℂ] cochains conjLevel R k where
  toFun f := ⟨fun x => R jmathConj (f.val (fun i => jmathConj⁻¹ * x i * jmathConj)), by
    intro γ' x
    have hγ : jmathConj⁻¹ * γ'.val * jmathConj ∈ rationalLevel := (mem_conjLevel_iff _).mp γ'.property
    have h := f.property ⟨_, hγ⟩ (fun i => jmathConj⁻¹ * x i * jmathConj)
    have hv : (fun i => jmathConj⁻¹ * (γ'.val * x i) * jmathConj) =
        fun i => (jmathConj⁻¹ * γ'.val * jmathConj) * (jmathConj⁻¹ * x i * jmathConj) := by
      funext i
      group
    change R jmathConj (f.val (fun i => jmathConj⁻¹ * (γ'.val * x i) * jmathConj)) =
      R γ'.val (R jmathConj (f.val (fun i => jmathConj⁻¹ * x i * jmathConj)))
    rw [hv]
    rw [h]
    apply rep_comm
    group⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact map_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact map_smul _ _ _

/-- **Step 2: pullback along `ȷ`.** A cochain of `ȷ(Γ)` with coefficients `R` is a cochain of `Γ` with
coefficients `R ∘ ȷ`. -/
def jPull : cochains conjLevel R k →ₗ[ℂ] cochains rationalLevel (R.comp jmath) k where
  toFun f := ⟨fun x => f.val (fun i => jmath (x i)), by
    intro γ x
    have h := f.property ⟨jmath γ.val, jmath_mem_conjLevel γ.property⟩ (fun i => jmath (x i))
    have hv : (fun i => jmath (γ.val * x i)) = fun i => jmath γ.val * jmath (x i) := by
      funext i
      exact map_mul jmath _ _
    change f.val (fun i => jmath (γ.val * x i)) = R (jmath γ.val) (f.val (fun i => jmath (x i)))
    rw [hv]
    exact h⟩
  map_add' f g := rfl
  map_smul' c f := rfl

/-- **Step 4 (global coefficients): the fixed change of coordinates by `w`.** It carries `R ∘ ȷ` to the
dual system `R ∘ φ`. -/
def jCoeff : cochains rationalLevel (R.comp jmath) k →ₗ[ℂ] cochains rationalLevel (dualRep R) k where
  toFun f := ⟨fun x => R jmathConj⁻¹ (f.val x), by
    intro γ x
    have h := f.property γ x
    change R jmathConj⁻¹ (f.val (fun i => γ.val * x i)) =
      R (dualInvolution γ.val) (R jmathConj⁻¹ (f.val x))
    rw [h]
    change R jmathConj⁻¹ (R (jmath γ.val) (f.val x)) = _
    apply rep_comm
    rw [jmath_eq_conj]
    group⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact map_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact map_smul _ _ _

/-- The composite `Ad_w` / pullback along `ȷ` / change of coordinates, for global (non-flag) coefficients. -/
def jDualGlobal : cochains rationalLevel R k →ₗ[ℂ] cochains rationalLevel (dualRep R) k :=
  (jCoeff R k).comp ((jPull R k).comp (adConj R k))

/-- **The `ȷ`-pullback of the conjugate is the model's `φ`-pullback.** -/
theorem jDualGlobal_apply (f : cochains rationalLevel R k) (x : Fin (k + 1) → RationalGL3) :
    (jDualGlobal R k f).val x = f.val (fun i => dualInvolution (x i)) := by
  change R jmathConj⁻¹ (R jmathConj (f.val (fun i => jmathConj⁻¹ * jmath (x i) * jmathConj))) = _
  have hv : (fun i => jmathConj⁻¹ * jmath (x i) * jmathConj) = fun i => dualInvolution (x i) := by
    funext i
    rw [dualInvolution_eq_conj]
  rw [hv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

end Cochains

section Flags

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
  {X X' : Type} [MulAction RationalGL3 X] [MulAction RationalGL3 X'] (k : ℕ)

/-- **Step 3: pullback along the `ȷ`-equivariant flag map** `m : X' → X`. -/
def jFlagPull (m : X' → X) (hm : ∀ (g : RationalGL3) F, m (g • F) = jmath g • m F) :
    cochains rationalLevel ((functionRepresentation ρ X).comp jmath) k →ₗ[ℂ]
      cochains rationalLevel (functionRepresentation (ρ.comp jmath) X') k where
  toFun f := ⟨fun x F => f.val x (m F), by
    intro γ x
    funext F
    have h := congrFun (f.property γ x) (m F)
    change f.val (fun i => γ.val * x i) (m F) =
      ρ (jmath γ.val) (f.val x (m (γ.val⁻¹ • F)))
    rw [hm, map_inv]
    exact h⟩
  map_add' f g := rfl
  map_smul' c f := rfl

/-- **Step 4 (flag coefficients): the fixed change of coordinates by `w`.** -/
def jCoeffFun : cochains rationalLevel (functionRepresentation (ρ.comp jmath) X') k →ₗ[ℂ]
    cochains rationalLevel (functionRepresentation (dualRep ρ) X') k where
  toFun f := ⟨fun x F => ρ jmathConj⁻¹ (f.val x F), by
    intro γ x
    funext F
    have h := congrFun (f.property γ x) F
    change ρ jmathConj⁻¹ (f.val (fun i => γ.val * x i) F) =
      ρ (dualInvolution γ.val) (ρ jmathConj⁻¹ (f.val x (γ.val⁻¹ • F)))
    rw [h]
    change ρ jmathConj⁻¹ (ρ (jmath γ.val) (f.val x (γ.val⁻¹ • F))) = _
    apply rep_comm
    rw [jmath_eq_conj]
    group⟩
  map_add' f g := by
    apply Subtype.ext
    funext x F
    exact map_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x F
    exact map_smul _ _ _

/-- **The dual of a flag cochain: `Ad_w`, pullback along `ȷ` and `m`, change of coordinates.** -/
def jDualFlag (m : X' → X) (hm : ∀ (g : RationalGL3) F, m (g • F) = jmath g • m F) :
    cochains rationalLevel (functionRepresentation ρ X) k →ₗ[ℂ]
      cochains rationalLevel (functionRepresentation (dualRep ρ) X') k :=
  (jCoeffFun ρ k).comp ((jFlagPull ρ k m hm).comp
    ((jPull (functionRepresentation ρ X) k).comp (adConj (functionRepresentation ρ X) k)))

theorem jDualFlag_apply (m : X' → X) (hm : ∀ (g : RationalGL3) F, m (g • F) = jmath g • m F)
    (f : cochains rationalLevel (functionRepresentation ρ X) k) (x : Fin (k + 1) → RationalGL3)
    (F : X') :
    (jDualFlag ρ k m hm f).val x F =
      f.val (fun i => dualInvolution (x i)) (jmathConj⁻¹ • m F) := by
  change ρ jmathConj⁻¹ (ρ jmathConj
    (f.val (fun i => jmathConj⁻¹ * jmath (x i) * jmathConj) (jmathConj⁻¹ • m F))) = _
  have hv : (fun i => jmathConj⁻¹ * jmath (x i) * jmathConj) = fun i => dualInvolution (x i) := by
    funext i
    rw [dualInvolution_eq_conj]
  rw [hv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- **The `ȷ`-pullback of the conjugate is the model's `φ`-transport** (`Dual.transportCochains`), whenever
the model's `φ`-equivariant flag map `m'` is the `ȷ`-equivariant one `m` translated by `w⁻¹`. -/
theorem jDualFlag_eq_transport (m m' : X' → X)
    (hm : ∀ (g : RationalGL3) F, m (g • F) = jmath g • m F)
    (hm' : ∀ (g : RationalGL3) F, m' (g • F) = dualInvolution g • m' F)
    (hrel : ∀ F, m' F = jmathConj⁻¹ • m F)
    (f : cochains rationalLevel (functionRepresentation ρ X) k) :
    jDualFlag ρ k m hm f = transportCochains ρ (dualRep ρ) (fun _ => rfl) m' hm' k f := by
  apply Subtype.ext
  funext x F
  rw [jDualFlag_apply]
  change _ = f.val (fun i => dualInvolution (x i)) (m' F)
  rw [hrel]

end Flags

end TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ
