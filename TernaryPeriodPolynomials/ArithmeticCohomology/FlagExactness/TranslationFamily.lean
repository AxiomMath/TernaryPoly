module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.FilteredUnipotence
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.CoefficientFiltration
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.OrbitPrimitive

@[expose] public section


/-!
# Rational translation families have constant cohomology class

Let `C k` (`k ∈ ℤ`) be homogeneous 2-cocycles on rational vertex tuples with values in
`HomogeneousPoly n`, all equivariant for a subgroup `Γ ≤ q U(ℚ) q⁻¹`, related by a fixed
`h ∈ q U(ℚ) q⁻¹` through `C k (h x) = ρ(h) C (k+1) x`, and periodic: `C K = C 0` for some
`K > 0`. Then `C 1 - C 0` is a `Γ`-coboundary.

Proof. Let `Λ` be the subgroup of `q U(ℚ) q⁻¹` of elements for which all `C k` are
equivariant; it contains `Γ` and is normalized by `h`. On inhomogeneous cocycles of `Λ`,
let `α ω (a, b) = ρ(h⁻¹) ω (h a h⁻¹, h b h⁻¹)`. The base-point prism shows
`[C (k+1)] = α [C k]`, so `α^K` fixes `[C 0]`. The defect of conjugation by `h` is central
and the coefficients carry the unipotent flag filtration, so `α - 1` is nilpotent
(`FilteredUnipotence`). In characteristic zero this forces `α [C 0] = [C 0]`. Finally
restrict to `Γ` and pass to homogeneous cochains (`OrbitPrimitive`).

No regularity of the cochains is used.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.FlagExactness.FilteredUnipotence
open TernaryPeriodPolynomials.FlagExactness.CentralTwist
open TernaryPeriodPolynomials.FlagExactness.Weight

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

variable {n : ℕ} (χ : RankOneCharacter)

/-- Elements of `q U(ℚ) q⁻¹` for which every member of the family is equivariant. -/
def familyStabilizer (q : RationalGL3) (C : ℤ → (Fin 3 → RationalGL3) → HomogeneousPoly n) :
    Subgroup RationalGL3 where
  carrier := {g | g ∈ conjUnitri q ∧
    ∀ k x, C k (fun i => g * x i) = rationalCoefficientComponent n χ g (C k x)}
  one_mem' := ⟨(conjUnitri q).one_mem, fun k x => by simp⟩
  mul_mem' := by
    rintro g g' ⟨hg, eg⟩ ⟨hg', eg'⟩
    refine ⟨(conjUnitri q).mul_mem hg hg', fun k x => ?_⟩
    have e := eg k (fun i => g' * x i)
    simp only [← mul_assoc] at e
    rw [e, eg', ← Module.End.mul_apply, ← map_mul]
  inv_mem' := by
    rintro g ⟨hg, eg⟩
    refine ⟨(conjUnitri q).inv_mem hg, fun k x => ?_⟩
    have e := eg k (fun i => g⁻¹ * x i)
    simp only [mul_inv_cancel_left] at e
    rw [e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem coc4 {C : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    (cocycle : ∀ x : Fin 4 → RationalGL3, C ![x 1, x 2, x 3] - C ![x 0, x 2, x 3] +
      C ![x 0, x 1, x 3] - C ![x 0, x 1, x 2] = 0) (a b c d : RationalGL3) :
    C ![b, c, d] - C ![a, c, d] + C ![a, b, d] - C ![a, b, c] = 0 :=
  cocycle ![a, b, c, d]

/-- **Constancy of the class of a rational translation family** (inhomogeneous form). -/
theorem translation_family_inhomogeneous (q h : RationalGL3) (hh : h ∈ conjUnitri q)
    (Γ : Subgroup RationalGL3) (hΓ : Γ ≤ conjUnitri q)
    (C : ℤ → (Fin 3 → RationalGL3) → HomogeneousPoly n)
    (cocycle : ∀ k (x : Fin 4 → RationalGL3), C k ![x 1, x 2, x 3] - C k ![x 0, x 2, x 3] +
      C k ![x 0, x 1, x 3] - C k ![x 0, x 1, x 2] = 0)
    (shift : ∀ k x, C k (fun i => h * x i) = rationalCoefficientComponent n χ h (C (k + 1) x))
    (equiv : ∀ k, ∀ γ ∈ Γ, ∀ x, C k (fun i => γ * x i) = rationalCoefficientComponent n χ γ (C k x))
    (K : ℕ) (hK : 0 < K) (period : ∀ x, C K x = C 0 x) :
    ∃ τ : Γ → HomogeneousPoly n, ∀ a b : Γ,
      C 1 ![1, a.val, a.val * b.val] - C 0 ![1, a.val, a.val * b.val] =
        rationalCoefficientComponent n χ a.val (τ b) - τ (a * b) + τ a := by
  set ρ := rationalCoefficientComponent n χ
  set Λ := familyStabilizer χ q C
  have hΓΛ : ∀ γ ∈ Γ, γ ∈ Λ := fun γ hγ => ⟨hΓ hγ, fun k x => equiv k γ hγ x⟩
  have shift' : ∀ k x, C (k + 1) x = ρ h⁻¹ (C k (fun i => h * x i)) := by
    intro k x
    rw [shift, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have unshift : ∀ k x, C (k + 1) (fun i => h⁻¹ * x i) = ρ h⁻¹ (C k x) := by
    intro k x
    rw [shift']
    simp only [mul_inv_cancel_left]
  have conj_mem : ∀ g ∈ Λ, h * g * h⁻¹ ∈ Λ := by
    rintro g ⟨hg, eg⟩
    refine ⟨(conjUnitri q).mul_mem ((conjUnitri q).mul_mem hh hg) ((conjUnitri q).inv_mem hh),
      fun k x => ?_⟩
    have e1 := shift k (fun i => g * (h⁻¹ * x i))
    simp only [← mul_assoc] at e1
    rw [e1]
    have e2 := eg (k + 1) (fun i => h⁻¹ * x i)
    simp only [← mul_assoc] at e2
    rw [e2, unshift]
    show ρ h (ρ g (ρ h⁻¹ (C k x))) = ρ (h * g * h⁻¹) (C k x)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc]
  let φ : Λ →* Λ :=
    { toFun := fun g => ⟨h * g.val * h⁻¹, conj_mem g.val g.property⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hφ : ∀ g : Λ, (φ g).val = h * g.val * h⁻¹ := fun g => rfl
  let ρΛ : Representation ℂ Λ (HomogeneousPoly n) := ρ.comp Λ.subtype
  have hρΛ : ∀ (g : Λ) v, ρΛ g v = ρ g.val v := fun g v => rfl
  let A : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n := ρ h⁻¹
  have hA : ∀ (g : Λ) v, A (ρΛ (φ g) v) = ρΛ g (A v) := by
    intro g v
    change ρ h⁻¹ (ρ (h * g.val * h⁻¹) v) = ρ g.val (ρ h⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have hdefect : ∀ a : Λ, (defect φ a).val = a.val⁻¹ * (h * a.val * h⁻¹) := fun a => rfl
  have hcen : ∀ a x : Λ, defect φ a * x = x * defect φ a := by
    intro a x
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hdefect]
    exact conj_defect_comm a.property.1 hh x.property.1
  have hfix : ∀ a : Λ, φ (defect φ a) = defect φ a := by
    intro a
    apply Subtype.ext
    rw [hφ, hdefect]
    have hc := conj_defect_comm a.property.1 hh hh
    rw [← hc]
    group
  -- the inhomogeneous cocycles of the family
  let ω : ℤ → Λ → Λ → HomogeneousPoly n := fun k a b => C k ![1, a.val, a.val * b.val]
  have hCeq : ∀ k (g : Λ) (a b c : RationalGL3),
      C k ![g.val * a, g.val * b, g.val * c] = ρ g.val (C k ![a, b, c]) := by
    intro k g a b c
    have e := g.property.2 k ![a, b, c]
    have ht : (fun i => g.val * (![a, b, c] : Fin 3 → RationalGL3) i) =
        ![g.val * a, g.val * b, g.val * c] := by
      funext i; fin_cases i <;> rfl
    rwa [ht] at e
  have hωc : ∀ k, IsCocycle2 ρΛ (ω k) := by
    intro k a b c
    have e := coc4 (cocycle k) 1 a.val (a.val * b.val) (a.val * b.val * c.val)
    have e1 : ρΛ a (ω k b c) = C k ![a.val, a.val * b.val, a.val * b.val * c.val] := by
      change ρ a.val (C k ![1, b.val, b.val * c.val]) = _
      rw [← hCeq]
      simp only [mul_one, mul_assoc]
    have e2 : ω k (a * b) c = C k ![1, a.val * b.val, a.val * b.val * c.val] := by
      simp only [ω, Subgroup.coe_mul]
    have e3 : ω k a (b * c) = C k ![1, a.val, a.val * b.val * c.val] := by
      simp only [ω, Subgroup.coe_mul, mul_assoc]
    rw [e1, e2, e3]
    exact e
  -- the prism cochain
  let σ : ℤ → Λ → HomogeneousPoly n := fun k a =>
    C k ![1, h, a.val * h] - C k ![1, a.val, a.val * h]
  have prism : ∀ k (a b : Λ), ρΛ a (σ k b) - σ k (a * b) + σ k a =
      C k ![h, a.val * h, a.val * b.val * h] - ω k a b := by
    intro k a b
    have i1 := coc4 (cocycle k) 1 h (a.val * h) (a.val * b.val * h)
    have i2 := coc4 (cocycle k) 1 a.val (a.val * h) (a.val * b.val * h)
    have i3 := coc4 (cocycle k) 1 a.val (a.val * b.val) (a.val * b.val * h)
    have e1 : ρΛ a (σ k b) = C k ![a.val, a.val * h, a.val * b.val * h] -
        C k ![a.val, a.val * b.val, a.val * b.val * h] := by
      change ρ a.val (C k ![1, h, b.val * h] - C k ![1, b.val, b.val * h]) = _
      rw [map_sub, ← hCeq, ← hCeq]
      simp only [mul_one, mul_assoc]
    have e2 : σ k (a * b) = C k ![1, h, a.val * b.val * h] - C k ![1, a.val * b.val, a.val * b.val * h] := by
      simp only [σ, Subgroup.coe_mul]
    rw [e1, e2]
    simp only [σ, ω]
    linear_combination (norm := abel) i2 - i3 - i1
  -- the coboundary space and the twist
  set f := pull2 φ A
  set B := LinearMap.range (dρ ρΛ)
  have hB : ∀ x ∈ B, f x ∈ B := by
    rintro _ ⟨τ, rfl⟩
    exact ⟨pull1 φ A τ, (pull2_dρ hA τ).symm⟩
  have hstep : ∀ k, ω (k + 1) - f (ω k) = dρ ρΛ (pull1 φ A (σ k)) := by
    intro k
    funext a b
    have hp := prism k (φ a) (φ b)
    rw [Pi.sub_apply, Pi.sub_apply, dρ_apply, pull1_apply, pull1_apply, pull1_apply, ← hA,
      map_mul, ← map_sub, ← map_add, hp]
    change C (k + 1) ![1, a.val, a.val * b.val] - ρ h⁻¹ (C k ![1, (φ a).val, (φ a).val * (φ b).val]) =
      ρ h⁻¹ (C k ![h, (φ a).val * h, (φ a).val * (φ b).val * h] - C k ![1, (φ a).val, (φ a).val * (φ b).val])
    rw [shift', map_sub, hφ, hφ]
    have ht : (fun i => h * (![1, a.val, a.val * b.val] : Fin 3 → RationalGL3) i) =
        ![h, h * a.val * h⁻¹ * h, h * a.val * h⁻¹ * (h * b.val * h⁻¹) * h] := by
      funext i
      fin_cases i <;> simp [mul_assoc]
    rw [ht]
  have hiter : ∀ m : ℕ, (f ^ m) (ω 0) - ω m ∈ B := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (f ^ (m + 1)) (ω 0) - ω ((m + 1 : ℕ) : ℤ) =
          f ((f ^ m) (ω 0) - ω m) - (ω ((m : ℤ) + 1) - f (ω m)) := by
        rw [pow_succ', Module.End.mul_apply, map_sub]
        push_cast
        abel
      rw [e, hstep]
      exact B.sub_mem (hB _ ih) ⟨_, rfl⟩
  have hper : (f ^ K) (ω 0) - ω 0 ∈ B := by
    have hK' : ω K = ω 0 := by
      funext a b
      exact period _
    have := hiter K
    rwa [hK'] at this
  have hN : ((f - 1) ^ (3 * (2 * n + 1))) (ω 0) ∈ B :=
    sub_one_pow_mem_range hA (flagFiltration n χ q) (flagFiltration_mono n χ q)
      (flagFiltration_zero n χ q)
      (fun i g v hv => flagFiltration_step χ g.property.1 i v hv)
      (fun i v hv => flagFiltration_step χ ((conjUnitri q).inv_mem hh) i v hv)
      hcen hfix (2 * n + 1) (ω 0) (hωc 0) (fun a b => flagFiltration_top n χ q _)
  have hfix0 := sub_mem_of_unipotent_periodic f B hB (ω 0) _ K hK hN hper
  have hmem : ω 1 - ω 0 ∈ B := by
    have e : ω 1 - ω 0 = (ω (0 + 1) - f (ω 0)) + (f (ω 0) - ω 0) := by
      simp only [zero_add]
      abel
    rw [e, hstep]
    exact B.add_mem ⟨_, rfl⟩ hfix0
  obtain ⟨τΛ, hτΛ⟩ := hmem
  refine ⟨fun a => τΛ ⟨a.val, hΓΛ a.val a.property⟩, fun a b => ?_⟩
  have e := congrFun (congrFun hτΛ ⟨a.val, hΓΛ a.val a.property⟩) ⟨b.val, hΓΛ b.val b.property⟩
  rw [dρ_apply] at e
  exact e.symm

/-- **Constancy of the class of a rational translation family** (homogeneous form). -/
theorem translation_family_primitive (q h : RationalGL3) (hh : h ∈ conjUnitri q)
    (Γ : Subgroup RationalGL3) (hΓ : Γ ≤ conjUnitri q)
    (C : ℤ → (Fin 3 → RationalGL3) → HomogeneousPoly n)
    (cocycle : ∀ k (x : Fin 4 → RationalGL3), C k ![x 1, x 2, x 3] - C k ![x 0, x 2, x 3] +
      C k ![x 0, x 1, x 3] - C k ![x 0, x 1, x 2] = 0)
    (shift : ∀ k x, C k (fun i => h * x i) = rationalCoefficientComponent n χ h (C (k + 1) x))
    (equiv : ∀ k, ∀ γ ∈ Γ, ∀ x, C k (fun i => γ * x i) = rationalCoefficientComponent n χ γ (C k x))
    (K : ℕ) (hK : 0 < K) (period : ∀ x, C K x = C 0 x) :
    ∃ P : cochains Γ (rationalCoefficientComponent n χ) 1,
      ∀ x, (differentialOne Γ (rationalCoefficientComponent n χ) P).val x = C 1 x - C 0 x := by
  obtain ⟨τ, hτ⟩ := translation_family_inhomogeneous χ q h hh Γ hΓ C cocycle shift equiv K hK period
  let D : cochains Γ (rationalCoefficientComponent n χ) 2 :=
    ⟨fun x => C 1 x - C 0 x, fun γ x => by
      change C 1 (fun i => γ.val * x i) - C 0 (fun i => γ.val * x i) = _
      rw [equiv 1 γ.val γ.property, equiv 0 γ.val γ.property, map_sub]⟩
  have hD : ∀ x : Fin 4 → RationalGL3, D.val ![x 1, x 2, x 3] - D.val ![x 0, x 2, x 3] +
      D.val ![x 0, x 1, x 3] - D.val ![x 0, x 1, x 2] = 0 := by
    intro x
    have h1 := cocycle 1 x
    have h0 := cocycle 0 x
    change (C 1 _ - C 0 _) - (C 1 _ - C 0 _) + (C 1 _ - C 0 _) - (C 1 _ - C 0 _) = 0
    linear_combination (norm := abel) h1 - h0
  exact exists_primitive_of_inhomogeneous Γ _ D hD τ hτ

end TernaryPeriodPolynomials.FlagExactness
