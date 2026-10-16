module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeH1

@[expose] public section


/-!
# Hecke equivariance of the level-three period map

Let `α_j` (`j` in a finite index set) be right-coset representatives of `Γ₁(3)` in `GL₂(ℚ)`
(`HeckeH1.RightCosets`) of positive determinant, and let `h ∈ S_{m+2}(Γ₁(3))` be a cusp form with
`h = ∑_j det(α_j)^{-e} f ∣[m+2] α_j` (for `T_p`, `det α_j = p`, so `h = p^{-e} T_p f`).

The Eichler integral of `f` along each `α_j` is a primitive of `det(α_j)^{-e} f ∣ α_j`
(`LevelThreePeriodPrimitive.transform_isPrimitive`), so the Hecke trace `∑_j σ(α_j)⁻¹ P_f(α_j z)` is
a primitive of `h`, hence equals `P_h` up to a constant `κ` (`trace_eq`). By
`LevelThreeHeckeH1.crossedHeckeFun_primitive` the Hecke image of the period cocycle of `f` is
`z ↦ trace(γ i) - γ · trace(i)`, i.e. the period cocycle of `h` minus the coboundary of `κ`
(`periodMap_hecke`): the period class of `h` is the Hecke image of the period class of `f`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix UpperHalfPlane
open scoped Manifold ModularForm MatrixGroups
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
open TernaryPeriodPolynomials.Spectral.HeckeH1

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHecke

/-! ### Sums of primitives -/

section Sums

variable (m : ℕ)

theorem pointForm_sum {ι : Type*} (s : Finset ι) (g : ι → ℍ → ℂ) (z : ℂ) :
    pointForm m (∑ i ∈ s, g i) z = ∑ i ∈ s, pointForm m (g i) z := by
  simp only [pointForm, Finset.sum_apply, Finset.sum_smul]

theorem isPrimitive_sum {ι : Type*} (s : Finset ι) (g : ι → ℍ → ℂ) (P : ι → ℂ → V m)
    (h : ∀ i ∈ s, IsPrimitive m (g i) (P i)) :
    IsPrimitive m (∑ i ∈ s, g i) (fun z => ∑ i ∈ s, P i z) := by
  intro ℓ z hz
  rw [pointForm_sum, map_sum]
  have : (fun w => ℓ (∑ i ∈ s, P i w)) = fun w => ∑ i ∈ s, ℓ (P i w) := by
    funext w
    rw [map_sum]
  rw [this]
  exact HasDerivAt.fun_sum (fun i hi => h i hi ℓ z hz)

end Sums

/-! ### Rational matrices -/

section Rational

variable (m : ℕ) (e : ℤ)

/-- The real points of a rational matrix. -/
abbrev toReal : GL (Fin 2) ℚ →* GL (Fin 2) ℝ := GeneralLinearGroup.map (Rat.castHom ℝ)

theorem complexify_toReal (a : GL (Fin 2) ℚ) :
    complexify (toReal a) = GeneralLinearGroup.map (algebraMap ℚ ℂ) a := by
  apply Units.ext
  ext i j
  simp [complexify, toReal, GeneralLinearGroup.map_apply]

theorem rationalRho_eq (a : GL (Fin 2) ℚ) :
    rationalRho m e a = Binary.homogeneousAction m e (complexify (toReal a)) := by
  rw [complexify_toReal]
  rfl

theorem rationalRho_inv (a : GL (Fin 2) ℚ) :
    rationalRho m e a⁻¹ = Binary.homogeneousAction m e (complexify (toReal a))⁻¹ := by
  rw [rationalRho_eq, map_inv, map_inv]

theorem toReal_det (a : GL (Fin 2) ℚ) :
    (toReal a).val.det = ((a.val.det : ℚ) : ℝ) := by
  change ((a.val).map (Rat.castHom ℝ)).det = _
  exact (RingHom.map_det (Rat.castHom ℝ) a.val).symm

theorem toReal_det_pos (a : GL (Fin 2) ℚ) (ha : 0 < (((a.det : ℚˣ)) : ℚ)) :
    0 < (toReal a).val.det := by
  rw [toReal_det]
  have : (a.val.det : ℚ) = ((a.det : ℚˣ) : ℚ) := (GeneralLinearGroup.val_det_apply a).symm
  rw [this]
  exact_mod_cast ha

theorem compat_of {embed : core →* GL (Fin 2) ℚ} (hφ : ∀ k, toReal (embed k) = coreReal k)
    (k : core) : coreRep m e k = rationalRho m e (embed k) := by
  rw [coreRep_eq, rationalRho_eq, hφ]

end Rational

/-! ### The Hecke trace of the Eichler integral -/

section Trace

variable (m : ℕ) (e : ℤ) {embed : core →* GL (Fin 2) ℚ} (Sx : RightCosets embed)
  (hpos : ∀ j, 0 < (((Sx.rep j).det : ℚˣ) : ℚ))

/-- The Hecke trace of the Eichler integral, as a function on `ℂ`. -/
def traceIntegral (f : S m) (z : ℂ) : V m :=
  ∑ j, rationalRho m e (Sx.rep j)⁻¹ (primitive m ⇑f ((toReal (Sx.rep j) • ofComplex z : ℍ) : ℂ))

include hpos in
/-- The Hecke trace is a primitive of `∑_j det(α_j)^{-e} f ∣ α_j`. -/
theorem traceIntegral_isPrimitive (f : S m) :
    IsPrimitive m (∑ j, (((toReal (Sx.rep j)).val.det : ℂ) ^ (-e)) •
      (⇑f ∣[(m : ℤ) + 2] toReal (Sx.rep j))) (traceIntegral m e Sx f) := by
  have h := isPrimitive_sum m (Finset.univ : Finset Sx.index)
    (fun j => (((toReal (Sx.rep j)).val.det : ℂ) ^ (-e)) •
      (⇑f ∣[(m : ℤ) + 2] toReal (Sx.rep j)))
    (fun j z => Binary.homogeneousAction m e (complexify (toReal (Sx.rep j)))⁻¹
      (primitive m ⇑f ((toReal (Sx.rep j) • ofComplex z : ℍ) : ℂ)))
    (fun j _ => transform_isPrimitive m e (form_holo f) (toReal (Sx.rep j))
      (toReal_det_pos _ (hpos j)))
  have hfun : traceIntegral m e Sx f = fun z => ∑ j,
      Binary.homogeneousAction m e (complexify (toReal (Sx.rep j)))⁻¹
        (primitive m ⇑f ((toReal (Sx.rep j) • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [traceIntegral, rationalRho_inv]
  rw [hfun]
  exact h

end Trace

/-! ### Hecke equivariance -/

section Main

variable (m : ℕ) (e : ℤ) {embed : core →* GL (Fin 2) ℚ} (Sx : RightCosets embed)
  (hemb : Function.Injective embed) (hφ : ∀ k, toReal (embed k) = coreReal k)
  (hpos : ∀ j, 0 < (((Sx.rep j).det : ℚˣ) : ℚ))

include hpos in
/-- **The Hecke trace of the Eichler integral of `f` is the Eichler integral of `h` up to a
constant.** -/
theorem trace_eq (f h : S m)
    (hh : ⇑h = ∑ j, (((toReal (Sx.rep j)).val.det : ℂ) ^ (-e)) •
      (⇑f ∣[(m : ℤ) + 2] toReal (Sx.rep j))) (ζ : ℍ) :
    traceIntegral m e Sx f (ζ : ℂ) =
      primitive m ⇑h (ζ : ℂ) + traceIntegral m e Sx f Complex.I := by
  have hprim : IsPrimitive m ⇑h (traceIntegral m e Sx f) := by
    rw [hh]
    exact traceIntegral_isPrimitive m e Sx hpos f
  exact eq_primitive_add m (form_holo h) _ hprim ζ ζ.im_pos

include hemb hφ hpos in
/-- **Hecke equivariance of the period map.** If `h = ∑_j det(α_j)^{-e} f ∣[m+2] α_j`, the period
class of `h` is the Hecke image of the period class of `f`. -/
theorem periodMap_hecke (f h : S m)
    (hh : ⇑h = ∑ j, (((toReal (Sx.rep j)).val.det : ℂ) ^ (-e)) •
      (⇑f ∣[(m : ℤ) + 2] toReal (Sx.rep j))) :
    crossedHecke Sx (rationalRho m e) (coreRep m e) (compat_of m e hφ) hemb
        (levelThreePeriodMap m e f) = levelThreePeriodMap m e h := by
  let F : ℍ → V m := fun x => primitive m ⇑f (x : ℂ)
  have prim : ∀ (g : core) (x : ℍ), (periodCocycle m e f).val g =
      F (toReal (embed g) • x) - coreRep m e g (F x) := by
    intro g x
    rw [hφ g]
    exact periodCocycle_primitive m e f g x
  have hT := fun g x => crossedHeckeFun_primitive Sx (rationalRho m e) (coreRep m e)
    (compat_of m e hφ) toReal (periodCocycle m e f).val F prim g x
  obtain ⟨κ, hκ⟩ : ∃ κ : V m, κ = traceIntegral m e Sx f Complex.I := ⟨_, rfl⟩
  have trace_at : ∀ x : ℍ, LevelThreeHeckeH1.traceFunction Sx (rationalRho m e) toReal F x =
      primitive m ⇑h (x : ℂ) + κ := by
    intro x
    have := trace_eq m e Sx hpos f h hh x
    rw [hκ, ← this]
    simp only [LevelThreeHeckeH1.traceFunction, traceIntegral, F, ofComplex_apply]
  have hcocycle : crossedHeckeCocycles Sx (rationalRho m e) (coreRep m e) (compat_of m e hφ) hemb
      (periodCocycle m e f) = periodCocycle m e h - crossedBoundary (coreRep m e) κ := by
    apply Subtype.ext
    funext g
    change crossedHeckeFun Sx (rationalRho m e) (periodCocycle m e f).val g =
      (periodCocycle m e h).val g - (coreRep m e g κ - κ)
    rw [hT g I, trace_at, trace_at, hφ g, periodCocycle_apply]
    have hI : primitive m ⇑h ((I : ℍ) : ℂ) = 0 := by
      rw [UpperHalfPlane.coe_I]
      exact primitive_basepoint m ⇑h
    rw [hI, zero_add]
    abel
  rw [levelThreePeriodMap_apply, levelThreePeriodMap_apply, crossedHecke_mk, hcocycle,
    Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨-κ, ?_⟩
  rw [map_neg]
  abel

end Main

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHecke
