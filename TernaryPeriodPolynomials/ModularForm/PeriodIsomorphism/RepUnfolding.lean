module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.BinaryCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.Lifting

@[expose] public section


/-!
# Corollary 1.4, Step 1: representation unfolding and generator determinacy

Two load-bearing lemmas towards packaging the Eichler-Shimura cocycle `Φ` as a `LinearMap`:

* `modularBinaryRep_apply`: unfolds `(modularBinaryRep degree twist).ρ g` all the way down to
  the explicit polynomial substitution by `g⁻¹`'s complex cast.
* `cocycle_eq_of_eq_on_generators`: any two functions satisfying the raw
  inhomogeneous-1-cocycle relation `f(ab) = ρ(a)f(b) + f(a)` and agreeing at the two generators
  `ModularGroup.S` and `modularOrderSix` of `SL₂(ℤ)` agree everywhere.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open Matrix Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein.Binary (substitute action_apply homogeneousAction_coe homogeneousAction
  HomogeneousPoly Poly determinantCharacter)

/-! ## Part (a): the representation-unfolding lemma -/

private theorem castSL_apply (g : SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g) :
        Matrix (Fin 2) (Fin 2) ℂ) i j = ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℂ) := by
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl

private theorem castSL_coe (g : SpecialLinearGroup (Fin 2) ℤ) :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      (Int.castRingHom ℂ).mapMatrix (g : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  rw [castSL_apply]
  rfl

private theorem castSL_det_eq_one (g : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.det
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g)) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, castSL_coe, ← RingHom.map_det]
  simp [g.2]

private theorem castSL_inv (g : SpecialLinearGroup (Fin 2) ℤ) :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g))⁻¹ =
      GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g⁻¹) := by
  rw [← Matrix.GeneralLinearGroup.map_inv, ← map_inv (Matrix.SpecialLinearGroup.toGL) g]

/-- The representation `modularBinaryRep` unfolds to the explicit polynomial substitution by
`g⁻¹`'s complex cast. -/
theorem modularBinaryRep_apply (degree : ℕ) (twist : ℤ) (g : SpecialLinearGroup (Fin 2) ℤ)
    (f : HomogeneousPoly degree) :
    ((modularBinaryRep degree twist).ρ g f).1 =
      substitute (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g⁻¹)) f := by
  have unfold1 : (modularBinaryRep degree twist).ρ g =
      (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL g) := by
    show (Rep.res SpecialLinearGroup.toGL (arithmeticBinaryRep degree twist)).ρ g = _
    rw [Rep.res_obj_ρ]
    rfl
  have unfold2 : (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL g) =
      homogeneousAction degree twist
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g)) := by
    show (Rep.of ((homogeneousAction degree twist).comp
      (GeneralLinearGroup.map (Int.castRingHom ℂ)))).ρ (SpecialLinearGroup.toGL g) = _
    rw [Rep.of_ρ]
    rfl
  have happ : (modularBinaryRep degree twist).ρ g f =
      homogeneousAction degree twist
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g)) f :=
    DFunLike.congr_fun (unfold1.trans unfold2) f
  rw [happ, homogeneousAction_coe, action_apply]
  have hdetchar : determinantCharacter twist
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g)) = 1 := by
    show ((GeneralLinearGroup.det
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g)) : ℂˣ) : ℂ) ^
        twist = 1
    rw [castSL_det_eq_one]
    simp
  rw [hdetchar, one_smul, castSL_inv]

/-! ## Part (b): generator-determinacy for raw 1-cocycles -/

private theorem cocycle_map_one {V : Rep ℂ (SpecialLinearGroup (Fin 2) ℤ)}
    {f : SpecialLinearGroup (Fin 2) ℤ → V}
    (hf : ∀ a b, f (a * b) = V.ρ a (f b) + f a) : f 1 = 0 := by
  have h1 := hf 1 1
  rw [one_mul, map_one, Module.End.one_apply] at h1
  have h2 : f 1 + 0 = f 1 + f 1 := by rw [add_zero]; exact h1
  exact (add_left_cancel h2).symm

private theorem cocycle_inv {V : Rep ℂ (SpecialLinearGroup (Fin 2) ℤ)}
    {f : SpecialLinearGroup (Fin 2) ℤ → V}
    (hf : ∀ a b, f (a * b) = V.ρ a (f b) + f a) (x : SpecialLinearGroup (Fin 2) ℤ) :
    f x⁻¹ = -(V.ρ x⁻¹ (f x)) := by
  have h1 := hf x⁻¹ x
  rw [inv_mul_cancel, cocycle_map_one hf] at h1
  have h2 : V.ρ x⁻¹ (f x) + f x⁻¹ = 0 := h1.symm
  rw [add_comm] at h2
  exact eq_neg_of_add_eq_zero_left h2

/-- Two raw inhomogeneous-1-cocycles agreeing on `{ModularGroup.S, modularOrderSix}` agree
everywhere, by induction along `modularGenerators_closure`. -/
theorem cocycle_eq_of_eq_on_generators {V : Rep ℂ (SpecialLinearGroup (Fin 2) ℤ)}
    {f1 f2 : SpecialLinearGroup (Fin 2) ℤ → V}
    (h1 : ∀ a b, f1 (a * b) = V.ρ a (f1 b) + f1 a)
    (h2 : ∀ a b, f2 (a * b) = V.ρ a (f2 b) + f2 a)
    (hS : f1 ModularGroup.S = f2 ModularGroup.S)
    (hU : f1 modularOrderSix = f2 modularOrderSix) :
    ∀ x, f1 x = f2 x := by
  intro x
  have hx : x ∈ Subgroup.closure ({ModularGroup.S, modularOrderSix} :
      Set (SpecialLinearGroup (Fin 2) ℤ)) := modularGenerators_closure ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]; exact hS
      · rw [hy]; exact hU
  | one => rw [cocycle_map_one h1, cocycle_map_one h2]
  | mul a b _ _ iha ihb => rw [h1 a b, h2 a b, iha, ihb]
  | inv a _ iha => rw [cocycle_inv h1 a, cocycle_inv h2 a, iha]

end TernaryPeriodPolynomials.Argument.Corollary14
