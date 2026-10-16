module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.FiveNorms

@[expose] public section


/-!
# The twisted action and the substitution `x ∣ h`

For a `ℚ`-module `M` with an untwisted representation `ρ₀` of `GL₃(ℤ)` (for polynomials,
`ρ₀(g) f (x) = f(g⁻¹ x)`) and the determinant twist `ρ(g) = det(g) ρ₀(g)` (the module
`E_{n,1}`), the paper's substitution `x ∣ h` is `ρ₀(h⁻¹) x`, and
`ρ(h⁻¹) x = det(h) · (x ∣ h)`.  This file converts the stabilizer invariances and the signed
equivariance from the twisted form to the paper's form.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryCovectors
  TernaryPoly.OrdinaryCovectorOrbits TernaryPoly.OrdinaryApartmentFrames

section

variable {M : Type*} [AddCommGroup M] [Module ℚ M]
  (ρ₀ ρ : Representation ℚ IntegralGL M)

/-- The paper's substitution `x ∣ h`: the right action `ρ₀(h⁻¹) x`. -/
def slash (x : M) (h : IntegralGL) : M := ρ₀ h⁻¹ x

/-- `ρ` is the determinant twist of `ρ₀`. -/
def IsTwist : Prop :=
  ∀ (g : IntegralGL) (x : M), ρ g x = ((Matrix.GeneralLinearGroup.det g : ℤˣ) : ℤ) • ρ₀ g x

variable {ρ₀ ρ}

theorem IsTwist.rho_inv (hρ : IsTwist ρ₀ ρ) (h : IntegralGL) (x : M) :
    ρ h⁻¹ x = ((Matrix.GeneralLinearGroup.det h : ℤˣ) : ℤ) • slash ρ₀ x h := by
  rw [hρ, map_inv, Int.units_inv_eq_self]
  rfl

theorem IsTwist.slash_eq (hρ : IsTwist ρ₀ ρ) (h : IntegralGL) (x : M) :
    slash ρ₀ x h = ((Matrix.GeneralLinearGroup.det h : ℤˣ) : ℤ) • ρ h⁻¹ x := by
  rw [hρ.rho_inv, smul_smul, Int.units_coe_mul_self, one_smul]

theorem IsTwist.slash_eq_of_det (hρ : IsTwist ρ₀ ρ) {h : IntegralGL} {ε : ℤ}
    (hd : ((Matrix.GeneralLinearGroup.det h : ℤˣ) : ℤ) = ε) (x : M) :
    slash ρ₀ x h = ε • ρ h⁻¹ x := by
  rw [hρ.slash_eq, hd]

theorem det_signedPerm (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) :
    ((Matrix.GeneralLinearGroup.det (signedPerm s π) : ℤˣ) : ℤ) =
      (-1 : ℤ) ^ s.card * ((Equiv.Perm.sign π : ℤˣ) : ℤ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, signedPerm, Units.val_mul, Matrix.det_mul]
  have h1 : (signFrame s).val.det = (-1 : ℤ) ^ s.card := OrdinaryFiberComparison.signFrame_det s
  have h2 : (permFrame π).val.det = ((Equiv.Perm.sign π : ℤˣ) : ℤ) := by
    rw [permFrame_val, Matrix.det_permutation]
    simp [Equiv.Perm.sign_inv]
  rw [h1, h2]

/-- Invariance in the paper's form: `m ∣ h = (-1)^{|s|} m`. -/
theorem IsTwist.inv_iff (hρ : IsTwist ρ₀ ρ) (m : M) (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) :
    Inv ρ m s π ↔ slash ρ₀ m (signedPerm s π) = ((-1 : ℤ) ^ s.card) • m := by
  unfold Inv
  rw [hρ.rho_inv, det_signedPerm]
  set A : ℤ := (-1 : ℤ) ^ s.card with hAdef
  set σ : ℤ := ((Equiv.Perm.sign π : ℤˣ) : ℤ) with hσdef
  set X : M := slash ρ₀ m (signedPerm s π) with hX
  have hA : A * A = 1 := by
    rw [hAdef, ← pow_add, ← two_mul, pow_mul]
    simp
  have hσ : σ * σ = 1 := Int.units_coe_mul_self _
  have hAσ : (A * σ) * (A * σ) = 1 := by
    calc (A * σ) * (A * σ) = (A * A) * (σ * σ) := by ring
      _ = 1 := by rw [hA, hσ]; rfl
  constructor
  · intro h
    calc X = ((A * σ) * (A * σ)) • X := by rw [hAσ, one_smul]
      _ = (A * σ) • ((A * σ) • X) := mul_smul _ _ _
      _ = (A * σ) • (σ • m) := by rw [h]
      _ = ((A * σ) * σ) • m := (mul_smul _ _ _).symm
      _ = A • m := by
          congr 1
          calc (A * σ) * σ = A * (σ * σ) := by ring
            _ = A := by rw [hσ, mul_one]
  · intro h
    rw [h, smul_smul]
    calc ((A * σ) * A) • m = (σ * (A * A)) • m := by congr 1; ring
      _ = σ • m := by rw [hA, mul_one]

end

end TernaryPeriodPolynomials.Argument.FiberModel
