module

public import TernaryPeriodPolynomials.SymmetricSolution.NormalJet.Derivative

@[expose] public section


/-!
# `J_v = 0` forces `C_v = 0` (last sentence of the paper)

Formalized by Claude Sonnet 5.5.  Paper: "The operator on its right is invertible, since each factor has constant term one.
Consequently `J_v = 0` gives `C_v = 0`."  The operator `τ² B(3𝒟) B(𝒟)` is the image under the ring homomorphism `phi` (evaluation of power series at the nilpotent `𝒟`) of a
power series with constant term one, hence a unit of `End(ℂ[X,Y,Z]_m)`; `normal_jet_derivative_literal` identifies `∂_Z J_v|_{Z=3Y}` with its value on `C_v`.
-/

open MvPolynomial GeneralEisenstein PowerSeries

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.NormalJet

variable {m : ℕ}

theorem tauSub_hom (i : Fin 3) : (tauSub i).IsHomogeneous 1 := by
  fin_cases i
  · exact (isHomogeneous_X ℂ (0 : Fin 3)).sub (isHomogeneous_X ℂ (1 : Fin 3))
  · exact isHomogeneous_X ℂ (1 : Fin 3)
  · exact isHomogeneous_X ℂ (2 : Fin 3)

theorem periodC_isHomogeneous (v : HomogeneousPoly m) (hm : 0 < m) :
    (periodC v.val).IsHomogeneous m := by
  have hp := periodP_isHomogeneous v hm
  have h1 := TernaryPoly.isHomogeneous_bind₁_linear hp tauSub tauSub_hom
  have h2 := TernaryPoly.isHomogeneous_bind₁_linear
    ((mem_homogeneousSubmodule m v.val).mp v.2) hFrame hFrame_hom
  exact (h1.sub hp).sub h2

/-- The power series of the operator `τ² B(3𝒟) B(𝒟)`. -/
def jetOperatorSeries : PowerSeries ℂ :=
  exp ℂ * exp ℂ * rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * bernoulliPowerSeries ℂ

theorem jetOperatorSeries_isUnit : IsUnit jetOperatorSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h1 : constantCoeff (rescale (3 : ℂ) (bernoulliPowerSeries ℂ)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
    simp [bernoulliPowerSeries]
  have h2 : constantCoeff (bernoulliPowerSeries ℂ) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [bernoulliPowerSeries]
  simp [jetOperatorSeries, h1, h2]

/-- **`J_v = 0` implies `C_v = 0`**: for odd symmetric `v`, no norm hypothesis. -/
theorem periodC_eq_zero_of_J_zero (v : HomogeneousPoly m) (hodd : Odd m)
    (hs : ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : Poly)) v.val = v.val)
    (hJ : bernoulliObstruction v = 0) : periodC v.val = 0 := by
  have hm : 0 < m := hodd.pos
  have h := normal_jet_derivative_literal v hodd hs
  rw [hJ, map_zero, map_zero] at h
  let c : HomogeneousPoly m :=
    ⟨periodC v.val, (mem_homogeneousSubmodule m _).mpr (periodC_isHomogeneous v hm)⟩
  have hunit : IsUnit (phi hm jetOperatorSeries) := jetOperatorSeries_isUnit.map _
  have hval : (phi hm jetOperatorSeries c).val =
      bind₁ tauSub (bind₁ tauSub (bernoulliOperator m (3 * X 1) (bernoulliOperator m (X 1) c.val))) := by
    unfold jetOperatorSeries
    rw [map_mul, map_mul, map_mul]
    change ((phi hm (exp ℂ) * phi hm (exp ℂ) * phi hm (rescale (3 : ℂ) (bernoulliPowerSeries ℂ)) *
      phi hm (bernoulliPowerSeries ℂ)) c).val = _
    rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, phi_exp_val, phi_exp_val,
      phi_rescale_val, phi_bernoulli_val]
  have hzero : phi hm jetOperatorSeries c = 0 := Subtype.ext (by rw [hval]; exact h.symm)
  have hinj := ((Module.End.isUnit_iff _).mp hunit).1
  have : c = 0 := hinj (by rw [hzero, map_zero])
  exact congrArg Subtype.val this

end TernaryPeriodPolynomials.Argument.Identities.NormalJet
