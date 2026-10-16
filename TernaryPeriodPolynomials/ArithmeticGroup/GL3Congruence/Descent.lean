module

public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Energy

@[expose] public section


noncomputable section
namespace TernaryPoly.IntegralGL3Congruence
variable {ι : Type} [Fintype ι]

omit [Fintype ι] in
/-- A finite-period linear map cannot translate a vector by a nonzero fixed vector. -/
theorem periodic_fixed_difference (L : Module.End ℤ (ι → ℤ)) (m : ℕ) (hm : 0<m)
    (hp : L^m=1) (v : ι → ℤ) (hd : L (L v-v)=L v-v) : L v=v := by
  have he (k : ℕ) : (L^k) v=(k : ℤ) • (L v-v)+v := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [pow_succ',Module.End.mul_apply,hk,map_add,map_smul,hd]
      simp only [Nat.cast_add,Nat.cast_one,add_smul,one_smul]
      abel
  have h := he m
  rw [hp] at h
  change v=(m : ℤ) • (L v-v)+v at h
  have hz : (m : ℤ) • (L v-v)=0 := by
    simpa only [add_eq_right] using h.symm
  have hdelta : L v-v=0 := (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hm.ne')
  exact sub_eq_zero.mp hdelta

/-- Minkowski's descent in an integral lattice: a finite-order map congruent to the identity
modulo three is itself the identity. The proof uses averaged integral energy, not p-adic logarithms. -/
theorem periodic_modThree_eq_one (L : Module.End ℤ (ι → ℤ)) (m : ℕ) (hm : 0<m)
    (hp : L^m=1) (hc : ∀ v : ι → ℤ,∃ w : ι → ℤ,L v-v=(3 : ℤ) • w) : L=1 := by
  have hfix : ∀ q : ℕ,∀ v : ι → ℤ,(orbitEnergy L m v).toNat=q → L v=v := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro v hvq
      by_cases hv : v=0
      · simp [hv]
      obtain ⟨w,hw⟩ := hc v
      have hE := orbitEnergy_sub_le L m (L v) v
      rw [hw,orbitEnergy_smul,orbitEnergy_apply L m hp] at hE
      have hpos := orbitEnergy_pos L m hm v hv
      have hwnonneg := orbitEnergy_nonneg L m w
      have hsmall : orbitEnergy L m w<orbitEnergy L m v := by nlinarith
      have hsmallNat : (orbitEnergy L m w).toNat<q := by
        rw [←hvq]
        omega
      have hwfix := ih _ hsmallNat w rfl
      apply periodic_fixed_difference L m hm hp v
      rw [hw,map_smul,hwfix]
  apply LinearMap.ext
  intro v
  exact hfix (orbitEnergy L m v).toNat v rfl

end TernaryPoly.IntegralGL3Congruence
