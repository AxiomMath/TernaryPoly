module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHeckeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CuspTValue

@[expose] public section


/-!
# The boundary functional on `H¹(SL₂(ℤ), Sym^d ⊗ det^τ)`

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped MatrixGroups ModularForm
open Matrix MvPolynomial GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1

namespace TernaryPeriodPolynomials.Spectral.BoundaryFunctional

/-- A homogeneous binary polynomial of degree `n` scales by `r ^ n` under `x ↦ r • x`. -/
theorem aeval_smul_of_isHomogeneous {n : ℕ} {φ : Binary.Poly} (hφ : φ.IsHomogeneous n) (r : ℂ)
    (x : Fin 2 → ℂ) : aeval (r • x) φ = r ^ n * aeval x φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [aeval_monomial, aeval_monomial]
  have hdeg := hφ (mem_support_iff.mp hm)
  have hsum : m 0 + m 1 = n := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [Fin.sum_univ_two]
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_two, Pi.smul_apply, smul_eq_mul, mul_pow, ← hsum, pow_add]
  ring

/-- Evaluation after a linear substitution. -/
theorem aeval_substitute (M : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (f : Binary.Poly) :
    aeval x (Binary.substitute M f) = aeval (fun i => ∑ j, M i j * x j) f := by
  rw [Binary.substitute, aeval_bind₁]
  congr 2
  funext i
  simp [Binary.linearForm]

/-- The boundary functional: the value at `(1, 0)`, i.e. the coefficient of `X₀ ^ d`. -/
def ell (d : ℕ) : Binary.HomogeneousPoly d →ₗ[ℂ] ℂ :=
  (aeval ![(1 : ℂ), 0]).toLinearMap ∘ₗ (Binary.HomogeneousPoly d).subtype

theorem ell_apply (d : ℕ) (v : Binary.HomogeneousPoly d) :
    ell d v = aeval ![(1 : ℂ), 0] (v : Binary.Poly) := rfl

variable (d : ℕ) (τ : ℤ)

/-- On `SL₂(ℤ)` the determinant twist is trivial: `σ` acts by substituting `σ⁻¹`. -/
theorem rho_modular_val (σ : SL(2, ℤ)) (v : Binary.HomogeneousPoly d) :
    (show Binary.HomogeneousPoly d from (modularBinaryRep d τ).ρ σ v).val =
      Binary.substitute (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ))
        (v : Binary.Poly) := by
  change Binary.action τ
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL σ)) (v : Binary.Poly) = _
  rw [Binary.action_apply]
  have hdet : Binary.determinantCharacter τ
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL σ)) = 1 := by
    have h := (Int.castRingHom ℂ).map_det (σ : Matrix (Fin 2) (Fin 2) ℤ)
    rw [show (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 from σ.property, map_one] at h
    unfold Binary.determinantCharacter
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, GeneralLinearGroup.val_det_apply]
    change ((Int.castRingHom ℂ).mapMatrix (σ : Matrix (Fin 2) (Fin 2) ℤ)).det ^ τ = 1
    rw [← h, _root_.one_zpow]
  have hinv : (((GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL σ))⁻¹ :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ) := by
    rw [← map_inv, ← map_inv]
    rfl
  rw [hdet, one_smul, hinv]

theorem ell_modular (σ : SL(2, ℤ)) (v : Binary.HomogeneousPoly d) :
    ell d ((modularBinaryRep d τ).ρ σ v) =
      aeval (fun i => (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i 0 : ℂ)) (v : Binary.Poly) := by
  change aeval ![(1 : ℂ), 0] (show Binary.HomogeneousPoly d from (modularBinaryRep d τ).ρ σ v).val = _
  rw [rho_modular_val, aeval_substitute]
  congr 2
  funext i
  simp [Fin.sum_univ_two]

/-- `ell` on the carrier of `modularBinaryRep d τ`. -/
abbrev ellRep : modularBinaryRep d τ →ₗ[ℂ] ℂ := ell d

theorem ellRep_apply (v : Binary.HomogeneousPoly d) : ellRep d τ (toModular d τ v) = ell d v := rfl

theorem ellRep_modular (σ : SL(2, ℤ)) (v : modularBinaryRep d τ) :
    ellRep d τ ((modularBinaryRep d τ).ρ σ v) =
      aeval (fun i => (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i 0 : ℂ))
        (show Binary.HomogeneousPoly d from v).val :=
  ell_modular d τ σ v

/-- **`ell` is `T`-invariant.** -/
theorem ell_rho_T (v : modularBinaryRep d τ) :
    ellRep d τ ((modularBinaryRep d τ).ρ ModularGroup.T v) = ellRep d τ v := by
  rw [ellRep_modular, ModularGroup.coe_T_inv]
  change _ = aeval ![(1 : ℂ), 0] (show Binary.HomogeneousPoly d from v).val
  congr 2
  funext i
  fin_cases i <;> simp

theorem ell_rho_T_pow (k : ℕ) (v : modularBinaryRep d τ) :
    ellRep d τ ((modularBinaryRep d τ).ρ (ModularGroup.T ^ k) v) = ellRep d τ v := by
  induction k with
  | zero => rw [pow_zero, map_one, Module.End.one_apply]
  | succ k ih =>
    rw [pow_succ', map_mul, Module.End.mul_apply, ell_rho_T, ih]

theorem ell_rho_S_inv (v : modularBinaryRep d τ) :
    ellRep d τ ((modularBinaryRep d τ).ρ ModularGroup.S⁻¹ v) =
      aeval ![(0 : ℂ), 1] (show Binary.HomogeneousPoly d from v).val := by
  rw [ellRep_modular, inv_inv, ModularGroup.coe_S]
  congr 2
  funext i
  fin_cases i <;> simp

/-- `z ↦ ell (z T)` on one-cocycles. -/
def ellT : groupCohomology.cocycles₁ (modularBinaryRep d τ) →ₗ[ℂ] ℂ where
  toFun z := ellRep d τ (z ModularGroup.T)
  map_add' z w := map_add (ellRep d τ) (z ModularGroup.T) (w ModularGroup.T)
  map_smul' a z := map_smul (ellRep d τ) a (z ModularGroup.T)

theorem ellT_apply (z : groupCohomology.cocycles₁ (modularBinaryRep d τ)) :
    ellT d τ z = ellRep d τ (z ModularGroup.T) := rfl

/-- Coboundaries vanish under `ellT`, since `ell (T w - w) = 0`. -/
theorem ker_le_ker_ellT :
    LinearMap.ker (groupCohomology.H1π (modularBinaryRep d τ)).hom ≤ LinearMap.ker (ellT d τ) := by
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  obtain ⟨w, hw⟩ := (groupCohomology.H1π_eq_zero_iff z).mp hz
  have hzT : z ModularGroup.T = (modularBinaryRep d τ).ρ ModularGroup.T w - w := by
    rw [← hw]
    rfl
  rw [ellT_apply, hzT, map_sub, ell_rho_T, sub_self]

/-- **The boundary functional on `H¹(SL₂(ℤ), Sym^d ⊗ det^τ)`**: the class of `z` goes to
`ell (z T)`. -/
def beta : groupCohomology.H1 (modularBinaryRep d τ) →ₗ[ℂ] ℂ :=
  ((LinearMap.ker (groupCohomology.H1π (modularBinaryRep d τ)).hom).liftQ (ellT d τ)
    (ker_le_ker_ellT d τ)) ∘ₗ (H1Equiv (modularBinaryRep d τ)).symm.toLinearMap

theorem beta_H1π (z : groupCohomology.cocycles₁ (modularBinaryRep d τ)) :
    beta d τ (groupCohomology.H1π (modularBinaryRep d τ) z) = ell d (z ModularGroup.T) := by
  have hsymm : (H1Equiv (modularBinaryRep d τ)).symm (groupCohomology.H1π _ z) =
      Submodule.Quotient.mk (p := LinearMap.ker (groupCohomology.H1π (modularBinaryRep d τ)).hom) z := by
    apply (H1Equiv (modularBinaryRep d τ)).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  simp only [beta, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hsymm,
    Submodule.liftQ_apply]
  rfl

section Nonvanishing

open TernaryPeriodPolynomials.Spectral.ModularH1

/-- The monomial `X₀ ^ d`. -/
def topMonomial : Binary.HomogeneousPoly d := ⟨X 0 ^ d, isHomogeneous_X_pow 0 d⟩

theorem S_sq_inv_val :
    (((ModularGroup.S ^ 2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 0; 0, -1] := by
  have hinv : (ModularGroup.S ^ 2)⁻¹ = ModularGroup.S ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, modularOrderFour]
  rw [hinv, sq]
  change (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) = _
  rw [ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- In even degree `-1 = S²` fixes `X₀ ^ d`. -/
theorem rho_S_sq_topMonomial (heven : Even d) :
    (modularBinaryRep d τ).ρ (ModularGroup.S ^ 2) (toModular d τ (topMonomial d)) =
      toModular d τ (topMonomial d) := by
  apply Subtype.ext
  rw [rho_modular_val, S_sq_inv_val]
  change Binary.substitute _ (X 0 ^ d) = X 0 ^ d
  rw [map_pow, Binary.substitute_X]
  simp [Binary.linearForm, Fin.sum_univ_two, heven.neg_pow]

theorem T_eq_S_inv_mul : ModularGroup.T = ModularGroup.S⁻¹ * modularOrderSix := by
  rw [modularOrderSix, inv_mul_cancel_left]

/-- The value at `T` of the Mayer–Vietoris cocycle `z_w`: `z_w(T) = T w - S⁻¹ w`. -/
theorem boundaryCocycle_T (w : modularBinaryRep d τ)
    (hw : (modularBinaryRep d τ).ρ (ModularGroup.S ^ 2) w = w) :
    boundaryCocycle w hw ModularGroup.T =
      (modularBinaryRep d τ).ρ ModularGroup.T w - (modularBinaryRep d τ).ρ ModularGroup.S⁻¹ w := by
  rw [T_eq_S_inv_mul, cocycle_mul, boundaryCocycle_U, cocycle_inv, boundaryCocycle_S, map_zero,
    neg_zero, add_zero, map_sub, rho_rho]

/-- **The boundary functional is nonzero** in positive even degree: the class of `z_w` with
`w = X₀ ^ d` has `ell (z_w(T)) = 1`. -/
theorem beta_ne_zero (hd : 0 < d) (heven : Even d) : beta d τ ≠ 0 := by
  intro h
  have hz := beta_H1π d τ (boundaryCocycle (toModular d τ (topMonomial d)) (rho_S_sq_topMonomial d τ heven))
  rw [h, LinearMap.zero_apply] at hz
  have hvalue : ellRep d τ (boundaryCocycle (toModular d τ (topMonomial d))
      (rho_S_sq_topMonomial d τ heven) ModularGroup.T) = 1 := by
    rw [boundaryCocycle_T, map_sub, ell_rho_T, ell_rho_S_inv]
    change aeval ![(1 : ℂ), 0] (X 0 ^ d) - aeval ![(0 : ℂ), 1] (X 0 ^ d) = 1
    simp [hd.ne']
  exact one_ne_zero (hvalue.symm.trans hz.symm)

end Nonvanishing

section Hecke

open TernaryPeriodPolynomials.Spectral.ModularH1

variable (p : Nat.Primes)

/-- The eigenvalue of `T_p` on the boundary functional: `q = p ^ (d + 1 - τ) + p ^ (-τ)`. -/
def q : ℂ := (p.val : ℂ) ^ ((d : ℤ) + 1 - τ) + (p.val : ℂ) ^ (-τ)

theorem ell_hecke_none (v : modularBinaryRep d τ) :
    ellRep d τ (modularRho d τ (binaryHeckeRepresentative p none)⁻¹ v) =
      (p.val : ℂ) ^ (-τ) * (p.val : ℂ) ^ d * ellRep d τ v := by
  have h := rationalBinaryRep_hecke_inverse_coe d τ p none v
  change aeval ![(1 : ℂ), 0] ((rationalBinaryRep d τ).ρ (binaryHeckeRepresentative p none)⁻¹
    (show Binary.HomogeneousPoly d from v)).val = _
  rw [h, map_smul, aeval_substitute, smul_eq_mul]
  have hpoint : (fun i => ∑ j, ((binaryHeckeRepresentative p none).val.map (algebraMap ℚ ℂ)) i j *
      ![(1 : ℂ), 0] j) = (p.val : ℂ) • ![(1 : ℂ), 0] := by
    funext i
    fin_cases i <;> simp [Fin.sum_univ_two, binaryHeckeRepresentative, binaryHeckeDilate]
  rw [hpoint, aeval_smul_of_isHomogeneous ((mem_homogeneousSubmodule d _).mp
    (show Binary.HomogeneousPoly d from v).property), mul_assoc]
  rfl

theorem ell_hecke_some (i : Fin p.val) (v : modularBinaryRep d τ) :
    ellRep d τ (modularRho d τ (binaryHeckeRepresentative p (some i))⁻¹ v) =
      (p.val : ℂ) ^ (-τ) * ellRep d τ v := by
  have h := rationalBinaryRep_hecke_inverse_coe d τ p (some i) v
  change aeval ![(1 : ℂ), 0] ((rationalBinaryRep d τ).ρ (binaryHeckeRepresentative p (some i))⁻¹
    (show Binary.HomogeneousPoly d from v)).val = _
  rw [h, map_smul, aeval_substitute, smul_eq_mul]
  have hpoint : (fun k => ∑ j, ((binaryHeckeRepresentative p (some i)).val.map (algebraMap ℚ ℂ)) k j *
      ![(1 : ℂ), 0] j) = ![(1 : ℂ), 0] := by
    funext k
    fin_cases k <;> simp [Fin.sum_univ_two, binaryHeckeRepresentative, binaryHeckeTranslate]
  rw [hpoint]
  rfl

/-- A transition is determined by the integral relation `δ α_k = α_j σ`. -/
theorem delta_eq (σ h : SL(2, ℤ)) (j k : Option (Fin p.val))
    (hmat : (h : Matrix (Fin 2) (Fin 2) ℤ) * M p k = M p j * (σ : Matrix (Fin 2) (Fin 2) ℤ)) :
    (modularCosets p).delta σ j = h := by
  have spec : modularEmbed h = binaryHeckeRepresentative p j * modularEmbed σ *
      (binaryHeckeRepresentative p k)⁻¹ :=
    (embed_eq_iff p (SpecialLinearGroup.toGL h) (SpecialLinearGroup.toGL σ) j k).mpr hmat
  have hk : k = (modularCosets p).next σ j := (modularCosets p).next_unique spec
  subst hk
  exact ((modularCosets p).delta_unique modularEmbed_injective spec).symm

/-- `α_∞ T = T^p α_∞`. -/
theorem delta_T_none : (modularCosets p).delta ModularGroup.T none = ModularGroup.T ^ p.val := by
  apply delta_eq p _ _ none none
  rw [← zpow_natCast, ModularGroup.coe_T_zpow, ModularGroup.coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- `α_j T = α_{j+1}` for `j + 1 < p`. -/
theorem delta_T_some (i : Fin p.val) (hi : i.val + 1 < p.val) :
    (modularCosets p).delta ModularGroup.T (some i) = 1 := by
  apply delta_eq p _ _ (some i) (some ⟨i.val + 1, hi⟩)
  rw [ModularGroup.coe_T]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    add_comm]

/-- `α_{p-1} T = T α_0`. -/
theorem delta_T_last :
    (modularCosets p).delta ModularGroup.T (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) =
      ModularGroup.T := by
  apply delta_eq p _ _ _ (some ⟨0, p.property.pos⟩)
  have hp : 1 ≤ p.val := p.property.pos
  rw [ModularGroup.coe_T]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_sub hp]

/-- `ell ((T_p z)(T)) = q · ell (z(T))`. -/
theorem ell_heckeCocycle_T (z : groupCohomology.cocycles₁ (modularBinaryRep d τ)) :
    ellRep d τ (heckeCocycle (modularCosets p) (modularBinaryRep d τ) (modularRho d τ)
        (modular_compat d τ) modularEmbed_injective z ModularGroup.T) =
      q d τ p * ellRep d τ (z ModularGroup.T) := by
  rw [heckeCocycle_apply, map_sum]
  change ∑ j : Option (Fin p.val), ellRep d τ (modularRho d τ (binaryHeckeRepresentative p j)⁻¹
    (z ((modularCosets p).delta ModularGroup.T j))) = _
  rw [Fintype.sum_option, ell_hecke_none, delta_T_none, cocycle_pow, map_sum]
  simp only [ell_hecke_some, ell_rho_T_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_eq_single ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩]
  · rw [delta_T_last]
    have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
    have hpow : (p.val : ℂ) ^ ((d : ℤ) + 1 - τ) = (p.val : ℂ) ^ (-τ) * (p.val : ℂ) ^ d * p.val := by
      rw [show (d : ℤ) + 1 - τ = -τ + (d : ℤ) + 1 by ring, zpow_add₀ hp, zpow_add₀ hp, zpow_natCast,
        zpow_one]
    rw [q, hpow]
    ring
  · intro i _ hne
    have hi : i.val + 1 < p.val := by
      have hval : i.val ≠ p.val - 1 := fun h => hne (Fin.ext h)
      have := i.isLt
      omega
    rw [delta_T_some p i hi, groupCohomology.cocycles₁_map_one, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Hecke equivariance of the boundary functional**: `β ∘ T_p = (p ^ (d + 1 - τ) + p ^ (-τ)) β`. -/
theorem beta_modularHecke (x : groupCohomology.H1 (modularBinaryRep d τ)) :
    beta d τ (modularHecke d τ p x) = q d τ p * beta d τ x := by
  obtain ⟨z, rfl⟩ := H1π_surjective (modularBinaryRep d τ) x
  rw [modularHecke, heckeH1_H1π, beta_H1π, beta_H1π]
  exact ell_heckeCocycle_T d τ p z

end Hecke

end TernaryPeriodPolynomials.Spectral.BoundaryFunctional
