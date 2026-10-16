module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.Functional
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeH1

@[expose] public section


/-!
# Hecke equivariance of the boundary functional at `∞`

For the level-three Hecke operator `T_p = levelHecke m e p hp3` on
`H¹(Γ₁'(3), Sym^m ⊗ det^e)` (`p ≠ 3` prime, cosets `α_j = [[1,j],[0,p]]` and
`α_∞ = ε_p [[p,0],[0,1]]`, `ε_p = ±1 ≡ p mod 3`) we prove

`betaInf_levelHecke : β_∞ (T_p x) = q_∞ · β_∞ x`,
`q_∞ = qInf m e p = p ^ (-e) · (ε_p ^ m · p ^ (m + 1) + 1)`.

The transitions of `T = [[1,1],[0,1]]` are `α_j T = α_{j+1}` for `j + 1 < p` (transition `1`),
`α_{p-1} T = T α_0` (transition `T`) and `α_∞ T = T^p α_∞` (transition `T^p`); on the values at
`(1, 0)` the representation acts by `v ↦ det(α)^{-e} · v(α (1, 0))`, which is `p^{-e}` at the
finite cosets and `p^{-e} (ε_p p)^m` at `∞`, while `β_∞ (z (T^k)) = k β_∞(z)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryHecke

open Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators ParabolicBounds FullBound
open LevelThreeCosets LevelThreeHeckeH1 LevelThreeBoundaryFunctional
open GeneralEisenstein

section Delta

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- A transition is determined by the integral relation `δ α_k = α_j g`. -/
theorem levelDelta_eq (g h : binaryArithmeticLevel) (j k : Option (Fin p.val))
    (hmat : (h.val : Matrix (Fin 2) (Fin 2) ℤ) * N p k =
      N p j * (g.val : Matrix (Fin 2) (Fin 2) ℤ)) :
    levelDelta p hp3 g j = h := by
  have spec : levelEmbed h = heckeRep p j * levelEmbed g * (heckeRep p k)⁻¹ := by
    rw [levelEmbed_apply, levelEmbed_apply]
    exact (embed_eq_iff p h.val g.val j k).mpr hmat
  have hk : k = levelNext p hp3 g j :=
    (levelCosets p hp3).next_unique (g := g) (h := h) (j := j) (k := k) spec
  subst hk
  exact ((levelCosets p hp3).delta_unique levelEmbed_injective spec).symm

/-- `α_i T = α_{i+1}` for `i + 1 < p`. -/
theorem levelDelta_upper_some_lt (i : Fin p.val) (hi : i.val + 1 < p.val) :
    levelDelta p hp3 (upper 1) (some i) = 1 := by
  refine levelDelta_eq p hp3 _ _ (some i) (some ⟨i.val + 1, hi⟩) ?_
  rw [N_some, N_some]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [upper, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `α_{p-1} T = T α_0`. -/
theorem levelDelta_upper_last :
    levelDelta p hp3 (upper 1) (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) =
      upper 1 := by
  have hp : 1 ≤ p.val := p.property.pos
  refine levelDelta_eq p hp3 _ _ _ (some ⟨0, p.property.pos⟩) ?_
  rw [N_some, N_some]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_sub hp]

/-- `α_∞ T = T^p α_∞`. -/
theorem levelDelta_upper_none : levelDelta p hp3 (upper 1) none = upper 1 ^ p.val := by
  have h : levelDelta p hp3 (upper 1) none = upper (p.val : ℤ) := by
    refine levelDelta_eq p hp3 _ _ none none ?_
    rw [N_none]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [upper, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [h, upper_zpow (p.val : ℤ), zpow_natCast]

end Delta

section Matrices

variable (p : Nat.Primes)

theorem heckeMatC_none :
    (heckeRep p none : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ) =
      !![(((signP p : ℤˣ) : ℤ) : ℂ) * (p.val : ℂ), 0; 0, (((signP p : ℤˣ) : ℤ) : ℂ)] := by
  rw [heckeRep_none]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem heckeMatC_some (i : Fin p.val) :
    (heckeRep p (some i) : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ) =
      !![1, (i.val : ℂ); 0, (p.val : ℂ)] := by
  rw [heckeRep_some]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem det_none :
    ((heckeRep p none : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ)).det = (p.val : ℂ) := by
  have h : (((signP p : ℤˣ) : ℤ) : ℂ) * (((signP p : ℤˣ) : ℤ) : ℂ) = 1 := by
    exact_mod_cast signP_mul_self p
  rw [heckeMatC_none, Matrix.det_fin_two_of]
  linear_combination (p.val : ℂ) * h

theorem det_some (i : Fin p.val) :
    ((heckeRep p (some i) : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ)).det = (p.val : ℂ) := by
  rw [heckeMatC_some, Matrix.det_fin_two_of]
  ring

end Matrices

section Evaluation

variable (m : ℕ) (e : ℤ)

/-- `ρ(α⁻¹) v = det(α)^{-e} · v(α x)`, on the level of polynomials. -/
theorem rationalRho_inv_coe (α : GL (Fin 2) ℚ) (d : ℂ)
    (hd : ((α : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ)).det = d)
    (v : Binary.HomogeneousPoly m) :
    ((rationalRho m e α⁻¹ v : Binary.HomogeneousPoly m) : Binary.Poly) =
      d ^ (-e) • Binary.substitute ((α : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ))
        (v : Binary.Poly) := by
  have hdet : ((GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) α) : ℂˣ) :
      ℂ) = d := by
    rw [GeneralLinearGroup.val_det_apply]
    exact hd
  have hchar : Binary.determinantCharacter e
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) α)⁻¹ = d ^ (-e) := by
    show ((GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) α)⁻¹ : ℂˣ) :
      ℂ) ^ e = d ^ (-e)
    rw [map_inv, Units.val_inv_eq_inv_val, hdet, _root_.inv_zpow']
  change (Binary.homogeneousAction m e
    (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) α⁻¹) v).val = _
  rw [Binary.homogeneousAction_coe, Binary.action_apply, map_inv, inv_inv, hchar]
  try rfl

/-- Evaluation of `ρ(α⁻¹) v` at a point: `det(α)^{-e} · v(α x)`. -/
theorem eval_rationalRho_inv (α : GL (Fin 2) ℚ) (d : ℂ)
    (hd : ((α : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ)).det = d)
    (v : Binary.HomogeneousPoly m) (x y : Fin 2 → ℂ)
    (hy : ∀ i, ∑ j, ((α : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ)) i j * x j = y i) :
    eval x (rationalRho m e α⁻¹ v : Binary.HomogeneousPoly m).val = d ^ (-e) * eval y v.val := by
  rw [rationalRho_inv_coe m e α d hd v, MvPolynomial.smul_eval,
    TernaryPeriodPolynomials.Spectral.ModularSymDimension.eval_substitute]
  exact congrArg (fun w : Fin 2 → ℂ => d ^ (-e) * eval w v.val) (funext hy)

variable (p : Nat.Primes)

/-- Value at `(1, 0)` of `ρ(α_∞)⁻¹ v`: `p^{-e} (ε_p p)^m v(1, 0)`. -/
theorem ev10_inv_none (v : Binary.HomogeneousPoly m) :
    eval ![1, 0] (rationalRho m e (heckeRep p none)⁻¹ v : Binary.HomogeneousPoly m).val =
      (p.val : ℂ) ^ (-e) * ((((signP p : ℤˣ) : ℤ) : ℂ) * (p.val : ℂ)) ^ m *
        eval ![1, 0] v.val := by
  have hy : ∀ i, ∑ j, ((heckeRep p none : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ)) i j *
      (![1, 0] : Fin 2 → ℂ) j =
      (((((signP p : ℤˣ) : ℤ) : ℂ) * (p.val : ℂ)) • (![1, 0] : Fin 2 → ℂ)) i := by
    intro i
    rw [heckeMatC_none]
    fin_cases i <;> simp [Fin.sum_univ_two]
  rw [eval_rationalRho_inv m e (heckeRep p none) (p.val : ℂ) (det_none p) v ![1, 0]
    (((((signP p : ℤˣ) : ℤ) : ℂ) * (p.val : ℂ)) • (![1, 0] : Fin 2 → ℂ)) hy,
    SymFixed.eval_smul_of_homogeneous (SymFixed.isHomogeneous v)]
  exact (mul_assoc _ _ _).symm

/-- Value at `(1, 0)` of `ρ(α_i)⁻¹ v`: `p^{-e} v(1, 0)`. -/
theorem ev10_inv_some (i : Fin p.val) (v : Binary.HomogeneousPoly m) :
    eval ![1, 0] (rationalRho m e (heckeRep p (some i))⁻¹ v : Binary.HomogeneousPoly m).val =
      (p.val : ℂ) ^ (-e) * eval ![1, 0] v.val := by
  have hy : ∀ j, ∑ k, ((heckeRep p (some i) : Matrix (Fin 2) (Fin 2) ℚ).map
      (algebraMap ℚ ℂ)) j k * (![1, 0] : Fin 2 → ℂ) k = (![1, 0] : Fin 2 → ℂ) j := by
    intro j
    rw [heckeMatC_some]
    fin_cases j <;> simp [Fin.sum_univ_two]
  rw [eval_rationalRho_inv m e (heckeRep p (some i)) (p.val : ℂ) (det_some p i) v ![1, 0]
    (![1, 0] : Fin 2 → ℂ) hy]

end Evaluation

section Cocycle

variable (m : ℕ) (e : ℤ)

/-- `β_∞(z(T^n)) = n β_∞(z)`. -/
theorem ev10_cocycle_pow (z : crossedCocycles (levelRep m e)) (n : ℕ) :
    eval ![1, 0] (z.val (upper 1 ^ n)).val = (n : ℂ) * eval ![1, 0] (z.val (upper 1)).val := by
  induction n with
  | zero =>
    rw [pow_zero, TwoGenerator.cocycle_one z]
    simp
  | succ n ih =>
    rw [pow_succ', TwoGenerator.cocycle_mul z, Submodule.coe_add, map_add, ev10_T e, ih]
    push_cast
    ring

end Cocycle

section Eigenvalue

variable (m : ℕ) (e : ℤ) (p : Nat.Primes)

/-- **The Eisenstein scalar at the cusp `∞`**:
`q_∞ = p ^ (-e) · (ε_p ^ m · p ^ (m + 1) + 1)`, `ε_p = ±1 ≡ p mod 3`. -/
def qInf : ℂ :=
  (p.val : ℂ) ^ (-e) * ((((signP p : ℤˣ) : ℤ) : ℂ) ^ m * (p.val : ℂ) ^ (m + 1) + 1)

variable (hp3 : p.val ≠ 3)

/-- The cocycle-level formula: `β_∞((T_p z)(T)) = q_∞ β_∞(z(T))`. -/
theorem ev10_hecke_upper (z : crossedCocycles (levelRep m e)) :
    eval ![1, 0] ((crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e) (levelRep m e)
      (level_compat m e) levelEmbed_injective z).val (upper 1)).val =
      qInf m e p * eval ![1, 0] (z.val (upper 1)).val := by
  have hsum : (crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e) (levelRep m e)
      (level_compat m e) levelEmbed_injective z).val (upper 1) =
      ∑ j : Option (Fin p.val), rationalRho m e (heckeRep p j)⁻¹
        (z.val (levelDelta p hp3 (upper 1) j)) :=
    levelHeckeCocycles_apply m e p hp3 z (upper 1)
  have hmap : eval ![1, 0] (∑ j : Option (Fin p.val), rationalRho m e (heckeRep p j)⁻¹
        (z.val (levelDelta p hp3 (upper 1) j)) : Binary.HomogeneousPoly m).val =
      ∑ j : Option (Fin p.val), eval ![1, 0] (rationalRho m e (heckeRep p j)⁻¹
        (z.val (levelDelta p hp3 (upper 1) j)) : Binary.HomogeneousPoly m).val := by
    exact map_sum (SymFixed.evalAt (m := m) ![1, 0]) _ _
  have hlast : (∑ i : Fin p.val, eval ![1, 0] (rationalRho m e (heckeRep p (some i))⁻¹
      (z.val (levelDelta p hp3 (upper 1) (some i))) : Binary.HomogeneousPoly m).val) =
      (p.val : ℂ) ^ (-e) * eval ![1, 0] (z.val (upper 1)).val := by
    rw [Finset.sum_eq_single (⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩ : Fin p.val)]
    · rw [levelDelta_upper_last, ev10_inv_some]
    · intro i _ hne
      have hi : i.val + 1 < p.val := by
        have hval : i.val ≠ p.val - 1 := fun h => hne (Fin.ext h)
        have := i.isLt
        omega
      rw [levelDelta_upper_some_lt p hp3 i hi]
      simp [TwoGenerator.cocycle_one z]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum, hmap, Fintype.sum_option, ev10_inv_none, levelDelta_upper_none, ev10_cocycle_pow,
    hlast]
  unfold qInf
  ring1

/-- **Hecke equivariance of the boundary functional at `∞`**:
`β_∞ (T_p x) = q_∞ · β_∞ x`. -/
theorem betaInf_levelHecke (x : CrossedH1 (levelRep m e)) :
    betaInf m e (levelHecke m e p hp3 x) = qInf m e p * betaInf m e x :=
  cuspFunctional_map (levelRep m e) (upper 1) (SymFixed.evalAt (m := m) ![1, 0])
    (evalInf_sub m e) (levelHecke m e p hp3)
    (fun z => crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e) (levelRep m e)
      (level_compat m e) levelEmbed_injective z)
    (levelHecke_mk m e p hp3) (qInf m e p) (ev10_hecke_upper m e p hp3) x

end Eigenvalue

end TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryHecke
