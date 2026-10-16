module

public import TernaryPeriodPolynomials.Polynomial.NormKernel.Projector
public import TernaryPeriodPolynomials.Polynomial.CharTwo.SymmetricCoordinates

@[expose] public section


/-!
# Appendix D: consequences of the projector identities

The paper (the paper, Appendix D,
after `mf:eq:projector`) draws from `N̄ π g = 0` and `π g = g + Θ N̄ g` the consequences
that `π` takes values in symmetric polynomials, `π² = π` and `im π = ker N̄` on symmetric
polynomials, with `π` the identity on that kernel, that `π` is linear over
`R = k[d₄, d₆, d₇]`, and that `π K_j = K_j` (after `mf:eq:projected-exps`). These are stated
and proved here for the projector `substitutionProjector` of the definitions, from
the target `normKernel_projector`.

Written by Claude Opus 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.AppendixD

open TernaryPeriodPolynomials.Argument TernaryPoly.CharTwoNorm

/-- The unitriangular part `U` of the substitution `𝐱 ↦ U P 𝐱`. -/
private def unipotentSubstitution (s t u : ZMod 2) : Fin 3 → Poly2 :=
  ![X 0 + C s * X 1 + C t * X 2, X 1 + C u * X 2, X 2]

private theorem projectorSubstitution_eq_rename (σ : Equiv.Perm (Fin 3)) (s t u : ZMod 2) :
    projectorSubstitution σ s t u = fun i => rename σ (unipotentSubstitution s t u i) := by
  funext i
  fin_cases i <;> simp [projectorSubstitution, unipotentSubstitution]

private theorem rename_projectorSubstitution (τ σ : Equiv.Perm (Fin 3)) (s t u : ZMod 2) :
    (fun i => rename τ (projectorSubstitution σ s t u i)) =
      projectorSubstitution (τ * σ) s t u := by
  funext i
  fin_cases i <;> simp [projectorSubstitution, Equiv.Perm.mul_apply]

/-- `π g` is symmetric for every `g`: permuting the variables permutes the matrices `P`. -/
theorem substitutionProjector_isSymmetric (g : Poly2) : (substitutionProjector g).IsSymmetric := by
  intro τ
  simp only [substitutionProjector, map_sum, rename_bind₁, rename_projectorSubstitution]
  exact Fintype.sum_equiv (Equiv.mulLeft τ)
    (fun σ => ∑ s : ZMod 2, ∑ t : ZMod 2, ∑ u : ZMod 2,
      bind₁ (projectorSubstitution (τ * σ) s t u) g)
    (fun σ => ∑ s : ZMod 2, ∑ t : ZMod 2, ∑ u : ZMod 2,
      bind₁ (projectorSubstitution σ s t u) g)
    (fun _ => rfl)

private theorem thetaOperator_zero : thetaOperator 0 = 0 := by
  simp [thetaOperator]

/-- `π` is the identity on symmetric polynomials with `N̄ g = 0`. -/
theorem substitutionProjector_eq_self {g : Poly2} (hg : g.IsSymmetric) (hN : norm g = 0) :
    substitutionProjector g = g := by
  rw [(normKernel_projector.1 g hg).2, hN, thetaOperator_zero, add_zero]

/-- `π² = π` on symmetric polynomials. -/
theorem substitutionProjector_idem {g : Poly2} (hg : g.IsSymmetric) :
    substitutionProjector (substitutionProjector g) = substitutionProjector g :=
  substitutionProjector_eq_self (substitutionProjector_isSymmetric g)
    (normKernel_projector.1 g hg).1

/-- `im π = ker N̄` on symmetric polynomials. -/
theorem image_substitutionProjector :
    substitutionProjector '' {g : Poly2 | g.IsSymmetric} =
      {g : Poly2 | g.IsSymmetric ∧ norm g = 0} := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨substitutionProjector_isSymmetric g, (normKernel_projector.1 g hg).1⟩
  · rintro ⟨hs, hN⟩
    exact ⟨h, hs, substitutionProjector_eq_self hs hN⟩

/-- `π` is `k`-linear. -/
def substitutionProjectorLinear : Poly2 →ₗ[ZMod 2] Poly2 where
  toFun := substitutionProjector
  map_add' f g := by
    simp only [substitutionProjector, map_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [substitutionProjector, map_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem substitutionProjectorLinear_apply (g : Poly2) :
    substitutionProjectorLinear g = substitutionProjector g := rfl

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly2) = ((n % 2 : ℕ) : Poly2) := CharP.cast_eq_mod Poly2 2 n

private theorem zmod_two_cases (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s
  decide

set_option maxRecDepth 10000 in
private theorem unipotent_d4 (s t u : ZMod 2) : bind₁ (unipotentSubstitution s t u) d4 = d4 := by
  rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl <;>
    rcases zmod_two_cases u with rfl | rfl <;>
    simp [unipotentSubstitution, d4, a, b, c] <;> ring_nf <;> simp only [ofNat_mod] <;> norm_num

set_option maxRecDepth 10000 in
private theorem unipotent_d6 (s t u : ZMod 2) : bind₁ (unipotentSubstitution s t u) d6 = d6 := by
  rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl <;>
    rcases zmod_two_cases u with rfl | rfl <;>
    simp [unipotentSubstitution, d6, a, b, c] <;> ring_nf <;> simp only [ofNat_mod] <;> norm_num

set_option maxRecDepth 10000 in
private theorem unipotent_d7 (s t u : ZMod 2) : bind₁ (unipotentSubstitution s t u) d7 = d7 := by
  rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl <;>
    rcases zmod_two_cases u with rfl | rfl <;>
    simp [unipotentSubstitution, d7, cplus, a, b, c] <;> ring_nf <;> simp only [ofNat_mod] <;>
    norm_num

private theorem isSymmetric_pow {φ : Poly2} (h : φ.IsSymmetric) : ∀ n : ℕ, (φ ^ n).IsSymmetric
  | 0 => by rw [pow_zero]; exact IsSymmetric.one
  | n + 1 => by rw [pow_succ]; exact (isSymmetric_pow h n).mul h

private theorem isSymmetric_a : (a : Poly2).IsSymmetric := by
  rw [← esymm_one_eq_a]
  exact esymm_isSymmetric _ _ _

private theorem isSymmetric_b : (b : Poly2).IsSymmetric := by
  rw [← esymm_two_eq_b]
  exact esymm_isSymmetric _ _ _

private theorem isSymmetric_c : (c : Poly2).IsSymmetric := by
  rw [← esymm_three_eq_c]
  exact esymm_isSymmetric _ _ _

private theorem isSymmetric_d4 : (d4 : Poly2).IsSymmetric := by
  unfold d4
  exact ((isSymmetric_pow isSymmetric_a 4).add (isSymmetric_pow isSymmetric_b 2)).add
    (isSymmetric_a.mul isSymmetric_c)

private theorem isSymmetric_d6 : (d6 : Poly2).IsSymmetric := by
  unfold d6
  exact ((((isSymmetric_pow isSymmetric_a 2).mul (isSymmetric_pow isSymmetric_b 2)).add
    ((isSymmetric_pow isSymmetric_a 3).mul isSymmetric_c)).add
    ((isSymmetric_a.mul isSymmetric_b).mul isSymmetric_c)).add (isSymmetric_pow isSymmetric_c 2)

private theorem isSymmetric_d7 : (d7 : Poly2).IsSymmetric := by
  unfold d7 cplus
  exact (isSymmetric_a.mul isSymmetric_c).mul
    ((isSymmetric_a.mul isSymmetric_b).add isSymmetric_c)

private theorem substitution_fixes {d : Poly2} (hs : d.IsSymmetric)
    (hu : ∀ s t u, bind₁ (unipotentSubstitution s t u) d = d)
    (σ : Equiv.Perm (Fin 3)) (s t u : ZMod 2) :
    bind₁ (projectorSubstitution σ s t u) d = d := by
  rw [projectorSubstitution_eq_rename, ← rename_bind₁, hu, hs σ]

/-- Every substitution `𝐱 ↦ U P 𝐱` of the projector fixes `R = k[d₄, d₆, d₇]`. -/
theorem projectorSubstitution_fixes (σ : Equiv.Perm (Fin 3)) (s t u : ZMod 2) {r : Poly2}
    (hr : r ∈ Algebra.adjoin (ZMod 2) ({d4, d6, d7} : Set Poly2)) :
    bind₁ (projectorSubstitution σ s t u) r = r := by
  have hle : Algebra.adjoin (ZMod 2) ({d4, d6, d7} : Set Poly2) ≤
      AlgHom.equalizer (bind₁ (projectorSubstitution σ s t u)) (AlgHom.id (ZMod 2) Poly2) := by
    rw [Algebra.adjoin_le_iff]
    rintro x (rfl | rfl | rfl)
    · exact substitution_fixes isSymmetric_d4 unipotent_d4 σ s t u
    · exact substitution_fixes isSymmetric_d6 unipotent_d6 σ s t u
    · exact substitution_fixes isSymmetric_d7 unipotent_d7 σ s t u
  exact hle hr

/-- `π` is linear over `R = k[d₄, d₆, d₇]`: `π (r g) = r π g`. -/
theorem substitutionProjector_mul {r : Poly2}
    (hr : r ∈ Algebra.adjoin (ZMod 2) ({d4, d6, d7} : Set Poly2)) (g : Poly2) :
    substitutionProjector (r * g) = r * substitutionProjector g := by
  unfold substitutionProjector
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_mul, projectorSubstitution_fixes σ s t u hr]

/-- `π K_j = K_j` (after `mf:eq:projected-exps`). -/
theorem substitutionProjector_generator (j : Fin 8) :
    substitutionProjector (generator j) = generator j := by
  have hj := normKernel_projector.2 j
  rw [← hj]
  refine substitutionProjector_eq_self (substitutionProjector_isSymmetric _) ?_
  have hsrc : (projectedSource j).IsSymmetric := by
    fin_cases j
    · exact (isSymmetric_pow isSymmetric_a 2).mul isSymmetric_b
    · exact isSymmetric_a.mul (isSymmetric_pow isSymmetric_b 2)
    · exact isSymmetric_pow isSymmetric_b 3
    · exact (isSymmetric_pow isSymmetric_b 2).mul isSymmetric_c
    · exact isSymmetric_a.mul (isSymmetric_pow isSymmetric_c 2)
    · exact isSymmetric_b.mul (isSymmetric_pow isSymmetric_c 2)
    · exact isSymmetric_pow isSymmetric_c 3
    · exact isSymmetric_pow isSymmetric_b 5
  exact (normKernel_projector.1 _ hsrc).1

end TernaryPeriodPolynomials.Argument.Statements.AppendixD
