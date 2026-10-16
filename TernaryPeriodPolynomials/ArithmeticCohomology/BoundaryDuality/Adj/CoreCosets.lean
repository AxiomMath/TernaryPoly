module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreStab
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneCosets

@[expose] public section


/-!
# The level-one Hecke cosets, the cusp transversal and the Fricke-type involution

Let `Γ = SL₂(ℤ)` and let `α_∞ = [[p,0],[0,1]]`, `α_j = [[1,j],[0,p]]` (`0 ≤ j < p`) be the
representatives of the `p + 1` right cosets `Γ α` in `Γ diag(p,1) Γ`.  Every identity below is an
identity between integral `2 × 2` matrices of the form `δ α_k = α_j g`, which says that the coset
`Γ α_j` is carried to `Γ α_k` by `g` with transition `δ`.

* The coset `Γ α₀` (`α₀ = [[1,0],[0,p]]`) is the base coset.  The matrices `S` (for `α_∞`) and
  `T^b` (for `α_b`) carry the base coset to every coset (`levelOneTransversal_spec`), and the
  corresponding transitions of `T` on the transversal are `1`, `T^p`, and `S T S⁻¹`
  (`transit_T_some`, `transit_T_last`, `transit_T_none`).  Consequently `T^p` and `S T S⁻¹` lie in
  the stabilizer of the base coset.
* The matrix `g_W = α₀⁻¹ S = [[0,-1],[1/p,0]]` has determinant `1/p` and satisfies
  `g_W² = -1/p` (a central scalar).  Conjugation by it, `h ↦ α₀⁻¹ S h S⁻¹ α₀`, preserves the
  stabilizer of the base coset and equals `h ↦ S h S⁻¹` followed by the transition at `α_∞`
  (`delta_conjW`).  It is an involutive automorphism of the stabilizer (`conjW_conjW`) exchanging
  `T^p` and `S T S⁻¹` (`conjW_T_pow`, `conjW_STS`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjCore

open scoped MatrixGroups
open Matrix TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (p : Nat.Primes)

/-- The base coset `Γ α₀` with `α₀ = [[1,0],[0,p]]`. -/
def levelOneBase : Option (Fin p.val) := some ⟨0, p.property.pos⟩

/-- The transversal carrying the base coset to every coset: `S` to `Γ α_∞` and `T^b` to
`Γ α_b`. -/
def levelOneTransversal : Option (Fin p.val) → SL(2, ℤ)
  | none => ModularGroup.S
  | some b => ModularGroup.T ^ (b.val : ℤ)

/-- The transversal at the cusp coset is `S`. -/
theorem levelOneTransversal_none : levelOneTransversal p none = ModularGroup.S := rfl

/-- The transversal at the coset `α_b` is `T^b`. -/
theorem levelOneTransversal_some (b : Fin p.val) :
    levelOneTransversal p (some b) = ModularGroup.T ^ (b.val : ℤ) := rfl

/-- The transversal at the base coset is trivial. -/
theorem levelOneTransversal_base : levelOneTransversal p (levelOneBase p) = 1 := by
  change ModularGroup.T ^ (((0 : ℕ)) : ℤ) = 1
  rw [Nat.cast_zero, _root_.zpow_zero]

/-- The transversal at the last coset `α_{p-1}` is `T^(p-1)`. -/
theorem levelOneTransversal_last :
    levelOneTransversal p (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) =
      ModularGroup.T ^ ((p.val : ℤ) - 1) := by
  have hp : 1 ≤ p.val := p.property.pos
  change ModularGroup.T ^ (((p.val - 1 : ℕ)) : ℤ) = _
  congr 1
  omega

/-! ### Rational and integral matrices -/

/-- The rational matrix of an element of `SL₂(ℤ)` is its entrywise image. -/
theorem modularEmbed_val (g : SL(2, ℤ)) :
    (modularEmbed g : Matrix (Fin 2) (Fin 2) ℚ) =
      (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := rfl

/-- The rational relation `ι(δ) = α_j ι(g) α_k⁻¹` for `SL₂(ℤ)` is the integral relation
`δ α_k = α_j g`. -/
theorem modularEmbed_eq_iff (δ g : SL(2, ℤ)) (j k : Option (Fin p.val)) :
    modularEmbed δ = binaryHeckeRepresentative p j * modularEmbed g *
        (binaryHeckeRepresentative p k)⁻¹ ↔
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * M p k = M p j * (g : Matrix (Fin 2) (Fin 2) ℤ) :=
  embed_eq_iff p (SpecialLinearGroup.toGL δ) (SpecialLinearGroup.toGL g) j k

/-- The coset index reached from `j` by `g` is determined by the rational relation. -/
theorem next_eq_of_spec {g h : SL(2, ℤ)} {j k : Option (Fin p.val)}
    (spec : modularEmbed h = binaryHeckeRepresentative p j * modularEmbed g *
      (binaryHeckeRepresentative p k)⁻¹) :
    (modularCosets p).next g j = k := by
  have hk : k = (modularCosets p).next g j := (modularCosets p).next_unique spec
  exact hk.symm

/-- The transition is determined by the rational relation. -/
theorem delta_eq_of_spec {g h : SL(2, ℤ)} {j k : Option (Fin p.val)}
    (spec : modularEmbed h = binaryHeckeRepresentative p j * modularEmbed g *
      (binaryHeckeRepresentative p k)⁻¹) :
    (modularCosets p).delta g j = h := by
  have hk : k = (modularCosets p).next g j := (modularCosets p).next_unique spec
  subst hk
  exact ((modularCosets p).delta_unique modularEmbed_injective spec).symm

/-- The coset index reached from `j` by `g` is determined by the integral relation
`δ α_k = α_j g`. -/
theorem next_eq_of {δ g : SL(2, ℤ)} {j k : Option (Fin p.val)}
    (hmat : (δ : Matrix (Fin 2) (Fin 2) ℤ) * M p k = M p j * (g : Matrix (Fin 2) (Fin 2) ℤ)) :
    (modularCosets p).next g j = k :=
  next_eq_of_spec p ((modularEmbed_eq_iff p δ g j k).mpr hmat)

/-- The transition is determined by the integral relation `δ α_k = α_j g`. -/
theorem delta_eq_of {δ g : SL(2, ℤ)} {j k : Option (Fin p.val)}
    (hmat : (δ : Matrix (Fin 2) (Fin 2) ℤ) * M p k = M p j * (g : Matrix (Fin 2) (Fin 2) ℤ)) :
    (modularCosets p).delta g j = δ :=
  delta_eq_of_spec p ((modularEmbed_eq_iff p δ g j k).mpr hmat)

/-- The inverse of `S` as an integral matrix. -/
theorem coe_modularS_inv :
    ((ModularGroup.S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ### Integral matrix identities -/

/-- `α_b T = α_{b+1}`. -/
theorem mat_T_some (b : Fin p.val) (hb : b.val + 1 < p.val) :
    ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M p (some ⟨b.val + 1, hb⟩) =
      M p (some b) * (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [ModularGroup.coe_T]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- `α_{p-1} T = T α₀`. -/
theorem mat_T_last :
    (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) * M p (levelOneBase p) =
      M p (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) *
        (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hp : 1 ≤ p.val := p.property.pos
  rw [ModularGroup.coe_T]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [M, modularHeckeMatrix, levelOneBase, Matrix.mul_apply, Fin.sum_univ_two,
      Nat.cast_sub hp]

/-- `α_∞ T = T^p α_∞`. -/
theorem mat_T_none :
    ((ModularGroup.T ^ (p.val : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M p none =
      M p none * (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [ModularGroup.coe_T_zpow, ModularGroup.coe_T]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- `α₀ T^p = T α₀`. -/
theorem mat_T_pow_base :
    (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) * M p (levelOneBase p) =
      M p (levelOneBase p) *
        ((ModularGroup.T ^ (p.val : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [ModularGroup.coe_T_zpow, ModularGroup.coe_T]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [M, modularHeckeMatrix, levelOneBase, Matrix.mul_apply, Fin.sum_univ_two]

/-- `α₀ (S T S⁻¹) = (S T^p S⁻¹) α₀`. -/
theorem mat_STS_base :
    ((ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹ : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) * M p (levelOneBase p) =
      M p (levelOneBase p) *
        ((ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T,
    ModularGroup.coe_T_zpow, coe_modularS_inv]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [M, modularHeckeMatrix, levelOneBase, Matrix.mul_apply, Fin.sum_univ_two]

/-- `α_∞ (S T^p S⁻¹) = (S T S⁻¹) α_∞`, with the factors arranged as a transition at `α_∞`. -/
theorem mat_conj_T_pow :
    ((ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) * M p none =
      M p none *
        ((ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹ : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T,
    ModularGroup.coe_T_zpow, coe_modularS_inv]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- `α_∞ (S (S T S⁻¹) S⁻¹) = T^p α_∞`, with the factors arranged as a transition at `α_∞`. -/
theorem mat_conj_STS :
    ((ModularGroup.T ^ (p.val : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M p none =
      M p none *
        ((ModularGroup.S * (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) *
            ModularGroup.S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T,
    ModularGroup.coe_T_zpow, coe_modularS_inv]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- `α_∞ S = S α₀`. -/
theorem mat_S_none :
    (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * M p (levelOneBase p) =
      M p none * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [ModularGroup.coe_S]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [M, modularHeckeMatrix, levelOneBase, Matrix.mul_apply, Fin.sum_univ_two]

/-- `α₀ S = S α_∞`. -/
theorem mat_S_base :
    (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * M p none =
      M p (levelOneBase p) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [ModularGroup.coe_S]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [M, modularHeckeMatrix, levelOneBase, Matrix.mul_apply, Fin.sum_univ_two]

/-- `α₀ T^b = α_b`. -/
theorem mat_transversal_some (b : Fin p.val) :
    ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M p (some b) =
      M p (levelOneBase p) *
        ((ModularGroup.T ^ (b.val : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [ModularGroup.coe_T_zpow]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [M, modularHeckeMatrix, levelOneBase, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The action on the cosets -/

/-- **The transversal carries the base coset to every coset**: `α₀ r_j ∈ Γ α_j`. -/
theorem levelOneTransversal_spec (j : Option (Fin p.val)) :
    (modularCosets p).next (levelOneTransversal p j) (levelOneBase p) = j := by
  cases j with
  | none =>
    change (modularCosets p).next ModularGroup.S (levelOneBase p) = none
    exact next_eq_of p (mat_S_base p)
  | some b =>
    change (modularCosets p).next (ModularGroup.T ^ (b.val : ℤ)) (levelOneBase p) = some b
    exact next_eq_of p (mat_transversal_some p b)

/-- `T` carries `Γ α_b` to `Γ α_{b+1}` for `b + 1 < p`. -/
theorem next_T_some (b : Fin p.val) (hb : b.val + 1 < p.val) :
    (modularCosets p).next ModularGroup.T (some b) = some ⟨b.val + 1, hb⟩ :=
  next_eq_of p (mat_T_some p b hb)

/-- `T` carries the last coset `Γ α_{p-1}` to the base coset. -/
theorem next_T_last :
    (modularCosets p).next ModularGroup.T
        (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) = levelOneBase p :=
  next_eq_of p (mat_T_last p)

/-- `T` fixes the cusp coset `Γ α_∞`. -/
theorem next_T_none : (modularCosets p).next ModularGroup.T none = none :=
  next_eq_of p (mat_T_none p)

/-- `S` carries the cusp coset `Γ α_∞` to the base coset. -/
theorem next_S_none : (modularCosets p).next ModularGroup.S none = levelOneBase p :=
  next_eq_of p (mat_S_none p)

/-- `S` carries the base coset to the cusp coset `Γ α_∞`. -/
theorem next_S_base : (modularCosets p).next ModularGroup.S (levelOneBase p) = none :=
  next_eq_of p (mat_S_base p)

/-- `S⁻¹` carries the base coset to the cusp coset `Γ α_∞`. -/
theorem next_S_inv_base : (modularCosets p).next ModularGroup.S⁻¹ (levelOneBase p) = none := by
  have h := next_inv_next (modularCosets p) ModularGroup.S none
  rw [next_S_none p] at h
  exact h

/-- The transition of `T` at `α_b` (`b + 1 < p`) is trivial. -/
theorem delta_T_some (b : Fin p.val) (hb : b.val + 1 < p.val) :
    (modularCosets p).delta ModularGroup.T (some b) = 1 :=
  delta_eq_of p (mat_T_some p b hb)

/-- The transition of `T` at the last coset is `T`. -/
theorem delta_T_last :
    (modularCosets p).delta ModularGroup.T
        (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) = ModularGroup.T :=
  delta_eq_of p (mat_T_last p)

/-- The transition of `T` at the cusp coset is `T^p`. -/
theorem delta_T_none :
    (modularCosets p).delta ModularGroup.T none = ModularGroup.T ^ (p.val : ℤ) :=
  delta_eq_of p (mat_T_none p)

/-- The transition of `T^p` at the base coset is `T`. -/
theorem delta_T_pow_base :
    (modularCosets p).delta (ModularGroup.T ^ (p.val : ℤ)) (levelOneBase p) = ModularGroup.T :=
  delta_eq_of p (mat_T_pow_base p)

/-- The transition of `S T S⁻¹` at the base coset is `S T^p S⁻¹`. -/
theorem delta_STS_base :
    (modularCosets p).delta (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹)
        (levelOneBase p) = ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹ :=
  delta_eq_of p (mat_STS_base p)

/-! ### The transitions of `T` along the transversal -/

/-- The transition of `T` at the coset `α_b` (`b + 1 < p`) is trivial. -/
theorem transit_T_some (b : Fin p.val) (hb : b.val + 1 < p.val) :
    (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
      (levelOneTransversal_spec p) ModularGroup.T (some b) : SL(2, ℤ)) = 1 := by
  refine (transit_val (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
    (levelOneTransversal_spec p) ModularGroup.T (some b)).trans ?_
  rw [next_T_some p b hb]
  change ModularGroup.T ^ (b.val : ℤ) * ModularGroup.T *
    (ModularGroup.T ^ ((b.val + 1 : ℕ) : ℤ))⁻¹ = 1
  have hc : ((b.val + 1 : ℕ) : ℤ) = (b.val : ℤ) + 1 := by omega
  rw [hc, _root_.zpow_add_one]
  exact _root_.mul_inv_cancel _

/-- The transition of `T` at the last coset is `T^p`. -/
theorem transit_T_last :
    (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
      (levelOneTransversal_spec p) ModularGroup.T
      (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) : SL(2, ℤ)) =
        ModularGroup.T ^ (p.val : ℤ) := by
  refine (transit_val (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
    (levelOneTransversal_spec p) ModularGroup.T
    (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩)).trans ?_
  rw [next_T_last p, levelOneTransversal_last p, levelOneTransversal_base p,
    _root_.inv_one, _root_.mul_one, ← _root_.zpow_add_one, _root_.sub_add_cancel]

/-- The transition of `T` at the cusp coset is `S T S⁻¹`. -/
theorem transit_T_none :
    (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
      (levelOneTransversal_spec p) ModularGroup.T none : SL(2, ℤ)) =
        ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ := by
  refine (transit_val (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
    (levelOneTransversal_spec p) ModularGroup.T none).trans ?_
  rw [next_T_none p, levelOneTransversal_none]

/-- A sum over the cosets of a function vanishing at the cosets `α_b` with `b + 1 < p` is the sum
of its values at the last coset and at the cusp coset. -/
theorem sum_option_last {M : Type*} [AddCommMonoid M] (F : Option (Fin p.val) → M)
    (hF : ∀ b : Fin p.val, b.val + 1 < p.val → F (some b) = 0) :
    ∑ j, F j = F (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) + F none := by
  have hsum : ∑ b : Fin p.val, F (some b) =
      F (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) := by
    refine Finset.sum_eq_single (⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩ : Fin p.val) ?_ ?_
    · intro b _ hb
      apply hF b
      have hb' : b.val ≠ p.val - 1 := fun h => hb (Fin.ext h)
      have := b.isLt
      omega
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [Fintype.sum_option, hsum]
  exact _root_.add_comm _ _

/-- `T^p` lies in the stabilizer of the base coset. -/
theorem mem_stab_T_pow :
    ModularGroup.T ^ (p.val : ℤ) ∈ stab (modularCosets p) (levelOneBase p) := by
  have h := (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
    (levelOneTransversal_spec p) ModularGroup.T
    (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩)).property
  rwa [transit_T_last p] at h

/-- `S T S⁻¹` lies in the stabilizer of the base coset. -/
theorem mem_stab_STS :
    ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈
      stab (modularCosets p) (levelOneBase p) := by
  have h := (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
    (levelOneTransversal_spec p) ModularGroup.T none).property
  rwa [transit_T_none p] at h

/-! ### Conjugation in a group by an element whose product with a conjugator is central -/

/-- If `a b = s` with `s` central then conjugating by `a` after conjugating by `b` is trivial. -/
theorem central_conj_cancel {G : Type*} [Group G] (a b s X : G) (hab : a * b = s)
    (hs : ∀ Y : G, s * Y = Y * s) : a * (b * X * b⁻¹) * a⁻¹ = X := by
  have e : a * (b * X * b⁻¹) * a⁻¹ = s * X * s⁻¹ := by
    rw [← hab]
    group
  rw [e, hs X, _root_.mul_inv_cancel_right]

/-- If `a b = s` with `s` central then conjugation by `b` is conjugation by `a⁻¹`. -/
theorem central_conj_swap {G : Type*} [Group G] (a b s X : G) (hab : a * b = s)
    (hs : ∀ Y : G, s * Y = Y * s) : b * X * b⁻¹ = a⁻¹ * X * a := by
  have e : b = a⁻¹ * s := by
    rw [← hab, _root_.inv_mul_cancel_left]
  rw [e]
  calc a⁻¹ * s * X * (a⁻¹ * s)⁻¹ = a⁻¹ * (s * X) * s⁻¹ * a := by group
    _ = a⁻¹ * (X * s) * s⁻¹ * a := by rw [hs X]
    _ = a⁻¹ * X * a := by group

/-! ### The representatives `α₀`, `α_∞` -/

/-- The prime is nonzero in `ℚ`. -/
theorem prime_cast_ne_zero : (p.val : ℚ) ≠ 0 := by
  exact_mod_cast p.property.ne_zero

/-- `-1/p` is nonzero. -/
theorem neg_inv_prime_ne_zero : -(p.val : ℚ)⁻¹ ≠ 0 :=
  neg_ne_zero.mpr (inv_ne_zero (prime_cast_ne_zero p))

/-- The matrix of a scalar element of `GL₂(ℚ)`. -/
theorem gl_scalar_val (u : ℚˣ) :
    ((GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal (fun _ => (u : ℚ)) := rfl

/-- The matrix of `α₀`. -/
theorem rep_base_val :
    ((binaryHeckeRepresentative p (levelOneBase p) : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, (p.val : ℚ)] := by
  rw [rep_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, modularHeckeMatrix, levelOneBase]

/-- The matrix of `α_∞`. -/
theorem rep_none_val :
    ((binaryHeckeRepresentative p none : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![(p.val : ℚ), 0; 0, 1] := by
  rw [rep_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, modularHeckeMatrix]

/-- The matrix of `α₀⁻¹`. -/
theorem rep_base_inv_val :
    (((binaryHeckeRepresentative p (levelOneBase p))⁻¹ : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, (p.val : ℚ)⁻¹] := by
  have hp := prime_cast_ne_zero p
  rw [Matrix.coe_units_inv]
  apply Matrix.inv_eq_right_inv
  rw [rep_base_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp]

/-- `α₀ α_∞ = p` is a central scalar. -/
theorem rep_base_mul_rep_none :
    binaryHeckeRepresentative p (levelOneBase p) * binaryHeckeRepresentative p none =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p.val : ℚ) (prime_cast_ne_zero p)) := by
  apply Units.ext
  rw [Units.val_mul, rep_base_val, rep_none_val, gl_scalar_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugation by `α_∞` is conjugation by `α₀⁻¹`. -/
theorem rep_none_conj (X : GL (Fin 2) ℚ) :
    binaryHeckeRepresentative p none * X * (binaryHeckeRepresentative p none)⁻¹ =
      (binaryHeckeRepresentative p (levelOneBase p))⁻¹ * X *
        binaryHeckeRepresentative p (levelOneBase p) :=
  central_conj_swap _ _ _ X (rep_base_mul_rep_none p)
    (fun Y => GeneralLinearGroup.scalar_commute _ Y)

/-! ### The Fricke-type involution -/

/-- **The Fricke-type element** `g_W = α₀⁻¹ S = [[0,-1],[1/p,0]]` of `GL₂(ℚ)`. -/
def gW : GL (Fin 2) ℚ :=
  (binaryHeckeRepresentative p (levelOneBase p))⁻¹ * modularEmbed ModularGroup.S

/-- `α₀ g_W = S`. -/
theorem rep_base_mul_gW :
    binaryHeckeRepresentative p (levelOneBase p) * gW p = modularEmbed ModularGroup.S := by
  simp only [gW, _root_.mul_inv_cancel_left]

/-- The matrix of `g_W`. -/
theorem gW_val :
    (gW p : Matrix (Fin 2) (Fin 2) ℚ) = !![0, -1; (p.val : ℚ)⁻¹, 0] := by
  rw [gW, Units.val_mul, rep_base_inv_val, modularEmbed_val, ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`g_W² = -1/p`** is a central scalar. -/
theorem gW_mul_gW :
    gW p * gW p = GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 (-(p.val : ℚ)⁻¹) (neg_inv_prime_ne_zero p)) := by
  apply Units.ext
  rw [Units.val_mul, gW_val, gl_scalar_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The determinant of `g_W` is `1/p`.** -/
theorem val_det_gW : ((GeneralLinearGroup.det (gW p) : ℚˣ) : ℚ) = (p.val : ℚ)⁻¹ := by
  rw [GeneralLinearGroup.val_det_apply, gW_val, Matrix.det_fin_two_of]
  simp

/-! ### Conjugation by `g_W` on the stabilizer of the base coset -/

/-- `S` carries the cusp coset back and forth: `S h S⁻¹` fixes the cusp coset when `h` stabilizes
the base coset. -/
theorem next_conj_none {h : SL(2, ℤ)} (hh : h ∈ stab (modularCosets p) (levelOneBase p)) :
    (modularCosets p).next (ModularGroup.S * h * ModularGroup.S⁻¹) none = none := by
  have h1 : (modularCosets p).next (ModularGroup.S * h * ModularGroup.S⁻¹) none =
      (modularCosets p).next ModularGroup.S⁻¹
        ((modularCosets p).next h ((modularCosets p).next ModularGroup.S none)) := by
    rw [(modularCosets p).next_mul (ModularGroup.S * h) ModularGroup.S⁻¹ none,
      (modularCosets p).next_mul ModularGroup.S h none]
  rw [h1, next_S_none p, (mem_stab (modularCosets p)).mp hh, next_S_inv_base p]

/-- The transition of `S h S⁻¹` at the cusp coset is the conjugate of `S h S⁻¹` by `α_∞`. -/
theorem modularEmbed_delta_conj {h : SL(2, ℤ)}
    (hh : h ∈ stab (modularCosets p) (levelOneBase p)) :
    modularEmbed ((modularCosets p).delta (ModularGroup.S * h * ModularGroup.S⁻¹) none) =
      binaryHeckeRepresentative p none * modularEmbed (ModularGroup.S * h * ModularGroup.S⁻¹) *
        (binaryHeckeRepresentative p none)⁻¹ := by
  have h1 := (modularCosets p).delta_spec (ModularGroup.S * h * ModularGroup.S⁻¹) none
  rw [next_conj_none p hh] at h1
  exact h1

/-- The relation exhibiting `S h S⁻¹` as the transition at the base coset of the transition of
`S h S⁻¹` at the cusp coset. -/
theorem spec_conj_aux {h : SL(2, ℤ)} (hh : h ∈ stab (modularCosets p) (levelOneBase p)) :
    modularEmbed (ModularGroup.S * h * ModularGroup.S⁻¹) =
      binaryHeckeRepresentative p (levelOneBase p) *
        modularEmbed ((modularCosets p).delta (ModularGroup.S * h * ModularGroup.S⁻¹) none) *
          (binaryHeckeRepresentative p (levelOneBase p))⁻¹ := by
  rw [modularEmbed_delta_conj p hh]
  exact (central_conj_cancel _ _ _ _ (rep_base_mul_rep_none p)
    (fun Y => GeneralLinearGroup.scalar_commute _ Y)).symm

/-- The transition of `S h S⁻¹` at the cusp coset stabilizes the base coset. -/
theorem delta_conj_mem {h : SL(2, ℤ)} (hh : h ∈ stab (modularCosets p) (levelOneBase p)) :
    (modularCosets p).delta (ModularGroup.S * h * ModularGroup.S⁻¹) none ∈
      stab (modularCosets p) (levelOneBase p) :=
  (mem_stab (modularCosets p)).mpr (next_eq_of_spec p (spec_conj_aux p hh))

/-- **Conjugation by the Fricke-type element** on the stabilizer of the base coset:
`h ↦ α_∞ (S h S⁻¹) α_∞⁻¹`, the transition of `S h S⁻¹` at the cusp coset. -/
def conjW (h : stab (modularCosets p) (levelOneBase p)) :
    stab (modularCosets p) (levelOneBase p) :=
  ⟨(modularCosets p).delta (ModularGroup.S * (h : SL(2, ℤ)) * ModularGroup.S⁻¹) none,
    delta_conj_mem p h.2⟩

/-- `conjW` is conjugation by `g_W` in `GL₂(ℚ)`. -/
theorem modularEmbed_conjW (h : stab (modularCosets p) (levelOneBase p)) :
    modularEmbed (conjW p h : SL(2, ℤ)) = gW p * modularEmbed (h : SL(2, ℤ)) * (gW p)⁻¹ := by
  have e1 : modularEmbed (conjW p h : SL(2, ℤ)) =
      binaryHeckeRepresentative p none *
        modularEmbed (ModularGroup.S * (h : SL(2, ℤ)) * ModularGroup.S⁻¹) *
          (binaryHeckeRepresentative p none)⁻¹ :=
    modularEmbed_delta_conj p h.2
  rw [e1, rep_none_conj p]
  simp only [gW, map_mul, map_inv]
  group

/-- The transition of `conjW h` at the base coset is `S h S⁻¹`. -/
theorem delta_conjW (h : stab (modularCosets p) (levelOneBase p)) :
    (modularCosets p).delta (conjW p h : SL(2, ℤ)) (levelOneBase p) =
      ModularGroup.S * (h : SL(2, ℤ)) * ModularGroup.S⁻¹ :=
  delta_eq_of_spec p (spec_conj_aux p h.2)

/-- `conjW` is multiplicative. -/
theorem conjW_mul (h k : stab (modularCosets p) (levelOneBase p)) :
    conjW p (h * k) = conjW p h * conjW p k := by
  apply Subtype.ext
  apply modularEmbed_injective
  rw [modularEmbed_conjW p (h * k)]
  simp only [Subgroup.coe_mul, map_mul, modularEmbed_conjW]
  group

/-- **Conjugation by `g_W` as an endomorphism** of the stabilizer of the base coset. -/
def conjWHom :
    stab (modularCosets p) (levelOneBase p) →* stab (modularCosets p) (levelOneBase p) where
  toFun := conjW p
  map_one' := by
    show conjW p 1 = 1
    apply Subtype.ext
    apply modularEmbed_injective
    rw [modularEmbed_conjW p 1]
    simp only [Subgroup.coe_one, map_one, _root_.mul_one, _root_.mul_inv_cancel]
  map_mul' := conjW_mul p

/-- The endomorphism `conjWHom` is `conjW`. -/
theorem conjWHom_apply (h : stab (modularCosets p) (levelOneBase p)) :
    conjWHom p h = conjW p h := rfl

/-- **`conjW` is an involution** (since `g_W²` is central). -/
theorem conjW_conjW (h : stab (modularCosets p) (levelOneBase p)) : conjW p (conjW p h) = h := by
  apply Subtype.ext
  apply modularEmbed_injective
  rw [modularEmbed_conjW p (conjW p h), modularEmbed_conjW p h]
  exact central_conj_cancel _ _ _ _ (gW_mul_gW p)
    (fun Y => GeneralLinearGroup.scalar_commute _ Y)

/-- **`conjW` exchanges `T^p` and `S T S⁻¹`**: the image of `T^p` is `S T S⁻¹`. -/
theorem conjW_T_pow :
    (conjW p ⟨ModularGroup.T ^ (p.val : ℤ), mem_stab_T_pow p⟩ : SL(2, ℤ)) =
      ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ := by
  change (modularCosets p).delta (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) *
    ModularGroup.S⁻¹) none = _
  exact delta_eq_of p (mat_conj_T_pow p)

/-- **`conjW` exchanges `T^p` and `S T S⁻¹`**: the image of `S T S⁻¹` is `T^p`. -/
theorem conjW_STS :
    (conjW p ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩ :
        SL(2, ℤ)) = ModularGroup.T ^ (p.val : ℤ) := by
  change (modularCosets p).delta (ModularGroup.S *
    (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) * ModularGroup.S⁻¹) none = _
  exact delta_eq_of p (mat_conj_STS p)

end TernaryPeriodPolynomials.BoundaryDuality.AdjCore
