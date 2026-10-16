module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.FareyChains

@[expose] public section


/-!
# The three neighbours of a triangle

Formalized by Claude Sonnet 5.5.

* `cusp3`, and the action of the rotation `rho` on the three cusps of the standard triangle.
* `nbF t`: the finite set of oriented dual edges leaving the triangle `t` (`nb_finite`), with
  `nbF (g • t) = g • nbF t` and `nbF_triPlus : nbF triPlus = {p0, rho • p0, rho2 • p0}` (`snd_of_edge`: the second triangle
  over an edge of `triPlus` is determined by the two cusps of the edge).
* `sum_nbF`: sums over the neighbours of `g • triPlus`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeDuality

open CategoryTheory TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree
open scoped MonoidAlgebra Classical

/-- The third cusp `⟨e₁ + e₂⟩` of the standard triangle. -/
abbrev cusp3 : Line := plusLine e12_unimod

theorem isGen_cusp3 : IsGen cusp3 (e1 + e2) := isGen_plusLine e12_unimod

theorem smul_cusp3_eq {g : IntegralGL} {x : Line} {v : IntegralVector} (hx : IsGen x v)
    (h : (fun i => g.val i 0 + g.val i 1) = v ∨ (fun i => g.val i 0 + g.val i 1) = -v) :
    g • cusp3 = x := by
  have h0 : IsGen (g • cusp3) (fun i => g.val i 0 + g.val i 1) := by
    rw [smul_plus]; exact col_sum_isGen g
  exact ((hx.line_eq_iff h0).mpr (by tauto)).symm

theorem rho_c1 : rho • cusp1 = cusp2 :=
  smul_cusp1_eq isGen_cusp2 (Or.inl (by funext i; fin_cases i <;> simp [rho, colGL_val_zero, e2]))

theorem rho_c2 : rho • cusp2 = cusp3 :=
  smul_cusp2_eq isGen_cusp3 (Or.inr (by
    funext i; fin_cases i <;> simp [rho, colGL_val_one, e12, e1, e2]))

theorem rho_c3 : rho • cusp3 = cusp1 :=
  smul_cusp3_eq isGen_cusp1 (Or.inr (by
    funext i; fin_cases i <;> simp [rho, colGL_val_zero, colGL_val_one, e12, e1, e2]))

theorem rho2_c1 : rho2 • cusp1 = cusp3 :=
  smul_cusp1_eq isGen_cusp3 (Or.inr (by
    funext i; fin_cases i <;> simp [rho2, colGL_val_zero, e12, e1, e2]))

theorem rho2_c2 : rho2 • cusp2 = cusp1 :=
  smul_cusp2_eq isGen_cusp1 (Or.inl (by funext i; fin_cases i <;> simp [rho2, colGL_val_one, e1]))

theorem rho2_c3 : rho2 • cusp3 = cusp2 :=
  smul_cusp3_eq isGen_cusp2 (Or.inr (by
    funext i; fin_cases i <;> simp [rho2, colGL_val_zero, colGL_val_one, e12, e1, e2]))

theorem detQ_rho : detQ rho = 1 := by
  rw [detQ_eq]; simp [rho, colGL_val_zero, colGL_val_one, e2, e12]

theorem detQ_rho2 : detQ rho2 = 1 := by
  rw [detQ_eq]; simp [rho2, colGL_val_zero, colGL_val_one, e1, e12]

theorem mem_triPlus_cusps (x : Line) : x ∈ triPlus.1 ↔ x = cusp1 ∨ x = cusp2 ∨ x = cusp3 := by
  simp [triPlus]

theorem mem_triMinus_cusps12 : cusp1 ∈ triMinus.1 ∧ cusp2 ∈ triMinus.1 := by
  simp [triMinus]


/-- The oriented dual edges leaving a triangle. -/
def nb (t : Tri) : Set OTE := {q | q.1.1 = t}

theorem nb_finite (t : Tri) : (nb t).Finite := by
  obtain ⟨γ, rfl⟩ := exists_smul_triPlus t
  have := stabilizer_triPlus_finite
  refine (Set.finite_range (fun s : MulAction.stabilizer IntegralGL triPlus => (γ * s.1) • p0)).subset ?_
  intro q hq
  obtain ⟨δ, rfl⟩ := ote_transitive q
  have hδ : δ • triPlus = γ • triPlus := hq
  refine ⟨⟨γ⁻¹ * δ, ?_⟩, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, hδ, inv_smul_smul]
  · show (γ * (γ⁻¹ * δ)) • p0 = δ • p0
    rw [mul_inv_cancel_left]

/-- The finite set of oriented dual edges leaving a triangle. -/
def nbF (t : Tri) : Finset OTE := (nb_finite t).toFinset

theorem mem_nbF {t : Tri} {q : OTE} : q ∈ nbF t ↔ q.1.1 = t := by
  simp [nbF, nb]

theorem nbF_smul (g : IntegralGL) (t : Tri) : nbF (g • t) = (nbF t).image (g • ·) := by
  ext q
  rw [mem_nbF, Finset.mem_image]
  constructor
  · intro h
    refine ⟨g⁻¹ • q, ?_, by simp⟩
    rw [mem_nbF]
    show g⁻¹ • q.1.1 = t
    rw [h, inv_smul_smul]
  · rintro ⟨a, ha, rfl⟩
    rw [mem_nbF] at ha
    show g • a.1.1 = g • t
    rw [ha]

theorem snd_of_edge {γ k : IntegralGL} (hγ : γ • triPlus = triPlus) (hk : k • triPlus = triPlus)
    (h1 : γ • cusp1 = k • cusp1 ∨ γ • cusp1 = k • cusp2)
    (h2 : γ • cusp2 = k • cusp1 ∨ γ • cusp2 = k • cusp2)
    (hne : γ • cusp1 ≠ γ • cusp2) : γ • triMinus = k • triMinus := by
  have m1 : (k⁻¹ * γ) • cusp1 ∈ ((k⁻¹ * γ) • triMinus).1 :=
    smul_mem_tri_smul mem_triMinus_cusps12.1
  have m2 : (k⁻¹ * γ) • cusp2 ∈ ((k⁻¹ * γ) • triMinus).1 :=
    smul_mem_tri_smul mem_triMinus_cusps12.2
  have e1' : (k⁻¹ * γ) • cusp1 = cusp1 ∨ (k⁻¹ * γ) • cusp1 = cusp2 := by
    rw [mul_smul]
    rcases h1 with h | h <;> rw [h] <;> simp
  have e2' : (k⁻¹ * γ) • cusp2 = cusp1 ∨ (k⁻¹ * γ) • cusp2 = cusp2 := by
    rw [mul_smul]
    rcases h2 with h | h <;> rw [h] <;> simp
  have hne' : (k⁻¹ * γ) • cusp1 ≠ (k⁻¹ * γ) • cusp2 := by
    rw [mul_smul, mul_smul]
    intro e
    exact hne (MulAction.injective k⁻¹ e)
  have hc : cusp1 ∈ ((k⁻¹ * γ) • triMinus).1 ∧ cusp2 ∈ ((k⁻¹ * γ) • triMinus).1 := by
    rcases e1' with a | a <;> rcases e2' with b | b
    · exact absurd (a.trans b.symm) hne'
    · rw [a] at m1; rw [b] at m2; exact ⟨m1, m2⟩
    · rw [a] at m1; rw [b] at m2; exact ⟨m2, m1⟩
    · exact absurd (a.trans b.symm) hne'
  rcases tri_over_standard_edge hc.1 hc.2 with h | h
  · exfalso
    have : γ • triMinus = γ • triPlus := by
      rw [hγ]
      calc γ • triMinus = k • ((k⁻¹ * γ) • triMinus) := by rw [smul_smul, mul_inv_cancel_left]
        _ = k • triPlus := by rw [h]
        _ = triPlus := hk
    exact triPlus_ne_triMinus (MulAction.injective γ this).symm
  · calc γ • triMinus = k • ((k⁻¹ * γ) • triMinus) := by rw [smul_smul, mul_inv_cancel_left]
      _ = k • triMinus := by rw [h]

theorem nbF_triPlus : nbF triPlus = {p0, rho • p0, rho2 • p0} := by
  ext q
  rw [mem_nbF, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hq
    obtain ⟨γ, rfl⟩ := ote_transitive q
    have hγ : γ • triPlus = triPlus := hq
    have hx : γ • cusp1 ∈ triPlus.1 := by
      rw [← hγ]; exact smul_mem_tri_smul (by simp [triPlus])
    have hy : γ • cusp2 ∈ triPlus.1 := by
      rw [← hγ]; exact smul_mem_tri_smul (by simp [triPlus])
    have hne : γ • cusp1 ≠ γ • cusp2 := fun e => cusp1_ne_cusp2 (MulAction.injective γ e)
    have key : ∀ k : IntegralGL, k • triPlus = triPlus →
        (γ • cusp1 = k • cusp1 ∨ γ • cusp1 = k • cusp2) →
        (γ • cusp2 = k • cusp1 ∨ γ • cusp2 = k • cusp2) → γ • p0 = k • p0 := by
      intro k hk h1 h2
      apply Subtype.ext
      show (γ • triPlus, γ • triMinus) = (k • triPlus, k • triMinus)
      rw [hγ, hk, snd_of_edge hγ hk h1 h2 hne]
    rw [mem_triPlus_cusps] at hx hy
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
    · exact absurd (hx.trans hy.symm) hne
    · left
      have := key 1 (one_smul _ _) (Or.inl (by rw [hx, one_smul])) (Or.inr (by rw [hy, one_smul]))
      rwa [one_smul] at this
    · right; right
      exact key rho2 rho2_mem (Or.inr (by rw [hx, rho2_c2])) (Or.inl (by rw [hy, rho2_c1]))
    · left
      have := key 1 (one_smul _ _) (Or.inr (by rw [hx, one_smul])) (Or.inl (by rw [hy, one_smul]))
      rwa [one_smul] at this
    · exact absurd (hx.trans hy.symm) hne
    · right; left
      exact key rho rho_mem (Or.inl (by rw [hx, rho_c1])) (Or.inr (by rw [hy, rho_c2]))
    · right; right
      exact key rho2 rho2_mem (Or.inl (by rw [hx, rho2_c1])) (Or.inr (by rw [hy, rho2_c2]))
    · right; left
      exact key rho rho_mem (Or.inr (by rw [hx, rho_c2])) (Or.inl (by rw [hy, rho_c1]))
    · exact absurd (hx.trans hy.symm) hne
  · rintro (rfl | rfl | rfl)
    · rfl
    · exact (show (rho • p0).1.1 = triPlus from rho_mem)
    · exact (show (rho2 • p0).1.1 = triPlus from rho2_mem)


theorem cusp3_ne_cusp1 : cusp3 ≠ cusp1 := plus12_ne_cusp1

theorem cusp3_ne_cusp2 : cusp3 ≠ cusp2 := plus12_ne_cusp2

theorem cusp3_notMem_triMinus : cusp3 ∉ triMinus.1 := by
  intro h
  simp only [triMinus, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with e | e | e
  · exact cusp3_ne_cusp1 e
  · exact cusp3_ne_cusp2 e
  · exact plusLine_ne_minusLine e12_unimod e

theorem rho_triMinus_ne : rho • triMinus ≠ triMinus := by
  intro h
  apply cusp3_notMem_triMinus
  rw [← h, ← rho_c2]
  exact smul_mem_tri_smul mem_triMinus_cusps12.2

theorem rho2_triMinus_ne : rho2 • triMinus ≠ triMinus := by
  intro h
  apply cusp3_notMem_triMinus
  rw [← h, ← rho2_c1]
  exact smul_mem_tri_smul mem_triMinus_cusps12.1

theorem rho2_mul_rho2 : rho2 * rho2 = rho := by
  apply eq_of_entries <;>
    simp [rho, rho2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, colGL_val_zero, colGL_val_one, e1, e2, e12]

theorem rho_triMinus_ne_rho2 : rho • triMinus ≠ rho2 • triMinus := by
  intro h
  apply rho_triMinus_ne
  calc rho • triMinus = (rho2 * rho2) • triMinus := by rw [rho2_mul_rho2]
    _ = rho2 • (rho2 • triMinus) := mul_smul _ _ _
    _ = rho2 • (rho • triMinus) := by rw [h]
    _ = (rho2 * rho) • triMinus := (mul_smul _ _ _).symm
    _ = triMinus := by rw [rho2_mul_rho, one_smul]

theorem p0_ne_rho : p0 ≠ rho • p0 := by
  intro h
  exact rho_triMinus_ne (congrArg (fun q : OTE => q.1.2) h).symm

theorem p0_ne_rho2 : p0 ≠ rho2 • p0 := by
  intro h
  exact rho2_triMinus_ne (congrArg (fun q : OTE => q.1.2) h).symm

theorem rho_p0_ne_rho2 : rho • p0 ≠ rho2 • p0 := by
  intro h
  exact rho_triMinus_ne_rho2 (congrArg (fun q : OTE => q.1.2) h)

theorem sum_nbF_triPlus {M : Type*} [AddCommMonoid M] (f : OTE → M) :
    ∑ q ∈ nbF triPlus, f q = f p0 + f (rho • p0) + f (rho2 • p0) := by
  rw [nbF_triPlus, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton, add_assoc]
  · simpa using rho_p0_ne_rho2
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨p0_ne_rho, p0_ne_rho2⟩

theorem sum_nbF {M : Type*} [AddCommMonoid M] (f : OTE → M) (g : IntegralGL) :
    ∑ q ∈ nbF (g • triPlus), f q = f (g • p0) + f ((g * rho) • p0) + f ((g * rho2) • p0) := by
  rw [nbF_smul, Finset.sum_image (fun a _ b _ h => MulAction.injective g h), sum_nbF_triPlus, mul_smul,
    mul_smul]

end TernaryPeriodPolynomials.Argument.HeckeDuality
