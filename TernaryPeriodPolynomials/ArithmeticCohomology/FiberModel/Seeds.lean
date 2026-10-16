module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Group

@[expose] public section


/-!
# Signed-permutation equivariant functions are determined by their three seeds

For an arbitrary `ℚ`-module `M` with a representation `ρ` of `GL₃(ℤ)`, the functions
`F : 𝒮 → M` with `F(r h) = sgn(π) ρ(h⁻¹) F(r)` for all signed permutation matrices `h = D π` are
determined by `P = F(1,0,0)`, `Q = F(1,1,0)`, `f = F(1,1,1)`
(`IsSignedEquivariant.ext_of_rep`); a triple of seeds extends if and only if each seed is invariant
under the stabilizer of its covector (`exists_signedEquivariant`, `IsSignedEquivariant.stab`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryCovectors
  TernaryPoly.OrdinaryApartmentFrames

section

variable {M : Type*} [AddCommGroup M] [Module ℚ M] (ρ : Representation ℚ IntegralGL M)

/-- The signed-permutation equivariance `F(r h) = sgn(π) ρ(h⁻¹) F(r)`, `h = D π`. -/
structure IsSignedEquivariant (F : NonzeroCovector → M) : Prop where
  signed : ∀ (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) (r : NonzeroCovector),
    F (act r (signedPerm s π)) =
      ((Equiv.Perm.sign π : ℤˣ) : ℤ) • ρ (signedPerm s π)⁻¹ (F r)

variable {ρ}

theorem IsFiberSystem.toSigned {F : NonzeroCovector → M} (h : IsFiberSystem ρ F) :
    IsSignedEquivariant ρ F := ⟨h.signed⟩

theorem IsSignedEquivariant.toFiberSystem {F : NonzeroCovector → M}
    (h : IsSignedEquivariant ρ F) (hn : ∀ r, normExpr ρ F r = 0) : IsFiberSystem ρ F :=
  ⟨h.signed, hn⟩

variable (ρ)

/-- The vector `m` transforms by `sgn(π)` under the signed permutation `(s, π)`. -/
def Inv (m : M) (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) : Prop :=
  ρ (signedPerm s π)⁻¹ m = ((Equiv.Perm.sign π : ℤˣ) : ℤ) • m

variable {ρ}

omit [Module ℚ M] in
theorem sign_smul_sign_smul (π : Equiv.Perm (Fin 3)) (x : M) :
    ((Equiv.Perm.sign π : ℤˣ) : ℤ) • ((Equiv.Perm.sign π : ℤˣ) : ℤ) • x = x := by
  rw [smul_smul, Int.units_coe_mul_self, one_smul]

theorem Inv.empty (m : M) : Inv ρ m ∅ 1 := by
  unfold Inv
  rw [signedPerm_empty_one, inv_one, map_one, Module.End.one_apply, map_one, Units.val_one,
    one_smul]

theorem Inv.mul {m : M} {s s' : Finset (Fin 3)} {π π' : Equiv.Perm (Fin 3)}
    (h : Inv ρ m s π) (h' : Inv ρ m s' π') :
    Inv ρ m (symmDiff s (s'.image π)) (π * π') := by
  unfold Inv at *
  rw [← signedPerm_mul, mul_inv_rev, rho_mul_apply, h, map_zsmul, h', smul_smul, map_mul,
    Units.val_mul, mul_comm]

theorem Inv.of_split {m : M} {s : Finset (Fin 3)} {π : Equiv.Perm (Fin 3)}
    (h1 : Inv ρ m s 1) (h2 : Inv ρ m ∅ π) : Inv ρ m s π := by
  have h := h1.mul h2
  rwa [Finset.image_empty, ← Finset.bot_eq_empty, symmDiff_bot, one_mul] at h

theorem Inv.flips {m : M} (Z : Finset (Fin 3)) (hZ : ∀ j ∈ Z, Inv ρ m {j} 1) :
    ∀ s : Finset (Fin 3), s ⊆ Z → Inv ρ m s 1 := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; exact Inv.empty m
  | insert j s hj ih =>
    intro hs
    have h1 := hZ j (hs (Finset.mem_insert_self j s))
    have h2 := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
    have h3 := h1.mul h2
    have e : symmDiff ({j} : Finset (Fin 3)) (s.image ⇑(1 : Equiv.Perm (Fin 3))) = insert j s := by
      ext x
      by_cases hx : x = j
      · subst hx
        simp [hj, Finset.mem_symmDiff]
      · by_cases hxs : x ∈ s <;> simp [hx, hxs, Finset.mem_symmDiff]
    rwa [e, mul_one] at h3

/-- Invariance of the three seeds under the stabilizers of their covectors, as in the paper's
list of stabilizer relations: `f` under all permutations, `Q` under the third sign change and the
transposition `(0 1)`, `P` under the second and third sign changes and the transposition `(1 2)`. -/
structure SeedStab (P Q f : M) : Prop where
  f_perm : ∀ π : Equiv.Perm (Fin 3), Inv ρ f ∅ π
  q_flip : Inv ρ Q {2} 1
  q_swap : Inv ρ Q ∅ (Equiv.swap 0 1)
  p_flip1 : Inv ρ P {1} 1
  p_flip2 : Inv ρ P {2} 1
  p_swap : Inv ρ P ∅ (Equiv.swap 1 2)

/-- The three seeds as a function on `Fin 3`. -/
def seedsOf (P Q f : M) : Fin 3 → M := ![P, Q, f]

/-- The invariance of all three seeds under the full stabilizers of their covectors. -/
def HStab (seed : Fin 3 → M) : Prop :=
  ∀ (i : Fin 3) (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)),
    act (rep i) (signedPerm s π) = rep i → Inv ρ (seed i) s π

theorem SeedStab.hstab {P Q f : M} (h : SeedStab (ρ := ρ) P Q f) : HStab (ρ := ρ) (seedsOf P Q f) := by
  intro i s π hs
  have hm : moveRow s π (rep i).1 = (rep i).1 := by
    rw [← act_signedPerm, hs]
  fin_cases i
  · obtain ⟨hsub, hπ⟩ := stab_rep0 s π hm
    have h1 : Inv ρ P s 1 := Inv.flips {1, 2} (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact h.p_flip1
      · exact h.p_flip2) s hsub
    rcases hπ with rfl | rfl
    · exact h1
    · exact h1.of_split h.p_swap
  · obtain ⟨hsub, hπ⟩ := stab_rep1 s π hm
    have h1 : Inv ρ Q s 1 := Inv.flips {2} (by
      intro j hj
      simp only [Finset.mem_singleton] at hj
      subst hj
      exact h.q_flip) s hsub
    rcases hπ with rfl | rfl
    · exact h1
    · exact h1.of_split h.q_swap
  · have hs2 := stab_rep2 s π hm
    subst hs2
    exact h.f_perm π


/-- Two signed permutations moving a seed's covector to the same covector give the same value. -/
theorem value_indep {seed : Fin 3 → M} (hst : HStab (ρ := ρ) seed) {i : Fin 3}
    {s₁ s₂ : Finset (Fin 3)} {π₁ π₂ : Equiv.Perm (Fin 3)}
    (h : act (rep i) (signedPerm s₁ π₁) = act (rep i) (signedPerm s₂ π₂)) :
    ((Equiv.Perm.sign π₁ : ℤˣ) : ℤ) • ρ (signedPerm s₁ π₁)⁻¹ (seed i) =
      ((Equiv.Perm.sign π₂ : ℤˣ) : ℤ) • ρ (signedPerm s₂ π₂)⁻¹ (seed i) := by
  have hu : signedPerm s₁ π₁ * (signedPerm s₂ π₂)⁻¹ =
      signedPerm (symmDiff s₁ ((s₂.image ⇑π₂⁻¹).image ⇑π₁)) (π₁ * π₂⁻¹) := by
    rw [signedPerm_inv, signedPerm_mul]
  have hact : act (rep i) (signedPerm s₁ π₁ * (signedPerm s₂ π₂)⁻¹) = rep i := by
    rw [act_mul, h, ← act_mul, mul_inv_cancel, act_one]
  rw [hu] at hact
  have hinv := hst i _ _ hact
  unfold Inv at hinv
  rw [← hu, mul_inv_rev, inv_inv, rho_mul_apply] at hinv
  -- hinv : ρ g₂ (ρ g₁⁻¹ (seed i)) = sgn(π₁ π₂⁻¹) • seed i
  have h2 := congrArg (ρ (signedPerm s₂ π₂)⁻¹) hinv
  rw [rho_inv_cancel', map_zsmul] at h2
  rw [h2, smul_smul]
  congr 1
  rw [map_mul, Equiv.Perm.sign_inv, Units.val_mul, ← mul_assoc, Int.units_coe_mul_self, one_mul]

variable (ρ) in
/-- The function on `𝒮` induced by three seeds. -/
def extendSeed (seed : Fin 3 → M) (r : NonzeroCovector) : M :=
  ((Equiv.Perm.sign (Classical.choose (cover r)).2.2 : ℤˣ) : ℤ) •
    ρ (signedPerm (Classical.choose (cover r)).2.1 (Classical.choose (cover r)).2.2)⁻¹
      (seed (Classical.choose (cover r)).1)

theorem extendSeed_eq {seed : Fin 3 → M} (hst : HStab (ρ := ρ) seed) {i : Fin 3}
    {s : Finset (Fin 3)} {π : Equiv.Perm (Fin 3)} {r : NonzeroCovector}
    (h : act (rep i) (signedPerm s π) = r) :
    extendSeed ρ seed r = ((Equiv.Perm.sign π : ℤˣ) : ℤ) • ρ (signedPerm s π)⁻¹ (seed i) := by
  have hd := Classical.choose_spec (cover r)
  set d := Classical.choose (cover r) with hdef
  have hdi : d.1 = i := by
    have h1 : moveRow d.2.1 d.2.2 (rep d.1).1 = moveRow s π (rep i).1 := by
      have e1 := congrArg Subtype.val hd
      have e2 := congrArg Subtype.val h
      rw [act_signedPerm] at e1 e2
      rw [e1, e2]
    exact orbits_disjoint _ _ _ _ _ _ h1
  have hact : act (rep i) (signedPerm d.2.1 d.2.2) = act (rep i) (signedPerm s π) := by
    have hd' : act (rep i) (signedPerm d.2.1 d.2.2) = r := by
      rw [← hdi]
      exact hd
    rw [hd', h]
  unfold extendSeed
  rw [← hdef, hdi]
  exact value_indep hst hact

theorem extendSeed_rep {seed : Fin 3 → M} (hst : HStab (ρ := ρ) seed) (i : Fin 3) :
    extendSeed ρ seed (rep i) = seed i := by
  rw [extendSeed_eq hst (s := ∅) (π := 1) (r := rep i)
    (by rw [signedPerm_empty_one, act_one]), signedPerm_empty_one]
  simp

theorem extendSeed_signed {seed : Fin 3 → M} (hst : HStab (ρ := ρ) seed) :
    IsSignedEquivariant ρ (extendSeed ρ seed) := by
  refine ⟨fun s π r => ?_⟩
  have hd := Classical.choose_spec (cover r)
  set d := Classical.choose (cover r) with hdef
  have hr : extendSeed ρ seed r = ((Equiv.Perm.sign d.2.2 : ℤˣ) : ℤ) •
      ρ (signedPerm d.2.1 d.2.2)⁻¹ (seed d.1) := by
    unfold extendSeed
    rw [← hdef]
  have h1 : act (rep d.1) (signedPerm (symmDiff d.2.1 (s.image ⇑d.2.2)) (d.2.2 * π)) =
      act r (signedPerm s π) := by
    rw [← signedPerm_mul, act_mul, hd]
  rw [extendSeed_eq hst h1, hr, ← signedPerm_mul, mul_inv_rev, rho_mul_apply, map_zsmul,
    smul_smul, map_mul, Units.val_mul]
  rw [mul_comm]

theorem exists_signedEquivariant {seed : Fin 3 → M} (hst : HStab (ρ := ρ) seed) :
    ∃ F : NonzeroCovector → M, IsSignedEquivariant ρ F ∧ ∀ i, F (rep i) = seed i :=
  ⟨extendSeed ρ seed, extendSeed_signed hst, extendSeed_rep hst⟩

/-- A signed-permutation equivariant function is determined by its three seeds. -/
theorem IsSignedEquivariant.ext_of_rep {F F' : NonzeroCovector → M}
    (hF : IsSignedEquivariant ρ F) (hF' : IsSignedEquivariant ρ F')
    (h : ∀ i, F (rep i) = F' (rep i)) : F = F' := by
  funext r
  obtain ⟨d, hd⟩ := cover r
  rw [← hd, hF.signed, hF'.signed, h]

/-- The seeds of a signed-permutation equivariant function are invariant under the stabilizers. -/
theorem IsSignedEquivariant.hstab {F : NonzeroCovector → M} (hF : IsSignedEquivariant ρ F) :
    HStab (ρ := ρ) (fun i => F (rep i)) := by
  intro i s π h
  have h1 := hF.signed s π (rep i)
  rw [h] at h1
  unfold Inv
  have h2 := congrArg (fun x => ((Equiv.Perm.sign π : ℤˣ) : ℤ) • x) h1
  simp only [sign_smul_sign_smul] at h2
  exact h2.symm

end

end TernaryPeriodPolynomials.Argument.FiberModel
