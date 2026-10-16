module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Slash

@[expose] public section


/-!
# Lemma 4.3 (`lem:three-seed`) for an arbitrary coefficient module

Let `M` be a `ℚ`-module with a representation `ρ₀` of `GL₃(ℤ)` (substitution of variables) and
`ρ` its determinant twist.  A signed-permutation equivariant function `F : 𝒮 → M` is determined by
its seeds `P = F(1,0,0)`, `Q = F(1,1,0)`, `f = F(1,1,1)` (`IsSignedEquivariant.ext_of_rep`); it
satisfies the norm relation if and only if the seeds satisfy the list of Lemma 4.3
(`IsSignedEquivariant.norm_iff_seedList`); and seeds with these properties extend uniquely
(`seedList_extension`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryCovectors
  TernaryPoly.OrdinaryCovectorOrbits TernaryPoly.OrdinaryApartmentFrames

section

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

theorem det_eq (h : IntegralGL) (e : ℤ) (he : h.val.det = e) :
    ((Matrix.GeneralLinearGroup.det h : ℤˣ) : ℤ) = e := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact he

theorem det_aG : ((Matrix.GeneralLinearGroup.det aG : ℤˣ) : ℤ) = 1 :=
  det_eq _ _ (by decide +kernel)
theorem det_aG_sq : ((Matrix.GeneralLinearGroup.det (aG ^ 2) : ℤˣ) : ℤ) = 1 := by
  rw [map_pow, Units.val_pow_eq_pow_val, det_aG, one_pow]
theorem det_T1 : ((Matrix.GeneralLinearGroup.det T1 : ℤˣ) : ℤ) = 1 := det_eq _ _ (by decide +kernel)
theorem det_T2 : ((Matrix.GeneralLinearGroup.det T2 : ℤˣ) : ℤ) = 1 := det_eq _ _ (by decide +kernel)
theorem det_T3 : ((Matrix.GeneralLinearGroup.det T3 : ℤˣ) : ℤ) = -1 := det_eq _ _ (by decide +kernel)
theorem det_T4 : ((Matrix.GeneralLinearGroup.det T4 : ℤˣ) : ℤ) = -1 := det_eq _ _ (by decide +kernel)
theorem det_T5 : ((Matrix.GeneralLinearGroup.det T5 : ℤˣ) : ℤ) = -1 := det_eq _ _ (by decide +kernel)
theorem det_U1 : ((Matrix.GeneralLinearGroup.det U1 : ℤˣ) : ℤ) = 1 := det_eq _ _ (by decide +kernel)
theorem det_U2 : ((Matrix.GeneralLinearGroup.det U2 : ℤˣ) : ℤ) = 1 := det_eq _ _ (by decide +kernel)

theorem aG_sq_inv : (aG ^ 2)⁻¹ = aG := by decide +kernel

theorem signedPerm_one (s : Finset (Fin 3)) : signedPerm s 1 = signFrame s := by
  rw [signedPerm, map_one, mul_one]

theorem signedPerm_empty (π : Equiv.Perm (Fin 3)) : signedPerm ∅ π = permFrame π := by
  rw [signedPerm, signFrame_empty, one_mul]

variable (ρ₀ ρ : Representation ℚ IntegralGL M)

/-- The list of Lemma 4.3 on the seeds `f = F(1,1,1)`, `P = F(1,0,0)`, `Q = F(1,1,0)`, written with
the substitution `x ∣ h`: `f` symmetric; `Q(a,b,c) = Q(b,a,c) = -Q(a,b,-c)`;
`P(a,b,c) = P(a,c,b) = -P(a,-b,c) = -P(a,b,-c)`; `N₁₂ f = N₁₂ Q = N₂₃ P = 0`; and
`eq:mixed1`, `eq:mixed2`. -/
structure SeedList (f P Q : M) : Prop where
  f_symm : ∀ π : Equiv.Perm (Fin 3), slash ρ₀ f (permFrame π) = f
  q_swap : slash ρ₀ Q (permFrame (Equiv.swap 0 1)) = Q
  q_odd : slash ρ₀ Q (signFrame {2}) = -Q
  p_swap : slash ρ₀ P (permFrame (Equiv.swap 1 2)) = P
  p_odd2 : slash ρ₀ P (signFrame {1}) = -P
  p_odd3 : slash ρ₀ P (signFrame {2}) = -P
  nf : f + slash ρ₀ f aG + slash ρ₀ f (aG ^ 2) = 0
  nq : Q + slash ρ₀ Q aG + slash ρ₀ Q (aG ^ 2) = 0
  np : P + slash ρ₀ P U1 + slash ρ₀ P U2 = 0
  mixed1 : slash ρ₀ Q T1 - Q = slash ρ₀ f T2
  mixed2 : slash ρ₀ P T3 - slash ρ₀ P T5 = slash ρ₀ Q T4

variable {ρ₀ ρ}

theorem IsTwist.seedStab_iff (hρ : IsTwist ρ₀ ρ) (f P Q : M) :
    SeedStab (ρ := ρ) P Q f ↔
      (∀ π : Equiv.Perm (Fin 3), slash ρ₀ f (permFrame π) = f) ∧
      slash ρ₀ Q (permFrame (Equiv.swap 0 1)) = Q ∧ slash ρ₀ Q (signFrame {2}) = -Q ∧
      slash ρ₀ P (permFrame (Equiv.swap 1 2)) = P ∧ slash ρ₀ P (signFrame {1}) = -P ∧
      slash ρ₀ P (signFrame {2}) = -P := by
  have e1 : ∀ (m : M) (π : Equiv.Perm (Fin 3)),
      Inv ρ m ∅ π ↔ slash ρ₀ m (permFrame π) = m := by
    intro m π
    rw [hρ.inv_iff, signedPerm_empty]
    simp
  have e2 : ∀ (m : M) (j : Fin 3),
      Inv ρ m {j} 1 ↔ slash ρ₀ m (signFrame {j}) = -m := by
    intro m j
    rw [hρ.inv_iff, signedPerm_one]
    simp
  constructor
  · intro h
    exact ⟨fun π => (e1 f π).mp (h.f_perm π), (e1 Q _).mp h.q_swap, (e2 Q 2).mp h.q_flip,
      (e1 P _).mp h.p_swap, (e2 P 1).mp h.p_flip1, (e2 P 2).mp h.p_flip2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨fun π => (e1 f π).mpr (h1 π), (e2 Q 2).mpr h3, (e1 Q _).mpr h2, (e2 P 1).mpr h5,
      (e2 P 2).mpr h6, (e1 P _).mpr h4⟩


/-- The signed equivariance in the paper's form `F(r h) = χ₁(h) F(r) ∣ h`, with
`χ₁(D π) = (-1)^{|s|}`. -/
def PaperSigned (ρ₀ : Representation ℚ IntegralGL M) (F : NonzeroCovector → M) : Prop :=
  ∀ (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) (r : NonzeroCovector),
    F (act r (signedPerm s π)) = ((-1 : ℤ) ^ s.card) • slash ρ₀ (F r) (signedPerm s π)

theorem IsTwist.signed_iff (hρ : IsTwist ρ₀ ρ) (F : NonzeroCovector → M) :
    IsSignedEquivariant ρ F ↔ PaperSigned ρ₀ F := by
  constructor
  · intro h s π r
    rw [h.signed, hρ.rho_inv, det_signedPerm, smul_smul, mul_left_comm,
      Int.units_coe_mul_self, mul_one]
  · intro h
    refine ⟨fun s π r => ?_⟩
    rw [h s π r, hρ.rho_inv, det_signedPerm, smul_smul, mul_left_comm,
      Int.units_coe_mul_self, mul_one]

theorem rho_eq_zero_iff (g : IntegralGL) (x : M) : ρ g x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 := congrArg (ρ g⁻¹) h
    rwa [rho_inv_cancel', map_zero] at h2
  · intro h
    rw [h, map_zero]

theorem stab_f : ∀ π : Equiv.Perm (Fin 3), act (rep 2) (signedPerm ∅ π) = rep 2 := by
  intro π
  apply Subtype.ext
  rw [act_signedPerm]
  revert π
  decide +kernel

theorem IsSignedEquivariant.seedStab {F : NonzeroCovector → M} (hF : IsSignedEquivariant ρ F) :
    SeedStab (ρ := ρ) (F (rep 0)) (F (rep 1)) (F (rep 2)) := by
  have h := hF.hstab
  refine ⟨fun π => h 2 ∅ π (stab_f π), h 1 {2} 1 ?_, h 1 ∅ (Equiv.swap 0 1) ?_, h 0 {1} 1 ?_,
    h 0 {2} 1 ?_, h 0 ∅ (Equiv.swap 1 2) ?_⟩ <;>
  · apply Subtype.ext
    rw [act_signedPerm]
    decide +kernel

theorem slash_N_iff (hρ : IsTwist ρ₀ ρ) (m : M) :
    m + slash ρ₀ m aG + slash ρ₀ m (aG ^ 2) = 0 ↔ m + ρ aG m + ρ (aG ^ 2) m = 0 := by
  rw [hρ.slash_eq_of_det det_aG, hρ.slash_eq_of_det det_aG_sq,
    ReferenceCoefficientMatrices.a_inv_eq_sq, aG_sq_inv, one_smul, one_smul, add_right_comm]

omit [Module ℚ M] in
theorem neg_sub_neg_iff (a b c : M) : -a - -b = -c ↔ a - b - c = 0 := by
  rw [neg_sub_neg, sub_eq_zero, ← neg_sub a b, neg_inj]

/-- **Lemma 4.3, norm criterion (`ρ`-version).** -/
theorem IsSignedEquivariant.norm_iff_seedList (hρ : IsTwist ρ₀ ρ) {F : NonzeroCovector → M}
    (hF : IsSignedEquivariant ρ F) :
    (∀ r, normExpr ρ F r = 0) ↔ SeedList ρ₀ (F (rep 2)) (F (rep 0)) (F (rep 1)) := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := (hρ.seedStab_iff _ _ _).mp hF.seedStab
  have n0 : F (rep 0) + slash ρ₀ (F (rep 0)) U1 + slash ρ₀ (F (rep 0)) U2 = 0 ↔
      normExpr ρ F ⟨representative 0, rep_ne_zero 0⟩ = 0 := by
    rw [norm_eq0 hF, rho_eq_zero_iff, hρ.slash_eq_of_det det_U1, hρ.slash_eq_of_det det_U2,
      one_smul, one_smul]
  have n1 : F (rep 1) + slash ρ₀ (F (rep 1)) aG + slash ρ₀ (F (rep 1)) (aG ^ 2) = 0 ↔
      normExpr ρ F (rep 1) = 0 := by
    rw [slash_N_iff hρ, norm_rep1]
  have n2 : F (rep 2) + slash ρ₀ (F (rep 2)) aG + slash ρ₀ (F (rep 2)) (aG ^ 2) = 0 ↔
      normExpr ρ F (rep 2) = 0 := by
    rw [slash_N_iff hρ, norm_rep2]
  have n3 : slash ρ₀ (F (rep 1)) T1 - F (rep 1) = slash ρ₀ (F (rep 2)) T2 ↔
      normExpr ρ F ⟨representative 3, rep_ne_zero 3⟩ = 0 := by
    rw [norm_eq3 hF, neg_eq_zero, rho_eq_zero_iff, hρ.slash_eq_of_det det_T1,
      hρ.slash_eq_of_det det_T2, one_smul, one_smul, sub_sub, sub_eq_zero, sub_eq_iff_eq_add,
      add_comm]
  have n4 : slash ρ₀ (F (rep 0)) T3 - slash ρ₀ (F (rep 0)) T5 = slash ρ₀ (F (rep 1)) T4 ↔
      normExpr ρ F ⟨representative 4, rep_ne_zero 4⟩ = 0 := by
    rw [norm_eq4 hF, rho_eq_zero_iff, hρ.slash_eq_of_det det_T3, hρ.slash_eq_of_det det_T5,
      hρ.slash_eq_of_det det_T4]
    simp only [neg_smul, one_smul]
    exact neg_sub_neg_iff _ _ _
  constructor
  · intro h
    exact ⟨s1, s2, s3, s4, s5, s6, n2.mpr (h _), n1.mpr (h _), n0.mpr (h _), n3.mpr (h _),
      n4.mpr (h _)⟩
  · intro h
    apply hF.norm_of_five
    intro i
    fin_cases i
    · exact n0.mp h.np
    · exact n1.mp h.nq
    · exact n2.mp h.nf
    · exact n3.mp h.mixed1
    · exact n4.mp h.mixed2


/-- **Lemma 4.3, converse and extension.**  Seeds satisfying the list extend to a function
satisfying the signed equivariance and the norm relation, uniquely among the signed
equivariant functions with these seeds. -/
theorem seedList_extension (hρ : IsTwist ρ₀ ρ) {f P Q : M} (h : SeedList ρ₀ f P Q) :
    ∃ F : NonzeroCovector → M, IsFiberSystem ρ F ∧ F (rep 0) = P ∧ F (rep 1) = Q ∧
      F (rep 2) = f ∧ ∀ F' : NonzeroCovector → M, IsSignedEquivariant ρ F' → F' (rep 0) = P →
        F' (rep 1) = Q → F' (rep 2) = f → F' = F := by
  have hs : SeedStab (ρ := ρ) P Q f :=
    (hρ.seedStab_iff f P Q).mpr ⟨h.f_symm, h.q_swap, h.q_odd, h.p_swap, h.p_odd2, h.p_odd3⟩
  obtain ⟨F, hF, hrep⟩ := exists_signedEquivariant hs.hstab
  have h0 : F (rep 0) = P := hrep 0
  have h1 : F (rep 1) = Q := hrep 1
  have h2 : F (rep 2) = f := hrep 2
  have hn : ∀ r, normExpr ρ F r = 0 := by
    rw [hF.norm_iff_seedList hρ, h0, h1, h2]
    exact h
  refine ⟨F, ⟨hF.signed, hn⟩, h0, h1, h2, fun F' hF' e0 e1 e2 => ?_⟩
  apply hF'.ext_of_rep hF
  intro i
  fin_cases i
  · exact e0.trans h0.symm
  · exact e1.trans h1.symm
  · exact e2.trans h2.symm


/-- The norm relation `F(r) + F(rA²) ∣ A + F(rA) ∣ A² = 0` (`eq:fiber-norm`) in the
paper's form, for a function on `𝒮`. -/
def PaperNorm (ρ₀ : Representation ℚ IntegralGL M) (F : NonzeroCovector → M) : Prop :=
  ∀ r : NonzeroCovector,
    F r + slash ρ₀ (F (act r (aG ^ 2))) aG + slash ρ₀ (F (act r aG)) (aG ^ 2) = 0

theorem IsTwist.paperNorm_iff (hρ : IsTwist ρ₀ ρ) (F : NonzeroCovector → M) :
    PaperNorm ρ₀ F ↔ ∀ r, normExpr ρ F r = 0 := by
  unfold PaperNorm normExpr
  refine forall_congr' fun r => ?_
  rw [hρ.slash_eq_of_det det_aG, hρ.slash_eq_of_det det_aG_sq,
    ReferenceCoefficientMatrices.a_inv_eq_sq, aG_sq_inv, one_smul, one_smul, add_right_comm]

/-- **Lemma 4.3, uniqueness.** A signed-permutation equivariant function is determined by its
seeds. -/
theorem lemma43_unique (hρ : IsTwist ρ₀ ρ) {F F' : NonzeroCovector → M}
    (hF : PaperSigned ρ₀ F) (hF' : PaperSigned ρ₀ F')
    (h0 : F (rep 0) = F' (rep 0)) (h1 : F (rep 1) = F' (rep 1)) (h2 : F (rep 2) = F' (rep 2)) :
    F = F' := by
  apply ((hρ.signed_iff F).mpr hF).ext_of_rep ((hρ.signed_iff F').mpr hF')
  intro i
  fin_cases i
  exacts [h0, h1, h2]

/-- **Lemma 4.3, norm criterion.** A signed-permutation equivariant function satisfies the norm
relation if and only if its seeds satisfy the list. -/
theorem lemma43_iff (hρ : IsTwist ρ₀ ρ) {F : NonzeroCovector → M} (hF : PaperSigned ρ₀ F) :
    PaperNorm ρ₀ F ↔ SeedList ρ₀ (F (rep 2)) (F (rep 0)) (F (rep 1)) := by
  rw [hρ.paperNorm_iff]
  exact ((hρ.signed_iff F).mpr hF).norm_iff_seedList hρ

/-- **Lemma 4.3, converse and unique extension.** -/
theorem lemma43_extension (hρ : IsTwist ρ₀ ρ) {f P Q : M} (h : SeedList ρ₀ f P Q) :
    ∃! F : NonzeroCovector → M, PaperSigned ρ₀ F ∧ PaperNorm ρ₀ F ∧
      F (rep 0) = P ∧ F (rep 1) = Q ∧ F (rep 2) = f := by
  obtain ⟨F, hF, h0, h1, h2, hu⟩ := seedList_extension hρ h
  refine ⟨F, ⟨(hρ.signed_iff F).mp hF.toSigned, (hρ.paperNorm_iff F).mpr hF.norm, h0, h1, h2⟩, ?_⟩
  rintro F' ⟨hs, -, e0, e1, e2⟩
  exact hu F' ((hρ.signed_iff F').mpr hs) e0 e1 e2

end

end TernaryPeriodPolynomials.Argument.FiberModel
