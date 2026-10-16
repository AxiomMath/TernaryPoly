module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.PrimeWeight

@[expose] public section


/-!
# Hermite normal forms of determinant `±p` and the full prime plane count

Every integral `2 × 2` matrix of determinant `±p` is right `GL₂(ℤ)`-equivalent to exactly one of
the `p + 1` Hermite forms `[[1,0],[i,p]]` (`0 ≤ i < p`) and `[[p,0],[0,1]]`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n p : ℕ}

/-- The Hermite representatives. -/
def hnfInt (p : ℕ) (i : Fin (p + 1)) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (i : ℕ) < p then !![1, 0; ((i : ℕ) : ℤ), p] else !![(p : ℤ), 0; 0, 1]

theorem fin_two_eq {a b c d a' b' c' d' : ℤ} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by rw [h1, h2, h3, h4]

/-- **Existence of the Hermite form.** -/
theorem hnf_exists (hp : p.Prime) (X : Matrix (Fin 2) (Fin 2) ℤ) (hX : X.det = p ∨ X.det = -p) :
    ∃ i : Fin (p + 1), ∃ W : Matrix (Fin 2) (Fin 2) ℤ, W.det * W.det = 1 ∧ X * W = hnfInt p i := by
  have hdet : X.det = X 0 0 * X 1 1 - X 0 1 * X 1 0 := det_fin_two X
  obtain ⟨a', ha⟩ := Int.gcd_dvd_left (X 0 0) (X 0 1)
  obtain ⟨b', hb⟩ := Int.gcd_dvd_right (X 0 0) (X 0 1)
  have hg := Int.gcd_eq_gcd_ab (X 0 0) (X 0 1)
  set g : ℤ := ((X 0 0).gcd (X 0 1) : ℤ) with hgdef
  set x := (X 0 0).gcdA (X 0 1)
  set y := (X 0 0).gcdB (X 0 1)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdet0 : X.det ≠ 0 := by rcases hX with h | h <;> rw [h] <;> simpa using hp0
  have hg0 : g ≠ 0 := by
    intro h0
    apply hdet0
    rw [hdet, ha, hb, h0]; ring
  have hxy : x * a' + y * b' = 1 := by
    apply mul_left_cancel₀ hg0
    linear_combination (-x) * ha + (-y) * hb - hg
  have hge : g * (X 1 1 * a' - X 1 0 * b') = X.det := by
    rw [hdet]; linear_combination (-(X 1 1)) * ha + X 1 0 * hb
  have hgdvd : (X 0 0).gcd (X 0 1) ∣ p := by
    have h1 : g ∣ (p : ℤ) := by
      rcases hX with h | h
      · exact ⟨_, (hge.trans h).symm⟩
      · exact ⟨-(X 1 1 * a' - X 1 0 * b'), by rw [mul_neg, hge, h, neg_neg]⟩
    exact Int.natCast_dvd_natCast.mp h1
  have hXeta : X = !![X 0 0, X 0 1; X 1 0, X 1 1] := Matrix.eta_fin_two X
  rcases hp.eq_one_or_self_of_dvd _ hgdvd with h1 | h1
  · -- `g = 1`
    have hg1 : g = 1 := by rw [hgdef, h1]; rfl
    rw [hg1, one_mul] at ha hb
    rw [hg1, one_mul] at hge
    obtain ⟨ε, he, hε⟩ : ∃ ε : ℤ, X 1 1 * a' - X 1 0 * b' = ε * p ∧ ε * ε = 1 := by
      rcases hX with h | h
      · exact ⟨1, by rw [hge, h]; ring, by norm_num⟩
      · exact ⟨-1, by rw [hge, h]; ring, by norm_num⟩
    set c' := X 1 0 * x + X 1 1 * y with hc'
    have hdiv : c' % p + c' / p * p = c' := Int.emod_add_ediv_mul c' p
    set k := c' / p
    set r := c' % p
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hp0
    have hrp : r < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp.pos)
    have hrn : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
    have hrlt : r.toNat < p := by omega
    refine ⟨⟨r.toNat, by omega⟩, !![x + b' * ε * k, -b' * ε; y - a' * ε * k, a' * ε], ?_, ?_⟩
    · have hW : (!![x + b' * ε * k, -b' * ε; y - a' * ε * k, a' * ε] : Matrix (Fin 2) (Fin 2) ℤ).det
          = ε := by
        rw [det_fin_two_of]; linear_combination ε * hxy
      rw [hW, hε]
    · rw [hnfInt, ite_eq_left hrlt, hrn]
      rw [hXeta, mul_fin_two, ha, hb]
      refine fin_two_eq ?_ ?_ ?_ ?_
      · linear_combination hxy
      · ring
      · linear_combination -hdiv - hc' - ε * k * he - (p : ℤ) * k * hε
      · linear_combination ε * he + (p : ℤ) * hε
  · -- `g = p`
    have hgp : g = p := by rw [hgdef, h1]
    rw [hgp] at ha hb hge
    obtain ⟨ε, he, hε⟩ : ∃ ε : ℤ, X 1 1 * a' - X 1 0 * b' = ε ∧ ε * ε = 1 := by
      rcases hX with h | h
      · refine ⟨1, ?_, by norm_num⟩
        apply mul_left_cancel₀ hp0; rw [hge, h]; ring
      · refine ⟨-1, ?_, by norm_num⟩
        apply mul_left_cancel₀ hp0; rw [hge, h]; ring
    set c' := X 1 0 * x + X 1 1 * y with hc'
    refine ⟨Fin.last p, !![x + b' * ε * c', -b' * ε; y - a' * ε * c', a' * ε], ?_, ?_⟩
    · have hW : (!![x + b' * ε * c', -b' * ε; y - a' * ε * c', a' * ε] :
          Matrix (Fin 2) (Fin 2) ℤ).det = ε := by
        rw [det_fin_two_of]; linear_combination ε * hxy
      rw [hW, hε]
    · rw [hnfInt, ite_eq_right (by simp)]
      rw [hXeta, mul_fin_two, ha, hb]
      refine fin_two_eq ?_ ?_ ?_ ?_
      · linear_combination (p : ℤ) * hxy
      · ring
      · linear_combination -hc' - ε * c' * he - c' * hε
      · linear_combination ε * he + hε

/-- **Uniqueness of the Hermite form.** -/
theorem hnf_unique (hp : p.Prime) (i j : Fin (p + 1)) (K : Matrix (Fin 2) (Fin 2) ℤ)
    (h : hnfInt p j = hnfInt p i * K) : i = j := by
  have hp1 : 1 < p := hp.one_lt
  rw [Matrix.eta_fin_two K] at h
  by_cases hi : (i : ℕ) < p <;> by_cases hj : (j : ℕ) < p
  · rw [hnfInt, ite_eq_left hj, hnfInt, ite_eq_left hi, mul_fin_two] at h
    have e10 := congrFun (congrFun h 1) 0
    have e00 := congrFun (congrFun h 0) 0
    simp at e10 e00
    -- `j = i + p * K 1 0`
    have hmod : ((j : ℕ) : ℤ) % p = ((i : ℕ) : ℤ) % p := by
      rw [e10, ← e00]; simp [Int.add_mul_emod_self_left]
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hj),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hi)] at hmod
    exact Fin.ext (by exact_mod_cast hmod.symm)
  · rw [hnfInt, ite_eq_right hj, hnfInt, ite_eq_left hi, mul_fin_two] at h
    have e01 := congrFun (congrFun h 0) 1
    have e11 := congrFun (congrFun h 1) 1
    simp at e01 e11
    rw [← e01] at e11
    simp at e11
    have : (p : ℤ) ∣ 1 := ⟨_, e11⟩
    have := Int.eq_one_of_dvd_one (by positivity) this
    omega
  · rw [hnfInt, ite_eq_left hj, hnfInt, ite_eq_right hi, mul_fin_two] at h
    have e00 := congrFun (congrFun h 0) 0
    simp at e00
    have : (p : ℤ) ∣ 1 := ⟨_, e00⟩
    have := Int.eq_one_of_dvd_one (by positivity) this
    omega
  · exact Fin.ext (by omega)

theorem hnfInt_det (i : Fin (p + 1)) : (hnfInt p i).det = p := by
  unfold hnfInt
  split_ifs <;> simp [det_fin_two_of]

/-- The Hermite representatives in `GL₂(ℚ)`. -/
def hGL (hp : p.Prime) (i : Fin (p + 1)) : GeneralLinearGroup (Fin 2) ℚ :=
  Matrix.nonsingInvUnit ((hnfInt p i).map (Int.cast : ℤ → ℚ)) (by
    rw [intCast_det2, hnfInt_det]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hp.ne_zero))

theorem hGL_val (hp : p.Prime) (i : Fin (p + 1)) :
    (hGL hp i).val = (hnfInt p i).map (Int.cast : ℤ → ℚ) := rfl

/-- Every integral `B` of determinant `±p` is right `GL₂(ℤ)`-equivalent to a Hermite form. -/
theorem hGL_class (hp : p.Prime) (B : GeneralLinearGroup (Fin 2) ℚ)
    (hB : ∀ i j, ∃ z : ℤ, (z : ℚ) = B.val i j) (hdet : B.val.det = p ∨ B.val.det = -p) :
    ∃ i : Fin (p + 1), (hGL hp i)⁻¹ * B ∈ Γ2 := by
  choose X hX using hB
  have hXB : (Matrix.of X).map (Int.cast : ℤ → ℚ) = B.val := by ext i j; exact hX i j
  have hdetX : (Matrix.of X).det = p ∨ (Matrix.of X).det = -p := by
    have h := intCast_det2 (Matrix.of X)
    rw [hXB] at h
    rcases hdet with hd | hd
    · left; exact_mod_cast h.symm.trans hd
    · right; exact_mod_cast h.symm.trans hd
  obtain ⟨i, W, hW, hXW⟩ := hnf_exists hp (Matrix.of X) hdetX
  set V := W.det • W.adjugate with hV
  have hWV : W * V = 1 := by
    rw [hV, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hW, one_smul]
  have hdetV : V.det * V.det = 1 := by
    have h : V.det * W.det = 1 := by rw [mul_comm, ← det_mul, hWV, det_one]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h with e | e <;> rw [e] <;> norm_num
  have hXV : Matrix.of X = hnfInt p i * V := by
    rw [← hXW, Matrix.mul_assoc, hWV, Matrix.mul_one]
  refine ⟨i, mem_Γ2_of_int V ?_ hdetV⟩
  rw [Units.val_mul, ← hXB, hXV, intCast_map_mul2, ← hGL_val hp i, ← Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-- Distinct Hermite forms are inequivalent. -/
theorem hGL_inj (hp : p.Prime) {i j : Fin (p + 1)} (h : (hGL hp i)⁻¹ * hGL hp j ∈ Γ2) : i = j := by
  obtain ⟨k₀, hk⟩ := h
  have hj : hGL hp j = hGL hp i * GeneralLinearGroup.map (Int.castRingHom ℚ) k₀ := by
    rw [hk, mul_inv_cancel_left]
  have hval := congrArg Units.val hj
  rw [Units.val_mul, hGL_val, hGL_val,
    show (GeneralLinearGroup.map (Int.castRingHom ℚ) k₀).val = (k₀.val).map (Int.cast : ℤ → ℚ)
      from rfl, ← intCast_map_mul2] at hval
  have hint : hnfInt p j = hnfInt p i * k₀.val := by
    ext a b
    have := congrFun (congrFun hval a) b
    simp only [Matrix.map_apply] at this
    exact_mod_cast this
  exact hnf_unique hp i j k₀.val hint

theorem hGL_mk_eq (hp : p.Prime) (i : Fin (p + 1)) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    (QuotientGroup.mk (hGL hp i, (1 : ℚˣ)) : MP ⧸ ΓM0) = QuotientGroup.mk (B, s) ↔
      (hGL hp i)⁻¹ * B ∈ Γ2 ∧ s = 1 := by
  rw [QuotientGroup.eq]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp h
    rw [Subgroup.mem_bot] at h2
    refine ⟨h1, ?_⟩
    have : (1 : ℚˣ)⁻¹ * s = 1 := h2
    simpa using this
  · rintro ⟨h1, rfl⟩
    exact Subgroup.mem_prod.mpr ⟨h1, by
      rw [Subgroup.mem_bot]; change (1 : ℚˣ)⁻¹ * 1 = 1; simp⟩

/-- **The representatives with plane scalar `1` number `p (p + 1)`.** -/
theorem prime_plane_count_one (hp : p.Prime) (t : HeckeCorrespondence) (ht : AwayThree t)
    (hg : t.g = gP hp) (vP : RationalGL3 → ℚ × ℚ) (BP : RationalGL3 → GeneralLinearGroup (Fin 2) ℚ)
    (sP : RationalGL3 → ℚˣ) (γP : RationalGL3 → IntegralGL)
    (hP : ∀ r ∈ t.representatives,
      r = pU (vP r) * planeLevi (BP r) (sP r) * integralRational (γP r))
    (hsP : ∀ r ∈ t.representatives, 0 < (sP r : ℚ)) :
    (t.representatives.filter (fun r => ¬ (sP r : ℚ) = p)).card = p * (p + 1) := by
  classical
  have hRS := repSet ht
  have hDl : ∀ γ ∈ Γ, ∀ x ∈ DZ t.g, γ * x ∈ DZ t.g := fun γ hγ x hx => DZ_left hx hγ
  have hDr : ∀ x ∈ DZ t.g, ∀ γ ∈ Γ, x * γ ∈ DZ t.g := fun x hx γ hγ => DZ_right hx hγ
  have hdecP : ∀ r ∈ t.representatives, 0 < (((BP r, sP r) : MP).2 : ℚ) ∧
      r⁻¹ * (planeData.U (vP r) * planeData.L (BP r, sP r)) ∈ Γ := by
    intro r hr
    refine ⟨hsP r hr, ?_⟩
    change r⁻¹ * (pU (vP r) * planeLevi (BP r) (sP r)) ∈ Γ
    have : pU (vP r) * planeLevi (BP r) (sP r) = r * (integralRational (γP r))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact (hP r hr).symm
    rw [this, inv_mul_cancel_left]
    exact Γ.inv_mem ⟨_, rfl⟩
  let cls : RationalGL3 → MP ⧸ ΓM0 := fun r => QuotientGroup.mk (BP r, sP r)
  let H : Fin (p + 1) → MP ⧸ ΓM0 := fun i => QuotientGroup.mk (hGL hp i, (1 : ℚˣ))
  have hHinj : Function.Injective H := by
    intro i j hij
    have := (hGL_mk_eq hp i (hGL hp j) 1).mp hij
    exact hGL_inj hp this.1
  have hmaps : Set.MapsTo cls ↑(t.representatives.filter (fun r => ¬ (sP r : ℚ) = p))
      ↑(Finset.univ.image H) := by
    intro r hr
    rw [Finset.coe_filter] at hr
    obtain ⟨hr, hne⟩ := hr
    rcases prime_plane_levi hp _ _ _ (hsP r hr) (rep_plane_mem hp ht hg hr (hP r hr)) with
      ⟨hs, -⟩ | ⟨hs1, hB, hdet⟩
    · exact absurd hs hne
    obtain ⟨i, hi⟩ := hGL_class hp (BP r) hB hdet
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact ⟨i, (hGL_mk_eq hp i (BP r) (sP r)).mpr ⟨hi, Units.ext (by rw [hs1, Units.val_one])⟩⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_image (fun i _ j _ h => hHinj h)]
  have hterm : ∀ i : Fin (p + 1),
      ((t.representatives.filter (fun r => ¬ (sP r : ℚ) = p)).filter (fun r => cls r = H i)).card
        = p := by
    intro i
    have hfilt : (t.representatives.filter (fun r => ¬ (sP r : ℚ) = p)).filter
        (fun r => cls r = H i) = t.representatives.filter
          (fun r => (QuotientGroup.mk (BP r, sP r) : MP ⧸ ΓM0) =
            QuotientGroup.mk (hGL hp i, (1 : ℚˣ))) := by
      rw [Finset.filter_filter]
      refine Finset.filter_congr fun r _ => ?_
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        have := ((hGL_mk_eq hp i (BP r) (sP r)).mp h.symm).2
        rw [this, Units.val_one]
        exact_mod_cast hp.one_lt.ne
    rw [hfilt, planeData.fiber_card hRS ΓM0 ΓM0_le (fun m : MP => 0 < (m.2 : ℚ)) pos_class
      vP (fun r => (BP r, sP r)) hdecP (hGL hp i, (1 : ℚˣ)) (by simp)]
    have hC := plane_count hDl hDr (hGL hp i) 1
    have hdet1 : |(((1 : ℚˣ)⁻¹ : ℚˣ).val • (hGL hp i).val).det| = p := by
      rw [inv_one, Units.val_one, one_smul, hGL_val, intCast_det2, hnfInt_det]
      simp
    have hS : planeData.S (DZ t.g) (hGL hp i, (1 : ℚˣ)) = (zLat : Set (ℚ × ℚ)) := by
      ext u
      change pU u * planeLevi (hGL hp i) 1 ∈ DZ t.g ↔ u ∈ zLat
      rw [hg, plane_mem_DZ_gP_iff, mem_zLat, Units.val_one, mul_one, mul_one, mul_one, hGL_val,
        intCast_det2, hnfInt_det]
      constructor
      · rintro ⟨⟨-, -, h1, h2⟩, -⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨fun a b => ⟨_, rfl⟩, ⟨1, by simp⟩, h1, h2⟩, Or.inl rfl⟩
    have hNL : planeData.NL (DZ t.g) (hGL hp i, (1 : ℚˣ)) = 1 := by
      rw [ParabolicData.NL, hS, Set.ncard_eq_one]
      refine ⟨0, Set.ext fun y => ?_⟩
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [Set.mem_singleton_iff, QuotientAddGroup.eq_zero_iff]
        exact hu
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        exact ⟨0, zLat.zero_mem, by rw [hy]; rfl⟩
    rw [hdet1, hNL, Nat.cast_one, mul_one] at hC
    exact_mod_cast hC
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm]

/-- **The prime Hecke eigenvalue on plane sections.** For every correspondence of the double
coset of `diag(p,1,1)`, the plane eigenvalue is `W(1, p) + (p² + p) • W(diag(p,1), 1)`, and the
correspondence has `p² + p + 1` representatives. -/
theorem prime_plane_eigenvalue_explicit (D : InducingData n) (hp : p.Prime) (t : HeckeCorrespondence)
    (ht : AwayThree t) (hg : t.g = gP hp) :
    t.representatives.card = p ^ 2 + p + 1 ∧
      ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
        ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
          (ratPlaneWeight D 1 (pUnit hp) + ((p : ℂ) ^ 2 + p) * ratPlaneWeight D (dP hp) 1) *
            f g := by
  classical
  choose vP BP sP γP hsP hP using plane_iwasawa_pos
  have hform := plane_rational_formula D t ht vP BP sP γP (fun r _ => hP r)
  have hcount := prime_plane_count hp t ht hg vP BP sP γP (fun r _ => hP r) (fun r _ => hsP r)
  have hcount1 := prime_plane_count_one hp t ht hg vP BP sP γP (fun r _ => hP r)
    (fun r _ => hsP r)
  have hterm : ∀ r ∈ t.representatives, ratPlaneWeight D (BP r) (sP r) =
      if (sP r : ℚ) = p then ratPlaneWeight D 1 (pUnit hp) else ratPlaneWeight D (dP hp) 1 := by
    intro r hr
    have hmem := rep_plane_mem hp ht hg hr (hP r)
    rcases prime_plane_weight D hp _ _ _ (hsP r) hmem with ⟨hs, hw⟩ | ⟨hs, hw⟩
    · rw [ite_eq_left hs, hw, show sP r = pUnit hp from Units.ext (by rw [hs, pUnit_val])]
    · have hne : (sP r : ℚ) ≠ p := by rw [hs]; exact_mod_cast hp.one_lt.ne
      rw [ite_eq_right hne, hw, show sP r = 1 from Units.ext (by rw [hs, Units.val_one])]
  refine ⟨?_, fun f hf g => ?_⟩
  · rw [← Finset.card_filter_add_card_filter_not (fun r => (sP r : ℚ) = p), hcount, hcount1]
    ring
  rw [hform f hf g, Finset.sum_congr rfl hterm, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, hcount, hcount1]
  push_cast
  ring

end TernaryPeriodPolynomials.HeckeEigen.Satake
