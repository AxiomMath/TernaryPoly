module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.Comparison
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.SingleCharacterReduction

@[expose] public section


/-!
# Equality of the plane and line eigenvalues, and `SingleCharacter`

The plane and line eigenvalues of every away-from-three correspondence agree
(`plane_line_scalar`). Consequently the away-from-three Hecke algebra acts on every associate pair
through a single character (`singleCharacter`).

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.HeckeEigen

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n : ℕ}

/-! ### Invariances of the rational weights -/

theorem Bo_mul (B C : GeneralLinearGroup (Fin 2) ℚ) : Bo (B * C) = Bo B * Bo C := by
  simp only [Bo, glF, map_mul, glAway2_mul]

theorem glF_Γ2 {k : GeneralLinearGroup (Fin 2) ℚ} (hk : k ∈ Γ2) : glF k ∈ sphericalFinite := by
  obtain ⟨k₀, rfl⟩ := hk
  refine ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) k₀, ?_⟩
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  simp [GeneralLinearGroup.map_apply]

theorem Bo_Γ2 {k : GeneralLinearGroup (Fin 2) ℚ} (hk : k ∈ Γ2) : Bo k ∈ awayLevel placeThree :=
  glAway2_level (glF_Γ2 hk)

theorem Bo_transpose (B : GeneralLinearGroup (Fin 2) ℚ) : Bo (transposeGL B) = transposeGL (Bo B) := by
  simp only [Bo, glF]
  rw [← transposeGL_map, glAway2_transpose]

theorem ratPlaneWeight_mul (D : InducingData n) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ)
    {k : GeneralLinearGroup (Fin 2) ℚ} (hk : k ∈ Γ2) :
    ratPlaneWeight D (B * k) s = ratPlaneWeight D B s := by
  have hk' := Bo_Γ2 hk
  have hω := omega_level D.cusp (Bo B) (awayLevel placeThree).one_mem hk'
  rw [one_mul] at hω
  simp only [ratPlaneWeight, planeWeight]
  rw [Bo_mul, ← HeckeTranslate.HeckeInvariance.atFinite_mul, map_mul, np_mul,
    np_det_spherical hk'.2, mul_one, hω]

theorem ratLineWeight_mul (D : InducingData n) (A : GeneralLinearGroup (Fin 2) ℚ) (d : ℚˣ)
    {k : GeneralLinearGroup (Fin 2) ℚ} (hk : k ∈ Γ2) :
    ratLineWeight D (A * k) d = ratLineWeight D A d := by
  have hk' := Bo_Γ2 hk
  have hω := omega_level D.cusp (Bo A) (awayLevel placeThree).one_mem hk'
  rw [one_mul] at hω
  simp only [ratLineWeight, lineWeight]
  rw [Bo_mul, ← HeckeTranslate.HeckeInvariance.atFinite_mul, map_mul, np_mul,
    np_det_spherical hk'.2, mul_one, hω]

theorem ratPlaneWeight_transpose (D : InducingData n) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    ratPlaneWeight D (transposeGL B) s = ratPlaneWeight D B s := by
  have hBo : Bo B ∈ awayGroup placeThree := glAway2_mem _
  simp only [ratPlaneWeight, planeWeight]
  rw [Bo_transpose, omega_transpose D.cusp hBo, ← transposeGL_atFinite, det_transposeGL]

theorem delta_eq {d : ℚˣ} {A : GeneralLinearGroup (Fin 2) ℚ} (h1 : Int3 (d : ℚ))
    (h2 : Int3 (d : ℚ)⁻¹) (h3 : Int3 A.val.det) (h4 : Int3 (A.val.det)⁻¹) :
    normPower (sAd d) 2 * normPower (sAd (GeneralLinearGroup.det A)) (-1) =
      ((|((d⁻¹ : ℚˣ).val • A.val).det| : ℚ) : ℂ) := by
  have hdet : ((GeneralLinearGroup.det A : ℚˣ) : ℚ) = A.val.det := rfl
  have hd := adeleNorm_sAd h1 h2
  have hA := adeleNorm_sAd (q := GeneralLinearGroup.det A) (by rw [hdet]; exact h3)
    (by rw [hdet]; exact h4)
  have hd0 : (0 : ℝ) < |((d : ℚ) : ℝ)|⁻¹ := by
    have : ((d : ℚ) : ℝ) ≠ 0 := by exact_mod_cast d.ne_zero
    positivity
  have hA0 : (0 : ℝ) < |(((GeneralLinearGroup.det A : ℚˣ) : ℚ) : ℝ)|⁻¹ := by
    have : (((GeneralLinearGroup.det A : ℚˣ) : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast (GeneralLinearGroup.det A).ne_zero
    positivity
  rw [np_real_two hd0 hd, np_real_neg_one hA0 hA, ← Complex.ofReal_mul,
    ← Complex.ofReal_ratCast]
  congr 1
  rw [Matrix.det_smul, hdet]
  simp only [Fintype.card_fin]
  push_cast
  rw [abs_mul, abs_pow, abs_inv, inv_inv, inv_pow]

theorem ratLineWeight_eq (D : InducingData n) (A : GeneralLinearGroup (Fin 2) ℚ) (d : ℚˣ)
    (h1 : Int3 (d : ℚ)) (h2 : Int3 (d : ℚ)⁻¹) (h3 : Int3 A.val.det) (h4 : Int3 (A.val.det)⁻¹) :
    ratLineWeight D A d =
      ratPlaneWeight D A d * ((|((d⁻¹ : ℚˣ).val • A.val).det| : ℚ) : ℂ) := by
  have hBo : Bo A ∈ awayGroup placeThree := glAway2_mem _
  have hpw : planeWeight D (sAd d) (transposeGL (Bo A)) = ratPlaneWeight D A d := by
    rw [← Bo_transpose]
    show ratPlaneWeight D (transposeGL A) d = _
    exact ratPlaneWeight_transpose D A d
  rw [ratLineWeight, lineWeight_eq D _ hBo, det_atFinite_Bo, delta_eq h1 h2 h3 h4, hpw]

/-! ### Iwasawa decompositions with positive scalar -/

theorem planeLevi_neg_split (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    planeLevi B s = planeLevi B (-s) * planeLevi 1 (-1) := by
  have := (planeLeviHom ℚ).map_mul (B, -s) (1, -1)
  simp only [Prod.mk_mul_mk, mul_one, neg_mul_neg] at this
  exact this

theorem lineLevi_neg_split (d : ℚˣ) (A : GeneralLinearGroup (Fin 2) ℚ) :
    lineLevi d A = lineLevi (-d) A * lineLevi (-1) 1 := by
  have := (lineLeviHom ℚ).map_mul (-d, A) (-1, 1)
  simp only [Prod.mk_mul_mk, mul_one, neg_mul_neg] at this
  exact this

theorem planeLevi_neg_one_int :
    planeLevi (1 : GeneralLinearGroup (Fin 2) ℚ) (-1) =
      integralRational (planeLevi (1 : GeneralLinearGroup (Fin 2) ℤ) (-1)) := by
  rw [integralRational, planeLevi_map, map_one]
  congr 1

theorem lineLevi_neg_one_int :
    lineLevi (-1 : ℚˣ) (1 : GeneralLinearGroup (Fin 2) ℚ) =
      integralRational (lineLevi (-1 : ℤˣ) (1 : GeneralLinearGroup (Fin 2) ℤ)) := by
  rw [integralRational, lineLevi_map, map_one]
  congr 1

theorem plane_iwasawa_pos (x : RationalGL3) :
    ∃ v : ℚ × ℚ, ∃ B : GeneralLinearGroup (Fin 2) ℚ, ∃ s : ℚˣ, ∃ γ₀ : IntegralGL,
      0 < (s : ℚ) ∧ x = pU v * planeLevi B s * integralRational γ₀ := by
  obtain ⟨v, B, s, _, ⟨γ₀, rfl⟩, hx⟩ := plane_iwasawa x
  rcases lt_or_gt_of_ne (Units.ne_zero s) with hs | hs
  · refine ⟨v, B, -s, planeLevi 1 (-1) * γ₀, ?_, ?_⟩
    · rw [Units.val_neg]; linarith
    · rw [hx, planeLevi_neg_split B s, planeLevi_neg_one_int, map_mul]
      group
  · exact ⟨v, B, s, γ₀, hs, hx⟩

theorem line_iwasawa_pos (x : RationalGL3) :
    ∃ w : ℚ × ℚ, ∃ d : ℚˣ, ∃ A : GeneralLinearGroup (Fin 2) ℚ, ∃ γ₀ : IntegralGL,
      0 < (d : ℚ) ∧ x = lU w * lineLevi d A * integralRational γ₀ := by
  obtain ⟨w, d, A, _, ⟨γ₀, rfl⟩, hx⟩ := line_iwasawa x
  rcases lt_or_gt_of_ne (Units.ne_zero d) with hd | hd
  · refine ⟨w, -d, A, lineLevi (-1) 1 * γ₀, ?_, ?_⟩
    · rw [Units.val_neg]; linarith
    · rw [hx, lineLevi_neg_split d A, lineLevi_neg_one_int, map_mul]
      group
  · exact ⟨w, d, A, γ₀, hd, hx⟩

/-! ### The comparison -/

theorem out_class (m : MP) : ∃ h ∈ ΓM0, (QuotientGroup.mk m : MP ⧸ ΓM0).out = m * h :=
  ⟨m⁻¹ * (QuotientGroup.mk m : MP ⧸ ΓM0).out,
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk m : MP ⧸ ΓM0)).symm,
    by group⟩

theorem filter_empty_of_neg [DecidableEq (MP ⧸ ΓM0)] {R : Finset RationalGL3} (mR : RationalGL3 → MP)
    (hpos : ∀ r ∈ R, 0 < ((mR r).2 : ℚ)) (m : MP) (hm : ¬ 0 < (m.2 : ℚ)) :
    R.filter (fun r => (QuotientGroup.mk (mR r) : MP ⧸ ΓM0) = QuotientGroup.mk m) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro r hr hcr
  have h := QuotientGroup.eq.mp hcr
  obtain ⟨_, h2⟩ := Subgroup.mem_prod.mp h
  rw [Subgroup.mem_bot, Prod.snd_mul, Prod.snd_inv, inv_mul_eq_one] at h2
  exact hm (h2 ▸ hpos r hr)

open Classical in
/-- **The Satake comparison.** -/
theorem satake_sum (D : InducingData n) {t : HeckeCorrespondence} (ht : AwayThree t)
    (vP : RationalGL3 → ℚ × ℚ) (BP : RationalGL3 → GeneralLinearGroup (Fin 2) ℚ)
    (sP : RationalGL3 → ℚˣ) (γP : RationalGL3 → IntegralGL)
    (hP : ∀ r ∈ t.representatives,
      r = pU (vP r) * planeLevi (BP r) (sP r) * integralRational (γP r))
    (hsP : ∀ r ∈ t.representatives, 0 < (sP r : ℚ))
    (wL : RationalGL3 → ℚ × ℚ) (dL : RationalGL3 → ℚˣ)
    (AL : RationalGL3 → GeneralLinearGroup (Fin 2) ℚ) (γL : RationalGL3 → IntegralGL)
    (hL : ∀ r ∈ t.representatives,
      r = lU (wL r) * lineLevi (dL r) (AL r) * integralRational (γL r))
    (hdL : ∀ r ∈ t.representatives, 0 < (dL r : ℚ)) :
    ∑ r ∈ t.representatives, ratPlaneWeight D (BP r) (sP r) =
      ∑ r ∈ t.representatives, ratLineWeight D (AL r) (dL r) := by
  have hRS := repSet ht
  have hDl : ∀ γ ∈ Γ, ∀ x ∈ DZ t.g, γ * x ∈ DZ t.g := fun γ hγ x hx => DZ_left hx hγ
  have hDr : ∀ x ∈ DZ t.g, ∀ γ ∈ Γ, x * γ ∈ DZ t.g := fun x hx γ hγ => DZ_right hx hγ
  have wP : ∀ m : MP, ratPlaneWeight D (QuotientGroup.mk m : MP ⧸ ΓM0).out.1
      (QuotientGroup.mk m : MP ⧸ ΓM0).out.2 = ratPlaneWeight D m.1 m.2 := by
    intro m
    obtain ⟨h, hh, he⟩ := out_class m
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hh
    rw [Subgroup.mem_bot] at h2
    rw [he, Prod.fst_mul, Prod.snd_mul, h2, mul_one, ratPlaneWeight_mul D _ _ h1]
  have wL' : ∀ m : MP, ratLineWeight D (QuotientGroup.mk m : MP ⧸ ΓM0).out.1
      (QuotientGroup.mk m : MP ⧸ ΓM0).out.2 = ratLineWeight D m.1 m.2 := by
    intro m
    obtain ⟨h, hh, he⟩ := out_class m
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hh
    rw [Subgroup.mem_bot] at h2
    rw [he, Prod.fst_mul, Prod.snd_mul, h2, mul_one, ratLineWeight_mul D _ _ h1]
  have hdecP : ∀ r ∈ t.representatives, 0 < (((BP r, sP r) : MP).2 : ℚ) ∧
      r⁻¹ * (planeData.U (vP r) * planeData.L (BP r, sP r)) ∈ Γ := by
    intro r hr
    refine ⟨hsP r hr, ?_⟩
    change r⁻¹ * (pU (vP r) * planeLevi (BP r) (sP r)) ∈ Γ
    have : pU (vP r) * planeLevi (BP r) (sP r) = r * (integralRational (γP r))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact (hP r hr).symm
    rw [this, inv_mul_cancel_left]
    exact Γ.inv_mem ⟨_, rfl⟩
  have hdecL : ∀ r ∈ t.representatives, 0 < (((AL r, dL r) : MP).2 : ℚ) ∧
      r⁻¹ * (lineData.U (wL r) * lineData.L (AL r, dL r)) ∈ Γ := by
    intro r hr
    refine ⟨hdL r hr, ?_⟩
    change r⁻¹ * (lU (wL r) * lineLevi (dL r) (AL r)) ∈ Γ
    have : lU (wL r) * lineLevi (dL r) (AL r) = r * (integralRational (γL r))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact (hL r hr).symm
    rw [this, inv_mul_cancel_left]
    exact Γ.inv_mem ⟨_, rfl⟩
  rw [sum_by_class t.representatives (fun r => (QuotientGroup.mk (BP r, sP r) : MP ⧸ ΓM0))
      (fun r => ratPlaneWeight D (BP r) (sP r)) (fun c => ratPlaneWeight D c.out.1 c.out.2)
      (fun r _ => (wP (BP r, sP r)).symm),
    sum_by_class t.representatives (fun r => (QuotientGroup.mk (AL r, dL r) : MP ⧸ ΓM0))
      (fun r => ratLineWeight D (AL r) (dL r)) (fun c => ratLineWeight D c.out.1 c.out.2)
      (fun r _ => (wL' (AL r, dL r)).symm)]
  refine finsum_congr fun c => ?_
  obtain ⟨⟨B, s⟩, rfl⟩ := QuotientGroup.mk_surjective c
  rw [wP (B, s), wL' (B, s)]
  dsimp only
  by_cases hpos : 0 < (s : ℚ)
  · have fP := planeData.fiber_card hRS ΓM0 ΓM0_le (fun m : MP => 0 < (m.2 : ℚ)) pos_class
      vP (fun r => (BP r, sP r)) hdecP (B, s) hpos
    have fL := lineData.fiber_card hRS ΓM0 ΓM0_le (fun m : MP => 0 < (m.2 : ℚ)) pos_class
      wL (fun r => (AL r, dL r)) hdecL (B, s) hpos
    rw [fP, fL, line_count ht B s, NL_transpose hDl hDr]
    have hC := plane_count hDl hDr B s
    by_cases hN : planeData.NL (DZ t.g) (B, s) = 0
    · have h0 : ((QuotientAddGroup.mk : ℚ × ℚ → (ℚ × ℚ) ⧸ planeData.latt (B, s)) ''
          planeData.S (DZ t.g) (B, s)).ncard = 0 := by
        have : ((((QuotientAddGroup.mk : ℚ × ℚ → (ℚ × ℚ) ⧸ planeData.latt (B, s)) ''
            planeData.S (DZ t.g) (B, s)).ncard : ℕ) : ℚ) = 0 := by
          rw [hC, hN, Nat.cast_zero, mul_zero]
        exact_mod_cast this
      simp only [h0, hN, Nat.cast_zero, zero_mul]
    · have hne : (planeData.S (DZ t.g) (B, s)).Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        apply hN
        simp only [ParabolicData.NL, hemp, Set.image_empty, Set.ncard_empty]
      obtain ⟨v, hv⟩ := hne
      obtain ⟨i1, i2, i3, i4⟩ := plane_int3 ht (v := v) (A := B) (d := s) hv
      rw [ratLineWeight_eq D B s i1 i2 i3 i4]
      have hC' := congrArg (fun q : ℚ => (q : ℂ)) hC
      simp only [Rat.cast_natCast, Rat.cast_mul] at hC'
      rw [hC']
      ring
  · rw [filter_empty_of_neg (fun r => (BP r, sP r)) hsP (B, s) hpos,
      filter_empty_of_neg (fun r => (AL r, dL r)) hdL (B, s) hpos]
    simp

/-- **Plane and line eigenvalues agree.** -/
theorem plane_line_scalar (D : InducingData n) (t : HeckeCorrespondence) (ht : AwayThree t) :
    ∃ μ : ℂ,
      (∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
        ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) = μ * f g) ∧
      (∀ f : AdelicGL → ℂ, IsInduced D .line cohomologicalPoint f → ∀ g : AdelicGL,
        ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) = μ * f g) := by
  choose vP BP sP γP hsP hP using plane_iwasawa_pos
  choose wL dL AL γL hdL hL using line_iwasawa_pos
  refine ⟨∑ r ∈ t.representatives, ratPlaneWeight D (BP r) (sP r),
    plane_rational_formula D t ht vP BP sP γP (fun r _ => hP r), ?_⟩
  rw [satake_sum D ht vP BP sP γP (fun r _ => hP r) (fun r _ => hsP r) wL dL AL γL
    (fun r _ => hL r) (fun r _ => hdL r)]
  exact line_rational_formula D t ht wL dL AL γL (fun r _ => hL r)

/-- **`SingleCharacter`** for every associate pair and every actual boundary Hecke action. -/
theorem singleCharacter (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    SpectralSeparation.SingleCharacter (awayThreeHeckeAlgebra D hecke) (associatePair D) := by
  apply singleCharacter_of_common_scalar D hecke
  intro t ht
  obtain ⟨μ, hP, hL⟩ := plane_line_scalar D t ht
  exact common_scalar_of_eq D hecke t μ μ
    (summand_scalar_of_source D .plane t hecke hhecke μ (source_scalar_of_function t μ hP))
    (summand_scalar_of_source D .line t hecke hhecke μ (source_scalar_of_function t μ hL))
    (fun _ _ => rfl)

end TernaryPeriodPolynomials.HeckeEigen.Satake
