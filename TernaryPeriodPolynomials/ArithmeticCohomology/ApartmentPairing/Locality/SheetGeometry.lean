module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Geometry
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperFinite
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Basic

@[expose] public section


/-!
# Lemma 3.3, G3: the diagonal flat and the translates of a small box

For the finite-index congruence subgroup `Γ = principalSix` of `GL₃(ℤ)` acting on the symmetric space
`Space` of trace-one positive definite forms, `sheet_geometry` shows that a small closed coordinate
box `boxC ρ ρ` around the identity form `p0` is disjoint from all its nontrivial `Γ`-translates, and
that every nontrivial translate of it is disjoint from the whole diagonal flat `flat`.

The proof has three ingredients.  A diagonal image `g • S` of a form `S` in a compact set has all
diagonal entries bounded below (`diag_entry_lower`): the integral change of basis `g⁻¹` has a nonzero
integral column, and `S ≤ 1` for trace-one forms (`quad_le_dot`), so each pivot of `g S gᵀ` is at most
one, while `det S` is bounded below on the compact set.  Hence the translates meeting the flat form
a finite set (`finite_flat_transporter`), using properness of the arithmetic action.  Finally the
level six congruence subgroup moves the identity form off the flat unless it is trivial
(`eq_one_of_smul_p0_mem_flat`), and the finitely many remaining translates are separated by
continuity.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open Matrix TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceArithmeticProper
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

theorem quad_le_trace_mul (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosSemidef) (x : Fin 3 → ℝ) :
    x ⬝ᵥ (S *ᵥ x) ≤ S.trace * (x ⬝ᵥ x) := by
  obtain ⟨U, lam, hUU, hspec, htr, hev⟩ : ∃ (U : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ),
      U * Uᵀ = 1 ∧ S = U * diagonal lam * Uᵀ ∧ S.trace = ∑ i, lam i ∧ ∀ i, 0 ≤ lam i := by
    have hH := hS.1
    refine ⟨(hH.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ), hH.eigenvalues, ?_, ?_, ?_, ?_⟩
    · have := Unitary.mul_star_self_of_mem (hH.eigenvectorUnitary).2
      simpa [Matrix.star_eq_conjTranspose] using this
    · have h := hH.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at h
      simpa [Matrix.star_eq_conjTranspose] using h
    · have := hH.trace_eq_sum_eigenvalues
      simpa using this
    · exact fun i => hS.eigenvalues_nonneg i
  set y : Fin 3 → ℝ := x ᵥ* U with hy
  have h1 : x ⬝ᵥ (S *ᵥ x) = ∑ i, lam i * y i ^ 2 := by
    rw [hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.mulVec_transpose]
    simp [Matrix.mulVec_diagonal, dotProduct, ← hy, pow_two]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : x ⬝ᵥ x = ∑ i, y i ^ 2 := by
    have : x ⬝ᵥ x = x ⬝ᵥ ((U * Uᵀ) *ᵥ x) := by rw [hUU]; simp
    rw [this, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, ← hy]
    simp [dotProduct, pow_two]
  have hle : ∀ i, lam i ≤ ∑ j, lam j := fun i =>
    Finset.single_le_sum (fun j _ => hev j) (Finset.mem_univ i)
  rw [h1, h2, htr, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    have := hle i
    nlinarith [sq_nonneg (y i)]

theorem quad_le_dot (S : Space) (x : Fin 3 → ℝ) : x ⬝ᵥ (S.val *ᵥ x) ≤ x ⬝ᵥ x := by
  have := quad_le_trace_mul S.val S.property.1.posSemidef x
  rwa [S.property.2, one_mul] at this

theorem sq_sa_le (S : Space) (x : Fin 3 → ℝ) :
    (S.val *ᵥ x) ⬝ᵥ (S.val *ᵥ x) ≤ x ⬝ᵥ (S.val *ᵥ x) := by
  have hsym : S.val.transpose = S.val := S.property.1.1.eq
  have key : ∀ y, y = S.val *ᵥ x → y ⬝ᵥ y ≤ x ⬝ᵥ (S.val *ᵥ x) := by
    intro y hy
    have hxy : x ⬝ᵥ (S.val *ᵥ y) = y ⬝ᵥ y := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, ← hy]
    have hpos := S.property.1.posSemidef.dotProduct_mulVec_nonneg (x - y)
    have h2 := quad_le_dot S y
    simp only [star_trivial] at hpos
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hxy] at hpos
    have hyx : y ⬝ᵥ (S.val *ᵥ x) = y ⬝ᵥ y := by rw [← hy]
    rw [hyx] at hpos
    linarith
  exact key _ rfl

theorem one_le_sq_col (g : IntegralGL) (i : Fin 3) :
    1 ≤ ∑ j, ((realIntegral g⁻¹).val j i) ^ 2 := by
  have h1 : (g.val * (g⁻¹).val) i i = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]; simp
  rw [Matrix.mul_apply] at h1
  obtain ⟨j, hj⟩ : ∃ j, (g⁻¹).val j i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    simp [hcon] at h1
  have hz : (1 : ℝ) ≤ (((g⁻¹).val j i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ ((g⁻¹).val j i) ^ 2 := by
      have := Int.one_le_abs hj
      nlinarith [sq_abs ((g⁻¹).val j i)]
    exact_mod_cast this
  calc (1:ℝ) ≤ _ := hz
    _ ≤ _ := Finset.single_le_sum (f := fun j => ((realIntegral g⁻¹).val j i) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ j)

theorem conj_diag_le_one (g : IntegralGL) (S : Space)
    (hd : ∀ a b, a ≠ b → (act (realIntegral g) S).val a b = 0) (i : Fin 3) :
    conjugate (realIntegral g) S.val i i ≤ 1 := by
  set G := (realIntegral g).val with hG
  set H := (realIntegral g⁻¹).val with hH
  set M := conjugate (realIntegral g) S.val with hM
  have hHG : H * G = 1 := by
    rw [hH, hG, ← Units.val_mul, map_inv, inv_mul_cancel]; rfl
  have hMd : ∀ a b, a ≠ b → M a b = 0 := by
    intro a b hab
    rw [hM, conjugate_eq_scale_smul g S]
    simp [hd a b hab]
  have hSG : S.val * star G = H * M := by
    rw [hM, conjugate]
    rw [← hG, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hHG, Matrix.one_mul]
  have hcol : S.val *ᵥ (G i) = fun j => H j i * M i i := by
    funext j
    have := congrFun (congrFun hSG j) i
    rw [Matrix.mul_apply, Matrix.mul_apply] at this
    have hR : ∑ k, H j k * M k i = H j i * M i i :=
      Finset.sum_eq_single i (fun k _ hk => by rw [hMd k i hk, mul_zero]) (by simp)
    rw [hR] at this
    rw [← this]
    simp [Matrix.mulVec, dotProduct, Matrix.star_apply]
  have hm : M i i = (G i) ⬝ᵥ (S.val *ᵥ (G i)) := (row_quadratic g S i).symm
  have hpos : 0 < M i i := (conjugate_positive (realIntegral g) S.val S.property.1).diag_pos
  have hy : (S.val *ᵥ (G i)) ⬝ᵥ (S.val *ᵥ (G i)) = (M i i) ^ 2 * ∑ j, (H j i) ^ 2 := by
    rw [hcol]
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 := sq_sa_le S (G i)
  rw [← hm, hy] at h3
  have h4 := one_le_sq_col g i
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos hpos hpos]

theorem diag_entry_lower {δ : ℝ} (g : IntegralGL) (S : Space) (hδ : δ ≤ S.val.det)
    (hd : ∀ a b, a ≠ b → (act (realIntegral g) S).val a b = 0) (i : Fin 3) :
    δ / 27 ≤ (act (realIntegral g) S).val i i := by
  set T := act (realIntegral g) S with hT
  have hdet := normalized_determinant g S
  rw [← hT] at hdet
  have hs : scale g S ≤ 3 := by
    have : scale g S = ∑ k, conjugate (realIntegral g) S.val k k := rfl
    rw [this]
    have := fun k => conj_diag_le_one g S hd k
    simp only [Fin.sum_univ_three]
    linarith [this 0, this 1, this 2]
  have hs0 := scale_pos g S
  have hTdet : T.val.det = T.val 0 0 * T.val 1 1 * T.val 2 2 := by
    rw [Matrix.det_fin_three]
    simp [hd 0 1 (by decide), hd 0 2 (by decide), hd 1 0 (by decide), hd 1 2 (by decide),
      hd 2 0 (by decide), hd 2 1 (by decide)]
  have hp : ∀ k, 0 < T.val k k := fun k => T.property.1.diag_pos
  have hl : ∀ k, T.val k k ≤ 1 := fun k => diagonal_le_one T k
  have hs3 : scale g S ^ 3 ≤ 27 := by
    calc scale g S ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ hs0.le hs 3
      _ = 27 := by norm_num
  have hdetle : T.val.det ≤ T.val i i := by
    rw [hTdet]
    have := hp 0; have := hp 1; have := hp 2
    have := hl 0; have := hl 1; have := hl 2
    fin_cases i <;> simp <;> nlinarith [mul_pos (hp 0) (hp 1), mul_pos (hp 1) (hp 2), mul_pos (hp 0) (hp 2)]
  have hdp : 0 < T.val.det := T.property.1.det_pos
  calc δ / 27 ≤ S.val.det / 27 := by linarith
    _ = scale g S ^ 3 * T.val.det / 27 := by rw [hdet]
    _ ≤ 27 * T.val.det / 27 := by gcongr
    _ ≤ _ := by linarith

theorem exists_compact_diag (δ : ℝ) (hδ : 0 < δ) : ∃ K' : Set Space, IsCompact K' ∧
    ∀ T : Space, (∀ a b, a ≠ b → T.val a b = 0) → (∀ i, δ ≤ T.val i i) → T ∈ K' := by
  let P : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc δ 1) ∩ {d | ∑ i, d i = 1}
  have hP : IsCompact P :=
    (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  have hmem : ∀ d : P, (Matrix.diagonal (d.1)).PosDef ∧ (Matrix.diagonal (d.1)).trace = 1 := by
    intro d
    refine ⟨?_, ?_⟩
    · rw [Matrix.posDef_diagonal_iff]
      intro i
      exact lt_of_lt_of_le hδ (d.2.1 i (Set.mem_univ i)).1
    · simpa [Matrix.trace_diagonal] using d.2.2
  let f : P → Space := fun d => ⟨Matrix.diagonal d.1, hmem d⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact (Continuous.matrix_diagonal continuous_subtype_val)
  have : CompactSpace P := isCompact_iff_compactSpace.mp hP
  refine ⟨Set.range f, isCompact_range hf, ?_⟩
  intro T hoff hge
  have hd : T.val = Matrix.diagonal (fun i => T.val i i) := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · rw [hoff a b h]; simp [h]
  have hPmem : (fun i => T.val i i) ∈ P := by
    refine ⟨fun i _ => ⟨hge i, diagonal_le_one T i⟩, ?_⟩
    have := T.property.2
    simpa [Matrix.trace] using this
  exact ⟨⟨_, hPmem⟩, Subtype.ext hd.symm⟩

theorem prod_one_aux (a b c : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (h : a * b * c = 1) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  have hab : 1 ≤ a * b := by nlinarith
  have hbc : 1 ≤ b * c := by nlinarith
  have hac : 1 ≤ a * c := by nlinarith
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- An integral matrix congruent to `1` modulo six, of determinant one, whose rows are pairwise
orthogonal is the identity. -/
theorem int_gram_diag_eq_one (A : Matrix (Fin 3) (Fin 3) ℤ) (hdet : A.det = 1)
    (hmod : ∀ i j, (6 : ℤ) ∣ A i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j)
    (hoff : ∀ a b, a ≠ b → (A * Aᵀ) a b = 0) : A = 1 := by
  have hd : (A * Aᵀ).det = 1 := by rw [Matrix.det_mul, Matrix.det_transpose, hdet]; norm_num
  rw [Matrix.det_fin_three] at hd
  simp only [hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide), hoff 1 2 (by decide),
    hoff 2 0 (by decide), hoff 2 1 (by decide)] at hd
  have hrow : ∀ i, (A * Aᵀ) i i = A i 0 ^ 2 + A i 1 ^ 2 + A i 2 ^ 2 := by
    intro i
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_two]
  have hd' : (A 0 0 ^ 2 + A 0 1 ^ 2 + A 0 2 ^ 2) * (A 1 0 ^ 2 + A 1 1 ^ 2 + A 1 2 ^ 2) *
      (A 2 0 ^ 2 + A 2 1 ^ 2 + A 2 2 ^ 2) = 1 := by
    rw [← hrow, ← hrow, ← hrow]; linarith
  have hm : ∀ i j, (6 : ℤ) ∣ A i j - if i = j then 1 else 0 := fun i j => by
    simpa [Matrix.one_apply] using hmod i j
  have hdiag : ∀ i, 1 ≤ A i i ^ 2 := by
    intro i
    have := hm i i
    simp only [ite_true] at this
    have hne : A i i ≠ 0 := by
      intro h; rw [h] at this; omega
    have := Int.one_le_abs hne
    nlinarith [sq_abs (A i i)]
  have h0 := hdiag 0
  have h1 := hdiag 1
  have h2 := hdiag 2
  obtain ⟨e0, e1, e2⟩ := prod_one_aux _ _ _ (by nlinarith [sq_nonneg (A 0 1), sq_nonneg (A 0 2)])
    (by nlinarith [sq_nonneg (A 1 0), sq_nonneg (A 1 2)])
    (by nlinarith [sq_nonneg (A 2 0), sq_nonneg (A 2 1)]) hd'
  have hr1 : ∀ i, A i 0 ^ 2 + A i 1 ^ 2 + A i 2 ^ 2 = 1 := by
    intro i; fin_cases i
    · exact e0
    · exact e1
    · exact e2
  have hsq : ∀ i j, A i j ^ 2 ≤ 1 := by
    intro i j
    have := hr1 i
    have a0 := sq_nonneg (A i 0)
    have a1 := sq_nonneg (A i 1)
    have a2 := sq_nonneg (A i 2)
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith
  ext i j
  have hb := hsq i j
  have hmij := hm i j
  have hb' : -1 ≤ A i j ∧ A i j ≤ 1 := by constructor <;> nlinarith
  by_cases hij : i = j
  · subst hij
    simp only [ite_true] at hmij
    simp only [Matrix.one_apply_eq]
    omega
  · simp only [hij, ite_false] at hmij
    simp only [Matrix.one_apply_ne hij]
    omega

theorem p0_val : p0.val = (3:ℝ)⁻¹ • (1 : Mat) := by
  unfold p0 coordHomeo
  simp only [Homeomorph.symm_trans_apply]
  show (SymmetricSpaceFlagCoordinates.ldlHomeomorph.symm (uHomeo.symm 0, tHomeo.symm 0)).val = _
  rw [SymmetricSpaceFlagCoordinates.ldlHomeomorph_symm]
  have h1 : (tHomeo.symm (0 : R2)).1.val = 1 := by
    simp [tHomeo]
  have h2 : (tHomeo.symm (0 : R2)).2.val = 1 := by
    simp [tHomeo]
  have h3 : (uHomeo.symm (0 : R3)) = 0 := by simp [uHomeo]
  simp only [h1, h2, h3, Pi.zero_apply]
  have hu : SymmetricSpaceFlagCoordinates.upper 0 0 0 = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [SymmetricSpaceFlagCoordinates.upper]
  have hf : SymmetricSpaceFlagCoordinates.flagMatrix 0 0 0 1 1 = 1 := by
    have hd : SymmetricSpaceFlagCoordinates.diagonal 1 1 = 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [SymmetricSpaceFlagCoordinates.diagonal]
    simp [SymmetricSpaceFlagCoordinates.flagMatrix, hu, hd]
  rw [hf, SymmetricSpacePositive.normalize]
  simp

theorem flat_offdiag {S : Space} (h : S ∈ flat) : ∀ i j, i ≠ j → S.val i j = 0 := by
  refine (unip_eq_zero_iff S).mp ?_
  have h' : piR3 S = 0 := h
  have := congrArg (EuclideanSpace.equiv (Fin 3) ℝ) h'
  simpa [piR3] using this

/-- A nontrivial element of the level six congruence subgroup moves the identity form off the flat. -/
theorem eq_one_of_smul_p0_mem_flat (g : IntegralGL)
    (hg : g ∈ TernaryPoly.IntegralGL3Congruence.principalSix)
    (h : act (realIntegral g) p0 ∈ flat) : g = 1 := by
  have hoff := flat_offdiag h
  have hM : conjugate (realIntegral g) p0.val = scale g p0 • (act (realIntegral g) p0).val :=
    conjugate_eq_scale_smul g p0
  have hG : ∀ a b, a ≠ b → (g.val * g.valᵀ) a b = 0 := by
    intro a b hab
    have h1 := congrFun (congrFun hM a) b
    rw [Matrix.smul_apply, hoff a b hab, smul_zero, p0_val] at h1
    have h2 : conjugate (realIntegral g) ((3:ℝ)⁻¹ • (1 : Mat)) =
        (3:ℝ)⁻¹ • ((realIntegral g).val * star (realIntegral g).val) := by
      rw [conjugate_smul]; simp [conjugate]
    rw [h2] at h1
    simp only [Matrix.smul_apply, smul_eq_mul, mul_eq_zero, inv_eq_zero] at h1
    have h3 : (((g.val * g.valᵀ) a b : ℤ) : ℝ) = 0 := by
      rcases h1 with h1 | h1
      · norm_num at h1
      · rw [← h1]
        simp [Matrix.mul_apply, Matrix.star_apply]
    exact_mod_cast h3
  have := int_gram_diag_eq_one g.val (TernaryPoly.IntegralGL3Congruence.principalSix_det_one g hg)
    (fun i j => (TernaryPoly.IntegralGL3Congruence.mem_principal_iff 6 g).mp hg i j) hG
  exact Units.ext this

/-- Only finitely many arithmetic translates of a compact set meet the diagonal flat. -/
theorem finite_flat_transporter (K : Set Space) (hK : IsCompact K) :
    {g : IntegralGL | ∃ S ∈ K, act (realIntegral g) S ∈ flat}.Finite := by
  obtain ⟨δ, hδ, hδK⟩ := compact_det_lower K hK
  obtain ⟨K', hK', hmem⟩ := exists_compact_diag (δ / 27) (by positivity)
  refine (compact_transporter_finite K K' hK hK').subset ?_
  rintro g ⟨S, hS, hf⟩
  refine ⟨S, hS, hmem _ (flat_offdiag hf) fun i => ?_⟩
  exact diag_entry_lower g S (hδK S hS) (flat_offdiag hf) i

theorem isClosed_flat : IsClosed flat :=
  isClosed_eq piR3.continuous continuous_const

theorem boxC_subset_nhds {N : Set Space} (hN : N ∈ nhds p0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → boxC ρ ρ ⊆ N := by
  have hcont : ContinuousAt coordHomeo.symm (0, 0) := coordHomeo.symm.continuous.continuousAt
  have h0 : coordHomeo.symm (0, 0) = p0 := rfl
  have hN' : coordHomeo.symm ⁻¹' N ∈ nhds ((0 : R3), (0 : R2)) := by
    apply hcont
    rw [h0]; exact hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN'
  refine ⟨ε / 2, by positivity, fun ρ hρ hρε S hS => ?_⟩
  have hmem : coordHomeo S ∈ Metric.ball ((0 : R3), (0 : R2)) ε := by
    rw [Metric.mem_ball, Prod.dist_eq]
    have h1 : dist (coordHomeo S).1 0 ≤ ρ := Metric.mem_closedBall.mp hS.1
    have h2 : dist (coordHomeo S).2 0 ≤ ρ := Metric.mem_closedBall.mp hS.2
    exact max_lt (by linarith) (by linarith)
  have := hball hmem
  simpa using this

open scoped Pointwise

theorem disjoint_smul_iff {g : TernaryPoly.IntegralGL3Congruence.principalSix} {A B : Set Space} :
    Disjoint (g • A) B ↔ ∀ x ∈ A, act (realIntegral (g : IntegralGL)) x ∉ B := by
  rw [Set.disjoint_left]
  constructor
  · intro h x hx hxB
    exact h (Set.smul_mem_smul_set hx) hxB
  · rintro h _ ⟨x, hx, rfl⟩
    exact h x hx

/-- The local statement for one nontrivial element. -/
theorem sheet_local (g : TernaryPoly.IntegralGL3Congruence.principalSix) (hg : g ≠ 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
      Disjoint (g • boxC ρ ρ) (boxC ρ ρ) ∧ Disjoint (g • boxC ρ ρ) flat := by
  have hg1 : (g : IntegralGL) ≠ 1 := fun h => hg (Subtype.ext h)
  have hnf : act (realIntegral (g : IntegralGL)) p0 ∉ flat := fun h =>
    hg1 (eq_one_of_smul_p0_mem_flat g g.2 h)
  have hne : act (realIntegral (g : IntegralGL)) p0 ≠ p0 := fun h =>
    hnf (by rw [h]; exact p0_mem_flat)
  obtain ⟨U, V, hU, hV, hp, hgp, hUV⟩ := t2_separation hne.symm
  have hcont : Continuous (act (realIntegral (g : IntegralGL))) := continuous_act _
  have hN : (U ∩ (act (realIntegral (g : IntegralGL))) ⁻¹' (V ∩ flatᶜ)) ∈ nhds p0 :=
    (hU.inter ((hV.inter isClosed_flat.isOpen_compl).preimage hcont)).mem_nhds ⟨hp, ⟨hgp, hnf⟩⟩
  obtain ⟨r, hr, hsub⟩ := boxC_subset_nhds hN
  refine ⟨r, hr, fun ρ hρ hρr => ⟨?_, ?_⟩⟩
  · rw [disjoint_smul_iff]
    intro x hx hxB
    have h1 := hsub ρ hρ hρr hx
    have h2 := hsub ρ hρ hρr hxB
    exact Set.disjoint_left.mp hUV h2.1 h1.2.1
  · rw [disjoint_smul_iff]
    intro x hx hxB
    exact (hsub ρ hρ hρr hx).2.2 hxB

/-- **Sheet geometry.**  For small `ρ`, the closed coordinate cube `boxC ρ ρ` around the identity
form is disjoint from its nontrivial translates under the level six congruence subgroup, and every
nontrivial translate of it is disjoint from the diagonal flat. -/
theorem sheet_geometry : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    (∀ g : TernaryPoly.IntegralGL3Congruence.principalSix, g ≠ 1 →
        Disjoint (g • boxC ρ ρ) (boxC ρ ρ)) ∧
    (∀ g : TernaryPoly.IntegralGL3Congruence.principalSix, g ≠ 1 →
        Disjoint (g • boxC ρ ρ) flat) := by
  have hK : IsCompact (boxC 1 1) := isCompact_boxC 1 1
  have hT1 := compact_transporter_finite (boxC 1 1) (boxC 1 1) hK hK
  have hT2 := finite_flat_transporter (boxC 1 1) hK
  let B : Set TernaryPoly.IntegralGL3Congruence.principalSix :=
    {g | g ≠ 1 ∧ ((g : IntegralGL) ∈ transporter (boxC 1 1) (boxC 1 1) ∨
      (g : IntegralGL) ∈ {g : IntegralGL | ∃ S ∈ boxC 1 1, act (realIntegral g) S ∈ flat})}
  have hB : B.Finite := by
    refine Set.Finite.subset ((hT1.union hT2).preimage (Subtype.val_injective.injOn)) ?_
    intro g hg
    exact hg.2
  have hev : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ g ∈ B,
      Disjoint (g • boxC ρ ρ) (boxC ρ ρ) ∧ Disjoint (g • boxC ρ ρ) flat := by
    rw [Filter.eventually_all_finite hB]
    intro g hg
    obtain ⟨r, hr, h⟩ := sheet_local g hg.1
    filter_upwards [Ioc_mem_nhdsGT hr] with ρ hρ using h ρ hρ.1 hρ.2
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨min u 1, lt_min hu (by norm_num), fun ρ hρ hρu => ?_⟩
  have hρ1 : ρ ≤ 1 := hρu.trans (min_le_right _ _)
  have hρu' : ρ ≤ u := hρu.trans (min_le_left _ _)
  have hsubK : boxC ρ ρ ⊆ boxC 1 1 := fun S hS =>
    ⟨Metric.closedBall_subset_closedBall hρ1 hS.1, Metric.closedBall_subset_closedBall hρ1 hS.2⟩
  have hgood : ∀ g : TernaryPoly.IntegralGL3Congruence.principalSix, g ≠ 1 →
      Disjoint (g • boxC ρ ρ) (boxC ρ ρ) ∧ Disjoint (g • boxC ρ ρ) flat := by
    intro g hg
    by_cases hgB : g ∈ B
    · exact hsub ⟨hρ, hρu'⟩ g hgB
    · have hn : ¬ ((g : IntegralGL) ∈ transporter (boxC 1 1) (boxC 1 1) ∨
          (g : IntegralGL) ∈ {g : IntegralGL | ∃ S ∈ boxC 1 1, act (realIntegral g) S ∈ flat}) :=
        fun h => hgB ⟨hg, h⟩
      push Not at hn
      refine ⟨?_, ?_⟩
      · rw [disjoint_smul_iff]
        intro x hx hxB
        exact hn.1 ⟨x, hsubK hx, hsubK hxB⟩
      · rw [disjoint_smul_iff]
        intro x hx hxB
        exact hn.2 ⟨x, hsubK hx, hxB⟩
  exact ⟨fun g hg => (hgood g hg).1, fun g hg => (hgood g hg).2⟩

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
