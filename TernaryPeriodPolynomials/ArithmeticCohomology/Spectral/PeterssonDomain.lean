module

public import Mathlib

@[expose] public section


/-!
# The modular fundamental domain as a measure-theoretic fundamental domain

`PGL(2,ℝ)` acts faithfully on the upper half-plane and preserves the hyperbolic measure. The image
`modularImage` of `SL₂(ℤ)` in `PGL(2,ℝ)` (that is, `PSL₂(ℤ)`) is countable, and the standard closed
fundamental domain `𝒟 = ModularGroup.fd` is a fundamental domain for it in the sense of
`MeasureTheory.IsFundamentalDomain` (`fd_isFundamentalDomain`): the translates of `𝒟` cover `ℍ`, and
two distinct translates meet only on the boundary arcs `|z| = 1`, `|Re z| = 1/2`, which are null.
Moreover `𝒟` has finite hyperbolic volume (`volume_fd_lt_top`).

Two generic facts about fundamental domains are added: a fundamental domain of a subgroup of finite
index is the union of the translates of a fundamental domain of the group by coset representatives
(`isFundamentalDomain_subgroup`), and translating a fundamental domain by `α` gives one of the
conjugate subgroup (`isFundamentalDomain_conj`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory
open scoped MatrixGroups Pointwise

namespace TernaryPeriodPolynomials.Spectral.PeterssonDomain

/-! ### The action of `PGL(2,ℝ)` -/

theorem measurable_glSmul (g : GL (Fin 2) ℝ) : Measurable fun z : ℍ => g • z :=
  (continuous_const_smul g).measurable

instance : MeasurableConstSMul PGL(2, ℝ) ℍ where
  measurable_const_smul h := by
    obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective h
    have : (fun z : ℍ => ProjGenLinGroup.mk g • z) = fun z => g • z := by
      funext z
      exact pglMk_smul g z
    rw [this]
    exact measurable_glSmul g

instance : SMulInvariantMeasure PGL(2, ℝ) ℍ volume where
  measure_preimage_smul h s hs := by
    obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective h
    have : (fun z : ℍ => ProjGenLinGroup.mk g • z) = fun z => g • z := by
      funext z
      exact pglMk_smul g z
    rw [this]
    exact SMulInvariantMeasure.measure_preimage_smul g hs

/-- `SL₂(ℤ) → PGL(2,ℝ)`. -/
def psl : SL(2, ℤ) →* PGL(2, ℝ) :=
  ProjGenLinGroup.mk.comp (SpecialLinearGroup.mapGL ℝ)

theorem psl_smul (γ : SL(2, ℤ)) (z : ℍ) : psl γ • z = γ • z := by
  change ProjGenLinGroup.mk (SpecialLinearGroup.mapGL ℝ γ) • z = _
  rw [pglMk_smul]
  rfl

theorem countable_SL : Countable SL(2, ℤ) := by
  have : Function.Injective (fun g : SL(2, ℤ) => fun i j : Fin 2 => g i j) := by
    intro a b h
    apply Subtype.ext
    ext i j
    exact congrFun (congrFun h i) j
  exact this.countable

/-- The image of `SL₂(ℤ)` in `PGL(2,ℝ)`. -/
abbrev modularImage : Subgroup PGL(2, ℝ) := psl.range

instance countable_map (K : Subgroup SL(2, ℤ)) : Countable (K.map psl) := by
  have := countable_SL
  have hc : (Set.range fun k : K => psl k.val).Countable := Set.countable_range _
  apply Set.Countable.to_subtype
  convert hc using 1
  ext x
  simp

instance countable_range : Countable modularImage := by
  have := countable_SL
  exact Set.Countable.to_subtype (Set.countable_range _)

/-- The point `2i`, in the interior of the fundamental domain. -/
def twoI : ℍ := ⟨2 * Complex.I, by simp⟩

theorem twoI_mem_fdo : twoI ∈ ModularGroup.fdo := by
  constructor
  · change 1 < Complex.normSq (2 * Complex.I)
    rw [Complex.normSq_mul, Complex.normSq_I]
    norm_num [Complex.normSq_ofNat]
  · change |(2 * Complex.I).re| < 1 / 2
    simp

theorem psl_eq_iff_smul (γ δ : SL(2, ℤ)) : psl γ = psl δ ↔ ∀ z : ℍ, γ • z = δ • z := by
  constructor
  · intro h z
    rw [← psl_smul, ← psl_smul, h]
  · intro h
    apply eq_of_smul_eq_smul (α := ℍ)
    intro z
    rw [psl_smul, psl_smul, h]

theorem psl_eq_iff (γ δ : SL(2, ℤ)) : psl γ = psl δ ↔ γ = δ ∨ γ = -δ := by
  rw [psl_eq_iff_smul]
  constructor
  · intro h
    have hfix : (δ⁻¹ * γ) • twoI = twoI := by
      rw [mul_smul, h, inv_smul_smul]
    have hmem : (δ⁻¹ * γ) • twoI ∈ ModularGroup.fd := by
      rw [hfix]
      exact ModularGroup.fdo_subset_fd twoI_mem_fdo
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd twoI_mem_fdo hmem with h1 | h1
    · left
      rw [← mul_inv_cancel_left δ γ, h1, mul_one]
    · right
      rw [← mul_inv_cancel_left δ γ, h1, mul_neg_one]
  · rintro (rfl | rfl) z
    · rfl
    · exact ModularGroup.SL_neg_smul _ _

theorem psl_neg (γ : SL(2, ℤ)) : psl (-γ) = psl γ := (psl_eq_iff _ _).mpr (Or.inr rfl)

/-! ### Null boundary and the fundamental domain -/

theorem volume_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have hpre : {z : ℂ | z.re = c} = Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ Set.univ) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem volume_normSq_eq_one : volume {z : ℂ | Complex.normSq z = 1} = 0 := by
  have hsub : {z : ℂ | Complex.normSq z = 1} ⊆ Metric.sphere (0 : ℂ) 1 := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    simp only [mem_sphere_iff_norm, sub_zero]
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    nlinarith [norm_nonneg z]
  exact measure_mono_null hsub (Measure.addHaar_sphere volume 0 1)

/-- The boundary arcs of `𝒟`. -/
def boundaryArcs : Set ℍ := {z | Complex.normSq (z : ℂ) = 1} ∪ {z | |z.re| = 1 / 2}

theorem volume_coe_boundaryArcs : volume (UpperHalfPlane.coe '' boundaryArcs) = 0 := by
  apply measure_mono_null (t := {z : ℂ | Complex.normSq z = 1} ∪ ({z : ℂ | z.re = 1 / 2} ∪
    {z : ℂ | z.re = -(1 / 2)}))
  · rintro _ ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact Or.inl hz
    · right
      have : (z : ℂ).re = 1 / 2 ∨ (z : ℂ).re = -(1 / 2) := abs_eq (by norm_num) |>.mp hz
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr h
  · exact measure_union_null volume_normSq_eq_one
      (measure_union_null (volume_re_eq _) (volume_re_eq _))

theorem volume_boundaryArcs : volume boundaryArcs = 0 := by
  rw [volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ volume_coe_boundaryArcs

theorem fd_diff_fdo_subset : ModularGroup.fd \ ModularGroup.fdo ⊆ boundaryArcs := by
  rintro z ⟨⟨h1, h2⟩, hno⟩
  by_contra hb
  apply hno
  simp only [boundaryArcs, Set.mem_union, Set.mem_ofPred_eq, not_or] at hb
  exact ⟨lt_of_le_of_ne h1 (Ne.symm hb.1), lt_of_le_of_ne h2 hb.2⟩

theorem smul_def' (h : modularImage) (z : ℍ) : h • z = h.val • z := rfl

theorem fd_inter_smul_null (γ : SL(2, ℤ)) (hγ : psl γ ≠ 1) :
    volume (ModularGroup.fd ∩ psl γ • ModularGroup.fd) = 0 := by
  apply measure_mono_null _ volume_boundaryArcs
  intro w ⟨hw, hγw⟩
  apply fd_diff_fdo_subset
  refine ⟨hw, fun hwo => hγ ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← map_inv, psl_smul] at hγw
  rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hwo hγw with h | h
  · rw [inv_eq_one] at h
    rw [h, map_one]
  · have : γ = -1 := by
      rw [← inv_inv γ, h]
      simp
    rw [this, psl_neg, map_one]

/-- **`𝒟` is a fundamental domain for `PSL₂(ℤ)`.** -/
theorem fd_isFundamentalDomain : IsFundamentalDomain modularImage ModularGroup.fd volume where
  nullMeasurableSet := ModularGroup.isClosed_fd.measurableSet.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun z => by
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    refine ⟨⟨psl g, g, rfl⟩, ?_⟩
    rw [smul_def', psl_smul]
    exact hg
  aedisjoint := by
    intro h h' hne
    change volume (h • ModularGroup.fd ∩ h' • ModularGroup.fd) = 0
    obtain ⟨γ, hγ⟩ := (h⁻¹ * h').property
    have hne' : psl γ ≠ 1 := by
      rw [hγ]
      intro h1
      apply hne
      have := h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      exact Subtype.ext (inv_mul_eq_one.mp this)
    have hset : h • ModularGroup.fd ∩ h' • ModularGroup.fd =
        h • (ModularGroup.fd ∩ (h⁻¹ * h') • ModularGroup.fd) := by
      rw [Set.smul_set_inter, mul_smul, smul_inv_smul]
    rw [hset, measure_smul]
    have : (h⁻¹ * h') • ModularGroup.fd = psl γ • ModularGroup.fd := by
      ext z
      simp only [Set.mem_smul_set, smul_def', hγ]
    rw [this]
    exact fd_inter_smul_null γ hne'

/-! ### Finite volume -/

theorem coe_fd_subset : UpperHalfPlane.coe '' ModularGroup.fd ⊆
    Complex.measurableEquivRealProd ⁻¹' (Set.Icc (-(1 / 2)) (1 / 2) ×ˢ Set.Ici (1 / 2)) := by
  rintro _ ⟨z, hz, rfl⟩
  have him := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hre := hz.2
  simp only [Set.mem_preimage, Complex.measurableEquivRealProd, Set.mem_prod, Set.mem_Icc,
    Set.mem_Ici]
  refine ⟨abs_le.mp hre, ?_⟩
  change 1 / 2 ≤ z.im
  nlinarith [z.im_pos]

theorem lintegral_inv_sq_lt_top :
    ∫⁻ y in Set.Ici (1 / 2 : ℝ), (((1 / ‖y‖₊) ^ 2 : NNReal) : ENNReal) < ⊤ := by
  rw [setLIntegral_congr Ioi_ae_eq_Ici.symm]
  have hint := integrableOn_Ioi_rpow_of_lt (a := -2) (c := 1 / 2) (by norm_num) (by norm_num)
  have hlt := hint.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) hlt
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  change (((1 / ‖y‖₊) ^ 2 : NNReal) : ENNReal) = ENNReal.ofReal (y ^ (-2 : ℝ))
  rw [ENNReal.ofReal_eq_coe_nnreal (Real.rpow_nonneg hy0.le _)]
  congr 1
  apply NNReal.eq
  simp only [one_div, NNReal.coe_pow, NNReal.coe_inv, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos hy0, NNReal.coe_mk]
  rw [Real.rpow_neg hy0.le, Real.rpow_two, inv_pow]

/-- **`𝒟` has finite hyperbolic volume.** -/
theorem volume_fd_lt_top : volume ModularGroup.fd < ⊤ := by
  rw [volume_eq_lintegral]
  let G : ℝ × ℝ → ENNReal := fun q => (((1 / ‖q.2‖₊) ^ 2 : NNReal) : ENNReal)
  have hG : ∀ z : ℂ, (((1 / ‖z.im‖₊) ^ 2 : NNReal) : ENNReal) = G (Complex.measurableEquivRealProd z) :=
    fun z => rfl
  simp_rw [hG]
  calc ∫⁻ z in UpperHalfPlane.coe '' ModularGroup.fd, G (Complex.measurableEquivRealProd z)
      ≤ ∫⁻ z in Complex.measurableEquivRealProd ⁻¹' (Set.Icc (-(1 / 2)) (1 / 2) ×ˢ Set.Ici (1 / 2)),
          G (Complex.measurableEquivRealProd z) := lintegral_mono_set coe_fd_subset
    _ = ∫⁻ q in Set.Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.Ici (1 / 2), G q :=
        Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
          Complex.measurableEquivRealProd.measurableEmbedding G _
    _ = (∫⁻ x in Set.Icc (-(1 / 2) : ℝ) (1 / 2), 1) *
          ∫⁻ y in Set.Ici (1 / 2 : ℝ), (((1 / ‖y‖₊) ^ 2 : NNReal) : ENNReal) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← lintegral_prod_mul aemeasurable_const]
        · simp only [one_mul]
          rfl
        · exact (by fun_prop : Measurable fun y : ℝ => (((1 / ‖y‖₊) ^ 2 : NNReal) : ENNReal)).aemeasurable
    _ < ⊤ := by
        apply ENNReal.mul_lt_top
        · simp
        · exact lintegral_inv_sq_lt_top

instance : IsFiniteMeasure (volume.restrict ModularGroup.fd) :=
  isFiniteMeasure_restrict.mpr volume_fd_lt_top.ne

/-! ### Generic facts on fundamental domains -/

section Generic

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α}
  [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]

/-- **Fundamental domains of subgroups.** If `K = ⊔ᵢ gᵢ⁻¹ H` (uniquely) for subgroups `H ≤ K`, the
union of the translates `gᵢ • s` of a fundamental domain `s` of `K` is a fundamental domain of `H`. -/
theorem isFundamentalDomain_subgroup {K H : Subgroup G} {s : Set α}
    (hs : IsFundamentalDomain K s μ) (hHK : H ≤ K)
    {ι : Type*} [Countable ι] (g : ι → G) (hg : ∀ i, g i ∈ K)
    (hdecomp : ∀ x ∈ K, ∃ i, ∃ h ∈ H, x = (g i)⁻¹ * h)
    (hunique : ∀ i j (h h' : G), h ∈ H → h' ∈ H → (g i)⁻¹ * h = (g j)⁻¹ * h' → h = h') :
    IsFundamentalDomain H (⋃ i, g i • s) μ where
  nullMeasurableSet := NullMeasurableSet.iUnion fun i => by
    have : NullMeasurableSet s μ := hs.nullMeasurableSet
    exact this.smul (g i)
  ae_covers := by
    filter_upwards [hs.ae_covers] with x hx
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨i, h, hH, hx'eq⟩ := hdecomp x' x'.property
    refine ⟨⟨h, hH⟩, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.mk_smul, smul_smul, ← hx'eq]
    exact hx'
  aedisjoint := by
    intro a b hab
    change AEDisjoint μ ((a : G) • ⋃ i, g i • s) ((b : G) • ⋃ j, g j • s)
    rw [Set.smul_set_iUnion, Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff]
    intro i
    rw [AEDisjoint.iUnion_right_iff]
    intro j
    rw [smul_smul, smul_smul]
    have hne : (⟨(a : G) * g i, K.mul_mem (hHK a.property) (hg i)⟩ : K) ≠
        ⟨(b : G) * g j, K.mul_mem (hHK b.property) (hg j)⟩ := by
      intro heq
      apply hab
      have heq' : (a : G) * g i = (b : G) * g j := congrArg Subtype.val heq
      have h1 : (g i)⁻¹ * (a : G)⁻¹ = (g j)⁻¹ * (b : G)⁻¹ := by
        rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, heq']
      have := hunique i j _ _ (H.inv_mem a.property) (H.inv_mem b.property) h1
      exact Subtype.ext (inv_injective this)
    exact hs.aedisjoint hne

/-- **Conjugate fundamental domains.** -/
theorem isFundamentalDomain_conj (H : Subgroup G) {s : Set α} (hs : IsFundamentalDomain H s μ)
    (a : G) : IsFundamentalDomain (H.map (MulAut.conj a).toMonoidHom) (a • s) μ where
  nullMeasurableSet := by
    have : NullMeasurableSet s μ := hs.nullMeasurableSet
    exact this.smul a
  ae_covers := by
    have hae := (measurePreserving_smul a⁻¹ μ).quasiMeasurePreserving.ae hs.ae_covers
    filter_upwards [hae] with x hx
    obtain ⟨h, hh⟩ := hx
    refine ⟨⟨a * h * a⁻¹, h, h.property, by simp [MulAut.conj_apply]⟩, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change a⁻¹ • ((a * h * a⁻¹) • x) ∈ s
    rw [Subgroup.smul_def, smul_smul] at hh
    rw [smul_smul]
    simpa only [mul_assoc, inv_mul_cancel_left] using hh
  aedisjoint := by
    intro x y hxy
    obtain ⟨h₁, hh₁, hx⟩ := x.property
    obtain ⟨h₂, hh₂, hy⟩ := y.property
    change μ ((x : G) • a • s ∩ (y : G) • a • s) = 0
    have hx' : (x : G) = a * h₁ * a⁻¹ := hx.symm
    have hy' : (y : G) = a * h₂ * a⁻¹ := hy.symm
    have hne : (⟨h₁, hh₁⟩ : H) ≠ ⟨h₂, hh₂⟩ := by
      intro heq
      apply hxy
      apply Subtype.ext
      rw [hx', hy']
      have := congrArg Subtype.val heq
      simp only at this
      rw [this]
    have hset : (x : G) • a • s ∩ (y : G) • a • s = a • (h₁ • s ∩ h₂ • s) := by
      rw [Set.smul_set_inter, hx', hy', smul_smul, smul_smul, smul_smul, smul_smul,
        inv_mul_cancel_right, inv_mul_cancel_right]
    rw [hset, measure_smul]
    exact hs.aedisjoint hne

theorem setIntegral_smul_set {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : G)
    (s : Set α) (f : α → E) : ∫ x in a • s, f x ∂μ = ∫ x in s, f (a • x) ∂μ := by
  have hemb : MeasurableEmbedding fun x : α => a • x := (MeasurableEquiv.smul a).measurableEmbedding
  have h := (measurePreserving_smul a μ).setIntegral_preimage_emb hemb f (a • s)
  rw [Set.preimage_smul, inv_smul_smul] at h
  exact h.symm

end Generic

end TernaryPeriodPolynomials.Spectral.PeterssonDomain
