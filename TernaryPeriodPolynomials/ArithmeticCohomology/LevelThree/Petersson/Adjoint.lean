module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PeterssonHecke

@[expose] public section


/-!
# Adjointness of double-coset operators for the Petersson product (abstract)

Let `Γ ≤ GL₂(ℝ)` be a countable group of determinant-one matrices injecting into `PGL(2,ℝ)`,
with a fundamental domain `s` of finite volume for its image. A *coset datum* (`CosetData`) is a
finite family `αᵢ` of matrices of positive determinant such that the right cosets `Γ αᵢ` are
distinct, permuted by right multiplication by `Γ`, and form a single orbit; i.e. they are the
right cosets of one double coset `Γ α Γ`.

Fix a base index `i₀` and choose `βᵢ ∈ Γ` with `Γ α_{i₀} βᵢ = Γ αᵢ`. Then the `βᵢ` represent the
right cosets of `Γ_{α} = Γ ∩ α_{i₀}⁻¹ Γ α_{i₀}` (`stab`) in `Γ`, `⋃ βᵢ s` is a fundamental
domain of `Γ_α` (`isFundamentalDomain_stab`), and the Petersson integral unfolds
(`unfold`): `∫_s ⟨∑ F ∣ αᵢ, G⟩ = ∫_t ⟨F ∣ α_{i₀}, G⟩` for every fundamental domain `t` of `Γ_α`.

If two representatives satisfy `α_{i₁} α_{i₀} = u · 1`, conjugation by `α_{i₀}` carries
`Γ_{α_{i₀}}` to `Γ_{α_{i₁}}` (`stab_conj`), and the change of variables `τ ↦ α_{i₀} τ` gives the
adjointness relation (`adjoint`)
`det(α_{i₀})^{k-2} ∫_s ⟨F, ∑ G ∣ αᵢ⟩ = u^{k-2} ∫_s ⟨∑ F ∣ αᵢ, G⟩`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory ComplexConjugate
open scoped MatrixGroups Pointwise ModularForm

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonAdjoint

open TernaryPeriodPolynomials.Spectral.PeterssonDomain
open TernaryPeriodPolynomials.Spectral.PeterssonHecke

/-! ### Elementary identities -/

theorem petersson_swap (k : ℤ) (F G : ℍ → ℂ) (τ : ℍ) :
    petersson k F G τ = conj (petersson k G F τ) := by
  simp only [petersson, map_mul, Complex.conj_conj, map_zpow₀, Complex.conj_ofReal]
  ring

theorem scalar_comm (u : ℝˣ) (g : GL (Fin 2) ℝ) :
    GeneralLinearGroup.scalar (Fin 2) u * g = g * GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  ext i j
  simp [GeneralLinearGroup.scalar, mul_comm]

/-! ### The subgroups `Γ ∩ a⁻¹ Γ a` -/

variable (Γ : Subgroup (GL (Fin 2) ℝ))

/-- `Γ_a = Γ ∩ a⁻¹ Γ a`. -/
def stab (a : GL (Fin 2) ℝ) : Subgroup (GL (Fin 2) ℝ) where
  carrier := {x | x ∈ Γ ∧ a * x * a⁻¹ ∈ Γ}
  one_mem' := ⟨Γ.one_mem, by simp [Γ.one_mem]⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨Γ.mul_mem hx hy, ?_⟩
    convert Γ.mul_mem hx' hy' using 1
    group
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨Γ.inv_mem hx, ?_⟩
    convert Γ.inv_mem hx' using 1
    group

theorem mem_stab {a x : GL (Fin 2) ℝ} : x ∈ stab Γ a ↔ x ∈ Γ ∧ a * x * a⁻¹ ∈ Γ := Iff.rfl

theorem stab_le (a : GL (Fin 2) ℝ) : stab Γ a ≤ Γ := fun _ hx => hx.1

theorem countable_map_of_le [Countable Γ] {H : Subgroup (GL (Fin 2) ℝ)} (hH : H ≤ Γ) :
    Countable (H.map ProjGenLinGroup.mk) := by
  have hΓ : (Γ : Set (GL (Fin 2) ℝ)).Countable := Set.countable_coe_iff.mp ‹_›
  apply Set.Countable.to_subtype
  apply (hΓ.image ProjGenLinGroup.mk).mono
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hH hx, rfl⟩

/-- **Conjugate stabilizers.** If `b a` is scalar, conjugation by `a` carries `Γ_a` onto `Γ_b`. -/
theorem stab_conj (a b : GL (Fin 2) ℝ) (u : ℝˣ)
    (hab : b * a = GeneralLinearGroup.scalar (Fin 2) u) :
    ((stab Γ a).map ProjGenLinGroup.mk).map (MulAut.conj (ProjGenLinGroup.mk a)).toMonoidHom =
      (stab Γ b).map ProjGenLinGroup.mk := by
  have hb : b = GeneralLinearGroup.scalar (Fin 2) u * a⁻¹ := eq_mul_inv_of_mul_eq hab
  have key : ∀ y : GL (Fin 2) ℝ, b * y * b⁻¹ = a⁻¹ * y * a := by
    intro y
    calc b * y * b⁻¹ = GeneralLinearGroup.scalar (Fin 2) u * (a⁻¹ * y * a) *
          (GeneralLinearGroup.scalar (Fin 2) u)⁻¹ := by rw [hb]; group
      _ = (a⁻¹ * y * a) * GeneralLinearGroup.scalar (Fin 2) u *
          (GeneralLinearGroup.scalar (Fin 2) u)⁻¹ := by rw [scalar_comm]
      _ = a⁻¹ * y * a := by group
  ext z
  constructor
  · rintro ⟨_, ⟨x, ⟨hx, hx'⟩, rfl⟩, rfl⟩
    refine ⟨a * x * a⁻¹, ⟨hx', ?_⟩, ?_⟩
    · rw [key]
      convert hx using 1
      group
    · simp [MulAut.conj_apply]
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    refine ⟨ProjGenLinGroup.mk (a⁻¹ * y * a), ⟨a⁻¹ * y * a, ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · rw [← key]
      exact hy'
    · convert hy using 1
      group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      group

/-! ### Coset data -/

/-- The right cosets `Γ αᵢ` of a double coset `Γ α Γ`. -/
structure CosetData (ι : Type*) [Fintype ι] where
  /-- The representatives. -/
  α : ι → GL (Fin 2) ℝ
  det_pos : ∀ i, 0 < ((α i).det : ℝ)
  /-- Right multiplication by `Γ` permutes the cosets. -/
  next : ∀ γ ∈ Γ, ∀ i, ∃ j, α i * γ * (α j)⁻¹ ∈ Γ
  /-- The cosets are distinct. -/
  disjoint : ∀ i j, α i * (α j)⁻¹ ∈ Γ → i = j
  /-- The cosets form one orbit. -/
  trans : ∀ i j, ∃ γ ∈ Γ, α i * γ * (α j)⁻¹ ∈ Γ

namespace CosetData

/-- Coset data from transitivity relative to a single base index `i₀`. -/
def ofBase {ι : Type*} [Fintype ι] (α : ι → GL (Fin 2) ℝ) (det_pos : ∀ i, 0 < ((α i).det : ℝ))
    (next : ∀ γ ∈ Γ, ∀ i, ∃ j, α i * γ * (α j)⁻¹ ∈ Γ)
    (disjoint : ∀ i j, α i * (α j)⁻¹ ∈ Γ → i = j) (i₀ : ι)
    (base : ∀ j, ∃ γ ∈ Γ, α i₀ * γ * (α j)⁻¹ ∈ Γ) : CosetData Γ ι where
  α := α
  det_pos := det_pos
  next := next
  disjoint := disjoint
  trans i j := by
    obtain ⟨γi, hγi, hi⟩ := base i
    obtain ⟨γj, hγj, hj⟩ := base j
    refine ⟨γi⁻¹ * γj, Γ.mul_mem (Γ.inv_mem hγi) hγj, ?_⟩
    have e : α i * (γi⁻¹ * γj) * (α j)⁻¹ =
        (α i₀ * γi * (α i)⁻¹)⁻¹ * (α i₀ * γj * (α j)⁻¹) := by group
    rw [e]
    exact Γ.mul_mem (Γ.inv_mem hi) hj

variable {Γ} {ι : Type*} [Fintype ι] (D : CosetData Γ ι)

/-- `βᵢ ∈ Γ` with `Γ α_{i₀} βᵢ = Γ αᵢ`. -/
def beta (i₀ i : ι) : GL (Fin 2) ℝ := (D.trans i₀ i).choose

theorem beta_mem (i₀ i : ι) : D.beta i₀ i ∈ Γ := (D.trans i₀ i).choose_spec.1

theorem beta_spec (i₀ i : ι) : D.α i₀ * D.beta i₀ i * (D.α i)⁻¹ ∈ Γ :=
  (D.trans i₀ i).choose_spec.2

/-- The `βᵢ` cover `Γ` modulo `Γ_{α_{i₀}}`. -/
theorem decomp (i₀ : ι) {x : GL (Fin 2) ℝ} (hx : x ∈ Γ) :
    ∃ i, x * (D.beta i₀ i)⁻¹ ∈ stab Γ (D.α i₀) := by
  obtain ⟨j, hj⟩ := D.next x hx i₀
  refine ⟨j, Γ.mul_mem hx (Γ.inv_mem (D.beta_mem i₀ j)), ?_⟩
  convert Γ.mul_mem hj (Γ.inv_mem (D.beta_spec i₀ j)) using 1
  group

/-- The `βᵢ` are distinct modulo `Γ_{α_{i₀}}`. -/
theorem unique (i₀ : ι) (i j : ι) (h : D.beta i₀ i * (D.beta i₀ j)⁻¹ ∈ stab Γ (D.α i₀)) :
    i = j := by
  apply D.disjoint
  have e : D.α i * (D.α j)⁻¹ = (D.α i₀ * D.beta i₀ i * (D.α i)⁻¹)⁻¹ *
      (D.α i₀ * (D.beta i₀ i * (D.beta i₀ j)⁻¹) * (D.α i₀)⁻¹) *
      (D.α i₀ * D.beta i₀ j * (D.α j)⁻¹) := by group
  rw [e]
  exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (D.beta_spec i₀ i)) h.2) (D.beta_spec i₀ j)

variable (k : ℤ)

theorem slash_alpha {F : ℍ → ℂ} (hF : ∀ γ ∈ Γ, F ∣[k] γ = F) (i₀ i : ι) :
    F ∣[k] D.α i = (F ∣[k] D.α i₀) ∣[k] D.beta i₀ i := by
  have h : D.α i = (D.α i₀ * D.beta i₀ i * (D.α i)⁻¹)⁻¹ * D.α i₀ * D.beta i₀ i := by group
  rw [h, SlashAction.slash_mul, SlashAction.slash_mul, hF _ (Γ.inv_mem (D.beta_spec i₀ i))]

end CosetData

/-! ### Unfolding -/

section Unfolding

variable {Γ} (k : ℤ) (hdet : ∀ γ ∈ Γ, ((γ.det : ℝˣ) : ℝ) = 1)
  (hinj : ∀ γ ∈ Γ, ProjGenLinGroup.mk γ = 1 → γ = 1)
  {s : Set ℍ} (hs : IsFundamentalDomain (Γ.map ProjGenLinGroup.mk) s volume)
  (hvol : volume s < ⊤)
  {ι : Type*} [Fintype ι] (D : CosetData Γ ι)

include hdet in
theorem petersson_slash_mem (F G : ℍ → ℂ) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ) (τ : ℍ) :
    petersson k (F ∣[k] γ) (G ∣[k] γ) τ = petersson k F G (γ • τ) := by
  have h1 := hdet γ hγ
  have hpos : 0 < ((γ.det : ℝˣ) : ℝ) := by rw [h1]; norm_num
  rw [petersson_slash, h1, sigma_of_det_pos γ hpos]
  simp

include hdet in
theorem petersson_sum_eq {F G : ℍ → ℂ} (hF : ∀ γ ∈ Γ, F ∣[k] γ = F)
    (hG : ∀ γ ∈ Γ, G ∣[k] γ = G) (i₀ : ι) (τ : ℍ) :
    petersson k (∑ i, F ∣[k] D.α i) G τ =
      ∑ i, petersson k (F ∣[k] D.α i₀) G (D.beta i₀ i • τ) := by
  rw [petersson_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D.slash_alpha k hF i₀ i, ← petersson_slash_mem k hdet _ _ (D.beta_mem i₀ i),
    hG _ (D.beta_mem i₀ i)]

include hinj hs in
/-- **`⋃ βᵢ s` is a fundamental domain of `Γ_{α_{i₀}}`.** -/
theorem isFundamentalDomain_stab (i₀ : ι) :
    IsFundamentalDomain ((stab Γ (D.α i₀)).map ProjGenLinGroup.mk)
      (⋃ i, ProjGenLinGroup.mk (D.beta i₀ i) • s) volume := by
  apply isFundamentalDomain_subgroup hs (Subgroup.map_mono (stab_le Γ _))
    (fun i => ProjGenLinGroup.mk (D.beta i₀ i)) (fun i => ⟨_, D.beta_mem i₀ i, rfl⟩)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := D.decomp i₀ (Γ.inv_mem hx)
    refine ⟨i, ProjGenLinGroup.mk (D.beta i₀ i * x), ⟨_, ?_, rfl⟩, ?_⟩
    · have := (stab Γ _).inv_mem hi
      rwa [_root_.mul_inv_rev, inv_inv, inv_inv] at this
    · rw [map_mul, inv_mul_cancel_left]
  · intro i j h h' hh hh' heq
    obtain ⟨y, hy, rfl⟩ := hh
    obtain ⟨y', hy', rfl⟩ := hh'
    have h1 : ProjGenLinGroup.mk (D.beta i₀ j * (D.beta i₀ i)⁻¹ * y * y'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc (ProjGenLinGroup.mk _), heq]
      group
    have hmem : D.beta i₀ j * (D.beta i₀ i)⁻¹ * y * y'⁻¹ ∈ Γ :=
      Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (D.beta_mem i₀ j) (Γ.inv_mem (D.beta_mem i₀ i)))
        (stab_le Γ _ hy)) (Γ.inv_mem (stab_le Γ _ hy'))
    have h2 := hinj _ hmem h1
    have h3 : D.beta i₀ j * (D.beta i₀ i)⁻¹ = y' * y⁻¹ := by
      rw [← mul_inv_eq_one, ← h2]
      group
    have hji := D.unique i₀ j i (by rw [h3]; exact (stab Γ _).mul_mem hy' ((stab Γ _).inv_mem hy))
    subst hji
    rw [mul_inv_cancel, eq_comm, mul_inv_eq_one] at h3
    rw [h3]

include hinj hs in
theorem pairwise_aedisjoint (i₀ : ι) :
    Pairwise (Function.onFun (AEDisjoint volume)
      fun i => ProjGenLinGroup.mk (D.beta i₀ i) • s) := by
  intro i j hij
  have hne : (⟨ProjGenLinGroup.mk (D.beta i₀ i), _, D.beta_mem i₀ i, rfl⟩ :
      Γ.map ProjGenLinGroup.mk) ≠ ⟨ProjGenLinGroup.mk (D.beta i₀ j), _, D.beta_mem i₀ j, rfl⟩ := by
    intro h
    apply hij
    have h' : ProjGenLinGroup.mk (D.beta i₀ i * (D.beta i₀ j)⁻¹) = 1 := by
      have hv : ProjGenLinGroup.mk (D.beta i₀ i) = ProjGenLinGroup.mk (D.beta i₀ j) :=
        congrArg Subtype.val h
      rw [map_mul, map_inv, hv, mul_inv_cancel]
    have h1 := hinj _ (Γ.mul_mem (D.beta_mem i₀ i) (Γ.inv_mem (D.beta_mem i₀ j))) h'
    exact D.unique i₀ i j (by rw [h1]; exact (stab Γ _).one_mem)
  have h := hs.aedisjoint hne
  simp only [Function.onFun] at h ⊢
  rwa [subgroup_smul_set, subgroup_smul_set] at h

include hinj hs hvol in
/-- **Unfolding the sum over the `βᵢ`.** -/
theorem integral_sum_beta (i₀ : ι) {Φ : ℍ → ℂ} (hc : Continuous Φ)
    (hb : ∃ C, ∀ τ, ‖Φ τ‖ ≤ C) :
    ∫ τ in s, ∑ i, Φ (D.beta i₀ i • τ) =
      ∫ τ in ⋃ i, ProjGenLinGroup.mk (D.beta i₀ i) • s, Φ τ := by
  obtain ⟨C, hC⟩ := hb
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hvol.ne
  have hint : ∀ i, IntegrableOn (fun τ => Φ (D.beta i₀ i • τ)) s volume := fun i =>
    Integrable.of_bound (hc.comp (continuous_const_smul (D.beta i₀ i))).aestronglyMeasurable C
      (ae_of_all _ fun τ => hC _)
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have h1 : ∀ i, ∫ τ in s, Φ (D.beta i₀ i • τ) =
      ∫ τ in ProjGenLinGroup.mk (D.beta i₀ i) • s, Φ τ := by
    intro i
    rw [setIntegral_smul_set]
    simp only [pglMk_smul]
  simp_rw [h1]
  have hvolU : volume (⋃ i, ProjGenLinGroup.mk (D.beta i₀ i) • s) < ⊤ := by
    calc volume (⋃ i, ProjGenLinGroup.mk (D.beta i₀ i) • s)
        ≤ ∑ i, volume (ProjGenLinGroup.mk (D.beta i₀ i) • s) := measure_iUnion_fintype_le _ _
      _ = ∑ _i : ι, volume s := by simp only [measure_smul]
      _ < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ => hvol
  have : IsFiniteMeasure (volume.restrict (⋃ i, ProjGenLinGroup.mk (D.beta i₀ i) • s)) :=
    isFiniteMeasure_restrict.mpr hvolU.ne
  have hU : IntegrableOn Φ (⋃ i, ProjGenLinGroup.mk (D.beta i₀ i) • s) volume :=
    Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hC)
  have hnull : NullMeasurableSet s volume := hs.nullMeasurableSet
  rw [integral_iUnion_ae (fun i => hnull.smul _) (pairwise_aedisjoint hinj hs D i₀) hU,
    tsum_fintype]

variable [Countable Γ]

include hdet hinj hs hvol in
/-- **Unfolding**: `∫_s ⟨∑ F ∣ αᵢ, G⟩ = ∫_t ⟨F ∣ α_{i₀}, G⟩` for any fundamental domain `t` of
`Γ_{α_{i₀}}`. -/
theorem unfold {F G : ℍ → ℂ} (hF : ∀ γ ∈ Γ, F ∣[k] γ = F) (hG : ∀ γ ∈ Γ, G ∣[k] γ = G)
    (hFc : ∀ g : GL (Fin 2) ℝ, Continuous (F ∣[k] g)) (hGc : Continuous G)
    (hFb : PBounded k F) (hGb : PBounded k G) (i₀ : ι) {t : Set ℍ}
    (ht : IsFundamentalDomain ((stab Γ (D.α i₀)).map ProjGenLinGroup.mk) t volume) :
    ∫ τ in s, petersson k (∑ i, F ∣[k] D.α i) G τ =
      ∫ τ in t, petersson k (F ∣[k] D.α i₀) G τ := by
  have := countable_map_of_le Γ (stab_le Γ (D.α i₀))
  simp_rw [petersson_sum_eq k hdet D hF hG i₀]
  rw [integral_sum_beta hinj hs hvol D i₀ (petersson_continuous k (hFc _) hGc)
    (bounded_petersson k (pbounded_slash k hFb _) hGb)]
  apply (isFundamentalDomain_stab hinj hs D i₀).setIntegral_eq ht
  rintro ⟨_, y, ⟨hy, hy'⟩, rfl⟩ x
  change petersson k (F ∣[k] D.α i₀) G (ProjGenLinGroup.mk y • x) = _
  rw [pglMk_smul, ← petersson_slash_mem k hdet _ _ hy, hG _ hy, ← SlashAction.slash_mul]
  have e : D.α i₀ * y = (D.α i₀ * y * (D.α i₀)⁻¹) * D.α i₀ := by group
  rw [e, SlashAction.slash_mul, hF _ hy']

/-! ### Adjointness -/

include hdet hinj hs hvol in
/-- **Adjointness of a double-coset operator.** If `α_{i₁} α_{i₀} = u · 1`, then
`det(α_{i₀})^{k-2} ⟨F, ∑ G ∣ αᵢ⟩ = u^{k-2} ⟨∑ F ∣ αᵢ, G⟩`, the products being integrals over
the fundamental domain `s` of `Γ`. -/
theorem adjoint {F G : ℍ → ℂ} (hF : ∀ γ ∈ Γ, F ∣[k] γ = F) (hG : ∀ γ ∈ Γ, G ∣[k] γ = G)
    (hFc : ∀ g : GL (Fin 2) ℝ, Continuous (F ∣[k] g))
    (hGc : ∀ g : GL (Fin 2) ℝ, Continuous (G ∣[k] g))
    (hFb : PBounded k F) (hGb : PBounded k G) (i₀ i₁ : ι) (u : ℝˣ)
    (hu : D.α i₁ * D.α i₀ = GeneralLinearGroup.scalar (Fin 2) u) :
    ((((D.α i₀).det : ℝˣ) : ℝ) : ℂ) ^ (k - 2) * ∫ τ in s, petersson k F (∑ i, G ∣[k] D.α i) τ =
      ((u : ℝ) : ℂ) ^ (k - 2) * ∫ τ in s, petersson k (∑ i, F ∣[k] D.α i) G τ := by
  have hF1 : Continuous F := by simpa using hFc 1
  have hG1 : Continuous G := by simpa using hGc 1
  have ht₀ := isFundamentalDomain_stab hinj hs D i₀
  have ht₁ : IsFundamentalDomain ((stab Γ (D.α i₁)).map ProjGenLinGroup.mk)
      (ProjGenLinGroup.mk (D.α i₀) • ⋃ i, ProjGenLinGroup.mk (D.beta i₀ i) • s) volume := by
    have := isFundamentalDomain_conj _ ht₀ (ProjGenLinGroup.mk (D.α i₀))
    rwa [stab_conj Γ _ _ u hu] at this
  have hL := unfold k hdet hinj hs hvol D hF hG hFc hG1 hFb hGb i₀ ht₀
  have hR := unfold k hdet hinj hs hvol D hG hF hGc hF1 hGb hFb i₁ ht₁
  have hR' : ∫ τ in s, petersson k F (∑ i, G ∣[k] D.α i) τ =
      ∫ τ in ProjGenLinGroup.mk (D.α i₀) • ⋃ i, ProjGenLinGroup.mk (D.beta i₀ i) • s,
        petersson k F (G ∣[k] D.α i₁) τ := by
    simp_rw [petersson_swap k F]
    rw [integral_conj, integral_conj, hR]
  rw [hL, hR', setIntegral_smul_set, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext σ
  have h := petersson_slash k F (G ∣[k] D.α i₁) (D.α i₀) σ
  rw [sigma_of_det_pos _ (D.det_pos i₀), ← SlashAction.slash_mul, hu, slash_scalar,
    petersson_smul_right, abs_of_pos (D.det_pos i₀)] at h
  rw [pglMk_smul, ← h]

end Unfolding

end TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonAdjoint
