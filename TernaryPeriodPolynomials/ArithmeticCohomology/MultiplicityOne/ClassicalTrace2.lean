module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.ClassicalTrace

@[expose] public section


/-!
# Unfolding the Petersson product of `Γ₁(3)` against restriction and Atkin-Lehner

For even weight `k`:

* `petThree k (restrictThree k f) g = ∫_𝒟 ⟨f, Tr g⟩` (`petThree_restrict`), by splitting the
  fundamental domain `𝒟₃ = ⋃ rᵢ 𝒟` of `Γ₁(3)` into the four translates;
* `⟨g ∣ W, h⟩ = ⟨g, h ∣ W⟩` on `S_k(Γ₁(3))` (`petThree_atkinLehner_left`), since `W` normalizes
  `Γ₁(3)` and `W² = -3` is scalar;
* hence `petThree k (levelOneToThree k f) g = ∫_𝒟 ⟨f, Tr (g ∣ W)⟩` (`petThree_levelOneToThree`).

Original work by AxiomCode.
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory
open scoped ModularForm MatrixGroups Pointwise Manifold

namespace TernaryPeriodPolynomials.MultiplicityOne.Classical

open TernaryPeriodPolynomials.Spectral.PeterssonDomain
  (psl psl_smul psl_eq_iff modularImage fd_isFundamentalDomain setIntegral_smul_set
    isFundamentalDomain_conj)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum
  (levelThree mapGL_mem_levelThree)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonDomain
  (rep rep_unique fdThree fdThree_isFundamentalDomain imageThree imageThree_eq)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonForm (petThree)
open TernaryPeriodPolynomials.LevelThree.LevelThreeAtkinLehnerEmbed
  (levelOneToThree)

/-! ### Unfolding over the four translates of `𝒟` -/

theorem psl_rep_injective : Function.Injective fun i => psl (rep i) := by
  intro i j h
  have h' : psl (rep i) = psl (rep j) := h
  have hj : (((rep j * (rep j)⁻¹) 1 0 : ℤ) : ZMod 3) = 0 := by simp
  refine rep_unique (rep j)⁻¹ i j ?_ hj
  rcases (psl_eq_iff _ _).mp h' with h1 | h1
  · rw [h1]
    exact hj
  · rw [h1, neg_mul, mul_inv_cancel]
    simp

theorem pairwise_aedisjoint_rep :
    Pairwise (Function.onFun (AEDisjoint volume) fun i => psl (rep i) • ModularGroup.fd) := by
  intro i j hij
  have hne : (⟨psl (rep i), rep i, rfl⟩ : modularImage) ≠ ⟨psl (rep j), rep j, rfl⟩ := by
    intro h
    exact hij (psl_rep_injective (congrArg Subtype.val h))
  have h := fd_isFundamentalDomain.aedisjoint hne
  simp only [Function.onFun] at h ⊢
  rwa [Spectral.PeterssonHecke.subgroup_smul_set,
    Spectral.PeterssonHecke.subgroup_smul_set] at h

/-- **Unfolding**: `∫_𝒟 ∑ᵢ Φ(rᵢ τ) = ∫_{𝒟₃} Φ`. -/
theorem integral_rep_sum {Φ : ℍ → ℂ} (hc : Continuous Φ) (hb : ∃ C, ∀ τ, ‖Φ τ‖ ≤ C) :
    ∫ τ in ModularGroup.fd, ∑ i : Option (Fin 3), Φ (rep i • τ) = ∫ τ in fdThree, Φ τ := by
  obtain ⟨C, hC⟩ := hb
  have hint : ∀ i : Option (Fin 3),
      IntegrableOn (fun τ => Φ (rep i • τ)) ModularGroup.fd volume := by
    intro i
    apply Spectral.PeterssonHecke.integrableOn_fd
      (hc.comp (continuous_const_smul (SpecialLinearGroup.mapGL ℝ (rep i))))
    exact ⟨C, fun τ => hC _⟩
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have h1 : ∀ i : Option (Fin 3), ∫ τ in ModularGroup.fd, Φ (rep i • τ) =
      ∫ τ in psl (rep i) • ModularGroup.fd, Φ τ := by
    intro i
    rw [setIntegral_smul_set]
    simp only [psl_smul]
  simp_rw [h1]
  have hU : IntegrableOn Φ fdThree volume :=
    Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hC)
  rw [fdThree, integral_iUnion_ae (fun i => fd_isFundamentalDomain.nullMeasurableSet.smul _)
    pairwise_aedisjoint_rep hU, tsum_fintype]

theorem petersson_trace {k : ℤ} (hk : Even k) (f : CuspForm levelOne k)
    (g : CuspForm levelThree k) (τ : ℍ) :
    petersson k ⇑f ⇑(traceThree k hk g) τ =
      ∑ i : Option (Fin 3), petersson k ⇑f ⇑g (rep i • τ) := by
  rw [coe_traceThree, Spectral.PeterssonHecke.petersson_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Spectral.PeterssonHecke.petersson_mapGL k (⇑f) (⇑g) (rep i) τ
  rw [Spectral.PeterssonHecke.slash_levelOne k f (rep i)] at h
  exact h

/-- **Unfolding of the Petersson product against the inclusion**:
`⟨f, g⟩_{Γ₁(3)} = ∫_𝒟 ⟨f, Tr g⟩`. -/
theorem petThree_restrict {k : ℤ} (hk : Even k) (f : CuspForm levelOne k)
    (g : CuspForm levelThree k) :
    petThree k (restrictThree k f) g =
      ∫ τ in ModularGroup.fd, petersson k ⇑f ⇑(traceThree k hk g) τ := by
  have hc : Continuous (petersson k ⇑f ⇑g) :=
    petersson_continuous k (Spectral.PeterssonHecke.continuous_cuspForm k f)
      (LevelThree.LevelThreePeterssonForm.continuous_cuspForm k g)
  have hb : ∃ C, ∀ τ, ‖petersson k ⇑f ⇑g τ‖ ≤ C :=
    Spectral.PeterssonHecke.bounded_petersson k
      (Spectral.PeterssonHecke.pbounded_cuspForm k f)
      (LevelThree.LevelThreePeterssonForm.pbounded_cuspForm k g)
  have h1 := integral_rep_sum hc hb
  calc petThree k (restrictThree k f) g = ∫ τ in fdThree, petersson k ⇑f ⇑g τ := rfl
    _ = ∫ τ in ModularGroup.fd, ∑ i : Option (Fin 3), petersson k ⇑f ⇑g (rep i • τ) := h1.symm
    _ = ∫ τ in ModularGroup.fd, petersson k ⇑f ⇑(traceThree k hk g) τ := by
      congr 1
      funext τ
      exact (petersson_trace hk f g τ).symm

/-! ### The Atkin-Lehner involution is self-adjoint -/

/-- The image of `W` in `PGL(2, ℝ)`. -/
abbrev Wbar : PGL(2, ℝ) := ProjGenLinGroup.mk atkinLehnerMatrix

theorem Wbar_mul_self : Wbar * Wbar = 1 := by
  change ProjGenLinGroup.mk atkinLehnerMatrix * ProjGenLinGroup.mk atkinLehnerMatrix = 1
  rw [← map_mul, atkinLehnerMatrix_mul_self, ProjGenLinGroup.mk_scalar]

theorem Wbar_conj_mk {x : SL(2, ℤ)} (hx : x ∈ CongruenceSubgroup.Gamma1 3) :
    ∃ x' ∈ CongruenceSubgroup.Gamma1 3,
      MulAut.conj Wbar (ProjGenLinGroup.mk (SpecialLinearGroup.mapGL ℝ x)) =
        ProjGenLinGroup.mk (SpecialLinearGroup.mapGL ℝ x') := by
  obtain ⟨x', hx', h⟩ := exists_conjW hx
  refine ⟨x', hx', ?_⟩
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  change ProjGenLinGroup.mk atkinLehnerMatrix * ProjGenLinGroup.mk (SpecialLinearGroup.mapGL ℝ x) =
    ProjGenLinGroup.mk (SpecialLinearGroup.mapGL ℝ x') * ProjGenLinGroup.mk atkinLehnerMatrix
  rw [← map_mul, ← map_mul, h]

theorem conj_Wbar_mem {z : PGL(2, ℝ)} (hz : z ∈ imageThree) : MulAut.conj Wbar z ∈ imageThree := by
  rw [imageThree_eq] at hz ⊢
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨x', hx', h⟩ := Wbar_conj_mk hx
  exact ⟨x', hx', h.symm⟩

/-- **`W` normalizes the image of `Γ₁(3)` in `PGL(2, ℝ)`.** -/
theorem imageThree_map_Wbar : imageThree.map (MulAut.conj Wbar).toMonoidHom = imageThree := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact conj_Wbar_mem hz
  · intro z hz
    refine ⟨MulAut.conj Wbar z, conj_Wbar_mem hz, ?_⟩
    have hinv : Wbar⁻¹ = Wbar := inv_eq_of_mul_eq_one_right Wbar_mul_self
    change MulAut.conj Wbar (MulAut.conj Wbar z) = z
    simp only [MulAut.conj_apply, hinv]
    have e : Wbar * (Wbar * z * Wbar) * Wbar = (Wbar * Wbar) * z * (Wbar * Wbar) := by
      simp only [mul_assoc]
    rw [e, Wbar_mul_self, one_mul, mul_one]

theorem isFundamentalDomain_Wbar_smul_fdThree :
    IsFundamentalDomain imageThree (Wbar • fdThree) volume := by
  have := isFundamentalDomain_conj imageThree fdThree_isFundamentalDomain Wbar
  rwa [imageThree_map_Wbar] at this

theorem petersson_atkinLehner {k : ℤ} (hk : Even k) (F G : ℍ → ℂ) (τ : ℍ) :
    petersson k (F ∣[k] atkinLehnerMatrix) G τ =
      petersson k F (G ∣[k] atkinLehnerMatrix) (atkinLehnerMatrix • τ) := by
  have h := UpperHalfPlane.petersson_slash k F (G ∣[k] atkinLehnerMatrix) atkinLehnerMatrix τ
  have hdet := atkinLehnerMatrix_det
  have hpos : 0 < ((GeneralLinearGroup.det atkinLehnerMatrix : ℝˣ) : ℝ) := by
    rw [hdet]
    norm_num
  rw [Spectral.PeterssonHecke.sigma_of_det_pos _ hpos, hdet,
    slash_atkinLehnerMatrix_sq, Spectral.PeterssonHecke.petersson_smul_right] at h
  have habs : ((|(3 : ℝ)| : ℝ) : ℂ) = ((3 : ℝ) : ℂ) := by
    rw [abs_of_nonneg (by norm_num)]
  have hneg : ((-3 : ℝ) : ℂ) ^ (k - 2) = ((3 : ℝ) : ℂ) ^ (k - 2) := by
    rw [Complex.ofReal_neg]
    exact (hk.sub even_two).neg_zpow _
  have hT : ((3 : ℝ) : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (by norm_num)
  rw [hneg, habs] at h
  exact mul_left_cancel₀ hT h

theorem integral_atkinLehner_left {k : ℤ} (hk : Even k) (h g : CuspForm levelThree k) :
    ∫ τ in fdThree, petersson k (⇑h ∣[k] atkinLehnerMatrix) ⇑g τ =
      ∫ τ in fdThree, petersson k ⇑h (⇑g ∣[k] atkinLehnerMatrix) τ := by
  have hinv : ∀ (x : imageThree) (τ : ℍ),
      petersson k ⇑h (⇑g ∣[k] atkinLehnerMatrix) (x • τ) =
        petersson k ⇑h (⇑g ∣[k] atkinLehnerMatrix) τ := by
    intro x τ
    have hx : (x : PGL(2, ℝ)) ∈ (CongruenceSubgroup.Gamma1 3).map psl := by
      rw [← imageThree_eq]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    change petersson k ⇑h (⇑g ∣[k] atkinLehnerMatrix) ((x : PGL(2, ℝ)) • τ) = _
    rw [← hyx, psl_smul]
    have h1 : ⇑h ∣[k] SpecialLinearGroup.mapGL ℝ y = ⇑h :=
      SlashInvariantFormClass.slash_action_eq h _ (mapGL_mem_levelThree hy)
    have h3 := Spectral.PeterssonHecke.petersson_mapGL k ⇑h
      (⇑g ∣[k] atkinLehnerMatrix) y τ
    rw [h1, atkinLehnerFun_slash g y hy] at h3
    exact h3.symm
  symm
  rw [fdThree_isFundamentalDomain.setIntegral_eq isFundamentalDomain_Wbar_smul_fdThree hinv,
    setIntegral_smul_set]
  congr 1
  funext τ
  rw [pglMk_smul]
  exact (petersson_atkinLehner hk _ _ τ).symm

/-- **`W` is self-adjoint for the Petersson product of `Γ₁(3)`** (even weight). -/
theorem petThree_atkinLehner_left {k : ℤ} (hk : Even k) (h g : CuspForm levelThree k) :
    petThree k (atkinLehnerThree k h) g = petThree k h (atkinLehnerThree k g) :=
  integral_atkinLehner_left hk h g

/-- **Unfolding of the Petersson product against the embedding `f ↦ f(3τ)`**:
`⟨f(3·), g⟩_{Γ₁(3)} = ∫_𝒟 ⟨f, Tr (g ∣ W)⟩`. -/
theorem petThree_levelOneToThree {k : ℤ} (hk : Even k) (f : CuspForm levelOne k)
    (g : CuspForm levelThree k) :
    petThree k (levelOneToThree k f) g =
      ∫ τ in ModularGroup.fd, petersson k ⇑f ⇑(traceThree k hk (atkinLehnerThree k g)) τ := by
  rw [← atkinLehnerThree_restrictThree, petThree_atkinLehner_left hk, petThree_restrict hk]

end TernaryPeriodPolynomials.MultiplicityOne.Classical
