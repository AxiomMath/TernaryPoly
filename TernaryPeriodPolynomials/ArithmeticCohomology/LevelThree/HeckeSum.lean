module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHecke
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeBasic

@[expose] public section


/-!
# Sums of slash translates as cusp forms for `Γ₁(3)`

Let `Γ = Γ₁(3) ⊆ SL₂(ℤ)`, viewed inside `GL₂(ℝ)` as the repository's `binaryRealGammaOneThree`.
A *coset family* is a finite family of rational matrices `α_i` of positive determinant which is
permuted by right multiplication by `Γ` modulo `Γ`: for `g ∈ Γ` there is a permutation `π` with
`α_{π i} g ∈ Γ α_i`. For such a family the sum `∑_i f ∣[k] α_i` of a cusp form `f` for `Γ` is again
a cusp form for `Γ` (`CosetFamily.sumOp`, a `ℂ`-linear endomorphism of `S_k(Γ₁(3))`): slash
invariance by reindexing along `π`, holomorphy termwise, and vanishing at every cusp because the
cusps of the arithmetic group `Γ` are stable under rational matrices.

This is the common construction of the Hecke operators `T_p` (`p ≠ 3`) and `U_3` at level three.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups Manifold
open Matrix UpperHalfPlane
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum

open TernaryPeriodPolynomials

/-- `Γ₁(3)` as a subgroup of `GL₂(ℝ)` (the repository's `binaryRealGammaOneThree`). -/
abbrev levelThree : Subgroup (GL (Fin 2) ℝ) := binaryRealGammaOneThree

theorem levelThree_eq :
    levelThree = ((CongruenceSubgroup.Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  rfl

theorem mapGL_mem_levelThree {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma1 3) :
    SpecialLinearGroup.mapGL ℝ g ∈ levelThree :=
  ⟨g, hg, rfl⟩

/-- The translation `τ ↦ τ + 1` lies in `Γ₁(3)`, so `q = e^{2πiτ}` is a local parameter at `∞`. -/
theorem one_mem_strictPeriods : (1 : ℝ) ∈ levelThree.strictPeriods := by
  rw [levelThree_eq, Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem gammaOneThree_T_mem]
  exact AddSubgroup.mem_zmultiples 1

/-- The real matrix of a rational matrix. -/
abbrev real (a : GL (Fin 2) ℚ) : GL (Fin 2) ℝ := a.map (Rat.castHom ℝ)

theorem real_det (a : GL (Fin 2) ℚ) :
    ((real a).det : ℝ) = ((a.det : ℚ) : ℝ) := by
  change ((a : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ)).det = _
  exact (RingHom.map_det (Rat.castHom ℝ) (a : Matrix (Fin 2) (Fin 2) ℚ)).symm

theorem sigma_real {a : GL (Fin 2) ℚ} (ha : 0 < (a.det : ℚ)) (z : ℂ) : σ (real a) z = z := by
  have hpos : 0 < ((real a).det : ℝ) := by
    rw [real_det]
    exact_mod_cast ha
  simp only [σ]
  rw [ite_eq_left hpos]
  rfl

/-- A finite family of rational matrices of positive determinant, permuted on the right by
`Γ₁(3)` modulo `Γ₁(3)`. -/
structure CosetFamily (ι : Type*) [Fintype ι] where
  /-- The representatives. -/
  rep : ι → GL (Fin 2) ℚ
  det_pos : ∀ i, 0 < ((rep i).det : ℚ)
  transition : ∀ g ∈ CongruenceSubgroup.Gamma1 3, ∃ π : Equiv.Perm ι, ∀ i,
    ∃ γ ∈ CongruenceSubgroup.Gamma1 3,
      real (rep (π i)) * SpecialLinearGroup.mapGL ℝ g = SpecialLinearGroup.mapGL ℝ γ * real (rep i)

namespace CosetFamily

variable {ι : Type*} [Fintype ι] (F : CosetFamily ι) (k : ℤ)

/-- The sum of the slash translates `∑_i f ∣[k] α_i`. -/
def sumFun (f : ℍ → ℂ) : ℍ → ℂ := ∑ i, f ∣[k] real (F.rep i)

theorem sumFun_slash (f : ℍ → ℂ) (hf : ∀ γ ∈ levelThree, f ∣[k] γ = f) (g : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma1 3) :
    F.sumFun k f ∣[k] SpecialLinearGroup.mapGL ℝ g = F.sumFun k f := by
  obtain ⟨π, hπ⟩ := F.transition g hg
  unfold sumFun
  rw [Spectral.LevelOneHecke.sum_slash]
  simp_rw [← SlashAction.slash_mul]
  rw [← Equiv.sum_comp π]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨γ, hγ, h⟩ := hπ i
  rw [h, SlashAction.slash_mul, hf _ (mapGL_mem_levelThree hγ)]

theorem sumFun_mdifferentiable (f : CuspForm levelThree k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F.sumFun k f) := by
  unfold sumFun
  have hterm : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] real (F.rep i)) :=
    fun i => (CuspForm.translate f (real (F.rep i))).holo'
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mdifferentiable_const
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hterm a).add ih

theorem isCusp_real_smul (a : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c levelThree) :
    IsCusp (real a • c) levelThree := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  have h := hc.smul (real a)
  have := Subgroup.IsArithmetic.conj 𝒮ℒ a
  exact (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp h

theorem sumFun_zeroAt (f : CuspForm levelThree k) {c : OnePoint ℝ} (hc : IsCusp c levelThree) :
    c.IsZeroAt (F.sumFun k f) k := by
  intro g hg
  unfold sumFun
  rw [Spectral.LevelOneHecke.sum_slash]
  simp_rw [← SlashAction.slash_mul]
  have hterm : ∀ i, IsZeroAtImInfty (⇑f ∣[k] (real (F.rep i) * g)) := by
    intro i
    apply CuspFormClass.zero_at_cusps f (isCusp_real_smul (F.rep i) hc)
    rw [mul_smul, hg]
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hterm a).add ih

/-- **The operator `f ↦ ∑_i f ∣[k] α_i` on cusp forms for `Γ₁(3)`.** -/
def sumOp : CuspForm levelThree k →ₗ[ℂ] CuspForm levelThree k where
  toFun f :=
    { toFun := F.sumFun k f
      slash_action_eq' := by
        rintro γ ⟨g, hg, rfl⟩
        exact F.sumFun_slash k f (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) g hg
      holo' := F.sumFun_mdifferentiable k f
      zero_at_cusps' := fun hc => F.sumFun_zeroAt k f hc }
  map_add' f g := by
    ext τ
    change F.sumFun k (⇑f + ⇑g) τ = F.sumFun k f τ + F.sumFun k g τ
    simp only [sumFun, SlashAction.add_slash, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' a f := by
    ext τ
    change F.sumFun k (a • ⇑f) τ = a • F.sumFun k f τ
    simp only [sumFun, ModularForm.smul_slash, Finset.smul_sum, Finset.sum_apply, Pi.smul_apply,
      sigma_real (F.det_pos _)]

theorem sumOp_apply (f : CuspForm levelThree k) :
    (F.sumOp k f : ℍ → ℂ) = F.sumFun k f := rfl

end CosetFamily

end TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum
