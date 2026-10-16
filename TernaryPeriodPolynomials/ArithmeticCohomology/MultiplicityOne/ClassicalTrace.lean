module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Petersson.Form
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.AtkinLehner

@[expose] public section


/-!
# Restriction, trace and Atkin-Lehner operators between levels one and three

For even weight `k` we define the inclusion `restrictThree : S_k(SL₂ℤ) → S_k(Γ₁(3))` (the same
function), the trace `traceThree : S_k(Γ₁(3)) → S_k(SL₂ℤ)`, `g ↦ ∑ᵢ g ∣[k] rᵢ` over the right coset
representatives `rᵢ` of `Γ₀(3)` in `SL₂(ℤ)`, and the Atkin-Lehner operator
`atkinLehnerThree : g ↦ g ∣[k] W`, `W = [[0, -1], [3, 0]] = S · diag(3, 1)`, on `S_k(Γ₁(3))`.
One has `W (restrict f) = levelOneToThree f` exactly.

Original work by AxiomCode.
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory
open scoped ModularForm MatrixGroups Manifold

namespace TernaryPeriodPolynomials.MultiplicityOne.Classical

open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (scalar_slash_neg_one)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne heckeMatrix)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum
  (levelThree real mapGL_mem_levelThree)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeCosets
  (primeThree dvd_of_zmod_eq)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonDomain
  (rep rep_unique exists_rep_mul exists_gammaOne)
open TernaryPeriodPolynomials.LevelThree.LevelThreeAtkinLehnerEmbed
  (levelOneToThree)

/-! ### Cusps -/

theorem isCusp_levelOne_of_levelThree {c : OnePoint ℝ} (hc : IsCusp c levelThree) :
    IsCusp c levelOne := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact hc

/-- The cusps of `SL₂(ℤ)` map to cusps of `Γ₁(3)` under integral matrices. -/
theorem isCusp_smul_mapGL {c : OnePoint ℝ} (hc : IsCusp c levelOne) (r : SL(2, ℤ)) :
    IsCusp (SpecialLinearGroup.mapGL ℝ r • c) levelThree := by
  have h := LevelThree.LevelThreeAtkinLehner.isCusp_one_three
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL r)) hc
  have e : real (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL r)) =
      SpecialLinearGroup.mapGL ℝ r := Spectral.LevelOneHecke.map_toGL_eq_mapGL r
  rwa [e] at h

/-! ### Restriction -/

/-- **The inclusion** `S_k(SL₂(ℤ)) ⊆ S_k(Γ₁(3))`: the same function. -/
def restrictThree (k : ℤ) : CuspForm levelOne k →ₗ[ℂ] CuspForm levelThree k where
  toFun f :=
    { toFun := ⇑f
      slash_action_eq' := by
        rintro γ ⟨g, -, rfl⟩
        exact SlashInvariantFormClass.slash_action_eq f _ ⟨g, rfl⟩
      holo' := f.holo'
      zero_at_cusps' := fun hc =>
        CuspFormClass.zero_at_cusps f (isCusp_levelOne_of_levelThree hc) }
  map_add' f g := by
    ext τ
    rfl
  map_smul' a f := by
    ext τ
    rfl

theorem coe_restrictThree {k : ℤ} (f : CuspForm levelOne k) :
    (restrictThree k f : ℍ → ℂ) = ⇑f := rfl

theorem restrictThree_apply {k : ℤ} (f : CuspForm levelOne k) (τ : ℍ) :
    restrictThree k f τ = f τ := rfl

/-! ### Even weight: invariance under `Γ₀(3)` -/

theorem slash_neg_one_of_even {k : ℤ} (hk : Even k) (F : ℍ → ℂ) :
    F ∣[k] SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) = F := by
  rw [show SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) = ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) from rfl,
    ← ModularForm.SL_slash, scalar_slash_neg_one,
    LevelThree.LevelThreeHecke.neg_one_zpow_neg, hk.neg_one_zpow, one_smul]

/-- In even weight, cusp forms for `Γ₁(3)` are invariant under all of `Γ₀(3)`. -/
theorem slash_gamma0 {k : ℤ} (hk : Even k) (g : CuspForm levelThree k) (w : SL(2, ℤ))
    (h : ((w 1 0 : ℤ) : ZMod 3) = 0) :
    (⇑g) ∣[k] SpecialLinearGroup.mapGL ℝ w = ⇑g := by
  obtain ⟨w', hw', hpsl⟩ := exists_gammaOne w h
  rcases (Spectral.PeterssonDomain.psl_eq_iff _ _).mp hpsl with h1 | h1
  · rw [← h1]
    exact SlashInvariantFormClass.slash_action_eq g _ (mapGL_mem_levelThree hw')
  · have h2 : w = -w' := by rw [h1, neg_neg]
    have h3 : SpecialLinearGroup.mapGL ℝ (-w') =
        SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) * SpecialLinearGroup.mapGL ℝ w' := by
      rw [← map_mul, neg_one_mul]
    rw [h2, h3, SlashAction.slash_mul, slash_neg_one_of_even hk,
      SlashInvariantFormClass.slash_action_eq g _ (mapGL_mem_levelThree hw')]

/-! ### The trace -/

theorem SL_inv_10 (γ : SL(2, ℤ)) : (γ⁻¹ : SL(2, ℤ)) 1 0 = -γ 1 0 := by
  simp [adjugate_fin_two]

theorem exists_next (x : SL(2, ℤ)) (i : Option (Fin 3)) :
    ∃ j, (((rep i * x * (rep j)⁻¹) 1 0 : ℤ) : ZMod 3) = 0 := by
  obtain ⟨j, hj⟩ := exists_rep_mul (rep i * x)⁻¹
  refine ⟨j, ?_⟩
  have hz : rep j * (rep i * x)⁻¹ = (rep i * x * (rep j)⁻¹)⁻¹ := by group
  rw [hz, SL_inv_10, Int.cast_neg, neg_eq_zero] at hj
  exact hj

/-- The coset index `j` with `rᵢ x ∈ Γ₀(3) rⱼ`. -/
def nxt (x : SL(2, ℤ)) (i : Option (Fin 3)) : Option (Fin 3) := (exists_next x i).choose

theorem nxt_spec (x : SL(2, ℤ)) (i : Option (Fin 3)) :
    (((rep i * x * (rep (nxt x i))⁻¹) 1 0 : ℤ) : ZMod 3) = 0 :=
  (exists_next x i).choose_spec

theorem nxt_injective (x : SL(2, ℤ)) : Function.Injective (nxt x) := by
  intro i i' h
  have h1 := nxt_spec x i
  have h2 := nxt_spec x i'
  rw [← h] at h2
  exact rep_unique (x * (rep (nxt x i))⁻¹) i i' (by rwa [← mul_assoc]) (by rwa [← mul_assoc])

/-- The permutation of the cosets induced by `x`. -/
def nxtPerm (x : SL(2, ℤ)) : Equiv.Perm (Option (Fin 3)) :=
  Equiv.ofBijective (nxt x) (Finite.injective_iff_bijective.mp (nxt_injective x))

/-- The function `∑ᵢ g ∣[k] rᵢ`. -/
def traceFun (k : ℤ) (g : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : Option (Fin 3), g ∣[k] SpecialLinearGroup.mapGL ℝ (rep i)

theorem traceFun_slash {k : ℤ} (hk : Even k) (g : CuspForm levelThree k) (x : SL(2, ℤ)) :
    traceFun k g ∣[k] SpecialLinearGroup.mapGL ℝ x = traceFun k g := by
  unfold traceFun
  rw [Spectral.LevelOneHecke.sum_slash]
  simp_rw [← SlashAction.slash_mul]
  refine Fintype.sum_equiv (nxtPerm x) _ _ (fun i => ?_)
  change ⇑g ∣[k] (SpecialLinearGroup.mapGL ℝ (rep i) * SpecialLinearGroup.mapGL ℝ x) =
    ⇑g ∣[k] SpecialLinearGroup.mapGL ℝ (rep (nxt x i))
  have hmul : SpecialLinearGroup.mapGL ℝ (rep i) * SpecialLinearGroup.mapGL ℝ x =
      SpecialLinearGroup.mapGL ℝ (rep i * x * (rep (nxt x i))⁻¹) *
        SpecialLinearGroup.mapGL ℝ (rep (nxt x i)) := by
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  rw [hmul, SlashAction.slash_mul, slash_gamma0 hk g _ (nxt_spec x i)]

theorem traceFun_mdifferentiable (k : ℤ) (g : CuspForm levelThree k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (traceFun k g) := by
  unfold traceFun
  have hterm : ∀ i : Option (Fin 3), MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (⇑g ∣[k] SpecialLinearGroup.mapGL ℝ (rep i)) :=
    fun i => (CuspForm.translate g (SpecialLinearGroup.mapGL ℝ (rep i))).holo'
  classical
  induction (Finset.univ : Finset (Option (Fin 3))) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mdifferentiable_const
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hterm a).add ih

theorem traceFun_zeroAt (k : ℤ) (g : CuspForm levelThree k) {c : OnePoint ℝ}
    (hc : IsCusp c levelOne) : c.IsZeroAt (traceFun k g) k := by
  intro γ hγ
  unfold traceFun
  rw [Spectral.LevelOneHecke.sum_slash]
  simp_rw [← SlashAction.slash_mul]
  have hterm : ∀ i : Option (Fin 3),
      IsZeroAtImInfty (⇑g ∣[k] (SpecialLinearGroup.mapGL ℝ (rep i) * γ)) := by
    intro i
    apply CuspFormClass.zero_at_cusps g (isCusp_smul_mapGL hc (rep i))
    rw [mul_smul, hγ]
  classical
  induction (Finset.univ : Finset (Option (Fin 3))) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hterm a).add ih

theorem sigma_mapGL (x : SL(2, ℤ)) (a : ℂ) : σ (SpecialLinearGroup.mapGL ℝ x) a = a :=
  Spectral.PeterssonHecke.sigma_of_det_pos _
    (by rw [Spectral.PeterssonHecke.det_mapGL]; norm_num) a

/-- **The trace** `S_k(Γ₁(3)) → S_k(SL₂(ℤ))`, `g ↦ ∑ᵢ g ∣[k] rᵢ` over the right coset
representatives `rᵢ` of `Γ₀(3)` in `SL₂(ℤ)` (even weight). -/
def traceThree (k : ℤ) (hk : Even k) : CuspForm levelThree k →ₗ[ℂ] CuspForm levelOne k where
  toFun g :=
    { toFun := traceFun k g
      slash_action_eq' := by
        rintro γ ⟨x, rfl⟩
        exact traceFun_slash hk g x
      holo' := traceFun_mdifferentiable k g
      zero_at_cusps' := fun hc => traceFun_zeroAt k g hc }
  map_add' f g := by
    ext τ
    change traceFun k (⇑f + ⇑g) τ = traceFun k f τ + traceFun k g τ
    simp only [traceFun, SlashAction.add_slash, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' a f := by
    ext τ
    change traceFun k (a • ⇑f) τ = a • traceFun k f τ
    simp only [traceFun, ModularForm.smul_slash, Finset.smul_sum, Finset.sum_apply,
      Pi.smul_apply, sigma_mapGL]

theorem coe_traceThree {k : ℤ} (hk : Even k) (g : CuspForm levelThree k) :
    (traceThree k hk g : ℍ → ℂ) =
      ∑ i : Option (Fin 3), ⇑g ∣[k] SpecialLinearGroup.mapGL ℝ (rep i) := rfl

theorem traceThree_apply {k : ℤ} (hk : Even k) (g : CuspForm levelThree k) (τ : ℍ) :
    traceThree k hk g τ =
      ∑ i : Option (Fin 3), (⇑g ∣[k] SpecialLinearGroup.mapGL ℝ (rep i)) τ :=
  Finset.sum_apply τ Finset.univ (fun i => ⇑g ∣[k] SpecialLinearGroup.mapGL ℝ (rep i))

/-! ### The Atkin-Lehner matrix `W = [[0, -1], [3, 0]]` -/

/-- The rational matrix `[[0, -1], [3, 0]]`. -/
def atkinLehnerRat : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![(0 : ℚ), -1; 3, 0] (by
    rw [Matrix.det_fin_two_of]
    norm_num)

theorem atkinLehnerRat_val :
    (atkinLehnerRat : Matrix (Fin 2) (Fin 2) ℚ) = !![0, -1; 3, 0] :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- **The Atkin-Lehner matrix** `W = [[0, -1], [3, 0]] = S · diag(3, 1)` in `GL₂(ℝ)`. -/
def atkinLehnerMatrix : GL (Fin 2) ℝ := real atkinLehnerRat

theorem atkinLehnerMatrix_val :
    (atkinLehnerMatrix : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 3, 0] := by
  change ((atkinLehnerRat : Matrix (Fin 2) (Fin 2) ℚ)).map (Rat.castHom ℝ) = _
  rw [atkinLehnerRat_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem atkinLehnerMatrix_det :
    ((GeneralLinearGroup.det atkinLehnerMatrix : ℝˣ) : ℝ) = 3 := by
  change (atkinLehnerMatrix : Matrix (Fin 2) (Fin 2) ℝ).det = 3
  rw [atkinLehnerMatrix_val, Matrix.det_fin_two_of]
  norm_num

theorem sigma_atkinLehnerMatrix (a : ℂ) : σ atkinLehnerMatrix a = a :=
  Spectral.PeterssonHecke.sigma_of_det_pos _
    (by rw [atkinLehnerMatrix_det]; norm_num) a

/-- The unit `3` of `ℝ`. -/
def u3 : ℝˣ := Units.mk0 3 (by norm_num)

/-- The unit `-3` of `ℝ`. -/
def um3 : ℝˣ := Units.mk0 (-3) (by norm_num)

theorem atkinLehnerMatrix_eq : atkinLehnerMatrix =
    SpecialLinearGroup.mapGL ℝ ModularGroup.S * heckeMatrix primeThree none := by
  apply Units.ext
  rw [Units.val_mul, atkinLehnerMatrix_val,
    Spectral.PeterssonHecke.heckeMatrix_none_val,
    Spectral.PeterssonHecke.mapGL_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_S, primeThree]

theorem heckeMatrix_mul_atkinLehnerMatrix :
    heckeMatrix primeThree none * atkinLehnerMatrix =
      GeneralLinearGroup.scalar (Fin 2) u3 * SpecialLinearGroup.mapGL ℝ ModularGroup.S := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, atkinLehnerMatrix_val,
    Spectral.PeterssonHecke.heckeMatrix_none_val,
    Spectral.PeterssonHecke.mapGL_val, Spectral.PeterssonHecke.scalar_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_S, primeThree, u3]

theorem atkinLehnerMatrix_mul_self :
    atkinLehnerMatrix * atkinLehnerMatrix = GeneralLinearGroup.scalar (Fin 2) um3 := by
  apply Units.ext
  rw [Units.val_mul, atkinLehnerMatrix_val, Spectral.PeterssonHecke.scalar_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, um3]

/-- `γ' = W γ W⁻¹` for `γ = [[a, b], [3 c₁, d]]`: `γ' = [[d, -c₁], [-3 b, a]]`. -/
def conjW (γ : SL(2, ℤ)) (c₁ : ℤ) (hc : γ 1 0 = 3 * c₁) : SL(2, ℤ) :=
  ⟨!![γ 1 1, -c₁; -(3 * γ 0 1), γ 0 0], by
    rw [Matrix.det_fin_two_of]
    have := Spectral.PeterssonCosets.det_eq γ
    rw [hc] at this
    linear_combination this⟩

theorem conjW_mem (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 3) (c₁ : ℤ)
    (hc : γ 1 0 = 3 * c₁) : conjW γ c₁ hc ∈ CongruenceSubgroup.Gamma1 3 := by
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  have h3 : ((3 : ℤ) : ZMod 3) = 0 := by decide
  refine ⟨hγ.2.1, hγ.1, ?_⟩
  change ((-(3 * γ 0 1) : ℤ) : ZMod 3) = 0
  simp only [Int.cast_neg, Int.cast_mul, h3, zero_mul]
  erw [neg_zero]
  rfl

theorem atkinLehner_mul_mapGL (γ : SL(2, ℤ)) (c₁ : ℤ) (hc : γ 1 0 = 3 * c₁) :
    atkinLehnerMatrix * SpecialLinearGroup.mapGL ℝ γ =
      SpecialLinearGroup.mapGL ℝ (conjW γ c₁ hc) * atkinLehnerMatrix := by
  have hc' : (γ 1 0 : ℝ) = 3 * c₁ := by exact_mod_cast hc
  apply Units.ext
  simp only [Units.val_mul, atkinLehnerMatrix_val, Spectral.PeterssonHecke.mapGL_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, conjW, hc'] <;> ring

/-- **`W` normalizes `Γ₁(3)`.** -/
theorem exists_conjW {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma1 3) :
    ∃ γ' ∈ CongruenceSubgroup.Gamma1 3, atkinLehnerMatrix * SpecialLinearGroup.mapGL ℝ γ =
      SpecialLinearGroup.mapGL ℝ γ' * atkinLehnerMatrix := by
  have hγ' := hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ'
  obtain ⟨c₁, hc₁⟩ := dvd_of_zmod_eq (x := γ 1 0) (r := 0) (by rw [hγ'.2.2]; simp)
  have hc : γ 1 0 = 3 * c₁ := by linarith
  exact ⟨conjW γ c₁ hc, conjW_mem γ hγ c₁ hc, atkinLehner_mul_mapGL γ c₁ hc⟩

theorem atkinLehnerFun_slash {k : ℤ} (g : CuspForm levelThree k) (x : SL(2, ℤ))
    (hx : x ∈ CongruenceSubgroup.Gamma1 3) :
    (⇑g ∣[k] atkinLehnerMatrix) ∣[k] SpecialLinearGroup.mapGL ℝ x = ⇑g ∣[k] atkinLehnerMatrix := by
  obtain ⟨γ', hγ', h⟩ := exists_conjW hx
  rw [← SlashAction.slash_mul, h, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq g _ (mapGL_mem_levelThree hγ')]

theorem isCusp_atkinLehnerMatrix_smul {c : OnePoint ℝ} (hc : IsCusp c levelThree) :
    IsCusp (atkinLehnerMatrix • c) levelThree :=
  LevelThree.LevelThreeHeckeSum.CosetFamily.isCusp_real_smul atkinLehnerRat hc

/-- **The Atkin-Lehner operator** `g ↦ g ∣[k] W`, `W = [[0, -1], [3, 0]]`, on `S_k(Γ₁(3))`. -/
def atkinLehnerThree (k : ℤ) : CuspForm levelThree k →ₗ[ℂ] CuspForm levelThree k where
  toFun g :=
    { toFun := ⇑g ∣[k] atkinLehnerMatrix
      slash_action_eq' := by
        rintro γ ⟨x, hx, rfl⟩
        exact atkinLehnerFun_slash g x hx
      holo' := (CuspForm.translate g atkinLehnerMatrix).holo'
      zero_at_cusps' := by
        intro c hc γ hγ
        rw [← SlashAction.slash_mul]
        apply CuspFormClass.zero_at_cusps g (isCusp_atkinLehnerMatrix_smul hc)
        rw [mul_smul, hγ] }
  map_add' f g := by
    ext τ
    change ((⇑f + ⇑g) ∣[k] atkinLehnerMatrix) τ =
      (⇑f ∣[k] atkinLehnerMatrix) τ + (⇑g ∣[k] atkinLehnerMatrix) τ
    simp only [SlashAction.add_slash, Pi.add_apply]
  map_smul' a f := by
    ext τ
    change ((a • ⇑f) ∣[k] atkinLehnerMatrix) τ = a • (⇑f ∣[k] atkinLehnerMatrix) τ
    simp only [ModularForm.smul_slash, Pi.smul_apply, sigma_atkinLehnerMatrix]

theorem coe_atkinLehnerThree {k : ℤ} (g : CuspForm levelThree k) :
    (atkinLehnerThree k g : ℍ → ℂ) = ⇑g ∣[k] atkinLehnerMatrix := rfl

theorem atkinLehnerThree_apply {k : ℤ} (g : CuspForm levelThree k) (τ : ℍ) :
    atkinLehnerThree k g τ = (⇑g ∣[k] atkinLehnerMatrix) τ := rfl

/-- `W² = -3`, so `(g ∣ W) ∣ W = (-3)^{k-2} g`. -/
theorem slash_atkinLehnerMatrix_sq {k : ℤ} (G : ℍ → ℂ) :
    (G ∣[k] atkinLehnerMatrix) ∣[k] atkinLehnerMatrix = ((-3 : ℝ) : ℂ) ^ (k - 2) • G := by
  rw [← SlashAction.slash_mul, atkinLehnerMatrix_mul_self]
  exact Spectral.PeterssonHecke.slash_scalar k G um3

/-! ### `W` carries level one to the embedding `g ↦ g(3τ)` -/

/-- **`W (restrict f) = levelOneToThree f`**, i.e. `f ∣ W = f ∣ diag(3, 1) = 3^{k-1} f(3τ)`. -/
theorem atkinLehnerThree_restrictThree {k : ℤ} (f : CuspForm levelOne k) :
    atkinLehnerThree k (restrictThree k f) = levelOneToThree k f := by
  ext τ
  change (⇑f ∣[k] atkinLehnerMatrix) τ = (⇑f ∣[k] heckeMatrix primeThree none) τ
  rw [atkinLehnerMatrix_eq, SlashAction.slash_mul,
    Spectral.PeterssonHecke.slash_levelOne]

/-- **`W (levelOneToThree f) = 3^{k-2} restrict f`.** -/
theorem atkinLehnerThree_levelOneToThree {k : ℤ} (f : CuspForm levelOne k) :
    atkinLehnerThree k (levelOneToThree k f) =
      (3 : ℂ) ^ (k - 2) • (restrictThree k f : CuspForm levelThree k) := by
  ext τ
  change ((⇑f ∣[k] heckeMatrix primeThree none) ∣[k] atkinLehnerMatrix) τ =
    (3 : ℂ) ^ (k - 2) * f τ
  rw [← SlashAction.slash_mul, heckeMatrix_mul_atkinLehnerMatrix, SlashAction.slash_mul,
    Spectral.PeterssonHecke.slash_scalar, ModularForm.smul_slash, sigma_mapGL,
    Spectral.PeterssonHecke.slash_levelOne]
  have hu : (((u3 : ℝˣ) : ℝ) : ℂ) = 3 := by
    simp [u3]
  simp [hu]

end TernaryPeriodPolynomials.MultiplicityOne.Classical
