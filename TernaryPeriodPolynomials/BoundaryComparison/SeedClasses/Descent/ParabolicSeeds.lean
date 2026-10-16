module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ParabolicAnalytic
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ParabolicAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.BoundaryFunctional
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.CocycleCentral

@[expose] public section


/-!
# The seeds of cusp forms are parabolic classes (converse inclusion of the spanning clause)

Paper: Lemma C.3
(`ar:lem:seed`), last sentence: the mixed cuspidal group `𝒞_P` is spanned by the seeds.

For a subgroup `Λ ⊆ SL₂(ℤ)` and a cusp form `f` of weight `n + 3` for its image in `GL₂(ℝ)`, the
holomorphic and antiholomorphic period cocycles are coboundaries on every parabolic element of `Λ`
(`holCocycle_parabolic`, `antiholCocycle_parabolic`). For `γ = ± g T^k g⁻¹`, `k ≠ 0`, the
coinvariants of `γ` on `Sym^{n+1}` are one-dimensional when `γ` acts unipotently (the image of
`T - 1` is the hyperplane `w(1,0) = 0`, `ParabolicAlgebra`), the obstruction is the value of
`ε_f(γ)` at the first column of `g`, and it vanishes because `f` is a cusp form
(`ParabolicAnalytic.eval_eps_zero_of_cusp`); when `γ` acts with eigenvalue `-1` (`-T^k` on odd
degree) `γ - 1` is invertible. Hence the span of the period classes lies in `parabolicH1`
(`span_le_parabolicH1`), and under `ESSpan Λ n` equals it (`parabolicH1_eq_span`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups ModularForm OnePoint
open GeneralEisenstein Matrix MvPolynomial UpperHalfPlane
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.SymFixed

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section Alg

variable (d : ℕ)

/-- The action of `SL₂(ℤ)` on `Sym^d ⊗ det⁻¹`, as endomorphisms of `Sym^d`. -/
def rhoV : SL(2, ℤ) →* Module.End ℂ (Binary.HomogeneousPoly d) :=
  (modularBinaryRep d (-1)).ρ

/-- The central element `-1` acts on `Sym^d` by `(-1)^d`. -/
theorem rhoV_neg_one (P : Binary.HomogeneousPoly d) : rhoV d (-1) P = ((-1 : ℂ) ^ d) • P := by
  apply Subtype.ext
  change ((arithmeticBinaryRep d (-1)).ρ (SpecialLinearGroup.toGL (-1)) P).val = _
  rw [arithmeticBinaryRep_specialLinear_coe]
  have matrix_eq : (((-1 : SpecialLinearGroup (Fin 2) ℤ)⁻¹).val.map (Int.castRingHom ℂ)) =
      Matrix.scalar (Fin 2) (-1 : ℂ) := by
    rw [SpecialLinearGroup.SL2_inv_expl]
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.map]
  rw [matrix_eq, binary_substitute_scalar]
  rfl

/-- `T^k` acts on `Sym^d` through the shear `upperC k`. -/
theorem rhoV_T_zpow (k : ℤ) :
    rhoV d (ModularGroup.T ^ k) = Binary.homogeneousAction d (-1) (upperC (k : ℂ)) := by
  apply LinearMap.ext
  intro P
  change Binary.homogeneousAction d (-1)
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL (ModularGroup.T ^ k))) P =
      Binary.homogeneousAction d (-1) (upperC (k : ℂ)) P
  have : GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL (ModularGroup.T ^ k)) = upperC (k : ℂ) := by
    have hT : ((ModularGroup.T ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, k; 0, 1] :=
      ModularGroup.coe_T_zpow k
    apply Units.ext
    ext i j
    show (Int.castRingHom ℂ) (((ModularGroup.T ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j) = _
    rw [hT]
    fin_cases i <;> fin_cases j <;> simp [upperC]
  rw [this]

theorem exists_boundary_of_eval (g γ δ : SL(2, ℤ)) (k : ℤ) (hk : k ≠ 0)
    (hδ : rhoV d δ = Binary.homogeneousAction d (-1) (upperC (k : ℂ)))
    (hcomm : γ * g = g * δ) (P : Binary.HomogeneousPoly d)
    (hP : MvPolynomial.eval ![((g 0 0 : ℤ) : ℂ), ((g 1 0 : ℤ) : ℂ)] P.val = 0) :
    ∃ u : Binary.HomogeneousPoly d, rhoV d γ u - u = P := by
  set Q : Binary.HomogeneousPoly d := rhoV d g⁻¹ P with hQ
  have hQ0 : evalAt (m := d) ![1, 0] Q = 0 := by
    have h1 := TernaryPeriodPolynomials.Spectral.BoundaryFunctional.ell_modular
      d (-1) g⁻¹ P
    rw [inv_inv] at h1
    change MvPolynomial.eval ![1, 0] Q.val = 0
    have h2 : MvPolynomial.eval ![(1 : ℂ), 0] Q.val =
        MvPolynomial.aeval (fun i => ((g : Matrix (Fin 2) (Fin 2) ℤ) i 0 : ℂ)) P.val := h1
    rw [h2]
    have : (fun i => ((g : Matrix (Fin 2) (Fin 2) ℤ) i 0 : ℂ)) =
        ![((g 0 0 : ℤ) : ℂ), ((g 1 0 : ℤ) : ℂ)] := by
      funext i
      fin_cases i <;> rfl
    rw [this]
    exact hP
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hmem : Q ∈ movedSpace (m := d) (-1) (upperC (k : ℂ)) := by
    rw [movedSpace_upper_eq (-1) hkc]
    exact hQ0
  obtain ⟨u₀, hu₀⟩ := hmem
  refine ⟨rhoV d g u₀, ?_⟩
  have hu : rhoV d δ u₀ - u₀ = Q := by
    rw [hδ]
    exact hu₀
  calc rhoV d γ (rhoV d g u₀) - rhoV d g u₀ = rhoV d g (rhoV d δ u₀ - u₀) := by
        rw [map_sub, ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    _ = P := by
        rw [hu, hQ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply]


theorem exists_boundary_of_neg (g γ δ : SL(2, ℤ)) (k : ℤ) (hk : k ≠ 0)
    (hδ : rhoV d δ = -Binary.homogeneousAction d (-1) (upperC (k : ℂ)))
    (hcomm : γ * g = g * δ) (P : Binary.HomogeneousPoly d) :
    ∃ u : Binary.HomogeneousPoly d, rhoV d γ u - u = P := by
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hinj : Function.Injective ⇑(rhoV d γ - 1 : Module.End ℂ (Binary.HomogeneousPoly d)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hu' : rhoV d γ u = u := by
      have h0 : rhoV d γ u - u = 0 := hu
      exact sub_eq_zero.mp h0
    set Q : Binary.HomogeneousPoly d := rhoV d g⁻¹ u with hQ
    have hδQ : rhoV d δ Q = Q := by
      have h1 : g⁻¹ * γ = δ * g⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hcomm]
        group
      calc rhoV d δ Q = rhoV d (δ * g⁻¹) u := by rw [hQ, map_mul, Module.End.mul_apply]
        _ = rhoV d (g⁻¹ * γ) u := by rw [h1]
        _ = Q := by rw [map_mul, Module.End.mul_apply, hu']
    have hQeig : Binary.homogeneousAction d (-1) (upperC (k : ℂ)) Q = -Q := by
      have := hδQ
      rw [hδ] at this
      simpa using congrArg Neg.neg this
    have hQ0 := eq_zero_of_upper_eigen_neg (-1) hkc Q hQeig
    have : u = rhoV d g Q := by
      rw [hQ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [this, hQ0, map_zero]
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨u, hu⟩ := hsurj P
  exact ⟨u, by simpa using hu⟩

end Alg

section Assembly

variable {Λ : Subgroup SL(2, ℤ)} {n : ℕ}

theorem zero_at_cusp_of_comm (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) (γ g δ : SL(2, ℤ))
    (hγ : γ ∈ Λ) (k σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hk : k ≠ 0)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![σ, σ * k; 0, σ]) (hcomm : γ * g = g * δ) :
    IsZeroAtImInfty (⇑f ∣[((n + 3 : ℕ) : ℤ)] (SpecialLinearGroup.mapGL ℝ g)) := by
  have hδ10 : (SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) 1 0 = 0 := by
    have : (δ 1 0 : ℤ) = 0 := by simpa using congrFun (congrFun hδ 1) 0
    change ((δ 1 0 : ℤ) : ℝ) = 0
    rw [this]; simp
  have hfix : SpecialLinearGroup.mapGL ℝ δ • (∞ : OnePoint ℝ) = ∞ :=
    OnePoint.smul_infty_eq_self_iff.mpr hδ10
  have hcomm' : SpecialLinearGroup.mapGL ℝ γ * SpecialLinearGroup.mapGL ℝ g =
      SpecialLinearGroup.mapGL ℝ g * SpecialLinearGroup.mapGL ℝ δ := by
    rw [← map_mul, ← map_mul, hcomm]
  have hpar : (SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ).IsParabolic := by
    have hσ0 : (σ : ℝ) ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    refine (Matrix.isParabolic_iff_of_upperTriangular hδ10).2 ⟨?_, ?_⟩
    · have e1 : (δ 0 0 : ℤ) = σ := by simpa using congrFun (congrFun hδ 0) 0
      have e2 : (δ 1 1 : ℤ) = σ := by simpa using congrFun (congrFun hδ 1) 1
      change ((δ 0 0 : ℤ) : ℝ) = ((δ 1 1 : ℤ) : ℝ)
      rw [e1, e2]
    · have e1 : (δ 0 1 : ℤ) = σ * k := by simpa using congrFun (congrFun hδ 0) 1
      change ((δ 0 1 : ℤ) : ℝ) ≠ 0
      rw [e1]
      push_cast
      exact mul_ne_zero hσ0 (by exact_mod_cast hk)
  have hconj : (SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      SpecialLinearGroup.mapGL ℝ g * SpecialLinearGroup.mapGL ℝ δ *
        (SpecialLinearGroup.mapGL ℝ g)⁻¹ := by
    rw [← hcomm']; group
  have hc : IsCusp (SpecialLinearGroup.mapGL ℝ g • (∞ : OnePoint ℝ)) (LamGL Λ) := by
    refine ⟨SpecialLinearGroup.mapGL ℝ γ, ⟨γ, hγ, rfl⟩, ?_, ?_⟩
    · rw [hconj]
      exact (Matrix.GeneralLinearGroup.isParabolic_conj_iff _ _).2 hpar
    · rw [← mul_smul, hcomm', mul_smul, hfix]
  exact (CuspFormClass.zero_at_cusps f hc) (SpecialLinearGroup.mapGL ℝ g) rfl


theorem neg_T_zpow_eq (k : ℤ) :
    -(ModularGroup.T ^ k : SL(2, ℤ)) = (-1 : SL(2, ℤ)) * ModularGroup.T ^ k := by
  apply Subtype.ext
  simp

theorem eps_boundary (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) (γ g δ : SL(2, ℤ))
    (hγ : γ ∈ Λ) (k σ : ℤ)
    (hδT : (σ = 1 ∧ δ = ModularGroup.T ^ k) ∨ (σ = -1 ∧ δ = -(ModularGroup.T ^ k)))
    (hcomm : γ * g = g * δ) :
    ∃ u : Binary.HomogeneousPoly (n + 1), rhoV (n + 1) γ u - u =
      (eichlerForm f γ : Binary.HomogeneousPoly (n + 1)) := by
  have hσ : σ = 1 ∨ σ = -1 := by rcases hδT with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![σ, σ * k; 0, σ] := by
    rcases hδT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [ModularGroup.coe_T_zpow]; simp
    · rw [Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]
      ext i j; fin_cases i <;> fin_cases j <;> simp
  by_cases hk : k = 0
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    rw [map_zero, sub_zero]
    change (0 : MvPolynomial (Fin 2) ℂ) = eichlerCocycle n (momentPrim (LamGL Λ) n f)
      (SpecialLinearGroup.mapGL ℝ γ)
    have hI : mob (SpecialLinearGroup.mapGL ℝ γ) Complex.I = Complex.I := by
      have hdet : ∀ s : SL(2, ℤ), (SpecialLinearGroup.mapGL ℝ s).det = 1 :=
        fun s => SpecialLinearGroup.det_mapGL s
      have hpos : ∀ s : SL(2, ℤ), 0 < (SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ).det.val :=
        fun s => by simp [hdet s]
      have hI0 : 0 < (Complex.I : ℂ).im := by simp
      set w₀ := mob (SpecialLinearGroup.mapGL ℝ g⁻¹) Complex.I with hw₀
      have hw₀pos : 0 < w₀.im := mob_im_pos _ (hpos g⁻¹) hI0
      have h1 : mob (SpecialLinearGroup.mapGL ℝ g) w₀ = Complex.I := by
        rw [hw₀, ← mob_mul _ _ (hdet g) (hdet g⁻¹) hI0, ← map_mul, mul_inv_cancel, map_one]
        simp [mob]
      have hcomm' : SpecialLinearGroup.mapGL ℝ γ * SpecialLinearGroup.mapGL ℝ g =
          SpecialLinearGroup.mapGL ℝ g * SpecialLinearGroup.mapGL ℝ δ := by
        rw [← map_mul, ← map_mul, hcomm]
      have h2 : mob (SpecialLinearGroup.mapGL ℝ γ) (mob (SpecialLinearGroup.mapGL ℝ g) w₀) =
          mob (SpecialLinearGroup.mapGL ℝ g) (w₀ + k) := by
        rw [← mob_mul _ _ (hdet γ) (hdet g) hw₀pos, hcomm',
          mob_mul _ _ (hdet g) (hdet δ) hw₀pos, mob_pm_T δ k σ hσ hδ w₀]
      rw [h1, hk] at h2
      rw [h2]
      simpa using h1
    rw [eichlerCocycle, hI, eichlerPoly_base n _ (momentPrim_zero (LamGL Λ) n f)]
  · have hzero := zero_at_cusp_of_comm f γ g δ hγ k σ hσ hk hδ hcomm
    have key1 : (rhoV (n + 1) δ = Binary.homogeneousAction (n + 1) (-1) (upperC (k : ℂ)) ∧
          σ ^ (n + 1) = 1) ∨
        (rhoV (n + 1) δ = -Binary.homogeneousAction (n + 1) (-1) (upperC (k : ℂ)) ∧
          σ ^ (n + 1) ≠ 1) := by
      rcases hδT with ⟨h1, hδeq⟩ | ⟨h1, hδeq⟩
      · left
        exact ⟨by rw [hδeq]; exact rhoV_T_zpow _ _, by rw [h1]; simp⟩
      · have hρ : rhoV (n + 1) δ =
            ((-1 : ℂ) ^ (n + 1)) • Binary.homogeneousAction (n + 1) (-1) (upperC (k : ℂ)) := by
          rw [hδeq, neg_T_zpow_eq, map_mul, rhoV_T_zpow]
          apply LinearMap.ext
          intro P
          rw [Module.End.mul_apply, rhoV_neg_one]
          rfl
        rcases Nat.even_or_odd (n + 1) with he | ho
        · left
          exact ⟨by rw [hρ, he.neg_one_pow, one_smul], by rw [h1]; exact he.neg_one_pow⟩
        · right
          refine ⟨by
            rw [hρ, ho.neg_one_pow]
            exact neg_one_smul ℂ (Binary.homogeneousAction (n + 1) (-1) (upperC (k : ℂ))), ?_⟩
          rw [h1, ho.neg_one_pow]
          norm_num
    rcases key1 with ⟨hδρ, hm⟩ | ⟨hδρ, -⟩
    · have hP := eval_eps_zero_of_cusp f γ g δ hγ k σ hσ hδ hcomm hm hzero
      exact exists_boundary_of_eval (n + 1) g γ δ k hk hδρ hcomm _ hP
    · exact exists_boundary_of_neg (n + 1) g γ δ k hk hδρ hcomm _


/-- **The holomorphic period cocycle of a cusp form is trivial on every parabolic element.** -/
theorem holCocycle_parabolic (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) (γ : Λ)
    (hγ : IsParabolicSL γ.1) :
    ∃ u : binRep Λ n, holCocycle f γ = (binRep Λ n).ρ γ u - u := by
  obtain ⟨g, k, h | h⟩ := hγ
  · obtain ⟨u, hu⟩ := eps_boundary f γ.1 g (ModularGroup.T ^ k) γ.2 k 1 (Or.inl ⟨rfl, rfl⟩) (by
      rw [h]; group)
    exact ⟨u, hu.symm⟩
  · obtain ⟨u, hu⟩ := eps_boundary f γ.1 g (-(ModularGroup.T ^ k)) γ.2 k (-1) (Or.inr ⟨rfl, rfl⟩)
      (by
        rw [h]
        apply Subtype.ext
        simp [Matrix.SpecialLinearGroup.coe_mul])
    exact ⟨u, hu.symm⟩


/-- The antiholomorphic period cocycle is trivial on every parabolic element. -/
theorem antiholCocycle_parabolic (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) (γ : Λ)
    (hγ : IsParabolicSL γ.1) :
    ∃ u : binRep Λ n, antiholCocycle f γ = (binRep Λ n).ρ γ u - u := by
  obtain ⟨u, hu⟩ := holCocycle_parabolic f γ hγ
  let ub : binRep Λ n := (⟨MvPolynomial.map (starRingEnd ℂ) (bvalΛ u),
    (mem_homogeneousSubmodule _ _).mpr
      (((mem_homogeneousSubmodule _ _).mp (u : Binary.HomogeneousPoly (n + 1)).2).map _)⟩ :
        Binary.HomogeneousPoly (n + 1))
  refine ⟨ub, ?_⟩
  have h1 : bvalΛ (holCocycle f γ) =
      MvPolynomial.bind₁ (invCoordPoly (SpecialLinearGroup.mapGL ℝ γ.1)) (bvalΛ u) - bvalΛ u := by
    rw [hu]
    exact congrArg₂ (· - ·) (modularBinaryRep_coe (n + 1) γ.1 u) rfl
  have e2 : bvalΛ ((binRep Λ n).ρ γ ub) = MvPolynomial.bind₁
      (invCoordPoly (SpecialLinearGroup.mapGL ℝ γ.1)) (bvalΛ ub) :=
    modularBinaryRep_coe (n + 1) γ.1 ub
  apply Subtype.ext
  change MvPolynomial.map (starRingEnd ℂ) (bvalΛ (holCocycle f γ)) =
    bvalΛ ((binRep Λ n).ρ γ ub) - MvPolynomial.map (starRingEnd ℂ) (bvalΛ u)
  rw [e2, h1, map_sub, map_conj_bind_invCoordPoly]
  rfl

theorem holCocycle_mem_parabolicCocycles (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) :
    holCocycle f ∈ parabolicCocycles Λ n := fun γ hγ => holCocycle_parabolic f γ hγ

theorem antiholCocycle_mem_parabolicCocycles (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) :
    antiholCocycle f ∈ parabolicCocycles Λ n := fun γ hγ => antiholCocycle_parabolic f γ hγ

/-- **The seeds lie in the mixed cuspidal group**: the span of the holomorphic and
antiholomorphic period classes is contained in the parabolic cohomology. -/
theorem span_le_parabolicH1 :
    Submodule.span ℂ
      (Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) =>
          groupCohomology.H1π (binRep Λ n) (holCocycle f)) ∪
        Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) =>
          groupCohomology.H1π (binRep Λ n) (antiholCocycle f))) ≤ parabolicH1 Λ n := by
  rw [Submodule.span_le]
  rintro _ (⟨f, rfl⟩ | ⟨f, rfl⟩)
  · exact ⟨holCocycle f, holCocycle_mem_parabolicCocycles f, rfl⟩
  · exact ⟨antiholCocycle f, antiholCocycle_mem_parabolicCocycles f, rfl⟩

/-- **Spanning, with equality**: under `ESSpan Λ n` the parabolic cohomology is exactly the span of
the holomorphic and antiholomorphic period classes. -/
theorem parabolicH1_eq_span (hES : ESSpan Λ n) :
    parabolicH1 Λ n =
      Submodule.span ℂ
        (Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) =>
            groupCohomology.H1π (binRep Λ n) (holCocycle f)) ∪
          Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) =>
            groupCohomology.H1π (binRep Λ n) (antiholCocycle f))) :=
  le_antisymm hES span_le_parabolicH1

end Assembly

end TernaryPeriodPolynomials.Argument.SeedC3S4c
