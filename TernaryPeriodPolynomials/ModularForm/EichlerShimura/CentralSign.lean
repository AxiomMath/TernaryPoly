module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.BinCoeff

@[expose] public section


/-!
# The central element `-1` and Eichler–Shimura spanning in the trivial parity

If `-1 ∈ Λ` then `-1` acts on `Sym^{n+1} ⊗ det⁻¹` by `(-1)^{n+1}` (`binRep_neg_one`). A central
element acting by `-1` kills first cohomology (`cocycle_coboundary_of_central_neg`, char `≠ 2`), so for
even `n` every class of `H¹(Λ, Sym^{n+1} ⊗ det⁻¹)` vanishes and `ESSpan Λ n` holds trivially
(`esSpan_of_neg_one_mem_of_even`). This is the parity case of the level `N = 2` in the Assembly plan.

Written by Claude Opus 5.5.
-/

open GeneralEisenstein MvPolynomial CategoryTheory groupCohomology
open TernaryPeriodPolynomials.SphericalDetection.Helpers TernaryPeriodPolynomials.Argument.SeedC3
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.CentralSign

open TernaryPeriodPolynomials.Argument.SeedC3S4c

theorem eval_neg_of_isHomogeneous {P : MvPolynomial (Fin 2) ℂ} {d : ℕ} (hP : P.IsHomogeneous d)
    (v : Fin 2 → ℂ) : eval (fun i => -v i) P = (-1) ^ d * eval v P := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hP (mem_support_iff.mp hm)
  have e : ∀ i : Fin 2, (-v i) ^ (m i) = (-1) ^ (m i) * v i ^ (m i) := fun i => by
    rw [show -v i = (-1) * v i by ring, mul_pow]
  simp only [e, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have : ∑ i, m i = d := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype]
    · simp
    · simp
  rw [this]
  ring

theorem bind_neg_of_isHomogeneous {P : MvPolynomial (Fin 2) ℂ} {d : ℕ} (hP : P.IsHomogeneous d) :
    bind₁ (fun i => -X i) P = C ((-1) ^ d) * P := by
  apply MvPolynomial.funext
  intro v
  have h : eval v (bind₁ (fun i => -X i) P) = eval (fun i => -v i) P := by
    have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ) v (fun i => -X i) P
    change eval₂Hom (RingHom.id ℂ) v (bind₁ (fun i => -X i) P) = _
    rw [h]
    have hf : (fun i => (eval₂Hom (RingHom.id ℂ) v) (-X i : MvPolynomial (Fin 2) ℂ)) =
        fun i => -v i := by
      funext i; simp
    rw [hf]
    rfl
  rw [h, eval_neg_of_isHomogeneous hP, eval_mul, eval_C]

theorem invCoordPoly_neg_one :
    invCoordPoly (Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ))) = fun i => -X i := by
  funext i
  fin_cases i <;> simp [invCoordPoly, Matrix.SpecialLinearGroup.mapGL]

variable {Λ : Subgroup SL(2, ℤ)} {n : ℕ}

/-- `-1` acts on `Sym^{n+1} ⊗ det⁻¹` by `(-1)^{n+1}`. -/
theorem binRep_neg_one (h : (-1 : SL(2, ℤ)) ∈ Λ) (x : binRep Λ n) :
    (binRep Λ n).ρ ⟨-1, h⟩ x = ((-1 : ℂ) ^ (n + 1)) • x := by
  apply Subtype.ext
  have h1 : bvalΛ ((binRep Λ n).ρ ⟨-1, h⟩ x) =
      bind₁ (invCoordPoly (Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)))) (bvalΛ x) :=
    modularBinaryRep_coe (n + 1) (-1) x
  change bvalΛ ((binRep Λ n).ρ ⟨-1, h⟩ x) = ((-1 : ℂ) ^ (n + 1)) • bvalΛ x
  rw [h1, invCoordPoly_neg_one, bind_neg_of_isHomogeneous (BinCoeff.isHomogeneous_bvalΛ x),
    C_mul']

/-- A central element acting by `-1` makes every `1`-cocycle a coboundary. -/
theorem cocycle_coboundary_of_central_neg {G : Type} [Group G] (A : Rep ℂ G) (z : G)
    (hz : ∀ g, z * g = g * z) (hρ : ∀ v, A.ρ z v = -v) (c : cocycles₁ A) :
    ∃ u : A, ∀ g, c g = A.ρ g u - u := by
  have hc := (mem_cocycles₁_iff (A := A) c).1 c.2
  refine ⟨-(1 / 2 : ℂ) • c z, fun g => ?_⟩
  have h1 := hc z g
  have h2 := hc g z
  rw [hz g, h2, hρ] at h1
  rw [map_smul]
  have key : (2 : ℂ) • c g = c z - A.ρ g (c z) := by
    rw [two_smul]
    rw [← sub_eq_zero] at h1 ⊢
    have e : c g + c g - (c z - A.ρ g (c z)) = (A.ρ g (c z) + c g) - (-c g + c z) := by abel
    rw [e, h1]
  have : c g = (1 / 2 : ℂ) • ((2 : ℂ) • c g) := by
    rw [smul_smul]; norm_num
  rw [this, key, smul_sub]
  module

/-- For even `n` and `-1 ∈ Λ`, `H¹(Λ, Sym^{n+1} ⊗ det⁻¹) = 0`. -/
theorem H1π_eq_zero_of_neg_one_mem (h : (-1 : SL(2, ℤ)) ∈ Λ) (hn : Even n)
    (c : cocycles₁ (binRep Λ n)) : H1π (binRep Λ n) c = 0 := by
  have hodd : (-1 : ℂ) ^ (n + 1) = -1 := by
    rw [pow_succ, hn.neg_one_pow, one_mul]
  obtain ⟨u, hu⟩ := cocycle_coboundary_of_central_neg (binRep Λ n) ⟨-1, h⟩
    (fun g => by ext1; simp) (fun v => by rw [binRep_neg_one h, hodd, neg_one_smul]) c
  rw [H1π_eq_zero_iff]
  exact ⟨u, by funext g; rw [hu g]; rfl⟩

/-- **Eichler–Shimura spanning in the trivial parity.** If `-1 ∈ Λ` and `n` is even, `ESSpan Λ n`
holds: every parabolic class is zero. -/
theorem esSpan_of_neg_one_mem_of_even (h : (-1 : SL(2, ℤ)) ∈ Λ) (hn : Even n) : ESSpan Λ n := by
  rintro _ ⟨c, -, rfl⟩
  have : (H1π (binRep Λ n)).hom c = 0 := H1π_eq_zero_of_neg_one_mem h hn c
  rw [this]
  exact Submodule.zero_mem _

end TernaryPeriodPolynomials.Argument.ESFoundations.CentralSign
