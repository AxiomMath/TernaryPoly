module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level3Eichler

@[expose] public section


/-!
# Eichler--Shimura spanning at level three: `ESSpan (Gamma1 3) n`

Paper: Lemma C.3
(`ar:lem:seed`), last sentence, at the level-three plane cusp (Levi block `Γ₁(3)`).

`esSpan_gam3 n : ESSpan (Gamma1 3) n` is proved unconditionally. A parabolic class of
`H¹(Γ₁(3), Sym^{n+1} ⊗ det⁻¹)` is transported to a parabolic crossed cocycle of the library's
`core = ⟨T, L⟩` (`toCrossed`; `T` and `L = [[1,0],[3,1]]` are parabolic, `coreSL_coreT_parabolic`,
`coreSL_coreL_parabolic`); `crossed_ES` (library Eichler--Shimura for `Γ₁'(3)` in the two twists)
writes it, up to a coboundary, as `(c + ι c)/2 + (c' - ι c')/2` for the period cocycles of two
cusp forms; and `periodCocycle_val_eq`, `iotaVal_val_eq` identify these with the holomorphic
cocycle `(-1)^{n+1} holCocycle (liftL3 f)` and `-antiholCocycle (f^*)`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups Manifold ModularForm
open GeneralEisenstein Matrix MvPolynomial ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.GammaOneThree

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)

theorem coreSL_coreT_parabolic : IsParabolicSL (coreSL coreT) := by
  refine ⟨1, 1, Or.inl ?_⟩
  rw [one_mul, inv_one, mul_one, zpow_one]
  apply Subtype.ext
  rw [coreSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coreT, upper, ModularGroup.T]

theorem coreSL_coreL_parabolic : IsParabolicSL (coreSL coreL) := by
  refine ⟨ModularGroup.S, -3, Or.inl ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
    coreSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coreL, lower, ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]


section Final

open CategoryTheory groupCohomology
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive (V)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (crossedCocycles)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree

variable {n : ℕ}

/-- A value of `binRep Gam3 n` as an element of `Sym^{n+1}`. -/
def bvalV (x : binRep Gam3 n) : V (n + 1) := x

/-- A cocycle of `Gamma1 3` as a crossed cocycle of the library's `core`. -/
def toCrossed (c : cocycles₁ (binRep Gam3 n)) : crossedCocycles (coreRep (n + 1) 0) :=
  ⟨fun k => bvalV (c (coreToLam k)), fun g h => by
    have hc := (mem_cocycles₁_iff c).1 c.2 (coreToLam g) (coreToLam h)
    change bvalV (c (coreToLam (g * h))) =
      bvalV (c (coreToLam g)) + coreRep (n + 1) 0 g (bvalV (c (coreToLam h)))
    have hr : coreRep (n + 1) 0 g (bvalV (c (coreToLam h))) =
        bvalV ((binRep Gam3 n).ρ (coreToLam g) (c (coreToLam h))) :=
      LinearMap.congr_fun (coreRep_eq_binRep n 0 g) _
    rw [hr, map_mul, hc]
    exact add_comm (bvalV _) (bvalV _)⟩

theorem periodCocycle_val_eq (e : ℤ) (f : S (n + 1)) (k : core) :
    (periodCocycle (n + 1) e f).val k =
      ((-1 : ℂ) ^ (n + 1)) • bvalV (holCocycle (liftL3 f) (coreToLam k)) := by
  apply Subtype.ext
  rw [Submodule.coe_smul, smul_eq_C_mul]
  exact periodCocycle_eq e f k

theorem iotaVal_val_eq (f : S (n + 1)) (k : core) :
    iotaVal (n + 1) 0 (periodCocycle (n + 1) 0 f) k =
      -bvalV (antiholCocycle (fStarGen (LamGL Gam3) gam3_J_stable (liftL3 f)) (coreToLam k)) := by
  apply Subtype.ext
  rw [Submodule.coe_neg]
  have := iotaVal_eq 0 f k
  rw [this]
  simp only [zpow_zero, neg_smul, one_smul]
  rfl


/-- **Eichler--Shimura spanning for `Γ₁(3)`, unconditional.** Every parabolic class of
`H¹(Γ₁(3), Sym^{n+1} ⊗ det⁻¹)` is a combination of holomorphic and antiholomorphic period classes
of cusp forms of weight `n + 3` for `Γ₁(3)`. -/
theorem esSpan_gam3 (n : ℕ) : ESSpan Gam3 n := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hx
  have hz : toCrossed c ∈ TwoGenerator.parabolicCocycles (coreRep (n + 1) 0) coreT coreL := by
    have key : ∀ k : core, IsParabolicSL (coreSL k) →
        (toCrossed c).val k ∈ TwoGenerator.moved (coreRep (n + 1) 0) k := by
      intro k hk
      obtain ⟨u, hu⟩ := hc (coreToLam k) hk
      refine ⟨bvalV u, ?_⟩
      have hr : coreRep (n + 1) 0 k (bvalV u) = bvalV ((binRep Gam3 n).ρ (coreToLam k) u) :=
        LinearMap.congr_fun (coreRep_eq_binRep n 0 k) _
      change coreRep (n + 1) 0 k (bvalV u) - bvalV u = bvalV (c (coreToLam k))
      rw [hr, hu]
      rfl
    exact ⟨key coreT coreSL_coreT_parabolic, key coreL coreSL_coreL_parabolic⟩
  obtain ⟨f₀, f₁, v, hv⟩ := crossed_ES (n + 1) 0 (Nat.succ_pos n) (toCrossed c) hz
  set g₀ := liftL3 f₀ with hg₀
  set g₁ := liftL3 f₁ with hg₁
  set gs₀ := fStarGen (LamGL Gam3) gam3_J_stable g₀ with hgs₀
  set gs₁ := fStarGen (LamGL Gam3) gam3_J_stable g₁ with hgs₁
  set comb : cocycles₁ (binRep Gam3 n) :=
    (((2 : ℂ)⁻¹ * (-1 : ℂ) ^ (n + 1)) • holCocycle g₀ - (2 : ℂ)⁻¹ • antiholCocycle gs₀) +
      (((2 : ℂ)⁻¹ * (-1 : ℂ) ^ (n + 1)) • holCocycle g₁ + (2 : ℂ)⁻¹ • antiholCocycle gs₁)
    with hcomb
  have h0 : H1π (binRep Gam3 n) (c - comb) = 0 := by
    rw [H1π_eq_zero_iff]
    obtain ⟨vB, hvB⟩ : ∃ vB : binRep Gam3 n, bvalV vB = v := ⟨v, rfl⟩
    refine ⟨vB, ?_⟩
    funext γ
    obtain ⟨k, rfl⟩ := coreToLam_surjective γ
    rw [d₀₁_hom_apply]
    have hr : bvalV ((binRep Gam3 n).ρ (coreToLam k) vB) = coreRep (n + 1) 0 k v := by
      rw [← hvB]
      exact (LinearMap.congr_fun (coreRep_eq_binRep n 0 k) _).symm
    have e1 := hv k
    rw [periodCocycle_val_eq, periodCocycle_val_eq, iotaVal_val_eq, iotaVal_val_eq] at e1
    change bvalV ((binRep Gam3 n).ρ (coreToLam k) vB) - bvalV vB =
      bvalV (c (coreToLam k)) - bvalV (comb (coreToLam k))
    have e2 : bvalV (comb (coreToLam k)) =
        ((2 : ℂ)⁻¹ * (-1 : ℂ) ^ (n + 1)) • bvalV (holCocycle g₀ (coreToLam k)) -
          (2 : ℂ)⁻¹ • bvalV (antiholCocycle gs₀ (coreToLam k)) +
        (((2 : ℂ)⁻¹ * (-1 : ℂ) ^ (n + 1)) • bvalV (holCocycle g₁ (coreToLam k)) +
          (2 : ℂ)⁻¹ • bvalV (antiholCocycle gs₁ (coreToLam k))) := rfl
    rw [e2, hr, hvB]
    change bvalV (c (coreToLam k)) = _ at e1
    linear_combination (norm := module) (-1 : ℂ) • e1
  have hc' : H1π (binRep Gam3 n) c = H1π (binRep Gam3 n) comb := by
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  change H1π (binRep Gam3 n) c ∈ _
  rw [hc', hcomb]
  simp only [map_add, map_sub, _root_.map_smul]
  exact Submodule.add_mem _
    (Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨g₀, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨gs₀, rfl⟩))))
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨g₁, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨gs₁, rfl⟩))))

end Final

end TernaryPeriodPolynomials.Argument.SeedC3S4c
