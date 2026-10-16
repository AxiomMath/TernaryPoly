module

public import Mathlib

@[expose] public section


/-!
# The evaluation functional of a bar `3`-cycle on `H³(B, ℚ)`

Formalized by Claude Sonnet 5.5.

For a group `B` and a finite bar `3`-chain `z` (a finitely supported function on `B³`) which is a cycle (every coboundary `dα` of a rational `2`-cochain evaluates to `0` on `z`),
`cycleFunctional z hz` is the linear functional on Mathlib's `groupCohomology (Rep.trivial ℚ B ℚ) 3` sending the class of a `3`-cocycle `θ` to `∑ z(g) θ(g)`
(`cycleFunctional_cocycleClass`).  `dTwo_apply` and `dThree_apply` give the explicit inhomogeneous differentials.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

open CategoryTheory

section Chains

variable {B : Type}


/-- Evaluation of a rational `3`-cochain on a finite `3`-chain of the bar complex. -/
def chainEval (z : (Fin 3 → B) →₀ ℚ) (θ : (Fin 3 → B) → ℚ) : ℚ := z.sum fun g c => c * θ g

/-- Evaluation on a chain as a linear map on cochains. -/
def chainEvalL (z : (Fin 3 → B) →₀ ℚ) : ((Fin 3 → B) → ℚ) →ₗ[ℚ] ℚ where
  toFun := chainEval z
  map_add' θ θ' := by
    simp only [chainEval, Pi.add_apply, mul_add]
    exact Finsupp.sum_add
  map_smul' c θ := by
    simp only [chainEval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finsupp.mul_sum]
    refine Finset.sum_congr rfl fun g _ => by ring

theorem chainEvalL_apply (z : (Fin 3 → B) →₀ ℚ) (θ : (Fin 3 → B) → ℚ) : chainEvalL z θ = chainEval z θ := rfl

theorem chainEval_add (z w : (Fin 3 → B) →₀ ℚ) (θ : (Fin 3 → B) → ℚ) :
    chainEval (z + w) θ = chainEval z θ + chainEval w θ := by
  unfold chainEval
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem chainEval_neg (z : (Fin 3 → B) →₀ ℚ) (θ : (Fin 3 → B) → ℚ) : chainEval (-z) θ = - chainEval z θ := by
  unfold chainEval
  rw [Finsupp.sum_neg_index (fun _ => by simp)]
  rw [← Finsupp.sum_neg]
  exact Finsupp.sum_congr (fun _ _ => by ring)

theorem chainEval_sub (z w : (Fin 3 → B) →₀ ℚ) (θ : (Fin 3 → B) → ℚ) :
    chainEval (z - w) θ = chainEval z θ - chainEval w θ := by
  rw [sub_eq_add_neg, chainEval_add, chainEval_neg, sub_eq_add_neg]

theorem chainEval_single (g : Fin 3 → B) (c : ℚ) (θ : (Fin 3 → B) → ℚ) : chainEval (Finsupp.single g c) θ = c * θ g := by
  unfold chainEval
  rw [Finsupp.sum_single_index (by simp)]

end Chains

variable {B : Type} [Group B]


/-- The differential from `2`-cochains to `3`-cochains with trivial rational coefficients. -/
def dTwo (f : (Fin 2 → B) → ℚ) : (Fin 3 → B) → ℚ :=
  (inhomogeneousCochains.d (Rep.trivial ℚ B ℚ) 2).hom f

theorem dTwo_apply (f : (Fin 2 → B) → ℚ) (g : Fin 3 → B) :
    dTwo f g = f ![g 1, g 2] - f ![g 0 * g 1, g 2] + f ![g 0, g 1 * g 2] - f ![g 0, g 1] := by
  have h0 : Fin.contractNth 0 (fun x1 x2 : B => x1 * x2) g = ![g 0 * g 1, g 2] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h1 : Fin.contractNth 1 (fun x1 x2 : B => x1 * x2) g = ![g 0, g 1 * g 2] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h2 : Fin.contractNth 2 (fun x1 x2 : B => x1 * x2) g = ![g 0, g 1] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h3 : (fun i : Fin 2 => g i.succ) = ![g 1, g 2] := by
    ext i; fin_cases i <;> simp
  simp [dTwo, inhomogeneousCochains.d_hom_apply, Fin.sum_univ_three, h0, h1, h2, h3]
  ring

/-- The differential from `3`-cochains to `4`-cochains with trivial rational coefficients. -/
def dThree (f : (Fin 3 → B) → ℚ) : (Fin 4 → B) → ℚ :=
  (inhomogeneousCochains.d (Rep.trivial ℚ B ℚ) 3).hom f

theorem dThree_apply (f : (Fin 3 → B) → ℚ) (g : Fin 4 → B) :
    dThree f g = f ![g 1, g 2, g 3] - f ![g 0 * g 1, g 2, g 3] + f ![g 0, g 1 * g 2, g 3] - f ![g 0, g 1, g 2 * g 3] +
      f ![g 0, g 1, g 2] := by
  have h0 : Fin.contractNth 0 (fun x1 x2 : B => x1 * x2) g = ![g 0 * g 1, g 2, g 3] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h1 : Fin.contractNth 1 (fun x1 x2 : B => x1 * x2) g = ![g 0, g 1 * g 2, g 3] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h2 : Fin.contractNth 2 (fun x1 x2 : B => x1 * x2) g = ![g 0, g 1, g 2 * g 3] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h3 : Fin.contractNth 3 (fun x1 x2 : B => x1 * x2) g = ![g 0, g 1, g 2] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h4 : (fun i : Fin 3 => g i.succ) = ![g 1, g 2, g 3] := by
    ext i; fin_cases i <;> simp
  simp [dThree, inhomogeneousCochains.d_hom_apply, Fin.sum_univ_four, h0, h1, h2, h3, h4]
  ring


/-- A finite `3`-chain is a cycle when every coboundary of a `2`-cochain evaluates to zero on it. -/
def IsCycle (z : (Fin 3 → B) →₀ ℚ) : Prop := ∀ α : (Fin 2 → B) → ℚ, chainEval z (dTwo α) = 0


/-- Descent of a linear map along a surjection whose kernel it kills. -/
def descendQ {A C D : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup C] [Module ℚ C] [AddCommGroup D] [Module ℚ D]
    (f : A →ₗ[ℚ] C) (hf : Function.Surjective f) (g : A →ₗ[ℚ] D) (h : ∀ a, f a = 0 → g a = 0) : C →ₗ[ℚ] D :=
  (Submodule.liftQ (LinearMap.ker f) g (fun a ha => h a ha)) ∘ₗ (LinearMap.quotKerEquivOfSurjective f hf).symm.toLinearMap

theorem descendQ_apply {A C D : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup C] [Module ℚ C] [AddCommGroup D]
    [Module ℚ D] (f : A →ₗ[ℚ] C) (hf : Function.Surjective f) (g : A →ₗ[ℚ] D) (h : ∀ a, f a = 0 → g a = 0) (a : A) :
    descendQ f hf g h (f a) = g a := by
  unfold descendQ
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have : (LinearMap.quotKerEquivOfSurjective f hf).symm (f a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [this]
  rfl

/-- In a short complex of modules, a cycle with zero homology class is a boundary. -/
theorem boundary_of_homologyπ_eq_zero' (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℚ)) (z : S.cycles)
    (h : S.homologyπ.hom z = 0) : ∃ x : S.X₁, S.toCycles.hom x = z := by
  have h1 := congrArg (fun t => t.hom (S.moduleCatCyclesIso.hom z)) (S.moduleCatCyclesIso_inv_π)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  have e : S.moduleCatCyclesIso.inv.hom (S.moduleCatCyclesIso.hom z) = z := by
    simp
  rw [e, h] at h1
  have h2 : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom z) = 0 := by
    have := congrArg S.moduleCatHomologyIso.hom.hom h1
    have e2 : S.moduleCatHomologyIso.hom.hom (S.moduleCatHomologyIso.inv.hom
        (S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom z))) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom z) := by
      simp
    rw [e2, map_zero] at this
    exact this.symm
  have h3 : S.moduleCatCyclesIso.hom z ∈ LinearMap.range S.moduleCatToCycles :=
    (Submodule.Quotient.mk_eq_zero _).1 h2
  obtain ⟨x, hx⟩ := h3
  refine ⟨x, ?_⟩
  have h4 := congrArg (fun t => t.hom x) S.toCycles_moduleCatCyclesIso_hom
  have h5 : S.moduleCatCyclesIso.hom (S.toCycles.hom x) = S.moduleCatCyclesIso.hom z := by
    refine Eq.trans ?_ hx
    exact h4
  exact (ConcreteCategory.bijective_of_isIso S.moduleCatCyclesIso.hom).1 h5


/-- Evaluation on the cocycles. -/
def cocycleEval (z : (Fin 3 → B) →₀ ℚ) :
    (groupCohomology.cocycles (Rep.trivial ℚ B ℚ) 3) →ₗ[ℚ] ℚ :=
  chainEvalL z ∘ₗ (groupCohomology.iCocycles (Rep.trivial ℚ B ℚ) 3).hom

theorem cocycleEval_boundary (z : (Fin 3 → B) →₀ ℚ) (hz : IsCycle z)
    (w : groupCohomology.cocycles (Rep.trivial ℚ B ℚ) 3)
    (h : (groupCohomology.π (Rep.trivial ℚ B ℚ) 3).hom w = 0) : cocycleEval z w = 0 := by
  obtain ⟨x, hx⟩ := boundary_of_homologyπ_eq_zero' ((groupCohomology.inhomogeneousCochains (Rep.trivial ℚ B ℚ)).sc 3) w h
  have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((groupCohomology.inhomogeneousCochains (Rep.trivial ℚ B ℚ)).sc 3).toCycles_i) x
  have key : ∀ i (hi : i = 2) (α : (groupCohomology.inhomogeneousCochains (Rep.trivial ℚ B ℚ)).X i),
      chainEval z (((groupCohomology.inhomogeneousCochains (Rep.trivial ℚ B ℚ)).d i 3).hom α) = 0 := by
    rintro i rfl α
    exact hz α
  have h2 := key _ (CochainComplex.prev_nat_succ 2) x
  have h3 : cocycleEval z w = chainEval z (((groupCohomology.inhomogeneousCochains (Rep.trivial ℚ B ℚ)).d ((ComplexShape.up ℕ).prev 3) 3).hom x) := by
    rw [← hx]
    exact congrArg (chainEval z) h1
  rw [h3]
  exact h2


set_option backward.isDefEq.respectTransparency false in
/-- **The evaluation functional on `H³(B, ℚ)` of a bar `3`-cycle.** -/
def cycleFunctional (z : (Fin 3 → B) →₀ ℚ) (hz : IsCycle z) :
    groupCohomology (Rep.trivial ℚ B ℚ) 3 →ₗ[ℚ] ℚ :=
  descendQ (groupCohomology.π (Rep.trivial ℚ B ℚ) 3).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance) (cocycleEval z) (cocycleEval_boundary z hz)

/-- The functional evaluates a cocycle class on the cycle. -/
theorem cycleFunctional_cocycle (z : (Fin 3 → B) →₀ ℚ) (hz : IsCycle z) (θ : (Fin 3 → B) → ℚ)
    (hθ : dThree θ = 0) :
    cycleFunctional z hz ((groupCohomology.π (Rep.trivial ℚ B ℚ) 3).hom
      (groupCohomology.cocyclesMk θ hθ)) = chainEval z θ := by
  unfold cycleFunctional
  rw [descendQ_apply]
  show chainEval z (groupCohomology.iCocycles (Rep.trivial ℚ B ℚ) 3 (groupCohomology.cocyclesMk θ hθ)) = _
  rw [groupCohomology.iCocycles_mk (A := Rep.trivial ℚ B ℚ) θ hθ]



set_option backward.isDefEq.respectTransparency false in
/-- The class of a rational `3`-cocycle in `H³(B, ℚ)`. -/
def cocycleClass (θ : (Fin 3 → B) → ℚ) (hθ : dThree θ = 0) : groupCohomology (Rep.trivial ℚ B ℚ) 3 :=
  (groupCohomology.π (Rep.trivial ℚ B ℚ) 3).hom (groupCohomology.cocyclesMk θ hθ)

theorem cycleFunctional_cocycleClass (z : (Fin 3 → B) →₀ ℚ) (hz : IsCycle z) (θ : (Fin 3 → B) → ℚ)
    (hθ : dThree θ = 0) : cycleFunctional z hz (cocycleClass θ hθ) = chainEval z θ :=
  cycleFunctional_cocycle z hz θ hθ

end TernaryPeriodPolynomials.Argument.FlagH3
