module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellRep

@[expose] public section


/-!
# Exactness of the rational cellular complex

The augmented cellular permutation complex `cellPermComplex` of the well-rounded retract is exact over `ℚ`:
the library's exactness theorem for the complex `Γ(3)`-resolution (`wellRounded.boundary_exact`,
`wellRounded.surj`) descends from `ℂ` to `ℚ` (the boundary has rational entries, `castC_incQ`, so a
`ℚ`-linear retraction `ℂ → ℚ` applied coordinatewise, `retractChains`, turns a complex preimage into a rational
one: `descent`).  The result is `exact_zero`, `exact_succ`, `augQ_surj` and the exactness of the cellular
permutation complex above degree zero (`cellPerm_exactAt`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

open CategoryTheory Finsupp GeneralEisenstein TernaryPoly TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularLocalHomology TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing

theorem exists_ratRetract : ∃ r : ℂ →ₗ[ℚ] ℚ, ∀ q : ℚ, r (q : ℂ) = q := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.mpr (fun a b h => by simpa using h))
  refine ⟨r, fun q => ?_⟩
  have := LinearMap.congr_fun hr q
  simpa using this

/-- A `ℚ`-linear retraction `ℂ → ℚ` of the inclusion. -/
def ratRetract : ℂ →ₗ[ℚ] ℚ := Classical.choose exists_ratRetract

theorem ratRetract_cast (q : ℚ) : ratRetract (q : ℂ) = q := Classical.choose_spec exists_ratRetract q

/-- The coordinatewise retraction of complex chains to rational chains. -/
def retractChains (α : Type) : (α →₀ ℂ) →ₗ[ℚ] (α →₀ ℚ) :=
  Finsupp.mapRange.linearMap ratRetract

theorem retractChains_apply {α : Type} (w : α →₀ ℂ) (a : α) : retractChains α w a = ratRetract (w a) := by
  simp [retractChains]

theorem retractChains_castC {α : Type} (z : α →₀ ℚ) : retractChains α (castC α z) = z := by
  ext a
  rw [retractChains_apply, castC_apply, ratRetract_cast]

theorem retractChains_comm {S T : Type} (F : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ)) (f : (S →₀ ℚ) →ₗ[ℚ] (T →₀ ℚ))
    (hF : ∀ s, F (single s 1) = castC T (f (single s 1))) (w : S →₀ ℂ) :
    retractChains T (F w) = f (retractChains S w) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | single s a =>
    have e : (single s a : S →₀ ℂ) = a • single s 1 := by simp
    rw [e, map_smul, hF]
    ext t
    rw [retractChains_apply]
    have e2 : retractChains S (a • single s (1 : ℂ)) = single s (ratRetract a) := by
      ext s'
      rw [retractChains_apply]
      by_cases h : s = s'
      · subst h; simp
      · simp [h]
    rw [e2]
    have e3 : (single s (ratRetract a) : S →₀ ℚ) = ratRetract a • single s 1 := by simp
    rw [e3, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, castC_apply, smul_eq_mul, Rat.smul_def]
    rw [mul_comm, ← Rat.smul_def, map_smul, smul_eq_mul, Rat.cast_id, mul_comm]

theorem comm_castC {S T : Type} (F : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ)) (f : (S →₀ ℚ) →ₗ[ℚ] (T →₀ ℚ))
    (hF : ∀ s, F (single s 1) = castC T (f (single s 1))) (z : S →₀ ℚ) :
    F (castC S z) = castC T (f z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | single s q =>
    have e : (single s q : S →₀ ℚ) = q • single s 1 := by simp
    have e' : castC S (single s q) = (q : ℂ) • single s 1 := by simp [castC_single]
    rw [e', map_smul, hF, e, map_smul, map_smul]
    ext t
    simp [castC_apply, Rat.smul_def]

/-- Descent of a preimage from `ℂ` to `ℚ`. -/
theorem descent {S T : Type} (F : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ)) (f : (S →₀ ℚ) →ₗ[ℚ] (T →₀ ℚ))
    (hF : ∀ s, F (single s 1) = castC T (f (single s 1))) (z : T →₀ ℚ) (w : S →₀ ℂ)
    (h : F w = castC T z) : ∃ y, f y = z :=
  ⟨retractChains S w, by rw [← retractChains_comm F f hF, h, retractChains_castC]⟩

/-- The rational augmentation on grade-zero chains. -/
def augQ : (Graded 0 →₀ ℚ) →ₗ[ℚ] ℚ := EQ ∘ₗ incl 0

theorem augQ_single (C : Graded 0) : augQ (single C 1) = epsQ C.1 := by
  simp [augQ, incl, EQ]

theorem augQ_dLin : augQ ∘ₗ dLin 0 = 0 := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply, augQ, LinearMap.comp_apply, incl_dLin, ← LinearMap.comp_apply EQ LQ,
    EQ_LQ]
  rfl

/-- The complex boundary of the library's free resolution, in the types of this file. -/
def bdry (k : ℕ) : (Graded (k + 1) →₀ ℂ) →ₗ[ℂ] (Graded k →₀ ℂ) :=
  wellRounded.proj k ∘ₗ wellRounded.δ ∘ₗ wellRounded.incl (k + 1)

theorem bdry_single (k : ℕ) (s : Graded (k + 1)) :
    bdry k (single s 1) = castC (Graded k) (dLin k (single s 1)) := by
  have e : wellRounded.incl (k + 1) (single s 1) = (single s.1 1 : Cell →₀ ℂ) :=
    wellRounded.incl_single (k + 1) s 1
  change wellRounded.proj k (δC (wellRounded.incl (k + 1) (single s 1))) = _
  rw [e, ← castC_incQ]
  ext D
  refine (wellRounded.proj_apply k (castC Cell (incQ s.1)) D).trans ?_
  simp only [dLin, linearCombination_single, one_smul]
  rfl

theorem exact_succ (k : ℕ) (z : Graded (k + 1) →₀ ℚ) (hz : dLin k z = 0) :
    ∃ y, dLin (k + 1) y = z := by
  have h1 : bdry k (castC (Graded (k + 1)) z) = 0 := by
    rw [comm_castC (bdry k) (dLin k) (bdry_single k), hz, map_zero]
  have h2 : castC (Graded (k + 1)) z ∈ LinearMap.ker (bdry k) := h1
  obtain ⟨w, hw⟩ : castC (Graded (k + 1)) z ∈ LinearMap.range (bdry (k + 1)) :=
    wellRounded.boundary_exact (k + 1) h2
  exact descent (bdry (k + 1)) (dLin (k + 1)) (bdry_single (k + 1)) z w hw

theorem incl_castC (n : ℕ) (z : Graded n →₀ ℚ) :
    castC Cell (incl n z) = wellRounded.incl n (castC (Graded n) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact (map_zero (wellRounded.incl n)).symm
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv]
    exact (map_add (wellRounded.incl n) _ _).symm.trans
      (congrArg (wellRounded.incl n) (map_add (castC (Graded n)) u v).symm)
  | single C q =>
    rw [incl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, castC_single, castC_single]
    exact (wellRounded.incl_single n C q).symm

theorem exact_zero (z : Graded 0 →₀ ℚ) (hz : augQ z = 0) : ∃ y, dLin 0 y = z := by
  have h3 : wellRounded.ε (wellRounded.incl 0 (castC (Graded 0) z)) = ((augQ z : ℚ) : ℂ) :=
    (congrArg wellRounded.ε (incl_castC 0 z).symm).trans (εC_castC (incl 0 z))
  have h1 : (wellRounded.boundary 0) (castC (Graded 0) z) = 0 := by
    have e : (wellRounded.boundary 0) (castC (Graded 0) z) =
        (wellRounded.ε (wellRounded.incl 0 (castC (Graded 0) z))) • (single () 1 : Unit →₀ ℂ) := rfl
    refine e.trans ?_
    rw [h3, hz, Rat.cast_zero, zero_smul]
    rfl
  obtain ⟨w, hw⟩ : castC (Graded 0) z ∈ LinearMap.range (bdry 0) :=
    wellRounded.boundary_exact 0 (LinearMap.mem_ker.mpr h1)
  exact descent (bdry 0) (dLin 0) (bdry_single 0) z w hw

theorem augQ_surj : ∃ C : Graded 0, epsQ C.1 ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x : Cell, εC (single x 1) ≠ 0 := wellRounded.surj
  have hg : x.grade = 0 := by
    by_contra h
    exact hx (wellRounded.ε_grade x h)
  refine ⟨⟨x, hg⟩, ?_⟩
  intro h
  apply hx
  rw [εC_single, epsF_eq]
  rw [h]
  simp


theorem cellD_hom_apply (n : ℕ) (z : MonoidAlgebra ℚ (Graded (n + 1))) :
    (cellD n).hom z = (MonoidAlgebra.coeffLinearEquiv ℚ).symm
      (dLin n (MonoidAlgebra.coeffLinearEquiv ℚ z)) := rfl

theorem cellD_exact (n : ℕ) (x : MonoidAlgebra ℚ (Graded (n + 1))) (hx : (cellD n).hom x = 0) :
    ∃ y : MonoidAlgebra ℚ (Graded (n + 2)), (cellD (n + 1)).hom y = x := by
  rw [cellD_hom_apply] at hx
  have hx2 : dLin n (MonoidAlgebra.coeffLinearEquiv ℚ x) = 0 := by
    simpa using congrArg (MonoidAlgebra.coeffLinearEquiv ℚ) hx
  obtain ⟨y, hy⟩ := exact_succ n _ hx2
  refine ⟨(MonoidAlgebra.coeffLinearEquiv ℚ).symm y, ?_⟩
  rw [cellD_hom_apply, LinearEquiv.apply_symm_apply, hy, LinearEquiv.symm_apply_apply]

theorem cellPerm_d (n : ℕ) : cellPermComplex.d (n + 1) n = cellD n := ChainComplex.of_d _ _ _

theorem cellPerm_exactAt (n : ℕ) : cellPermComplex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply (ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (Rep ℚ principalSix) (ModuleCat ℚ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx1 : ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ)).map
      (cellPermComplex.d (n + 1) n)).hom x = 0 := hx
  rw [cellPerm_d] at hx1
  obtain ⟨y, hy⟩ := cellD_exact n x hx1
  refine ⟨y, ?_⟩
  change ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ)).map
      (cellPermComplex.d (n + 2) (n + 1))).hom y = x
  rw [cellPerm_d]
  exact hy

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
