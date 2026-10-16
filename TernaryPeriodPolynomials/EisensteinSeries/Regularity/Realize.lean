module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Action

@[expose] public section


/-!
# The realization map of the holomorphic model

For a finite-adelic model `M` (`FiniteModel`), a vector `F` of the Bergman space fixed by an
open compact subgroup `U` of `GL₂(𝔸_f)` takes values in the finite-dimensional space of
`U`-fixed vectors of `M.E`. Its realization is the absolutely convergent integral

`realizeU F x = ∫ ε (F w) (x · gBar w) |Im w|^(k/2) dμ_hyp(w)`,

where `gBar w = !![-Im w, Re w; 0, 1]` sends `i` to `conj w`. To keep the integrand a
continuous linear function of `F w`, the evaluation `e ↦ ε e y` on `U`-fixed vectors is
precomposed with the orthogonal projection onto them (`evalU`); on `U`-fixed vectors this is
`ε` itself (`evalU_of_mem`), so the integral does not depend on the level (`realizeU_eq_of_le`).
`realizeFun` is the realization of a smooth vector of `bergmanRep M` at a chosen level.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Complex
open TernaryPeriodPolynomials.Automorphic.SmoothVectors

namespace TernaryPeriodPolynomials.Regularity

variable {k : ℕ} (M : FiniteModel k)

theorem fixed_le_finiteSmooth {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) :
    fixedSubmodule M.σ U ≤ finiteSmooth M.σ :=
  fun _ he => mem_finiteSmooth_of_fixed M.σ hU he

/-- Evaluation at `y` of the realization of `U`-fixed vectors. -/
def evalFixed {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) (y : BinaryAdelicGL) :
    fixedSubmodule M.σ U →ₗ[ℂ] ℂ :=
  LinearMap.proj y ∘ₗ M.ε ∘ₗ Submodule.inclusion (fixed_le_finiteSmooth M hU)

/-- The orthogonal projection onto the (finite-dimensional) `U`-fixed vectors. -/
def projU {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) :
    M.E →L[ℂ] fixedSubmodule M.σ U :=
  haveI := M.finiteDimensional U hU
  (fixedSubmodule M.σ U).orthogonalProjectionOnto

theorem projU_of_mem {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) {e : M.E}
    (he : e ∈ fixedSubmodule M.σ U) : projU M hU e = ⟨e, he⟩ := by
  have := M.finiteDimensional U hU
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := fixedSubmodule M.σ U) ⟨e, he⟩

theorem norm_projU_le {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) (e : M.E) :
    ‖projU M hU e‖ ≤ ‖e‖ := by
  have := M.finiteDimensional U hU
  have h := ContinuousLinearMap.le_of_opNorm_le _
    (Submodule.orthogonalProjectionOnto_norm_le (fixedSubmodule M.σ U)) e
  rw [one_mul] at h
  exact h

/-- Evaluation at `y` on `U`-fixed vectors, as a continuous linear functional. -/
def evalFixedL {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) (y : BinaryAdelicGL) :
    fixedSubmodule M.σ U →L[ℂ] ℂ :=
  haveI := M.finiteDimensional U hU
  LinearMap.toContinuousLinearMap (evalFixed M hU y)

theorem evalFixedL_apply {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    (y : BinaryAdelicGL) (v : fixedSubmodule M.σ U) :
    evalFixedL M hU y v = M.ε ⟨v, fixed_le_finiteSmooth M hU v.2⟩ y :=
  rfl

/-- The functional `e ↦ ε (P_U e) y`, with `P_U` the orthogonal projection onto the `U`-fixed
vectors. -/
def evalU {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) (y : BinaryAdelicGL) :
    M.E →L[ℂ] ℂ :=
  (evalFixedL M hU y).comp (projU M hU)

theorem evalU_apply {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) (y : BinaryAdelicGL)
    (e : M.E) : evalU M hU y e = evalFixedL M hU y (projU M hU e) :=
  rfl

theorem evalU_of_mem {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) (y : BinaryAdelicGL)
    {e : M.E} (he : e ∈ fixedSubmodule M.σ U) :
    evalU M hU y e = M.ε ⟨e, fixed_le_finiteSmooth M hU he⟩ y := by
  rw [evalU_apply, projU_of_mem M hU he, evalFixedL_apply]

/-- The realization at level `U`: `∫ ε (F w) (x · gBar w) |Im w|^(k/2) dμ_hyp(w)`. -/
def realizeU {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) (F : BergmanSpace k M.E)
    (x : BinaryAdelicGL) : ℂ :=
  ∫ w, evalU M hU (x * atInfinity (gBar w)) (F w) * ((|w.im| ^ ((k : ℝ) / 2) : ℝ) : ℂ)
    ∂hypMeasure

/-- Passing to a smaller level does not change the realization of a vector whose values are
fixed by the larger level. -/
theorem realizeU_eq_of_le {U V : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    (hV : IsOpenCompact V) (hVU : V ≤ U) {F : BergmanSpace k M.E}
    (hF : ∀ w, F w ∈ fixedSubmodule M.σ U) : realizeU M hU F = realizeU M hV F := by
  funext x
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [evalU_of_mem M hU _ (hF w),
    evalU_of_mem M hV _ (fixedSubmodule_anti M.σ hVU (hF w))]

variable {M}

/-- A level of a smooth vector: an open compact subgroup of `GL₂(𝔸_f)` fixing it. -/
def level (F : smoothSubmodule (bergmanRep M)) : Subgroup BinaryFiniteGL :=
  (mem_smoothSubmodule.mp F.property).2.choose

theorem level_isOpenCompact (F : smoothSubmodule (bergmanRep M)) : IsOpenCompact (level F) :=
  ⟨(mem_smoothSubmodule.mp F.property).2.choose_spec.1,
    (mem_smoothSubmodule.mp F.property).2.choose_spec.2.1⟩

theorem level_fixed (F : smoothSubmodule (bergmanRep M)) (u : level F) :
    bergmanRep M (atFinite u.val) F.val = F.val :=
  (mem_smoothSubmodule.mp F.property).2.choose_spec.2.2 u

/-- The values of a vector fixed by `U` are `U`-fixed. -/
theorem apply_mem_fixed {U : Subgroup BinaryFiniteGL} {F : BergmanSpace k M.E}
    (hF : ∀ u : U, bergmanRep M (atFinite u.val) F = F) (w : ℂ) :
    F w ∈ fixedSubmodule M.σ U :=
  fun u => bergmanRep_apply_fixed M (hF u) w

/-- The realization of a smooth vector, at its chosen level. -/
def realizeFun (F : smoothSubmodule (bergmanRep M)) : BinaryAdelicGL → ℂ :=
  realizeU M (level_isOpenCompact F) F.val

/-- The realization of a smooth vector may be computed at any level fixing its values. -/
theorem realizeFun_eq (F : smoothSubmodule (bergmanRep M)) {U : Subgroup BinaryFiniteGL}
    (hU : IsOpenCompact U) (hF : ∀ w, (F.val : BergmanSpace k M.E) w ∈ fixedSubmodule M.σ U) :
    realizeFun F = realizeU M hU F.val := by
  have hW := (level_isOpenCompact F).inf hU
  rw [realizeFun, realizeU_eq_of_le M (level_isOpenCompact F) hW inf_le_left
      (apply_mem_fixed (level_fixed F)),
    realizeU_eq_of_le M hU hW inf_le_right hF]

/-- The realization of a smooth vector may be computed at any level fixing it. -/
theorem realizeFun_eq_of_fixed (F : smoothSubmodule (bergmanRep M)) {U : Subgroup BinaryFiniteGL}
    (hU : IsOpenCompact U) (hF : ∀ u : U, bergmanRep M (atFinite u.val) F.val = F.val) :
    realizeFun F = realizeU M hU F.val :=
  realizeFun_eq F hU (apply_mem_fixed hF)

end TernaryPeriodPolynomials.Regularity

end
