module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.FrameMetric
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Datum

@[expose] public section


/-!
# The Hodge datum of `Sym^m`

Foundation file of the unconditional Eichler--Shimura route.  The representation `symRep` and the unitary frame `frameS` of the Hodge metric give the
`HodgeDatum` of the `L²` Hodge projection (`L2.HodgeDatum`) for the coefficient space `ℂ^{m+1}` of
`Sym^m` in monomial coordinates: `ρ = toEuclideanCLM ∘ symRep`, `S z = toEuclideanCLM (frameS m z)`
(`hodgeDatumSym`).  Smoothness is `contDiffOn_frameS`, invertibility `isUnit_frameS`, and the
pointwise unitarity of `ρ` is `frameS_equiv` together with `inner_unitary`.

Formalized by Claude Sonnet 5.5.
-/

open Complex Matrix
open scoped MatrixGroups ContDiff InnerProductSpace
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

variable (m : ℕ)

theorem kap_pos (j : Fin (m + 1)) : 0 < kap m (j : ℕ) := by
  unfold kap
  have : (0 : ℝ) < (m.choose j : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  positivity

theorem frameS_apply (z : ℂ) (i j : Fin (m + 1)) :
    frameS m z i j = ((Real.sqrt (z.im ^ m * kap m (i : ℕ)) : ℝ) : ℂ) * frameT m z i j := by
  unfold frameS
  rw [Matrix.diagonal_mul]

theorem contDiffOn_frameS (i j : Fin (m + 1)) :
    ContDiffOn ℝ ∞ (fun z : ℂ => frameS m z i j) U := by
  simp_rw [frameS_apply]
  have h1 : ContDiffOn ℝ ∞ (fun z : ℂ => z.im ^ m * kap m (i : ℕ)) U :=
    ((Complex.imCLM.contDiff.pow m).mul contDiff_const).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun z : ℂ => Real.sqrt (z.im ^ m * kap m (i : ℕ))) U :=
    h1.sqrt (fun z hz => by
      have : 0 < z.im := hz
      exact (mul_pos (pow_pos this _) (kap_pos m i)).ne')
  have h3 : ContDiffOn ℝ ∞ (fun z : ℂ => ((Real.sqrt (z.im ^ m * kap m (i : ℕ)) : ℝ) : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h2
  exact h3.mul ((contDiffOn_frameT m i j).of_le (by simp))


/-- Smoothness of the operator field attached to a smooth matrix field. -/
theorem contDiffOn_toCLM {d : ℕ} {A : ℂ → Matrix (Fin d) (Fin d) ℂ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) U) :
    ContDiffOn ℝ ∞ (fun z => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (A z)) U := by
  have key : ∀ (c : ℝ) (M : Matrix (Fin d) (Fin d) ℂ),
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (c • M) =
        c • Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M := fun c M => by
    rw [show c • M = (c : ℂ) • M from (Complex.coe_smul c M).symm, map_smul]
    exact Complex.coe_smul (E := L2.Wd d →L[ℂ] L2.Wd d) c _
  let Φ : (Fin d → Fin d → ℂ) →ₗ[ℝ] (L2.Wd d →L[ℂ] L2.Wd d) :=
    { toFun := fun M => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M
      map_add' := fun M N => map_add _ M N
      map_smul' := fun c M => key c M }
  let Φc : (Fin d → Fin d → ℂ) →L[ℝ] (L2.Wd d →L[ℂ] L2.Wd d) := LinearMap.toContinuousLinearMap Φ
  have h : ContDiffOn ℝ ∞ (fun z => (fun i j => A z i j : Fin d → Fin d → ℂ)) U :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => hA i j
  exact (Φc.contDiff.comp_contDiffOn h :)


theorem isUnit_frameS {z : ℂ} (hz : z ∈ U) : IsUnit (frameS m z) := by
  have hy : 0 < z.im := hz
  unfold frameS
  refine IsUnit.mul ?_ ⟨⟨frameT m z, frameE m z, frameT_mul_frameE m z hy,
    frameE_mul_frameT m z hy⟩, rfl⟩
  rw [Matrix.isUnit_diagonal]
  refine Pi.isUnit_iff.2 fun j => ?_
  have : 0 < Real.sqrt (z.im ^ m * kap m (j : ℕ)) :=
    Real.sqrt_pos.2 (mul_pos (pow_pos hy _) (kap_pos m j))
  exact (Ne.isUnit (by exact_mod_cast this.ne'))

theorem inner_unitary {d : ℕ} {K : Matrix (Fin d) (Fin d) ℂ} (hK : star K * K = 1)
    (x y : L2.Wd d) :
    ⟪Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) K x,
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) K y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_left]
  have : ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) K) *
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) K = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_mul, hK, map_one]
  have h2 := congrArg (fun T : L2.Wd d →L[ℂ] L2.Wd d => T x) this
  simpa using congrArg (fun w => ⟪w, y⟫_ℂ) h2

/-- The matrix-to-operator map as a monoid homomorphism. -/
def toCLMHom (d : ℕ) : Matrix (Fin d) (Fin d) ℂ →* (L2.Wd d →L[ℂ] L2.Wd d) where
  toFun := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  map_one' := map_one _
  map_mul' := map_mul _

/-- The Hodge datum of `Sym^m`, in the convention of the `L²` Hodge projection: the operators
are those of `symRep` and of the unitary frame `frameS`. -/
def hodgeDatumSym (Γ : Subgroup SL(2, ℤ)) : L2.HodgeDatum Γ (m + 1) where
  ρ := (toCLMHom (m + 1)).comp ((symRep m).comp Γ.subtype)
  S z := Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) (frameS m z)
  S_smooth := contDiffOn_toCLM fun i j => contDiffOn_frameS m i j
  S_unit z hz := (isUnit_frameS m hz).map _
  S_equiv γ z hz u v := by
    obtain ⟨K, hK, hKe⟩ := frameS_equiv m (γ : SL(2, ℤ)) hz
    have key : ∀ w : L2.Wd (m + 1),
        Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) (frameS m (mob (γ : SL(2, ℤ)) z))
          (toCLMHom (m + 1) (symRep m (γ : SL(2, ℤ))) w) =
        Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) K
          (Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) (frameS m z) w) := fun w => by
      have h := congrArg (fun A => Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) A w) hKe
      simp only [map_mul, mul_apply_eq_comp] at h
      exact h
    have h := inner_unitary hK (Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) (frameS m z) u)
      (Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) (frameS m z) v)
    rw [← key u, ← key v] at h
    exact h

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
