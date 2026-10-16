module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.GL3
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlacePadicCoordinates

@[expose] public section


/-!
# Integral lift of `ι_v(k)` to `GL₃(IntegralAdeles)` (part 3a)

`IntGL3 v X` is the `3 × 3` analogue of `LocalAdelic.IntGL`: `X` is invertible with entries and
inverse entries in `O_v`.  `mem_gl3_integral_of_intGL3` says that a finite-adelic `GL₃` element that is
`GL₃(O_w)` at every place lifts to `GL₃(IntegralAdeles)`.  Consequently `ι_v(K)` lifts whenever
`K ∈ GL₃(O_v)` (`ιGL3_mem_integral`), and the norm form `ιGL3_mem_integral_of_norm` is the form used with
`SeedK0.exists_k0`.  `ιGL3_mul` is multiplicativity of `ι_v` as a group hom.

Formalized by Claude Haiku 5.5.
-/

open Matrix
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (OS mem_iff_norm)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.SphericalDetection.Helpers (finiteCompletionPadicEquiv)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift

variable {v : FinitePlace}

/-- `GL₃`-integrality at a place: the `3 × 3` analogue of `LocalAdelic.IntGL`. -/
def IntGL3 (w : FinitePlace) (X : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) : Prop :=
  IsUnit X.det ∧ (∀ i j, X i j ∈ OS w) ∧ (∀ i j, X⁻¹ i j ∈ OS w)

theorem intGL3_one (w : FinitePlace) : IntGL3 w 1 := by
  refine ⟨by rw [Matrix.det_one]; exact isUnit_one, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.one_apply]
    split_ifs
    · exact (OS w).one_mem
    · exact (OS w).zero_mem
  · rw [show (1 : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ))⁻¹ = 1 from
      Matrix.inv_eq_right_inv (by rw [Matrix.one_mul]), Matrix.one_apply]
    split_ifs
    · exact (OS w).one_mem
    · exact (OS w).zero_mem

/-- An element of `GL₃(ℚ_v)` which is `GL₃(O_w)` at every place lifts to `GL₃(𝔸_f^∞)` with integral
entries: the lift has entries `(evM3 w g)_{ij}` at each place `w`. -/
theorem mem_gl3_integral_of_intGL3 (g : GeneralLinearGroup (Fin 3) FiniteAdeles)
    (hX : ∀ w : FinitePlace, IntGL3 w (evM3 w g.val)) :
    ∃ gI : GeneralLinearGroup (Fin 3) IntegralAdeles,
      GeneralLinearGroup.map integralEmbedding gI = g := by
  let N : Matrix (Fin 3) (Fin 3) IntegralAdeles :=
    fun i j w => ⟨(evM3 w g.val) i j, (hX w).2.1 i j⟩
  let Ni : Matrix (Fin 3) (Fin 3) IntegralAdeles :=
    fun i j w => ⟨(evM3 w g.val)⁻¹ i j, (hX w).2.2 i j⟩
  have hevP : ∀ w, evM3 w (N.map integralEmbedding) = evM3 w g.val :=
    fun w => Matrix.ext fun _ _ => rfl
  have hevQ : ∀ w, evM3 w (Ni.map integralEmbedding) = (evM3 w g.val)⁻¹ :=
    fun w => Matrix.ext fun _ _ => rfl
  have hPQ : (N.map integralEmbedding) * (Ni.map integralEmbedding) = 1 := by
    apply ext_of_evM3
    intro w
    have hmul : evM3 w ((N.map integralEmbedding) * (Ni.map integralEmbedding)) =
        evM3 w (N.map integralEmbedding) * evM3 w (Ni.map integralEmbedding) := by
      unfold evM3
      exact Matrix.map_mul
    rw [hmul, hevP w, hevQ w, Matrix.mul_nonsing_inv _ (hX w).1]
    unfold evM3
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  have hQP : (Ni.map integralEmbedding) * (N.map integralEmbedding) = 1 := by
    apply ext_of_evM3
    intro w
    have hmul : evM3 w ((Ni.map integralEmbedding) * (N.map integralEmbedding)) =
        evM3 w (Ni.map integralEmbedding) * evM3 w (N.map integralEmbedding) := by
      unfold evM3
      exact Matrix.map_mul
    rw [hmul, hevP w, hevQ w, Matrix.nonsing_inv_mul _ (hX w).1]
    unfold evM3
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  have hNNi : N * Ni = 1 := by
    apply Matrix.map_injective integralEmbedding_injective
    show (N * Ni).map integralEmbedding = (1 : Matrix _ _ IntegralAdeles).map integralEmbedding
    rw [Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hNiN : Ni * N = 1 := by
    apply Matrix.map_injective integralEmbedding_injective
    show (Ni * N).map integralEmbedding = (1 : Matrix _ _ IntegralAdeles).map integralEmbedding
    rw [Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  let gI : GeneralLinearGroup (Fin 3) IntegralAdeles := ⟨N, Ni, hNNi, hNiN⟩
  exact ⟨gI, Units.ext (Matrix.ext fun i j => RestrictedProduct.ext _ _ fun w => rfl)⟩

/-- `ι_v` is multiplicative on `GL₃`. -/
theorem ιGL3_mul (w : FinitePlace) (A B : GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ)) :
    ιGL3 w (A * B) = ιGL3 w A * ιGL3 w B := by
  apply Units.ext
  show ιMat3 w (A * B).val = ιMat3 w A.val * ιMat3 w B.val
  rw [Units.val_mul, ιMat3_mul]

/-- **Integral lift of `ι_v(K)`.** If `K ∈ GL₃(O_v)`, then `ι_v(K)` is the image of an element of
`GL₃(IntegralAdeles)`: at `v` it is `K`, and at every other place it is the identity. -/
theorem ιGL3_mem_integral (w : FinitePlace) (K : GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hK : IntGL3 w K.val) :
    ∃ kI : GeneralLinearGroup (Fin 3) IntegralAdeles,
      GeneralLinearGroup.map integralEmbedding kI = ιGL3 w K := by
  apply mem_gl3_integral_of_intGL3
  intro u
  rw [ιGL3_val]
  by_cases hu : u = w
  · subst hu
    rw [evM3_ιMat3_self]
    exact hK
  · rw [evM3_ιMat3_ne w u hu]
    exact intGL3_one u

/-- Norm form of `GL₃(O_v)`: entries of `K` and of `K⁻¹` have norm at most one at `v`
(through the place-`v` `p`-adic coordinate). -/
theorem intGL3_of_norm (w : FinitePlace) (X : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ))
    (hdet : IsUnit X.det)
    (hX : ∀ i j, ‖finiteCompletionPadicEquiv w (X i j)‖ ≤ 1)
    (hXi : ∀ i j, ‖finiteCompletionPadicEquiv w (X⁻¹ i j)‖ ≤ 1) : IntGL3 w X :=
  ⟨hdet, fun i j => (mem_iff_norm w _).2 (hX i j), fun i j => (mem_iff_norm w _).2 (hXi i j)⟩

/-- **Integral lift of `ι_v(K)`, norm form.** For `K ∈ GL₃(ℚ_v)` whose entries and inverse entries
have norm at most one in the place-`v` `p`-adic coordinate, `ι_v(K)` lifts to `GL₃(IntegralAdeles)`. -/
theorem ιGL3_mem_integral_of_norm (w : FinitePlace) (K : GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hX : ∀ i j, ‖finiteCompletionPadicEquiv w (K.val i j)‖ ≤ 1)
    (hXi : ∀ i j, ‖finiteCompletionPadicEquiv w (K⁻¹.val i j)‖ ≤ 1) :
    ∃ kI : GeneralLinearGroup (Fin 3) IntegralAdeles,
      GeneralLinearGroup.map integralEmbedding kI = ιGL3 w K := by
  have hdet : IsUnit K.val.det :=
    Matrix.isUnit_det_of_right_inverse (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  exact ιGL3_mem_integral w K (intGL3_of_norm w K.val hdet hX (by simpa using hXi))

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift

end
