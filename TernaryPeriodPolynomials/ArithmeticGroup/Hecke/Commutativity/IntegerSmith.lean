module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.CosetDecomposition
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section


/-!
# Smith normal form for integer matrices and transposes in double cosets

`exists_eq_mul_diagonal_mul`: a nonsingular integer matrix is `A * diagonal a * Q` with
`A, Q ∈ GL_n(ℤ)` (from Mathlib's basis form of the Smith normal form).
`transpose_mem_doubleCoset`: for every `g ∈ GL₃(ℚ)`, `gᵀ ∈ GL₃(ℤ) g GL₃(ℤ)`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open Matrix

namespace TernaryPeriodPolynomials.HeckeCommutativity

variable {n : ℕ}

theorem mulVec_injective_of_det_ne_zero (X : Matrix (Fin n) (Fin n) ℤ) (hX : X.det ≠ 0) :
    Function.Injective X.mulVec := by
  intro v w h
  have hXq : (X.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [show X.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix X from rfl,
      ← RingHom.map_det, eq_intCast]
    exact_mod_cast hX
  have h0 : (X.map (Int.cast : ℤ → ℚ)) *ᵥ (fun i => ((v i - w i : ℤ) : ℚ)) = 0 := by
    funext i
    have := congrFun h i
    simp only [mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this ⊢
    have h2 : ∑ x, ((X i x : ℤ) : ℚ) * ((v x - w x : ℤ) : ℚ) =
        ((∑ x, X i x * v x - ∑ x, X i x * w x : ℤ) : ℚ) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      congr 1; funext x; ring
    rw [h2, this, sub_self, Int.cast_zero]
  have := Matrix.eq_zero_of_mulVec_eq_zero hXq h0
  funext i
  have hi := congrFun this i
  simp only [Pi.zero_apply] at hi
  have : ((v i - w i : ℤ) : ℚ) = 0 := hi
  exact_mod_cast sub_eq_zero.mp (by exact_mod_cast this)

/-- **Integer Smith normal form.** -/
theorem exists_eq_mul_diagonal_mul (X : Matrix (Fin n) (Fin n) ℤ) (hX : X.det ≠ 0) :
    ∃ A Q : Matrix (Fin n) (Fin n) ℤ, ∃ A' Q' : Matrix (Fin n) (Fin n) ℤ, ∃ a : Fin n → ℤ,
      A * A' = 1 ∧ A' * A = 1 ∧ Q * Q' = 1 ∧ Q' * Q = 1 ∧ X = A * diagonal a * Q := by
  classical
  have hinj := mulVec_injective_of_det_ne_zero X hX
  let f := Matrix.mulVecLin X
  have hfinj : Function.Injective f := hinj
  let N := LinearMap.range f
  have hrank : Module.finrank ℤ N = Module.finrank ℤ (Fin n → ℤ) :=
    LinearMap.finrank_range_of_inj hfinj
  obtain ⟨b', a, ab', hab⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq (Pi.basisFun ℤ (Fin n)) hrank
  let A : Matrix (Fin n) (Fin n) ℤ := (Pi.basisFun ℤ (Fin n)).toMatrix b'
  let A' : Matrix (Fin n) (Fin n) ℤ := b'.toMatrix (Pi.basisFun ℤ (Fin n))
  have hA : A * A' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hA' : A' * A = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hAij : ∀ i j, A i j = b' j i := by
    intro i j
    simp [A, Module.Basis.toMatrix_apply]
  -- columns of `X` lie in `N`
  have hcol : ∀ k, X *ᵥ Pi.single k 1 ∈ N := fun k => ⟨Pi.single k 1, rfl⟩
  let Q : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun j k => ab'.repr ⟨_, hcol k⟩ j
  -- preimages of the basis `ab'`
  have hpre : ∀ j, ∃ y : Fin n → ℤ, X *ᵥ y = (ab' j : Fin n → ℤ) := by
    intro j
    obtain ⟨y, hy⟩ := (ab' j).property
    exact ⟨y, hy⟩
  choose y hy using hpre
  let Y : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => y j i
  let C : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => (ab' j : Fin n → ℤ) i
  have hXY : X * Y = C := by
    apply Matrix.ext
    intro i j
    have := congrFun (hy j) i
    simp only [mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Y, C, Matrix.of_apply]
    exact this
  have hCQ : C * Q = X := by
    apply Matrix.ext
    intro i k
    have hsum := congrArg (fun v : N => (v : Fin n → ℤ) i) (ab'.sum_repr ⟨_, hcol k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hsum
    have hXk : (X *ᵥ Pi.single k 1) i = X i k := by
      simp [mulVec, dotProduct, Pi.single_apply]
    rw [hXk] at hsum
    rw [← hsum, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [C, Q, Matrix.of_apply]
    ring
  have hCA : C = A * diagonal a := by
    apply Matrix.ext
    intro i j
    simp only [C, Matrix.of_apply, mul_diagonal, hAij, hab j, Pi.smul_apply, smul_eq_mul]
    ring
  have hYQ : Y * Q = 1 := by
    have hXYQ : X * (Y * Q) = X * 1 := by rw [← Matrix.mul_assoc, hXY, hCQ, Matrix.mul_one]
    apply Matrix.ext
    intro i k
    have hk : X *ᵥ (fun i => (Y * Q) i k) = X *ᵥ (fun i => (1 : Matrix (Fin n) (Fin n) ℤ) i k) := by
      funext r
      have := congrFun (congrFun hXYQ r) k
      simpa [Matrix.mul_apply, mulVec, dotProduct] using this
    exact congrFun (hinj hk) i
  have hQY : Q * Y = 1 := mul_eq_one_comm.mp hYQ
  refine ⟨A, Q, A', Y, a, hA, hA', hQY, hYQ, ?_⟩
  rw [← hCQ, hCA]

end TernaryPeriodPolynomials.HeckeCommutativity
