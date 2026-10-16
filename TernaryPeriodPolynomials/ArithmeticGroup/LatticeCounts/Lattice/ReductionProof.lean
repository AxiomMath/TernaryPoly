module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.Adelic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FiniteReduction

@[expose] public section


/-!
# Global lattice reduction: `LatticeReductionExists`

Formalized by Claude Haiku 5.5.

Given `gf ∈ GL₂(𝔸_f)`, the bad set `T` of places where `gf` or `gf⁻¹` is not integral is finite.
Induction over finite sets of places multiplies in one local step (`LocalAdelic.local_step`) at
a time; the composed rational matrix `q` satisfies `q_v gf_v ∈ GL₂(O_v)` at every place `v`.
Then `γ = q` (with `det q > 0`) and the integral matrix `N` give `γ gf ∈ GL₂(ℤ̂)`.
-/

open Matrix
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof

/-- Evaluation of a finite-adelic matrix at the place `v`. -/
def evM (v : FinitePlace) (M : Matrix (Fin 2) (Fin 2) FiniteAdeles) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
  M.map (finiteEvaluation v)

/-- A rational matrix seen in the local field `K_v`. -/
def qv (v : FinitePlace) (q : Matrix (Fin 2) (Fin 2) ℚ) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
  q.map (algebraMap ℚ (v.adicCompletion ℚ))

/-- The place `v` is good for the pair `M`, `Mi`: all entries of both are integral at `v`. -/
def GoodPl (M Mi : Matrix (Fin 2) (Fin 2) FiniteAdeles) (v : FinitePlace) : Prop :=
  ∀ i j, M i j v ∈ OS v ∧ Mi i j v ∈ OS v

theorem intGL_of_right_inverse {v : FinitePlace}
    {X Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (hX : ∀ i j, X i j ∈ OS v) (hY : ∀ i j, Y i j ∈ OS v) (h : X * Y = 1) : IntGL v X :=
  ⟨Matrix.isUnit_det_of_right_inverse h, hX, by rw [Matrix.inv_eq_right_inv h]; exact hY⟩

theorem intGL_evM_of_good (M Mi : Matrix (Fin 2) (Fin 2) FiniteAdeles) (hM : M * Mi = 1)
    (v : FinitePlace) (hG : GoodPl M Mi v) : IntGL v (evM v M) := by
  refine intGL_of_right_inverse (Y := evM v Mi) (fun i j => (hG i j).1) (fun i j => (hG i j).2) ?_
  unfold evM
  rw [← Matrix.map_mul, hM]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem local_qv_det_unit (v : FinitePlace) (q : Matrix (Fin 2) (Fin 2) ℚ)
    (M : Matrix (Fin 2) (Fin 2) FiniteAdeles) (hq : 0 < q.det) (hM : IsUnit M.det) :
    IsUnit (qv v q * evM v M).det := by
  rw [Matrix.det_mul]
  refine IsUnit.mul ?_ ?_
  · have h : (qv v q).det = algebraMap ℚ (v.adicCompletion ℚ) q.det :=
      (RingHom.map_det (algebraMap ℚ (v.adicCompletion ℚ)) q).symm
    rw [h]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hq.ne')
  · have h : (evM v M).det = finiteEvaluation v M.det :=
      (RingHom.map_det (finiteEvaluation v) M).symm
    rw [h]
    exact hM.map (finiteEvaluation v)

/-- One induction step: multiply in the local step at a new place `v0`. -/
theorem step (M : Matrix (Fin 2) (Fin 2) FiniteAdeles) (hM : IsUnit M.det)
    (S : Finset FinitePlace) (v0 : FinitePlace) (hv0 : v0 ∉ S)
    (q : Matrix (Fin 2) (Fin 2) ℚ) (hqdet : 0 < q.det)
    (hq1 : ∀ w, w ∉ S → IntGL w (qv w q))
    (hq2 : ∀ v ∈ S, IntGL v (qv v q * evM v M)) :
    ∃ q' : Matrix (Fin 2) (Fin 2) ℚ, 0 < q'.det ∧
      (∀ w, w ∉ insert v0 S → IntGL w (qv w q')) ∧
      (∀ v ∈ insert v0 S, IntGL v (qv v q' * evM v M)) := by
  obtain ⟨ql, hl1, hl2, hl3, hint⟩ :=
    local_step v0 (qv v0 q * evM v0 M) (local_qv_det_unit v0 q M hqdet hM)
  refine ⟨ql * q, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact mul_pos hl1 hqdet
  · intro w hw
    have hwv : w ≠ v0 := fun h => hw (by rw [h]; exact Finset.mem_insert_self v0 S)
    have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
    have hmul : qv w (ql * q) = qv w ql * qv w q := by
      unfold qv
      rw [Matrix.map_mul]
    rw [hmul]
    exact intGL_mul (intGL_of_denom v0 w hwv ql hl2 hl3) (hq1 w hwS)
  · intro v hv
    have hmul : qv v (ql * q) * evM v M = qv v ql * (qv v q * evM v M) := by
      unfold qv evM
      rw [Matrix.map_mul, Matrix.mul_assoc]
    rw [hmul]
    rcases Finset.mem_insert.1 hv with h | hvS
    · rw [h]
      exact hint
    · have hvv0 : v ≠ v0 := fun h => hv0 (by rw [← h]; exact hvS)
      exact intGL_mul (intGL_of_denom v0 v hvv0 ql hl2 hl3) (hq2 v hvS)

/-- The composed rational matrix over any finite set of places. -/
theorem exists_matrix (M Mi : Matrix (Fin 2) (Fin 2) FiniteAdeles) (hM : M * Mi = 1)
    (S : Finset FinitePlace) :
    ∃ q : Matrix (Fin 2) (Fin 2) ℚ, 0 < q.det ∧
      (∀ w, w ∉ S → IntGL w (qv w q)) ∧ (∀ v ∈ S, IntGL v (qv v q * evM v M)) := by
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_right_inverse hM
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_, fun w _ => ?_, fun v hv => by simp at hv⟩
    · rw [Matrix.det_one]
      exact zero_lt_one
    · have h1 : qv w 1 = 1 := by
        unfold qv
        exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [h1]
      exact intGL_one w
  | @insert v0 S hv0 ih =>
    obtain ⟨q, hqdet, hq1, hq2⟩ := ih
    exact step M hdet S v0 hv0 q hqdet hq1 hq2

theorem evM_qFA (v : FinitePlace) (q : Matrix (Fin 2) (Fin 2) ℚ)
    (M : Matrix (Fin 2) (Fin 2) FiniteAdeles) :
    ((q.map (algebraMap ℚ FiniteAdeles)) * M).map (finiteEvaluation v) =
      qv v q * evM v M := by
  rw [Matrix.map_mul]
  unfold qv evM
  congr 1

/-- The global input `LatticeReductionExists`. -/
theorem latticeReductionExists : LatticeReductionExists := by
  intro gf
  have hM : gf.val * (gf⁻¹).val = 1 := Units.mul_inv gf
  have hall : ∀ᶠ v in Filter.cofinite, ∀ i j, gf.val i j v ∈ OS v ∧ (gf⁻¹).val i j v ∈ OS v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      (gf.val i j).2.and ((gf⁻¹).val i j).2
  have hT : {v : FinitePlace | ¬ GoodPl gf.val (gf⁻¹).val v}.Finite :=
    Filter.eventually_cofinite.1 hall
  obtain ⟨q, hqdet, hq1, hq2⟩ := exists_matrix gf.val (gf⁻¹).val hM hT.toFinset
  have hX : ∀ w, IntGL w (qv w q * evM w gf.val) := by
    intro w
    by_cases hw : w ∈ hT.toFinset
    · exact hq2 w hw
    · have hG : GoodPl gf.val (gf⁻¹).val w := by
        by_contra h
        exact hw ((Set.Finite.mem_toFinset hT).2 h)
      exact intGL_mul (hq1 w hw) (intGL_evM_of_good gf.val (gf⁻¹).val hM w hG)
  let N : Matrix (Fin 2) (Fin 2) IntegralAdeles :=
    fun i j v => ⟨(qv v q * evM v gf.val) i j, (hX v).2.1 i j⟩
  let Ni : Matrix (Fin 2) (Fin 2) IntegralAdeles :=
    fun i j v => ⟨(qv v q * evM v gf.val)⁻¹ i j, (hX v).2.2 i j⟩
  -- Images of `N`, `Ni` in the finite adeles; evaluation at `v` is the local matrix.
  have hevP : ∀ v, evM v (N.map integralEmbedding) = qv v q * evM v gf.val :=
    fun v => Matrix.ext fun _ _ => rfl
  have hevQ : ∀ v, evM v (Ni.map integralEmbedding) = (qv v q * evM v gf.val)⁻¹ :=
    fun v => Matrix.ext fun _ _ => rfl
  have hPQv : ∀ v, evM v ((N.map integralEmbedding) * (Ni.map integralEmbedding)) = evM v 1 := by
    intro v
    have hmul : evM v ((N.map integralEmbedding) * (Ni.map integralEmbedding)) =
        evM v (N.map integralEmbedding) * evM v (Ni.map integralEmbedding) := by
      unfold evM
      exact Matrix.map_mul
    rw [hmul, hevP v, hevQ v, Matrix.mul_nonsing_inv _ (hX v).1]
    unfold evM
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  have hQPv : ∀ v, evM v ((Ni.map integralEmbedding) * (N.map integralEmbedding)) = evM v 1 := by
    intro v
    have hmul : evM v ((Ni.map integralEmbedding) * (N.map integralEmbedding)) =
        evM v (Ni.map integralEmbedding) * evM v (N.map integralEmbedding) := by
      unfold evM
      exact Matrix.map_mul
    rw [hmul, hevP v, hevQ v, Matrix.nonsing_inv_mul _ (hX v).1]
    unfold evM
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  have hPQ : (N.map integralEmbedding) * (Ni.map integralEmbedding) = 1 :=
    Matrix.ext fun i j => RestrictedProduct.ext _ _ fun v => congrFun (congrFun (hPQv v) i) j
  have hQP : (Ni.map integralEmbedding) * (N.map integralEmbedding) = 1 :=
    Matrix.ext fun i j => RestrictedProduct.ext _ _ fun v => congrFun (congrFun (hQPv v) i) j
  have hNNi : N * Ni = 1 := by
    apply Matrix.map_injective integralEmbedding_injective
    show (N * Ni).map integralEmbedding = (1 : Matrix _ _ IntegralAdeles).map integralEmbedding
    rw [Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hNiN : Ni * N = 1 := by
    apply Matrix.map_injective integralEmbedding_injective
    show (Ni * N).map integralEmbedding = (1 : Matrix _ _ IntegralAdeles).map integralEmbedding
    rw [Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GeneralLinearGroup (Fin 2) IntegralAdeles := ⟨N, Ni, hNNi, hNiN⟩
  have hq0 : q.det ≠ 0 := hqdet.ne'
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero q hq0, ?_, ?_⟩⟩
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hqdet
  · rw [binaryIntegralFinite, MonoidHom.mem_range]
    refine ⟨g, ?_⟩
    refine Units.ext (Matrix.ext fun i j => RestrictedProduct.ext _ _ fun v => ?_)
    have key := congrFun (congrFun (evM_qFA v q gf.val) i) j
    exact key.symm

end TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof
