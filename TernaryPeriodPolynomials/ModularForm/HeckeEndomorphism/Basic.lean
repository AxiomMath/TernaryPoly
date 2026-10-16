module

public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.Slash
public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.Geometry
public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.Constructor

@[expose] public section


noncomputable section
open Matrix UpperHalfPlane Complex Filter
open scoped Manifold MatrixGroups ModularForm Topology
namespace TernaryPoly.BinaryCuspHeckeEndomorphism
open BinaryRationalHeckePrime BinaryCuspPeriod BinaryCuspHecke

@[simp] theorem val_finEquiv (p : ℕ) [NeZero p] (b : Fin p) : (ZMod.finEquiv p b).val = b.val := by
  cases p with
  | zero => exact Fin.elim0 b
  | succ p => rfl

/-- The actual slash sum has precisely the original standard pointwise prime normalization. -/
theorem slashSum_eq_primeOperator {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) (z : ℍ) :
    slashSum p f z = primeOperator p (Fact.out : p.Prime).pos f z := by
  simp only [slashSum,Finset.sum_apply,Fintype.sum_sum_type,slash_upper_finite,
    Fintype.sum_unique]
  rw [←Finset.mul_sum]
  have hs : (∑ b : ZMod p, f (divideTranslate p (Fact.out : p.Prime).pos ⟨b.val,ZMod.val_lt b⟩ z)) =
      ∑ b : Fin p, f (divideTranslate p (Fact.out : p.Prime).pos b z) := by
    rw [←(ZMod.finEquiv p).toEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro b _
    congr 2
    apply Fin.ext
    exact val_finEquiv p b
  rw [hs]
  change _ + ((f : ℍ → ℂ) ∣[(d : ℤ)+2] realify (upper p (.inr ()))) z = _
  rw [slash_upper_infty]
  exact add_comm (G := ℂ) _ _

theorem slashSum_holo {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) : MDiff (slashSum p f) :=
  MDifferentiable.sum (fun i _ => slash_upper_holo p f i)

theorem slashSum_zero_at_infty {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) :
    IsZeroAtImInfty (slashSum p f) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ => slash_upper_zero_at_infty p f i)
  change Tendsto (fun z => slashSum p f z) atImInfty (𝓝 0)
  simpa only [slashSum,Finset.sum_apply,Finset.sum_const_zero] using h

/-- The standard prime expression is an actual full-level holomorphic cusp form. -/
def cusp {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) : Forms d :=
  cuspOfInvariant ((d : ℤ)+2) (slashSum p f) (slashSum_invariant p f)
    (slashSum_holo p f) (slashSum_zero_at_infty p f)

@[simp] theorem cusp_apply {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) (z : ℍ) :
    cusp p f z = primeOperator p (Fact.out : p.Prime).pos f z := slashSum_eq_primeOperator p f z

/-- Genuine complex-linear prime Hecke endomorphisms of the actual full-level cusp-form space. -/
def T (d p : ℕ) [Fact p.Prime] : Module.End ℂ (Forms d) where
  toFun := cusp p
  map_add' f g := by
    apply DFunLike.ext
    intro z
    simp [cusp_apply,primeOperator,Finset.sum_add_distrib,mul_add]
    ring
  map_smul' c f := by
    apply DFunLike.ext
    intro z
    simp [cusp_apply,primeOperator,Finset.mul_sum,mul_add,mul_left_comm]

@[simp] theorem T_apply (d p : ℕ) [Fact p.Prime] (f : Forms d) (z : ℍ) :
    T d p f z = primeOperator p (Fact.out : p.Prime).pos f z := cusp_apply p f z

end TernaryPoly.BinaryCuspHeckeEndomorphism
