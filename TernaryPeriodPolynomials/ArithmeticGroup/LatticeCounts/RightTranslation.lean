module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.AdelicValue
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.ReductionProof
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.Adelic

@[expose] public section


/-!
# Right translation at one finite place, and the "hence everywhere" step

Formalized by Claude Haiku 5.5.
Paper: (`eq:lattice-hecke`, the right translation `v_h|A`, and "hence everywhere").

Proved here:
* `ιMat`, `ιGL`: the finite-adelic embedding `ι_v(A)` of `A ∈ GL₂(K_v)` (`A` at the place `v`,
  identity elsewhere), multiplicative (`ιMat_mul`, `ιMat_one`).
* `vhValue_of_gamma`: `v_h(g_∞, g_f) = F_h(γ g_∞)` for ANY rational `γ` with `γ g_f` integral.
* `vhValue_mul_integral`: right `GL₂(ℤ̂)`-invariance of `v_h`.
* `vhValue_rational`: diagonal action of `GL₂⁺(ℚ)`, `v_h(g_∞, δ g_f) = v_h(δ⁻¹ g_∞, g_f)`.
* `sum_perm`: reindexing of a finite sum under the lattice-permutation property `IsLatticePerm`.
* `hecke_right_everywhere`: the identity at finite coordinate one implies it at every `g_f`.

Hypotheses:
* `H1` of `hecke_right_everywhere`: the identity of eq:lattice-hecke at finite coordinate one
  (`g_f = 1`). Its proof is the prime-power recursion, owned by S5 (`HeckeRecursion*.lean`).
* `IsLatticePerm` is a property of a given family `x` and bijection `σ`; it is not derived here
  from lattice bases (a basis of `yΛ` is `y A_Λ`).
* `hL_int`, `hR_int`, `hL_diag`, `hR_diag` of `hecke_right_everywhere`: the transformation laws of
  the two sides of the identity. For the Hecke sum side `L` these are not derived from the
  definition of `L`; they are the inputs to be discharged when `L` and `R` are instantiated.
-/

open Matrix
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof (latticeReductionExists evM)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (OS)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary (Fh)

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation

/-! ### The embedding `ι_v` -/

/-- The adele with value `x` at the place `v` and `1` at all other places, entry `(i,j)` of
`ι_v(M)`. -/
def ιEntry (v : FinitePlace) (x : v.adicCompletion ℚ) (i j : Fin 2) : FiniteAdeles :=
  ⟨fun w => if hw : w = v then
      cast (congrArg (fun u : FinitePlace => u.adicCompletion ℚ) hw).symm x
    else (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j,
   (Filter.eventually_cofinite_ne v).mono fun w hw => by
     dsimp only
     rw [dite_eq_right hw, Matrix.one_apply]
     split_ifs
     · exact (OS w).one_mem
     · exact (OS w).zero_mem⟩

theorem eval_ιEntry_self (v : FinitePlace) (x : v.adicCompletion ℚ) (i j : Fin 2) :
    finiteEvaluation v (ιEntry v x i j) = x := by
  show (if h : v = v then _ else _) = x
  rw [dite_eq_left rfl]
  exact cast_eq _ x

theorem eval_ιEntry_ne (v w : FinitePlace) (hw : w ≠ v) (x : v.adicCompletion ℚ) (i j : Fin 2) :
    finiteEvaluation w (ιEntry v x i j) = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j := by
  show (if h : w = v then _ else _) = _
  rw [dite_eq_right hw]

/-- `ι_v(M)`: `M` at the place `v`, the identity at all other places. -/
def ιMat (v : FinitePlace) (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    Matrix (Fin 2) (Fin 2) FiniteAdeles :=
  fun i j => ιEntry v (M i j) i j

theorem evM_ιMat_self (v : FinitePlace) (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    evM v (ιMat v M) = M :=
  Matrix.ext fun i j => eval_ιEntry_self v (M i j) i j

theorem evM_ιMat_ne (v w : FinitePlace) (hw : w ≠ v) (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    evM w (ιMat v M) = 1 :=
  Matrix.ext fun i j => eval_ιEntry_ne v w hw (M i j) i j

/-- Two finite-adelic matrices with the same evaluation at every place agree. -/
theorem ext_of_evM {A B : Matrix (Fin 2) (Fin 2) FiniteAdeles}
    (h : ∀ w : FinitePlace, evM w A = evM w B) : A = B :=
  Matrix.ext fun i j => RestrictedProduct.ext _ _ fun w => congrFun (congrFun (h w) i) j

theorem ιMat_mul (v : FinitePlace) (M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    ιMat v (M * N) = ιMat v M * ιMat v N := by
  apply ext_of_evM
  intro w
  have hmul : evM w (ιMat v M * ιMat v N) = evM w (ιMat v M) * evM w (ιMat v N) := by
    unfold evM
    exact Matrix.map_mul
  rw [hmul]
  by_cases hw : w = v
  · subst hw
    rw [evM_ιMat_self, evM_ιMat_self, evM_ιMat_self]
  · rw [evM_ιMat_ne v w hw, evM_ιMat_ne v w hw, evM_ιMat_ne v w hw, one_mul]

theorem ιMat_one (v : FinitePlace) : ιMat v (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1 := by
  apply ext_of_evM
  intro w
  by_cases hw : w = v
  · subst hw
    rw [evM_ιMat_self]
    unfold evM
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  · rw [evM_ιMat_ne v w hw]
    unfold evM
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm

/-- `ι_v(A)` for `A ∈ GL₂(K_v)`, as an element of `GL₂(𝔸_f)`. -/
def ιGL (v : FinitePlace) (A : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) : BinaryFiniteGL :=
  ⟨ιMat v A.val, ιMat v A⁻¹.val,
    by rw [← ιMat_mul, Units.mul_inv, ιMat_one],
    by rw [← ιMat_mul, Units.inv_mul, ιMat_one]⟩

theorem ιGL_val (v : FinitePlace) (A : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    (ιGL v A).val = ιMat v A.val := rfl

/-! ### Reduction in the form used by the invariance proofs -/

/-- `v_h(g_∞, g_f) = F_h(γ g_∞)` for any rational `γ` with `0 < det γ` and `γ g_f` integral. -/
theorem vhValue_of_gamma (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) (γ : BinaryRationalGL) (hγ : 0 < (Matrix.GeneralLinearGroup.det γ).val)
    (hint : binaryRationalFinite γ * gf ∈ binaryIntegralFinite) :
    vhValue k h gInf gf = Fh k ⇑h (binaryRationalReal γ * gInf) :=
  vhValue_eq_of_reduction k h gInf hgInf gf ⟨γ, hγ, hint⟩

/-- At finite coordinate one, `v_h(g_∞, 1) = F_h(g_∞)` (the reduction `γ = 1`). -/
theorem vhValue_one (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val) :
    vhValue k h gInf 1 = Fh k ⇑h gInf := by
  have hpos : 0 < (Matrix.GeneralLinearGroup.det (1 : BinaryRationalGL)).val := by
    rw [map_one, Units.val_one]
    exact one_pos
  have hint : binaryRationalFinite (1 : BinaryRationalGL) * 1 ∈ binaryIntegralFinite := by
    rw [mul_one, map_one]
    exact Subgroup.one_mem _
  rw [vhValue_of_gamma k h gInf hgInf 1 1 hpos hint, map_one, one_mul]

/-! ### Right invariance under `GL₂(ℤ̂)` and the diagonal action of `GL₂⁺(ℚ)` -/

/-- Right invariance of `v_h` under `GL₂(ℤ̂)`: `v_h(g_∞, g_f u) = v_h(g_∞, g_f)`. -/
theorem vhValue_mul_integral (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf u : BinaryFiniteGL) (hu : u ∈ binaryIntegralFinite) :
    vhValue k h gInf (gf * u) = vhValue k h gInf gf := by
  obtain ⟨r⟩ := latticeReductionExists gf
  have hint : binaryRationalFinite r.γ * (gf * u) ∈ binaryIntegralFinite := by
    rw [← mul_assoc]
    exact Subgroup.mul_mem binaryIntegralFinite r.integral hu
  rw [vhValue_of_gamma k h gInf hgInf (gf * u) r.γ r.det_pos hint,
    vhValue_eq_of_reduction k h gInf hgInf gf r]

/-- `δ ↦ det δ⁻¹` keeps positivity. -/
theorem det_inv_pos' (δ : BinaryRationalGL) (hδ : 0 < (Matrix.GeneralLinearGroup.det δ).val) :
    0 < (Matrix.GeneralLinearGroup.det δ⁻¹).val := by
  rw [map_inv, Units.val_inv_eq_inv_val]
  exact inv_pos.2 hδ

/-- Diagonal action: `v_h(g_∞, δ g_f) = v_h(δ⁻¹ g_∞, g_f)` for `δ ∈ GL₂⁺(ℚ)`.
Proof: the reduction of `δ g_f` is `γ δ⁻¹` where `γ` reduces `g_f`; then both sides are
`F_h(γ δ⁻¹ g_∞)`, which is `vhValue_well_defined`-independent of the chosen reduction. -/
theorem vhValue_rational (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (δ : BinaryRationalGL) (hδ : 0 < (Matrix.GeneralLinearGroup.det δ).val) (gf : BinaryFiniteGL) :
    vhValue k h gInf (binaryRationalFinite δ * gf) =
      vhValue k h (binaryRationalReal δ⁻¹ * gInf) gf := by
  obtain ⟨r⟩ := latticeReductionExists gf
  have hpos : 0 < (Matrix.GeneralLinearGroup.det (r.γ * δ⁻¹)).val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos r.det_pos (det_inv_pos' δ hδ)
  have hint : binaryRationalFinite (r.γ * δ⁻¹) * (binaryRationalFinite δ * gf) ∈ binaryIntegralFinite := by
    have e : binaryRationalFinite (r.γ * δ⁻¹) * (binaryRationalFinite δ * gf) =
        binaryRationalFinite r.γ * gf := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
    rw [e]
    exact r.integral
  have hgInf' : 0 < (Matrix.GeneralLinearGroup.det (binaryRationalReal δ⁻¹ * gInf)).val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos (det_binaryRationalReal_pos δ⁻¹ (det_inv_pos' δ hδ)) hgInf
  rw [vhValue_of_gamma k h gInf hgInf (binaryRationalFinite δ * gf) (r.γ * δ⁻¹) hpos hint,
    vhValue_eq_of_reduction k h (binaryRationalReal δ⁻¹ * gInf) hgInf' gf r, map_mul, mul_assoc]

/-! ### The lattice-permutation property and the reindexing of the sum -/

/-- **Input P (lattice permutation).** For a finite family `x : ι → GL₂(𝔸_f)` (the family
`ι_p(A_Λ)` indexed by lattices), a bijection `σ` and an element `y`, every `y · x_i` equals
`x_{σ i}` times an element of `GL₂(ℤ̂)`. `yΛ` has basis `y A_Λ`, and two bases of the same
lattice differ on the right by `GL₂(ℤ_p)`. Stated as a hypothesis; not derived here. -/
def IsLatticePerm {ι : Type*} (y : BinaryFiniteGL) (x : ι → BinaryFiniteGL) (σ : ι ≃ ι) : Prop :=
  ∀ i, ∃ w ∈ binaryIntegralFinite, y * x i = x (σ i) * w

/-- Reindexing: under `IsLatticePerm y x σ`, `∑_i v_h(g_∞, g_f · y x_i) = ∑_i v_h(g_∞, g_f · x_i)`. -/
theorem sum_perm (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) {ι : Type*} [Fintype ι] (y : BinaryFiniteGL) (x : ι → BinaryFiniteGL)
    (σ : ι ≃ ι) (hP : IsLatticePerm y x σ) :
    ∑ i, vhValue k h gInf (gf * (y * x i)) = ∑ i, vhValue k h gInf (gf * x i) := by
  have step : ∀ i, vhValue k h gInf (gf * (y * x i)) = vhValue k h gInf (gf * x (σ i)) := by
    intro i
    obtain ⟨w, hw, hyx⟩ := hP i
    rw [hyx, ← mul_assoc]
    exact vhValue_mul_integral k h gInf hgInf _ w hw
  rw [Finset.sum_congr rfl fun i _ => step i]
  exact Equiv.sum_comp σ (fun i => vhValue k h gInf (gf * x i))

/-! ### The "hence everywhere" step -/

/-- **The hence-everywhere step.** Let `L`, `R` be the two sides of the
identity as functions of `(g_∞, g_f)`.

Hypothesis H1: the identity at finite coordinate one, `L g_∞ 1 = R g_∞ 1` for all `g_∞` with
`det > 0`. Its proof is the prime-power recursion, owned by S5 (`HeckeRecursion*.lean`).

HYPOTHESES hL_int, hR_int, hL_diag, hR_diag: the right `GL₂(ℤ̂)`-invariance and the diagonal
`GL₂⁺(ℚ)`-equivariance of the two sides, each for `g_∞` with `det > 0`. They are proved for `v_h`
itself (`vhValue_mul_integral`, `vhValue_rational`) and for the Hecke lattice sum in
`HeckeTransform.lean` (`latSum_*`, `vhRight_*`), where `L` is instantiated; the integral-invariance
of the lattice sum needs the lattice-permutation input `IsLatticePerm`.

Conclusion: the identity holds at every `g_f`. -/
theorem hecke_right_everywhere
    (L R : BinaryRealGL → BinaryFiniteGL → ℂ)
    (hL_int : ∀ (gInf : BinaryRealGL), 0 < (Matrix.GeneralLinearGroup.det gInf).val →
      ∀ (gf u : BinaryFiniteGL), u ∈ binaryIntegralFinite → L gInf (gf * u) = L gInf gf)
    (hR_int : ∀ (gInf : BinaryRealGL), 0 < (Matrix.GeneralLinearGroup.det gInf).val →
      ∀ (gf u : BinaryFiniteGL), u ∈ binaryIntegralFinite → R gInf (gf * u) = R gInf gf)
    (hL_diag : ∀ (gInf : BinaryRealGL), 0 < (Matrix.GeneralLinearGroup.det gInf).val →
      ∀ (δ : BinaryRationalGL) (gf : BinaryFiniteGL),
      0 < (Matrix.GeneralLinearGroup.det δ).val →
      L gInf (binaryRationalFinite δ * gf) = L (binaryRationalReal δ⁻¹ * gInf) gf)
    (hR_diag : ∀ (gInf : BinaryRealGL), 0 < (Matrix.GeneralLinearGroup.det gInf).val →
      ∀ (δ : BinaryRationalGL) (gf : BinaryFiniteGL),
      0 < (Matrix.GeneralLinearGroup.det δ).val →
      R gInf (binaryRationalFinite δ * gf) = R (binaryRationalReal δ⁻¹ * gInf) gf)
    (H1 : ∀ gInf : BinaryRealGL, 0 < (Matrix.GeneralLinearGroup.det gInf).val →
      L gInf 1 = R gInf 1) :
    ∀ gInf : BinaryRealGL, 0 < (Matrix.GeneralLinearGroup.det gInf).val →
      ∀ gf : BinaryFiniteGL, L gInf gf = R gInf gf := by
  intro gInf hgInf gf
  obtain ⟨r⟩ := latticeReductionExists gf
  have hgf : gf = binaryRationalFinite r.γ⁻¹ * (binaryRationalFinite r.γ * gf) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hγinv : 0 < (Matrix.GeneralLinearGroup.det r.γ⁻¹).val := det_inv_pos' r.γ r.det_pos
  have hpos : 0 < (Matrix.GeneralLinearGroup.det (binaryRationalReal r.γ * gInf)).val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos (det_binaryRationalReal_pos r.γ r.det_pos) hgInf
  have hint : binaryRationalFinite r.γ * gf ∈ binaryIntegralFinite := r.integral
  have hL : L gInf gf = L (binaryRationalReal r.γ * gInf) (binaryRationalFinite r.γ * gf) := by
    have h1 := hL_diag gInf hgInf r.γ⁻¹ (binaryRationalFinite r.γ * gf) hγinv
    rw [inv_inv, ← hgf] at h1
    exact h1
  have hR : R gInf gf = R (binaryRationalReal r.γ * gInf) (binaryRationalFinite r.γ * gf) := by
    have h1 := hR_diag gInf hgInf r.γ⁻¹ (binaryRationalFinite r.γ * gf) hγinv
    rw [inv_inv, ← hgf] at h1
    exact h1
  have hL1 : L (binaryRationalReal r.γ * gInf) (binaryRationalFinite r.γ * gf) =
      L (binaryRationalReal r.γ * gInf) 1 := by
    have h1 := hL_int (binaryRationalReal r.γ * gInf) hpos 1 (binaryRationalFinite r.γ * gf) hint
    rw [one_mul] at h1
    exact h1
  have hR1 : R (binaryRationalReal r.γ * gInf) (binaryRationalFinite r.γ * gf) =
      R (binaryRationalReal r.γ * gInf) 1 := by
    have h1 := hR_int (binaryRationalReal r.γ * gInf) hpos 1 (binaryRationalFinite r.γ * gf) hint
    rw [one_mul] at h1
    exact h1
  rw [hL, hR, hL1, hR1]
  exact H1 _ hpos

end TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
