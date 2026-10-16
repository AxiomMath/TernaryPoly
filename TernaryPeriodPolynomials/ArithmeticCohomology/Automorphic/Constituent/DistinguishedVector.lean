module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.Setting
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.KFinite
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgeBasic

@[expose] public section


/-!
# The distinguished vector of a cuspidal constituent

For a constituent `c` of the Bergman model (`n ≥ 3`), the Hilbert space of `c.cusp hn` is the closed
cyclic span of `c.v`, so `c.v` is a vector `Piece.vec` of it.  This file records the
plumbing facts about it that the later steps use:

* `vec_smooth`: it is a smooth vector (it is a lowest weight vector of a `K'`-fixed vector);
* `vec_level`: it is fixed by the level-three group (`levelThreeValues`), hence `cusp3`;
* `vec_rotation`: the rotations `binaryRotations a` act on it by `a ^ (-(n + 3))`;
* `central_positive`: the central character is trivial on the positive real ideles.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic
open TernaryPeriodPolynomials.Automorphic.AbstractIrreducibility
open TernaryPeriodPolynomials.Automorphic.SubRepresentation
open TernaryPeriodPolynomials.Regularity
open TernaryPeriodPolynomials.CuspIntegral
  (redGL mem_levelGroup_iff centralChar ideleSign ideleOf ideleOf_fst ideleOf_snd ideleReal_eq
    IdeleDecomp ideleReal signUnit)
open TernaryPeriodPolynomials.MultiplicityOne
  (LevelThreeCusp levelThreeValues mem_levelThreeValues)
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (binaryRotations)

namespace TernaryPeriodPolynomials.Automorphic.Constituent

/-! ### Arithmetic facts -/

/-- An integral matrix with second row `(0, 1)` modulo three lies in the level group `K'`. -/
theorem map_mem_bergmanK {k : Matrix.GeneralLinearGroup (Fin 2) IntegralAdeles} (hk : PlaneLeviLevel k) :
    Matrix.GeneralLinearGroup.map integralEmbedding k ∈ bergmanK := by
  obtain ⟨h0, h1⟩ := hk
  have h0' : (redGL k).val 1 0 = 0 := h0
  have h1' : (redGL k).val 1 1 = 1 := h1
  refine (mem_levelGroup_iff _).2 ⟨k, rfl, ?_⟩
  funext j
  fin_cases j
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h0']
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h1']

/-- The idele sign character is trivial on the positive real ideles. -/
theorem ideleSign_realAdeleUnit {t : ℝˣ} (ht : 0 < t.val) : ideleSign (realAdeleUnit t) = 1 := by
  have h : IdeleDecomp (realAdeleUnit t) 1 t 1 := by
    refine ⟨by simp, Units.ext (Prod.ext ?_ ?_)⟩
    · show t.val = (ideleOf 1 t 1).val.1
      rw [ideleOf_fst]
      simp
    · show (1 : FiniteAdeles) = (ideleOf 1 t 1).val.2
      rw [ideleOf_snd]
      simp
  change signUnit (ideleReal (realAdeleUnit t)) = 1
  rw [ideleReal_eq h, signUnit, ite_eq_right (not_lt.mpr ht.le)]

/-- The rotation `binaryRotations (exp (i θ))` is `rotGL θ`. -/
theorem binaryRotations_exp (θ : ℝ) : binaryRotations (Circle.exp θ) = rotGL θ := by
  apply Units.ext
  have h : (binaryRotations (Circle.exp θ)).val = !![((Circle.exp θ : Circle) : ℂ).re,
      -((Circle.exp θ : Circle) : ℂ).im; ((Circle.exp θ : Circle) : ℂ).im,
      ((Circle.exp θ : Circle) : ℂ).re] := rfl
  rw [h, rotGL_val, Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- The `(-(n + 3))`-th power of `exp (i θ)`. -/
theorem circleExp_zpow (θ : ℝ) (n : ℕ) :
    ((Circle.exp θ : Circle) : ℂ) ^ (-((n : ℤ) + 3)) =
      Complex.exp (-(((n + 3 : ℕ) : ℂ) * θ) * Complex.I) := by
  rw [Circle.coe_exp, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-! ### The vector -/

variable {n : ℕ}

/-- The underlying Bergman space vector of an element of the Hilbert space of `c.cusp hn`. -/
def Piece.toBergman (hn : 3 ≤ n) (c : Piece n) (w : (c.cusp hn).H) :
    BergmanSpace (n + 3) (bergmanModel n).E :=
  (Subtype.val : cyclicSpan (bergmanRep (bergmanModel n)) c.v → _) w

/-- The distinguished vector `c.v` of the Hilbert space of `c.cusp hn`. -/
def Piece.vec (hn : 3 ≤ n) (c : Piece n) : (c.cusp hn).H :=
  (⟨c.v, mem_cyclicSpan_self (bergmanRep (bergmanModel n)) c.v⟩ :
    cyclicSpan (bergmanRep (bergmanModel n)) c.v)

variable (hn : 3 ≤ n) (c : Piece n)

/-- The underlying vector of `Piece.vec` is `c.v`. -/
theorem Piece.vec_val : c.toBergman hn (c.vec hn) = c.v := rfl

/-- `toBergman` is injective. -/
theorem Piece.toBergman_injective : Function.Injective (c.toBergman hn) := by
  intro x y h
  exact Subtype.ext (p := fun w => w ∈ cyclicSpan (bergmanRep (bergmanModel n)) c.v) h

/-- The operators of `c.cusp hn` are the restrictions of those of the Bergman representation. -/
theorem Piece.toBergman_pi (g : BinaryAdelicGL) (w : (c.cusp hn).H) :
    c.toBergman hn ((c.cusp hn).π g w) = bergmanRep (bergmanModel n) g (c.toBergman hn w) := rfl

/-- `toBergman` commutes with scalars. -/
theorem Piece.toBergman_smul (z : ℂ) (w : (c.cusp hn).H) :
    c.toBergman hn (z • w) = z • c.toBergman hn w := rfl

/-- The distinguished vector is a smooth vector of the Bergman representation: it is the lowest
weight vector of a `K'`-fixed vector of the finite-adelic model. -/
theorem Piece.isSmoothVector_v :
    IsSmoothVector (bergmanRep (bergmanModel n)) c.v := by
  have hk : 2 ≤ n + 3 := by omega
  have hmem : c.v ∈ (fixedSubmodule (bergmanModel n).σ bergmanK).map (lowestMinusL hk) := by
    rw [← typeSubspace_eq_map (bergmanModel n) hk bergmanK]
    exact c.simple.le_typeSubspace c.mem
  obtain ⟨e, he, hev⟩ := Submodule.mem_map.1 hmem
  rw [← hev]
  exact isSmoothVector_lowestMinus (bergmanModel n) hk levelGroup_isOpenCompact he

/-- The distinguished vector is a smooth vector of `c.cusp hn`. -/
theorem Piece.vec_smooth : c.vec hn ∈ (c.cusp hn).smooth := by
  refine ((c.cusp hn).smooth_exact _).2 ?_
  exact (isSmoothVector_restrict_iff (isClosed_cyclicSpan (bergmanRep (bergmanModel n)) c.v)
    (fun g w hw => isInvariant_cyclicSpan (bergmanRep (bergmanModel n)) c.v g w hw)
    (c.vec hn)).2 c.isSmoothVector_v

/-- The distinguished vector is fixed by the level-three group. -/
theorem Piece.vec_level : c.vec hn ∈ levelThreeValues (c.cusp hn) := by
  refine mem_levelThreeValues.2 fun k hk => ?_
  refine c.toBergman_injective hn ?_
  rw [Piece.toBergman_pi, Piece.vec_val, bergmanRep_atFinite]
  exact finRep_eq_of_mem_typeSubspace (bergmanModel n) (c.simple.le_typeSubspace c.mem)
    (map_mem_bergmanK hk)

/-- The rotations act on the distinguished vector by the character `a ↦ a ^ (-(n + 3))`. -/
theorem Piece.vec_rotation (a : Circle) :
    (c.cusp hn).π (atInfinity (binaryRotations a)) (c.vec hn) =
      (a : ℂ) ^ (-((n : ℤ) + 3)) • c.vec hn := by
  obtain ⟨θ, rfl⟩ : ∃ θ : ℝ, a = Circle.exp θ := ⟨_, (Circle.exp_arg a).symm⟩
  refine c.toBergman_injective hn ?_
  rw [Piece.toBergman_pi, Piece.toBergman_smul, Piece.vec_val,
    bergmanRep_atInfinity, binaryRotations_exp,
    realRep_rot_eq_of_mem_typeSubspace (bergmanModel n) (c.simple.le_typeSubspace c.mem) θ,
    circleExp_zpow]

/-- The central character of `c.cusp hn` is trivial on the positive real ideles. -/
theorem Piece.central_positive (unit : ℝˣ) (hu : 0 < unit.val) :
    (c.cusp hn).centralCharacter (realAdeleUnit unit) = 1 := by
  have h : (c.cusp hn).centralCharacter = (bergmanModel n).χ := rfl
  have hχ : (bergmanModel n).χ = centralChar ((n + 3 : ℕ) : ℤ) := rfl
  rw [h, hχ]
  change (((ideleSign (realAdeleUnit unit) : ℤˣ) : ℤ) : ℂ) ^ ((n + 3 : ℕ) : ℤ) = 1
  rw [ideleSign_realAdeleUnit hu]
  simp

/-- `c.cusp hn` has a nonzero smooth level-three vector. -/
theorem Piece.cusp3 : LevelThreeCusp (c.cusp hn) := by
  unfold LevelThreeCusp
  refine ⟨⟨c.vec hn, c.vec_smooth hn⟩, fun h => c.ne ?_, c.vec_level hn⟩
  have h' : c.vec hn = 0 := congrArg Subtype.val h
  exact congrArg (c.toBergman hn) h'

end TernaryPeriodPolynomials.Automorphic.Constituent
