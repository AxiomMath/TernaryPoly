module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingInterior
public import TernaryPeriodPolynomials.SymmetricSpace.Corner.Separation
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section


/-!
# The six Weyl chambers of the compactified diagonal flat

In the Borel corner chart of the rational frame `g` the closed quadrant of simple-root parameters
`(t₁, t₂) ∈ [0,∞)²` (with trivial unipotent part) is the closure of one Weyl chamber of the diagonal
flat `{diag(a,b,(ab)⁻¹)}` of the symmetric space. For the frames `w_k` (`hexW`) obtained from the identity by
alternately multiplying by the transpositions `(0 1)` and `(1 2)`, adjacent chamber maps agree along
their common wall (`chamber_wall_one`, `chamber_wall_two`): the two corner-chart images of the wall
agree on the open interior (a Weyl-invariant diagonal form) and hence everywhere, since `Glued` is
Hausdorff.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceFlagCoordinates
  TernaryPoly.SymmetricSpaceRationalAction TernaryPoly.SymmetricSpaceRationalCharts
  TernaryPoly.SymmetricSpaceRationalGluing

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33

/-! ### The six Weyl chambers of the compactified diagonal flat -/

/-- The permutation matrix of a permutation of the coordinates, as a rational frame. -/
def permGL (σ : Equiv.Perm (Fin 3)) : RationalGL :=
  (Matrix.permMatrixHom (n := Fin 3) (R := ℚ)).toHomUnits σ

@[simp] theorem permGL_val (σ : Equiv.Perm (Fin 3)) :
    (permGL σ).val = (σ⁻¹).permMatrix ℚ := rfl

theorem permGL_mul (σ τ : Equiv.Perm (Fin 3)) : permGL (σ * τ) = permGL σ * permGL τ :=
  map_mul _ σ τ

/-- The interior point of the symmetric space with zero unipotent part and simple-root
parameters `(s,t)`. -/
def diagSpace (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : Space :=
  rootHomeomorph.symm (0, (⟨s, hs⟩, ⟨t, ht⟩))

theorem upper_zero : upper 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper]

theorem diagSpace_val (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (diagSpace s t hs ht).val =
      normalize (Matrix.diagonal ![(s ^ 2 * t ^ 2)⁻¹, (t ^ 2)⁻¹, 1]) := by
  unfold diagSpace
  rw [rootHomeomorph_symm]
  have h : flagMatrix 0 0 0 (s ^ 2 * t ^ 2)⁻¹ (t ^ 2)⁻¹ =
      Matrix.diagonal ![(s ^ 2 * t ^ 2)⁻¹, (t ^ 2)⁻¹, 1] := by
    simp [flagMatrix, upper_zero, SymmetricSpaceFlagCoordinates.diagonal]
  simpa using congrArg normalize h

theorem conjugate_normalize (g : RealGL) (M : Mat) (hM : M.PosDef) :
    normalize (conjugate g (normalize M)) = normalize (conjugate g M) := by
  change SymmetricSpacePositive.normalize (conjugate g (M.trace⁻¹ • M)) = _
  rw [conjugate_smul]
  exact SymmetricSpacePositive.normalize_smul _ (inv_ne_zero (ne_of_gt hM.trace_pos)) _

theorem conjugate_swap01 (a c : ℝ) :
    conjugate (realRational (permGL (Equiv.swap 0 1))) (Matrix.diagonal ![a, a, c]) =
      Matrix.diagonal ![a, a, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugate, permGL, Matrix.mul_apply, Fin.sum_univ_succ, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.swap_apply_def, Matrix.diagonal_apply, Matrix.star_eq_conjTranspose]

theorem conjugate_swap12 (a c : ℝ) :
    conjugate (realRational (permGL (Equiv.swap 1 2))) (Matrix.diagonal ![a, c, c]) =
      Matrix.diagonal ![a, c, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugate, permGL, Matrix.mul_apply, Fin.sum_univ_succ, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.swap_apply_def, Matrix.diagonal_apply, Matrix.star_eq_conjTranspose]

theorem cornerEmbedding_diagSpace (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    cornerEmbedding (diagSpace s t hs ht) =
      ((0 : Vec3), ((⟨s, hs.le⟩ : HalfLine), (⟨t, ht.le⟩ : HalfLine))) := by
  unfold cornerEmbedding cornerHomeomorph diagSpace
  simp [positiveCornerHomeomorph]

/-- The point `1` of the closed half-line. -/
def oneH : HalfLine := ⟨1, Set.mem_Ici.mpr zero_le_one⟩

/-- The chamber map on the closed quadrant of simple-root parameters, in the chart of the frame `g`. -/
def chamberH (g : RationalGL) (p : HalfLine × HalfLine) : Glued :=
  chart g ((0 : Vec3), p)

theorem continuous_chamberH (g : RationalGL) : Continuous (chamberH g) :=
  (continuous_chart g).comp (continuous_const.prodMk continuous_id)

theorem chamberH_pos (g : RationalGL) (p : HalfLine × HalfLine) (hs : 0 < p.1.1) (ht : 0 < p.2.1) :
    chamberH g p = embedding (act (realRational g) (diagSpace p.1.1 p.2.1 hs ht)) := by
  have h : chartEmbedding g (act (realRational g) (diagSpace p.1.1 p.2.1 hs ht)) =
      ((0 : Vec3), p) := by
    rw [chartEmbedding_apply, ← act_mul, ← map_mul, inv_mul_cancel, map_one, act_one,
      cornerEmbedding_diagSpace]
  rw [chamberH, ← h, chart_embedding]

theorem eq_of_pos {f g : HalfLine → Glued} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ u : HalfLine, 0 < u.1 → f u = g u) : f = g :=
  hf.ext_on positiveHalf_dense hg (fun u hu => h u hu)

theorem diagonal_posDef (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (Matrix.diagonal ![a, b, 1] : Mat).PosDef := by
  rw [Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> simp [ha, hb]

theorem act_swap01_diag (u : ℝ) (hu : 0 < u) :
    act (realRational (permGL (Equiv.swap 0 1))) (diagSpace 1 u one_pos hu) =
      diagSpace 1 u one_pos hu := by
  apply Subtype.ext
  have h1 : ((1 : ℝ) ^ 2 * u ^ 2)⁻¹ = (u ^ 2)⁻¹ := by simp
  change normalize (conjugate (realRational (permGL (Equiv.swap 0 1))) (diagSpace 1 u one_pos hu).val) =
    (diagSpace 1 u one_pos hu).val
  rw [diagSpace_val, h1, conjugate_normalize _ _ (diagonal_posDef _ _ (by positivity) (by positivity)),
    conjugate_swap01]

theorem act_swap12_diag (s : ℝ) (hs : 0 < s) :
    act (realRational (permGL (Equiv.swap 1 2))) (diagSpace s 1 hs one_pos) =
      diagSpace s 1 hs one_pos := by
  apply Subtype.ext
  have h1 : ((1 : ℝ) ^ 2)⁻¹ = 1 := by simp
  change normalize (conjugate (realRational (permGL (Equiv.swap 1 2))) (diagSpace s 1 hs one_pos).val) =
    (diagSpace s 1 hs one_pos).val
  rw [diagSpace_val, h1, conjugate_normalize _ _ (diagonal_posDef _ _ (by positivity) one_pos),
    conjugate_swap12]

/-- Adjacent chambers agree along their common wall `t₁ = 1`. -/
theorem chamberH_wall_one (w : RationalGL) (u : HalfLine) :
    chamberH (w * permGL (Equiv.swap 0 1)) (oneH, u) =
      chamberH w (oneH, u) := by
  have key : (fun u : HalfLine => chamberH (w * permGL (Equiv.swap 0 1)) (oneH, u)) =
      fun u : HalfLine => chamberH w (oneH, u) := by
    apply eq_of_pos
    · exact (continuous_chamberH _).comp (continuous_const.prodMk continuous_id)
    · exact (continuous_chamberH _).comp (continuous_const.prodMk continuous_id)
    · intro u hu
      have h1 : (0 : ℝ) < ((oneH : HalfLine), u).1.1 := one_pos
      rw [chamberH_pos _ _ h1 hu, chamberH_pos _ _ h1 hu, map_mul, act_mul]
      congr 1
      exact congrArg (act (realRational w)) (act_swap01_diag u hu)
  exact congrFun key u

/-- Adjacent chambers agree along their common wall `t₂ = 1`. -/
theorem chamberH_wall_two (w : RationalGL) (u : HalfLine) :
    chamberH (w * permGL (Equiv.swap 1 2)) (u, oneH) =
      chamberH w (u, oneH) := by
  have key : (fun u : HalfLine => chamberH (w * permGL (Equiv.swap 1 2)) (u, oneH)) =
      fun u : HalfLine => chamberH w (u, oneH) := by
    apply eq_of_pos
    · exact (continuous_chamberH _).comp (continuous_id.prodMk continuous_const)
    · exact (continuous_chamberH _).comp (continuous_id.prodMk continuous_const)
    · intro u hu
      have h1 : (0 : ℝ) < (u, (oneH : HalfLine)).2.1 := one_pos
      rw [chamberH_pos _ _ hu h1, chamberH_pos _ _ hu h1, map_mul, act_mul]
      congr 1
      exact congrArg (act (realRational w)) (act_swap12_diag u hu)
  exact congrFun key u

/-- The clamp of a real number to the closed half-line. -/
def clampH (r : ℝ) : HalfLine := ⟨max r 0, Set.mem_Ici.mpr (le_max_right _ _)⟩

theorem continuous_clampH : Continuous clampH := by
  unfold clampH
  exact Continuous.subtype_mk (by fun_prop) _

/-- The chamber map extended to the whole plane by clamping the parameters, so that affine
simplices in the plane can be pushed forward directly. -/
def chamber (g : RationalGL) : C(ℝ × ℝ, TopCat.of Glued) where
  toFun p := chamberH g (clampH p.1, clampH p.2)
  continuous_toFun :=
    (continuous_chamberH g).comp
      ((continuous_clampH.comp continuous_fst).prodMk (continuous_clampH.comp continuous_snd))

theorem chamber_wall_one (w : RationalGL) (u : ℝ) :
    chamber (w * permGL (Equiv.swap 0 1)) (1, u) = chamber w (1, u) := by
  have h1 : clampH 1 = oneH := Subtype.ext (by simp [clampH, oneH])
  change chamberH _ (clampH 1, clampH u) = chamberH _ (clampH 1, clampH u)
  rw [h1]
  exact chamberH_wall_one w (clampH u)

theorem chamber_wall_two (w : RationalGL) (u : ℝ) :
    chamber (w * permGL (Equiv.swap 1 2)) (u, 1) = chamber w (u, 1) := by
  have h1 : clampH 1 = oneH := Subtype.ext (by simp [clampH, oneH])
  change chamberH _ (clampH u, clampH 1) = chamberH _ (clampH u, clampH 1)
  rw [h1]
  exact chamberH_wall_two w (clampH u)

/-- The Weyl element of the `k`-th chamber around the hexagon. -/
def hexPerm (k : ℕ) : Equiv.Perm (Fin 3) :=
  Nat.rec 1 (fun j p => p * (if Even j then Equiv.swap 0 1 else Equiv.swap 1 2)) k

theorem hexPerm_six : hexPerm 6 = 1 := by decide

/-- The rational frame of the `k`-th chamber around the hexagon. -/
def hexW (k : ℕ) : RationalGL := permGL (hexPerm k)

theorem hexW_succ_even (k : ℕ) (hk : Even k) :
    hexW (k + 1) = hexW k * permGL (Equiv.swap 0 1) := by
  simp [hexW, hexPerm, hk, permGL_mul]

theorem hexW_succ_odd (k : ℕ) (hk : ¬ Even k) :
    hexW (k + 1) = hexW k * permGL (Equiv.swap 1 2) := by
  simp [hexW, hexPerm, hk, permGL_mul]

theorem hexW_six : hexW 6 = hexW 0 := by
  show permGL (hexPerm 6) = permGL (hexPerm 0)
  rw [hexPerm_six]
  rfl



end TernaryPeriodPolynomials.Argument.Lemma33
