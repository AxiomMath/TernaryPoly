module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.PlusHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeCosets

@[expose] public section


/-!
# The symmetric right cosets of `U_3` in `Γ₁(3)`

The right cosets `Γ₁(3) [[1,j],[0,3]]`, `j ∈ {0,1,2}`, as `HeckeH1.RightCosets` data for
`Γ₁(3) = core ⊆ GL₂(ℚ)` (`u3Std`, transitions from `LevelThreeHeckeCosets.u3_transition`), and the
symmetric version `u3Sym` whose representatives are
`[[1,0],[0,3]]`, `[[1,1],[0,3]]`, `[[1,-1],[0,3]]` (`twistCosets`: the same cosets with each
representative moved by an element of `Γ₁(3)`).

Conjugation by `ε' = diag(-1,1)` fixes the representative set of `u3Sym`
(`ε' α_j ε' = α_{-j}`), so `u3Sym` carries a `PlusHecke.Symmetry` for the reflection `ε` of
`Γ₁'(3)`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open scoped MatrixGroups
open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParityHecke
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeCosets
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThreeInjective.PlusHecke

namespace TernaryPeriodPolynomials.LevelThreeInjective.U3Cosets

/-! ### Moving the representatives -/

section Twist

variable {G 𝔾 : Type} [Group G] [Group 𝔾] {embed : G →* 𝔾}

/-- The same right cosets with each representative `α_j` replaced by `embed (τ j) · α_j`. -/
def twistCosets (S : RightCosets embed) (τ : S.index → G) : RightCosets embed where
  index := S.index
  fintype := S.fintype
  rep j := embed (τ j) * S.rep j
  next := S.next
  delta g j := τ j * S.delta g j * (τ (S.next g j))⁻¹
  delta_spec g j := by
    simp only [map_mul, map_inv, S.delta_spec]
    group
  disjoint i j g h := by
    apply S.disjoint i j ((τ i)⁻¹ * g * τ j)
    rw [map_mul, map_mul, map_inv, h]
    group

end Twist

/-! ### The standard cosets `[[1,j],[0,3]]` -/

theorem toGLQ_val (g : SL(2, ℤ)) : (toGLQ g).val = g.val.map (Int.castRingHom ℚ) := rfl

theorem coreEmbed_eq_toGLQ (k : core) : coreEmbed k = toGLQ (coreSL k) := by
  apply Units.ext
  exact integralEmbed_val (k : binaryArithmeticLevel).val

theorem u3_exists (g : core) (j : Fin 3) :
    ∃ δ : core, coreEmbed δ =
      u3Rep j * coreEmbed g * (u3Rep ((u3Perm (coreSL g)).symm j))⁻¹ := by
  obtain ⟨γ, hγ, h⟩ := u3_transition (coreSL_mem g) ((u3Perm (coreSL g)).symm j)
  obtain ⟨δ, rfl⟩ := exists_core_of_mem γ hγ
  refine ⟨δ, ?_⟩
  rw [Equiv.apply_symm_apply] at h
  have hrel := rat_relation (u3Int_rational ((u3Perm (coreSL g)).symm j)) (u3Int_rational j) h
  rw [coreEmbed_eq_toGLQ, coreEmbed_eq_toGLQ, hrel, mul_inv_cancel_right]

/-- The transition element of `U_3`. -/
def u3Delta (g : core) (j : Fin 3) : core := (u3_exists g j).choose

theorem u3Delta_spec (g : core) (j : Fin 3) :
    coreEmbed (u3Delta g j) =
      u3Rep j * coreEmbed g * (u3Rep ((u3Perm (coreSL g)).symm j))⁻¹ :=
  (u3_exists g j).choose_spec

theorem u3_disjoint (g : SL(2, ℤ)) (i j : Fin 3) (h : toGLQ g * u3Rep j = u3Rep i) : i = j := by
  have hM : ∀ i : Fin 3, modularHeckeMatrix primeThree (some i) = !![1, (i : ℤ); 0, 3] :=
    fun _ => rfl
  have hv := congrArg (fun x : GL (Fin 2) ℚ => (x : Matrix (Fin 2) (Fin 2) ℚ)) h
  simp only [Units.val_mul] at hv
  rw [← u3Int_rational j, ← u3Int_rational i, toGLQ_val, ← Matrix.map_mul] at hv
  have e := Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective hv
  rw [hM, hM] at e
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00
  simp [Matrix.mul_apply, Fin.sum_univ_two, e00] at e01
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  omega

/-- **The right cosets of `U_3` in `Γ₁(3)`**, representatives `[[1,j],[0,3]]`. -/
def u3Std : RightCosets coreEmbed where
  index := Fin 3
  rep := u3Rep
  next g j := (u3Perm (coreSL g)).symm j
  delta := u3Delta
  delta_spec := u3Delta_spec
  disjoint i j g h := by
    apply u3_disjoint (coreSL g) i j
    rw [← coreEmbed_eq_toGLQ, h, inv_mul_cancel_right]

/-! ### The symmetric representatives -/

theorem fin3_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  revert j
  decide

/-- The translation `[[1,-1],[0,1]]` in `Γ₁(3)`. -/
def tauTwo : core := ⟨upper (-1), upper_neg_mem⟩

/-- The correction moving `[[1,2],[0,3]]` to `[[1,-1],[0,3]]`. -/
def symTau (j : Fin 3) : core := if j = 2 then tauTwo else 1

theorem symTau_zero : symTau 0 = 1 := by
  unfold symTau
  exact ite_eq_right (by decide)

theorem symTau_one : symTau 1 = 1 := by
  unfold symTau
  exact ite_eq_right (by decide)

theorem symTau_two : symTau 2 = tauTwo := by
  unfold symTau
  exact ite_eq_left rfl

/-- **The symmetric right cosets of `U_3`**, representatives
`[[1,0],[0,3]]`, `[[1,1],[0,3]]`, `[[1,-1],[0,3]]`. -/
def u3Sym : RightCosets coreEmbed := twistCosets u3Std symTau

theorem u3Sym_rep (j : Fin 3) : u3Sym.rep j = coreEmbed (symTau j) * u3Rep j := rfl

theorem u3Rep_val (j : Fin 3) : (u3Rep j).val = !![1, ((j : ℕ) : ℚ); 0, 3] := by
  rw [← u3Int_rational j]
  change (!![1, ((j : ℕ) : ℤ); 0, 3] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) = _
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem coreEmbed_tauTwo_val : (coreEmbed tauTwo).val = !![1, -1; 0, 1] := by
  show (integralEmbed (upper (-1)).val).val = _
  rw [integralEmbed_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [upper]

theorem flip_val : (levelEmbed reflection).val = !![-1, 0; 0, 1] := by
  rw [levelEmbed_apply, integralEmbed_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [reflection]

theorem sym_zero_val : (coreEmbed (symTau 0) * u3Rep 0).val = !![1, 0; 0, 3] := by
  rw [symTau_zero, map_one, one_mul, u3Rep_val]
  simp

theorem sym_one_val : (coreEmbed (symTau 1) * u3Rep 1).val = !![1, 1; 0, 3] := by
  rw [symTau_one, map_one, one_mul, u3Rep_val]
  simp

theorem sym_two_val : (coreEmbed (symTau 2) * u3Rep 2).val = !![1, -1; 0, 3] := by
  rw [symTau_two, Units.val_mul, coreEmbed_tauTwo_val, u3Rep_val]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem flip_sym (j : Fin 3) :
    levelEmbed reflection * (coreEmbed (symTau j) * u3Rep j) * levelEmbed reflection =
      coreEmbed (symTau (-j)) * u3Rep (-j) := by
  apply Units.ext
  rcases fin3_cases j with rfl | rfl | rfl
  · have h : (-(0 : Fin 3)) = 0 := by decide
    rw [h, Units.val_mul, Units.val_mul, flip_val, sym_zero_val]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · have h : (-(1 : Fin 3)) = 2 := by decide
    rw [h, Units.val_mul, Units.val_mul, flip_val, sym_one_val, sym_two_val]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · have h : (-(2 : Fin 3)) = 1 := by decide
    rw [h, Units.val_mul, Units.val_mul, flip_val, sym_two_val, sym_one_val]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`u3Sym` is symmetric under the reflection**: `ε' α_j ε' = α_{-j}`. -/
def u3Symmetry : Symmetry normalCore u3Sym where
  flip := levelEmbed reflection
  flip_mul_self := by rw [← map_mul, reflection_mul_self, map_one]
  embed_conj k := by
    show levelEmbed (reflection * (k : binaryArithmeticLevel) * reflection) =
      levelEmbed reflection * levelEmbed (k : binaryArithmeticLevel) * levelEmbed reflection
    rw [map_mul, map_mul]
  bar j := Neg.neg (α := Fin 3) j
  rep_bar j := (flip_sym j).symm

theorem u3Sym_det (j : Fin 3) : (u3Sym.rep j).val.det = 3 := by
  rcases fin3_cases j with rfl | rfl | rfl
  · rw [u3Sym_rep, sym_zero_val, Matrix.det_fin_two_of]
    norm_num
  · rw [u3Sym_rep, sym_one_val, Matrix.det_fin_two_of]
    norm_num
  · rw [u3Sym_rep, sym_two_val, Matrix.det_fin_two_of]
    norm_num

theorem u3Sym_det_pos (j : Fin 3) : 0 < (((u3Sym.rep j).det : ℚˣ) : ℚ) := by
  rw [GeneralLinearGroup.val_det_apply, u3Sym_det]
  norm_num

end TernaryPeriodPolynomials.LevelThreeInjective.U3Cosets
