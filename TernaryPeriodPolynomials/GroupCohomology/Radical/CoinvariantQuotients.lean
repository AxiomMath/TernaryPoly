module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantAlgebra
public import TernaryPeriodPolynomials.Polynomial.GLAction

@[expose] public section

open MvPolynomial

noncomputable section
namespace TernaryPoly.RadicalCoinvariantAlgebra

abbrev H := PolynomialGLAction.HomogeneousPoly
abbrev BinaryH (n : ℕ) := homogeneousSubmodule (Fin 2) ℚ n
abbrev UnaryH (n : ℕ) := homogeneousSubmodule (Fin 1) ℚ n

def homogeneousBind {σ τ : Type*} (n : ℕ) (g : σ → MvPolynomial τ ℚ)
    (hg : ∀ i, (g i).IsHomogeneous 1) :
    homogeneousSubmodule σ ℚ n →ₗ[ℚ] homogeneousSubmodule τ ℚ n where
  toFun p := ⟨bind₁ g p, isHomogeneous_bind₁_linear p.property g hg⟩
  map_add' p q := Subtype.ext (map_add (bind₁ g) (p : MvPolynomial σ ℚ) q)
  map_smul' c p := Subtype.ext ((bind₁ g).toLinearMap.map_smul c p)

def homogeneousShear (n : ℕ) (i j : Fin 3) : H n →ₗ[ℚ] H n where
  toFun p := ⟨shear i j p, shear_homogeneous i j p.property⟩
  map_add' p q := Subtype.ext (map_add (shear i j) (p : Poly) q)
  map_smul' c p := Subtype.ext ((shear i j).toLinearMap.map_smul c p)

def difference (n : ℕ) (i j : Fin 3) : H n →ₗ[ℚ] H n :=
  homogeneousShear n i j - LinearMap.id

def planeEvalAlg : Poly →ₐ[ℚ] MvPolynomial (Fin 2) ℚ := bind₁ ![X 0, X 1, 0]
def lineEvalAlg : Poly →ₐ[ℚ] MvPolynomial (Fin 1) ℚ := bind₁ ![X 0, 0, 0]

def planeEval (n : ℕ) : H n →ₗ[ℚ] BinaryH n :=
  homogeneousBind n ![X 0, X 1, 0] (by
    intro i; fin_cases i
    · exact isHomogeneous_X ℚ 0
    · exact isHomogeneous_X ℚ 1
    · exact isHomogeneous_zero _ _ _)

def lineEval (n : ℕ) : H n →ₗ[ℚ] UnaryH n :=
  homogeneousBind n ![X 0, 0, 0] (by
    intro i; fin_cases i
    · exact isHomogeneous_X ℚ 0
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_zero _ _ _)

@[simp] theorem planeEval_coe (n : ℕ) (p : H n) :
    (planeEval n p : MvPolynomial (Fin 2) ℚ) = planeEvalAlg p := rfl
@[simp] theorem lineEval_coe (n : ℕ) (p : H n) :
    (lineEval n p : MvPolynomial (Fin 1) ℚ) = lineEvalAlg p := rfl

 theorem plane_rename_eval (p : Poly) :
    rename (![0, 1] : Fin 2 → Fin 3) (planeEvalAlg p) = erase 2 p := by
  have h : (rename (![0, 1] : Fin 2 → Fin 3)).comp planeEvalAlg = erase 2 := by
    ext k; fin_cases k <;> simp [planeEvalAlg, erase]
  exact DFunLike.congr_fun h p

theorem line_rename_eval (p : Poly) :
    rename (![0] : Fin 1 → Fin 3) (lineEvalAlg p) = erase 2 (erase 1 p) := by
  have h : (rename (![0] : Fin 1 → Fin 3)).comp lineEvalAlg =
      (erase 2).comp (erase 1) := by
    ext k; fin_cases k <;> simp [lineEvalAlg, erase]
  exact DFunLike.congr_fun h p

theorem planeEval_surjective (n : ℕ) : Function.Surjective (planeEval n) := by
  intro p
  refine ⟨⟨rename (![0, 1] : Fin 2 → Fin 3) p, p.property.rename_isHomogeneous⟩, ?_⟩
  apply Subtype.ext
  change planeEvalAlg (rename (![0, 1] : Fin 2 → Fin 3) p) = p
  have h : planeEvalAlg.comp (rename (![0, 1] : Fin 2 → Fin 3)) = AlgHom.id ℚ _ := by
    ext k; fin_cases k <;> simp [planeEvalAlg]
  exact DFunLike.congr_fun h (p : MvPolynomial (Fin 2) ℚ)

theorem lineEval_surjective (n : ℕ) : Function.Surjective (lineEval n) := by
  intro p
  refine ⟨⟨rename (![0] : Fin 1 → Fin 3) p, p.property.rename_isHomogeneous⟩, ?_⟩
  apply Subtype.ext
  change lineEvalAlg (rename (![0] : Fin 1 → Fin 3) p) = p
  have h : lineEvalAlg.comp (rename (![0] : Fin 1 → Fin 3)) = AlgHom.id ℚ _ := by
    ext k; fin_cases k; simp [lineEvalAlg]
  exact DFunLike.congr_fun h (p : MvPolynomial (Fin 1) ℚ)

def planeRelations (n : ℕ) : Submodule ℚ (H n) :=
  LinearMap.range (difference n 0 2) ⊔ LinearMap.range (difference n 1 2)

def lineRelations (n : ℕ) : Submodule ℚ (H n) :=
  LinearMap.range (difference n 0 1) ⊔ LinearMap.range (difference n 0 2)

theorem mem_difference_range (n : ℕ) (j : Fin 2) (p : H n) :
    p ∈ LinearMap.range (difference n 0 j.succ) ↔ erase j.succ p = 0 := by
  rw [← exists_homogeneous_shear_sub_iff j p p.property]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, q.property, congrArg Subtype.val hq⟩
  · rintro ⟨q, hq, he⟩
    exact ⟨⟨q, hq⟩, Subtype.ext he⟩

theorem planeEval_shear (i : Fin 3) (p : Poly) :
    planeEvalAlg (shear i 2 p) = planeEvalAlg p := by
  have h : planeEvalAlg.comp (shear i 2) = planeEvalAlg := by
    ext k
    by_cases hk : k = i
    · subst k
      simp [planeEvalAlg, shear]
    · simp [shear, hk]
  exact DFunLike.congr_fun h p

theorem lineEval_shear (j : Fin 2) (p : Poly) :
    lineEvalAlg (shear 0 j.succ p) = lineEvalAlg p := by
  have h : lineEvalAlg.comp (shear 0 j.succ) = lineEvalAlg := by
    ext k
    fin_cases k <;> fin_cases j <;> simp [lineEvalAlg, shear]
  exact DFunLike.congr_fun h p

theorem planeRelations_eq_ker (n : ℕ) : planeRelations n = LinearMap.ker (planeEval n) := by
  apply le_antisymm
  · apply sup_le
    all_goals
      rintro p ⟨q, rfl⟩
      apply Subtype.ext
      change planeEvalAlg (shear _ 2 q - q) = 0
      rw [map_sub, planeEval_shear, sub_self]
  · intro p hp
    apply (show LinearMap.range (difference n 0 2) ≤ planeRelations n from le_sup_left)
    apply (show p ∈ LinearMap.range (difference n 0 2) ↔ erase 2 p = 0 from by
      simpa using mem_difference_range n (1 : Fin 2) p).mpr
    have hp' : planeEvalAlg p = 0 := congrArg Subtype.val hp
    rw [← plane_rename_eval, hp', map_zero]

theorem erase_homogeneous (j : Fin 3) {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    (erase j p).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hp
  intro k
  split_ifs
  · exact isHomogeneous_zero _ _ _
  · exact isHomogeneous_X ℚ k

theorem erase_idem (j : Fin 3) (p : Poly) : erase j (erase j p) = erase j p := by
  have h : (erase j).comp (erase j) = erase j := by
    ext k
    by_cases hk : k = j <;> simp [hk]
  exact DFunLike.congr_fun h p

theorem lineRelations_eq_ker (n : ℕ) : lineRelations n = LinearMap.ker (lineEval n) := by
  apply le_antisymm
  · apply sup_le
    all_goals
      rintro p ⟨q, rfl⟩
      apply Subtype.ext
      change lineEvalAlg (shear 0 _ q - q) = 0
      rw [map_sub]
    · simpa using sub_eq_zero.mpr (lineEval_shear (0 : Fin 2) q)
    · simpa using sub_eq_zero.mpr (lineEval_shear (1 : Fin 2) q)
  · intro p hp
    let q : H n := ⟨erase 1 p, erase_homogeneous 1 p.property⟩
    have hfirst : p - q ∈ LinearMap.range (difference n 0 1) := by
      apply (show p - q ∈ LinearMap.range (difference n 0 1) ↔ erase 1 (p - q) = 0 from by
        simpa using mem_difference_range n (0 : Fin 2) (p - q)).mpr
      change erase 1 (p - erase 1 p) = 0
      rw [map_sub, erase_idem, sub_self]
    have hsecond : q ∈ LinearMap.range (difference n 0 2) := by
      apply (show q ∈ LinearMap.range (difference n 0 2) ↔ erase 2 q = 0 from by
        simpa using mem_difference_range n (1 : Fin 2) q).mpr
      change erase 2 (erase 1 p) = 0
      have hp' : lineEvalAlg p = 0 := congrArg Subtype.val hp
      rw [← line_rename_eval, hp', map_zero]
    have hsum := Submodule.add_mem_sup hfirst hsecond
    simpa only [sub_add_cancel, lineRelations] using hsum

/-- Coinvariants of the two plane-radical shears are binary homogeneous polynomials. -/
def planeQuotientEquiv (n : ℕ) : (H n ⧸ planeRelations n) ≃ₗ[ℚ] BinaryH n :=
  (Submodule.quotEquivOfEq _ _ (planeRelations_eq_ker n)).trans
    ((planeEval n).quotKerEquivOfSurjective (planeEval_surjective n))

/-- Coinvariants of the two line-radical shears are the homogeneous axis line. -/
def lineQuotientEquiv (n : ℕ) : (H n ⧸ lineRelations n) ≃ₗ[ℚ] UnaryH n :=
  (Submodule.quotEquivOfEq _ _ (lineRelations_eq_ker n)).trans
    ((lineEval n).quotKerEquivOfSurjective (lineEval_surjective n))

@[simp] theorem planeQuotientEquiv_mk (n : ℕ) (p : H n) :
    planeQuotientEquiv n (Submodule.Quotient.mk p) = planeEval n p := rfl

@[simp] theorem lineQuotientEquiv_mk (n : ℕ) (p : H n) :
    lineQuotientEquiv n (Submodule.Quotient.mk p) = lineEval n p := rfl

end TernaryPoly.RadicalCoinvariantAlgebra
