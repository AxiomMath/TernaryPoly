module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantMatrices
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeEdgeCohomologyMatrices
open RelativeStabilizerConsumer RelativeStabilizerParameters RelativeStabilizerMatrices
open RadicalCoinvariantAlgebra

/-- The three primitive upper triangular root subgroups, ordered E12,E13,E23. -/
def bbRoot (k : Fin 3) (t : ℤ) : HBBGroup :=
  ⟨rootElement k t, by fin_cases k <;> exact bbElement_mem _ _ _ _ _⟩

/-- The good-edge roots, ordered E13,3E32,E12. -/
def bgRoot (k : Fin 3) (t : ℤ) : HBGGroup :=
  ⟨![bgElement 1 1 0 t 0, bgElement 1 1 0 0 t, bgElement 1 1 t 0 0] k,
    by fin_cases k <;> exact bgElement_mem _ _ _ _ _⟩

/-- The literal diagonal sign homomorphism into the BB stabilizer. -/
def bbSigns : (ℤˣ × ℤˣ) →* HBBGroup where
  toFun ε := ⟨diagonalHom ε, (diagonalHom_mem_both ε).1⟩
  map_one' := Subtype.ext (map_one diagonalHom)
  map_mul' ε δ := Subtype.ext (map_mul diagonalHom ε δ)

/-- The same two independent signs in the BG stabilizer. -/
def bgSigns : (ℤˣ × ℤˣ) →* HBGGroup where
  toFun ε := ⟨diagonalHom ε, (diagonalHom_mem_both ε).2⟩
  map_one' := Subtype.ext (map_one diagonalHom)
  map_mul' ε δ := Subtype.ext (map_mul diagonalHom ε δ)

abbrev bbFirst := bbSigns (-1,1)
abbrev bbSecond := bbSigns (1,-1)
abbrev bgFirst := bgSigns (-1,1)
abbrev bgSecond := bgSigns (1,-1)

@[simp] lemma bbRoot_zero (k : Fin 3) : bbRoot k 0 = 1 :=
  Subtype.ext (rootElement_zero k)

lemma bbRoot_mul (k : Fin 3) (s t : ℤ) : bbRoot k s * bbRoot k t = bbRoot k (s+t) :=
  Subtype.ext (rootElement_mul k s t)

@[simp] lemma bbRoot_inv (k : Fin 3) (t : ℤ) : (bbRoot k t)⁻¹ = bbRoot k (-t) :=
  Subtype.ext (rootElement_inv k t)

@[simp] lemma bgRoot_zero (k : Fin 3) : bgRoot k 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [bgRoot, bgMatrix]

lemma bgRoot_mul (k : Fin 3) (s t : ℤ) : bgRoot k s * bgRoot k t = bgRoot k (s+t) := by
  apply Subtype.ext
  apply Units.ext
  change _ * _ = _
  fin_cases k <;> ext i j <;> rw [Matrix.mul_apply] <;>
    fin_cases i <;> fin_cases j <;> simp [bgRoot, bgMatrix, Fin.sum_univ_three] <;> ring

@[simp] lemma bgRoot_inv (k : Fin 3) (t : ℤ) : (bgRoot k t)⁻¹ = bgRoot k (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [bgRoot_mul, add_neg_cancel, bgRoot_zero]

lemma bb_signs_involutions : bbFirst*bbFirst=1 ∧ bbSecond*bbSecond=1 ∧
    bbFirst*bbSecond=bbSecond*bbFirst := by
  simp [← map_mul, bbFirst, bbSecond]
  exact map_one bbSigns

lemma bg_signs_involutions : bgFirst*bgFirst=1 ∧ bgSecond*bgSecond=1 ∧
    bgFirst*bgSecond=bgSecond*bgFirst := by
  simp [← map_mul, bgFirst, bgSecond]
  exact map_one bgSigns

/-- Exact diagonal conjugation on all three BB root parameters. -/
lemma bbFirst_root (k : Fin 3) (t : ℤ) :
    bbFirst * bbRoot k t = bbRoot k (![(-t),(-t),t] k) * bbFirst := by
  apply Subtype.ext
  apply Units.ext
  change _ * _ = _ * _
  fin_cases k <;> ext i j <;> rw [Matrix.mul_apply, Matrix.mul_apply] <;>
    fin_cases i <;> fin_cases j <;>
    simp [bbFirst, bbSigns, diagonalHom, bbRoot, rootElement, bbMatrix, Fin.sum_univ_three]

lemma bbSecond_root (k : Fin 3) (t : ℤ) :
    bbSecond * bbRoot k t = bbRoot k (![(-t),t,(-t)] k) * bbSecond := by
  apply Subtype.ext
  apply Units.ext
  change _ * _ = _ * _
  fin_cases k <;> ext i j <;> rw [Matrix.mul_apply, Matrix.mul_apply] <;>
    fin_cases i <;> fin_cases j <;>
    simp [bbSecond, bbSigns, diagonalHom, bbRoot, rootElement, bbMatrix, Fin.sum_univ_three]

/-- Exact diagonal conjugation, including the nonprimitive BG root. -/
lemma bgFirst_root (k : Fin 3) (t : ℤ) :
    bgFirst * bgRoot k t = bgRoot k (![(-t),t,(-t)] k) * bgFirst := by
  apply Subtype.ext
  apply Units.ext
  change _ * _ = _ * _
  fin_cases k <;> ext i j <;> rw [Matrix.mul_apply, Matrix.mul_apply] <;>
    fin_cases i <;> fin_cases j <;>
    simp [bgFirst, bgSigns, diagonalHom, bgRoot, bbMatrix, bgMatrix, Fin.sum_univ_three]

lemma bgSecond_root (k : Fin 3) (t : ℤ) :
    bgSecond * bgRoot k t = bgRoot k (![t,(-t),(-t)] k) * bgSecond := by
  apply Subtype.ext
  apply Units.ext
  change _ * _ = _ * _
  fin_cases k <;> ext i j <;> rw [Matrix.mul_apply, Matrix.mul_apply] <;>
    fin_cases i <;> fin_cases j <;>
    simp [bgSecond, bgSigns, diagonalHom, bgRoot, bbMatrix, bgMatrix, Fin.sum_univ_three]

lemma bb_first_central (s t : ℤ) : bbRoot 0 s * bbRoot 1 t = bbRoot 1 t * bbRoot 0 s := by
  apply Subtype.ext
  apply Units.ext
  change _ * _ = _ * _
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [bbRoot, rootElement, bbMatrix, Fin.sum_univ_three]

lemma bg_first_central (s t : ℤ) : bgRoot 0 s * bgRoot 2 t = bgRoot 2 t * bgRoot 0 s := by
  apply Subtype.ext
  apply Units.ext
  change _ * _ = _ * _
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [bgRoot, bgMatrix, Fin.sum_univ_three]

/-- The BB Heisenberg commutator has its actual primitive central parameter. -/
lemma bb_commutator (s t : ℤ) :
    bbRoot 0 s * bbRoot 2 t = bbRoot 2 t * bbRoot 0 s * bbRoot 1 (s*t) := by
  apply Subtype.ext
  apply Units.ext
  change _ * _ = (_ * _) * _
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [bbRoot, rootElement, bbMatrix]

/-- The level-three BG root produces three times the primitive central root. -/
lemma bg_commutator (s t : ℤ) :
    bgRoot 0 s * bgRoot 1 t = bgRoot 1 t * bgRoot 0 s * bgRoot 2 (3*s*t) := by
  apply Subtype.ext
  apply Units.ext
  change _ * _ = (_ * _) * _
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [bgRoot, bgMatrix]
  ring

/-- Reverse root order factors every actual BB matrix without a rational denominator. -/
lemma bb_parameter_factor (ε₀ ε₁ : ℤˣ) (a b c : ℤ) :
    (bbElement ε₀ ε₁ a b c : ModThreeGoodAction.IntegralGL) =
      (bbRoot 2 c * bbRoot 1 b * bbRoot 0 (a*ε₁.val) * bbSigns (ε₀,ε₁)).val := by
  apply Units.ext
  change (bbElement ε₀ ε₁ a b c).val = ((_ * _) * _) * _
  rcases Int.units_eq_one_or ε₀ with rfl | rfl <;>
    rcases Int.units_eq_one_or ε₁ with rfl | rfl <;>
    ext i j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    fin_cases i <;> fin_cases j <;>
    simp [bbRoot, rootElement, bbSigns, diagonalHom, bbMatrix]

/-- The BG factorization preserves the exact multiple-of-three root lattice. -/
lemma bg_parameter_factor (ε₀ ε₁ : ℤˣ) (a b k : ℤ) :
    (bgElement ε₀ ε₁ a b k : ModThreeGoodAction.IntegralGL) =
      (bgRoot 1 (k*ε₁.val) * bgRoot 2 (a*ε₁.val) * bgRoot 0 b * bgSigns (ε₀,ε₁)).val := by
  apply Units.ext
  change (bgElement ε₀ ε₁ a b k).val = ((_ * _) * _) * _
  rcases Int.units_eq_one_or ε₀ with rfl | rfl <;>
    rcases Int.units_eq_one_or ε₁ with rfl | rfl <;>
    ext i j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    fin_cases i <;> fin_cases j <;>
    simp [bgRoot, bgSigns, diagonalHom, bbMatrix, bgMatrix]

lemma bb_factor (g : HBBGroup) :
    ∃ (ε₀ ε₁ : ℤˣ) (a b c : ℤ),
      g = bbRoot 2 c * bbRoot 1 b * bbRoot 0 a * bbSigns (ε₀,ε₁) := by
  obtain ⟨ε₀,ε₁,a,b,c,hg⟩ := (hbb_iff_parameter g.val).mp g.property
  exact ⟨ε₀,ε₁,a*ε₁.val,b,c,Subtype.ext (hg.trans (bb_parameter_factor ε₀ ε₁ a b c))⟩

lemma bg_factor (g : HBGGroup) :
    ∃ (ε₀ ε₁ : ℤˣ) (a b k : ℤ),
      g = bgRoot 1 k * bgRoot 2 a * bgRoot 0 b * bgSigns (ε₀,ε₁) := by
  obtain ⟨ε₀,ε₁,a,b,k,hg⟩ := (hbg_iff_parameter g.val).mp g.property
  exact ⟨ε₀,ε₁,a*ε₁.val,b,k*ε₁.val,Subtype.ext (hg.trans (bg_parameter_factor ε₀ ε₁ a b k))⟩

def bbRootHom (k : Fin 3) : Multiplicative ℤ →* HBBGroup where
  toFun t := bbRoot k t.toAdd
  map_one' := bbRoot_zero k
  map_mul' s t := (bbRoot_mul k s.toAdd t.toAdd).symm

def bgRootHom (k : Fin 3) : Multiplicative ℤ →* HBGGroup where
  toFun t := bgRoot k t.toAdd
  map_one' := bgRoot_zero k
  map_mul' s t := (bgRoot_mul k s.toAdd t.toAdd).symm

lemma bbRoot_zpow (k : Fin 3) (t : ℤ) : bbRoot k t = (bbRoot k 1)^t := by
  simpa [bbRootHom] using (map_zpow (bbRootHom k) (Multiplicative.ofAdd 1) t)

lemma bgRoot_zpow (k : Fin 3) (t : ℤ) : bgRoot k t = (bgRoot k 1)^t := by
  simpa [bgRootHom] using (map_zpow (bgRootHom k) (Multiplicative.ofAdd 1) t)

end TernaryPoly.RelativeEdgeCohomologyMatrices
