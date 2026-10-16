module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Matrices

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeStabilizerParameters
open ModThreeGoodAction RelativeStabilizerCoordinates RelativeStabilizerMatrices

abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) ℤ

/-- The exact congruence subgroup occurring as the lower line-stabilizer block. -/
def Gamma : Subgroup GL2 where
  carrier := {D | Matrix.vecMul (![0,1] : Fin 2 → ZMod 3)
    (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) D).val = ![0,1]}
  one_mem' := by simp
  mul_mem' hg hh := by
    change Matrix.vecMul _ (Matrix.GeneralLinearGroup.map _ (_*_)).val = _
    rw [map_mul,Units.val_mul,← Matrix.vecMul_vecMul,hg,hh]
  inv_mem' := by
    intro D hD
    have h := congrArg (fun row => Matrix.vecMul row
      (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) D⁻¹).val) hD
    rw [Matrix.vecMul_vecMul] at h
    have he : (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) D).val *
        (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) D⁻¹).val = 1 := by
      rw [← Units.val_mul,← map_mul,mul_inv_cancel,map_one,Units.val_one]
    rw [he,Matrix.vecMul_one] at h
    exact h.symm

theorem mem_Gamma_iff (D : GL2) : D ∈ Gamma ↔ GammaEntries D.val := by
  change Matrix.vecMul (![0,1] : Fin 2 → ZMod 3)
    (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) D).val = ![0,1] ↔ _
  simp only [funext_iff,Fin.forall_fin_succ,Fin.forall_fin_zero]
  simp [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.GeneralLinearGroup.map_apply,GammaEntries]

def planeElement (A : GL2) (u : Fin 2 → ℤ) : IntegralGL :=
  Matrix.GeneralLinearGroup.mk'' (planeMatrix A.val u) (by
    rw [det_planeMatrix]
    exact (Matrix.isUnit_iff_isUnit_det A.val).mp A.isUnit)

def lineElement (ε : ℤˣ) (u : Fin 2 → ℤ) (D : GL2) : IntegralGL :=
  Matrix.GeneralLinearGroup.mk'' (lineMatrix ε.val u D.val) (by
    rw [det_lineMatrix]
    exact ε.isUnit.mul ((Matrix.isUnit_iff_isUnit_det D.val).mp D.isUnit))

def bbElement (ε₀ ε₁ : ℤˣ) (a b c : ℤ) : IntegralGL :=
  Matrix.GeneralLinearGroup.mk'' (bbMatrix ε₀.val ε₁.val a b c) (by
    rw [det_bbMatrix]
    exact ε₀.isUnit.mul ε₁.isUnit)

def bgElement (ε₀ ε₁ : ℤˣ) (a b k : ℤ) : IntegralGL :=
  Matrix.GeneralLinearGroup.mk'' (bgMatrix ε₀.val ε₁.val a b k) (by
    rw [det_bgMatrix]
    exact ε₀.isUnit.mul ε₁.isUnit)

@[simp] theorem planeElement_val (A : GL2) (u : Fin 2 → ℤ) :
    (planeElement A u).val = planeMatrix A.val u := Matrix.GeneralLinearGroup.val_mk'' _ _

@[simp] theorem lineElement_val (ε : ℤˣ) (u : Fin 2 → ℤ) (D : GL2) :
    (lineElement ε u D).val = lineMatrix ε.val u D.val := Matrix.GeneralLinearGroup.val_mk'' _ _

@[simp] theorem bbElement_val (ε₀ ε₁ : ℤˣ) (a b c : ℤ) :
    (bbElement ε₀ ε₁ a b c).val = bbMatrix ε₀.val ε₁.val a b c := Matrix.GeneralLinearGroup.val_mk'' _ _

@[simp] theorem bgElement_val (ε₀ ε₁ : ℤˣ) (a b k : ℤ) :
    (bgElement ε₀ ε₁ a b k).val = bgMatrix ε₀.val ε₁.val a b k := Matrix.GeneralLinearGroup.val_mk'' _ _

theorem planeElement_mem (A : GL2) (u : Fin 2 → ℤ) : HP (planeElement A u) := by
  rw [hp_iff,planeElement_val]
  simp [planeMatrix]

theorem lineElement_mem_iff (ε : ℤˣ) (u : Fin 2 → ℤ) (D : GL2) :
    HL (lineElement ε u D) ↔ GammaEntries D.val := by
  rw [hl_iff,lineElement_val]
  simp [lineMatrix,GammaEntries]

theorem bbElement_mem (ε₀ ε₁ : ℤˣ) (a b c : ℤ) : HBB (bbElement ε₀ ε₁ a b c) := by
  rw [hbb_iff_entries,bbElement_val]
  simp [bbMatrix]

theorem bgElement_mem (ε₀ ε₁ : ℤˣ) (a b k : ℤ) : HBG (bgElement ε₀ ε₁ a b k) := by
  rw [hbg_iff_entries,bgElement_val]
  have h3 : (3 : ZMod 3) = 0 := by decide +kernel
  simp [bgMatrix,h3]

def topBlock (g : IntegralGL) : Mat2 := ![![g.val 0 0,g.val 0 1],![g.val 1 0,g.val 1 1]]
def bottomBlock (g : IntegralGL) : Mat2 := ![![g.val 1 1,g.val 1 2],![g.val 2 1,g.val 2 2]]

/-- Every actual bad-plane stabilizer has a genuine GL₂ block and arbitrary integral column. -/
theorem hp_iff_parameter (g : IntegralGL) : HP g ↔
    ∃ (A : GL2) (u : Fin 2 → ℤ), g = planeElement A u := by
  constructor
  · intro hg
    obtain ⟨h20,h21,h22⟩ := (hp_iff g).mp hg
    have he : g.val = planeMatrix (topBlock g) ![g.val 0 2,g.val 1 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [planeMatrix,topBlock,h20,h21,h22]
    have hu : IsUnit (topBlock g).det := by
      rw [← det_planeMatrix (topBlock g) ![g.val 0 2,g.val 1 2],← he]
      exact det_isUnit g
    refine ⟨Matrix.GeneralLinearGroup.mk'' (topBlock g) hu,![g.val 0 2,g.val 1 2],?_⟩
    apply Units.ext
    rw [planeElement_val,Matrix.GeneralLinearGroup.val_mk'']
    exact he
  · rintro ⟨A,u,rfl⟩; exact planeElement_mem A u

/-- The line sign is unrestricted, while the bottom GL₂ block is the exact row-fixer. -/
theorem hl_iff_parameter (g : IntegralGL) : HL g ↔
    ∃ (ε : ℤˣ) (u : Fin 2 → ℤ) (D : GL2), GammaEntries D.val ∧ g = lineElement ε u D := by
  constructor
  · intro hg
    obtain ⟨h10,h20,h21,h22⟩ := (hl_iff g).mp hg
    have he : g.val = lineMatrix (g.val 0 0) ![g.val 0 1,g.val 0 2] (bottomBlock g) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lineMatrix,bottomBlock,h10,h20]
    have hd := det_isUnit g
    rw [he,det_lineMatrix] at hd
    let ε := (unit_of_mul_left hd).unit
    let D := Matrix.GeneralLinearGroup.mk'' (bottomBlock g) (unit_of_mul_right hd)
    refine ⟨ε,![g.val 0 1,g.val 0 2],D,?_,?_⟩
    · change GammaEntries (Matrix.GeneralLinearGroup.mk'' _ _).val
      rw [Matrix.GeneralLinearGroup.val_mk'']
      exact ⟨h21,h22⟩
    · apply Units.ext
      rw [lineElement_val]
      change g.val = lineMatrix ((unit_of_mul_left hd).unit).val _ (Matrix.GeneralLinearGroup.mk'' _ _).val
      rw [IsUnit.unit_spec,Matrix.GeneralLinearGroup.val_mk'']
      exact he
  · rintro ⟨ε,u,D,hD,rfl⟩; exact (lineElement_mem_iff ε u D).mpr hD

/-- Both diagonal signs in the bad/bad flag are independent integral units. -/
theorem hbb_iff_parameter (g : IntegralGL) : HBB g ↔
    ∃ (ε₀ ε₁ : ℤˣ) (a b c : ℤ), g = bbElement ε₀ ε₁ a b c := by
  constructor
  · intro hg
    obtain ⟨h10,h20,h21,h22⟩ := (hbb_iff_entries g).mp hg
    obtain ⟨hs0,hs1,_⟩ := edge_diagonal_signs (Or.inl hg)
    let u0 := (Int.isUnit_iff.mpr hs0).unit
    let u1 := (Int.isUnit_iff.mpr hs1).unit
    refine ⟨u0,u1,g.val 0 1,g.val 0 2,g.val 1 2,?_⟩
    apply Units.ext
    rw [bbElement_val]
    have hu0 : u0.val = g.val 0 0 := IsUnit.unit_spec _
    have hu1 : u1.val = g.val 1 1 := IsUnit.unit_spec _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bbMatrix,hu0,hu1,h10,h20,h21,h22]
  · rintro ⟨ε₀,ε₁,a,b,c,rfl⟩; exact bbElement_mem ε₀ ε₁ a b c

/-- The lower-left off-diagonal parameter in the good plane is exactly a multiple of three. -/
theorem hbg_iff_parameter (g : IntegralGL) : HBG g ↔
    ∃ (ε₀ ε₁ : ℤˣ) (a b k : ℤ), g = bgElement ε₀ ε₁ a b k := by
  constructor
  · intro hg
    obtain ⟨h10,h20,h12,h21,h22⟩ := (hbg_iff_entries g).mp hg
    obtain ⟨hs0,hs1,_⟩ := edge_diagonal_signs (Or.inr hg)
    have hd : (3 : ℤ) ∣ g.val 2 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h21
    obtain ⟨k,hk⟩ := hd
    let u0 := (Int.isUnit_iff.mpr hs0).unit
    let u1 := (Int.isUnit_iff.mpr hs1).unit
    refine ⟨u0,u1,g.val 0 1,g.val 0 2,k,?_⟩
    apply Units.ext
    rw [bgElement_val]
    have hu0 : u0.val = g.val 0 0 := IsUnit.unit_spec _
    have hu1 : u1.val = g.val 1 1 := IsUnit.unit_spec _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bgMatrix,hu0,hu1,h10,h20,h12,hk,h22]
  · rintro ⟨ε₀,ε₁,a,b,k,rfl⟩; exact bgElement_mem ε₀ ε₁ a b k

/-- The common independent-sign diagonal subgroup, as an explicit group homomorphism. -/
def diagonalHom : (ℤˣ × ℤˣ) →* IntegralGL where
  toFun ε := bbElement ε.1 ε.2 0 0 0
  map_one' := by
    apply Units.ext
    rw [bbElement_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bbMatrix]
  map_mul' ε δ := by
    apply Units.ext
    rw [Units.val_mul,bbElement_val,bbElement_val,bbElement_val]
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [bbMatrix,Fin.sum_univ_three]

theorem diagonalHom_injective : Function.Injective diagonalHom := by
  intro ε δ h
  have he := congrArg Units.val h
  change (bbElement ε.1 ε.2 0 0 0).val = (bbElement δ.1 δ.2 0 0 0).val at he
  rw [bbElement_val,bbElement_val] at he
  apply Prod.ext
  · apply Units.ext
    exact congrArg (fun M : Mat => M 0 0) he
  · apply Units.ext
    exact congrArg (fun M : Mat => M 1 1) he

theorem diagonalHom_mem_both (ε : ℤˣ × ℤˣ) : HBB (diagonalHom ε) ∧ HBG (diagonalHom ε) := by
  refine ⟨bbElement_mem _ _ _ _ _,?_⟩
  change HBG (bbElement ε.1 ε.2 0 0 0)
  rw [hbg_iff_entries,bbElement_val]
  simp [bbMatrix]

end TernaryPoly.RelativeStabilizerParameters
