module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Coordinates

@[expose] public section

noncomputable section
namespace TernaryPoly.RelativeStabilizerMatrices
open ModThreeGoodAction RelativeStabilizerCoordinates

abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℤ

def IsSign (z : ℤ) : Prop := z = 1 ∨ z = -1

theorem det_isUnit (g : IntegralGL) : IsUnit g.val.det :=
  (Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit

theorem unit_of_mul_left {a b : ℤ} (h : IsUnit (a*b)) : IsUnit a :=
  ((Commute.all a b).isUnit_mul_iff).mp h |>.1

theorem unit_of_mul_right {a b : ℤ} (h : IsUnit (a*b)) : IsUnit b :=
  ((Commute.all a b).isUnit_mul_iff).mp h |>.2

theorem sign_eq_one_of_residue {z : ℤ} (hz : IsSign z) (hr : (z : ZMod 3) = 1) : z = 1 := by
  rcases hz with rfl | rfl
  · rfl
  · exact False.elim ((by decide +kernel : (-1 : ZMod 3) ≠ 1) hr)

/-- Exact bad-plane stabilizer predicate in the full integral matrix group. -/
def HP (g : IntegralGL) : Prop := g ∈ K3 ∧ Stabilizes g P0
/-- Exact bad-line stabilizer predicate. -/
def HL (g : IntegralGL) : Prop := g ∈ K3 ∧ Stabilizes g L0
/-- Exact bad-line/bad-plane flag stabilizer. -/
def HBB (g : IntegralGL) : Prop := g ∈ K3 ∧ Stabilizes g L0 ∧ Stabilizes g P0
/-- Exact bad-line/good-plane flag stabilizer. -/
def HBG (g : IntegralGL) : Prop := g ∈ K3 ∧ Stabilizes g L0 ∧ Stabilizes g P1

theorem hp_iff (g : IntegralGL) : HP g ↔
    g.val 2 0 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1 := by
  rw [HP,mem_K3_iff,stabilizes_P0_iff]
  constructor
  · rintro ⟨⟨_,_,hr⟩,h0,h1⟩
    refine ⟨h0,h1,sign_eq_one_of_residue ?_ hr⟩
    have hd := det_isUnit g
    have he : g.val.det = (g.val 0 0*g.val 1 1-g.val 0 1*g.val 1 0)*g.val 2 2 := by
      rw [Matrix.det_fin_three,h0,h1]
      ring
    rw [he] at hd
    exact Int.isUnit_iff.mp (unit_of_mul_right hd)
  · rintro ⟨h0,h1,h2⟩
    simp [h0,h1,h2]

theorem hl_iff (g : IntegralGL) : HL g ↔
    g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧
      (g.val 2 1 : ZMod 3) = 0 ∧ (g.val 2 2 : ZMod 3) = 1 := by
  rw [HL,mem_K3_iff,stabilizes_L0_iff]
  constructor
  · rintro ⟨⟨_,h21,h22⟩,h10,h20⟩; exact ⟨h10,h20,h21,h22⟩
  · rintro ⟨h10,h20,h21,h22⟩; exact ⟨⟨by simp [h20],h21,h22⟩,h10,h20⟩

theorem hl_line_sign {g : IntegralGL} (hg : HL g) : IsSign (g.val 0 0) := by
  obtain ⟨h10,h20,_,_⟩ := (hl_iff g).mp hg
  have hd := det_isUnit g
  have he : g.val.det = g.val 0 0*(g.val 1 1*g.val 2 2-g.val 1 2*g.val 2 1) := by
    rw [Matrix.det_fin_three,h10,h20]
    ring
  rw [he] at hd
  exact Int.isUnit_iff.mp (unit_of_mul_left hd)

theorem hbb_iff_entries (g : IntegralGL) : HBB g ↔
    g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1 := by
  change (g ∈ K3 ∧ Stabilizes g L0 ∧ Stabilizes g P0) ↔ _
  constructor
  · rintro ⟨hk,hl,hp⟩
    obtain ⟨h20,h21,h22⟩ := (hp_iff g).mp ⟨hk,hp⟩
    exact ⟨((stabilizes_L0_iff g).mp hl).1,h20,h21,h22⟩
  · rintro ⟨h10,h20,h21,h22⟩
    obtain ⟨hk,hp⟩ := (hp_iff g).mpr ⟨h20,h21,h22⟩
    exact ⟨hk,(stabilizes_L0_iff g).mpr ⟨h10,h20⟩,hp⟩

theorem hbg_iff_entries (g : IntegralGL) : HBG g ↔
    g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 1 2 = 0 ∧
      (g.val 2 1 : ZMod 3) = 0 ∧ g.val 2 2 = 1 := by
  rw [HBG,mem_K3_iff,stabilizes_L0_iff,stabilizes_P1_iff]
  constructor
  · rintro ⟨⟨_,h21,h22⟩,⟨h10,h20⟩,⟨_,h12⟩⟩
    refine ⟨h10,h20,h12,h21,sign_eq_one_of_residue ?_ h22⟩
    have hd := det_isUnit g
    have he : g.val.det = (g.val 0 0*g.val 1 1)*g.val 2 2 := by
      rw [Matrix.det_fin_three,h10,h20,h12]
      ring
    rw [he] at hd
    exact Int.isUnit_iff.mp (unit_of_mul_right hd)
  · rintro ⟨h10,h20,h12,h21,h22⟩
    exact ⟨⟨by simp [h20],h21,by simp [h22]⟩,⟨h10,h20⟩,⟨h10,h12⟩⟩

theorem edge_diagonal_signs {g : IntegralGL} (hg : HBB g ∨ HBG g) :
    IsSign (g.val 0 0) ∧ IsSign (g.val 1 1) ∧ g.val 2 2 = 1 := by
  have he : g.val.det = g.val 0 0*g.val 1 1 ∧ g.val 2 2 = 1 := by
    rcases hg with hg | hg
    · obtain ⟨h10,h20,h21,h22⟩ := (hbb_iff_entries g).mp hg
      refine ⟨?_,h22⟩
      rw [Matrix.det_fin_three,h10,h20,h21,h22]
      ring
    · obtain ⟨h10,h20,h12,_,h22⟩ := (hbg_iff_entries g).mp hg
      refine ⟨?_,h22⟩
      rw [Matrix.det_fin_three,h10,h20,h12,h22]
      ring
  have hd := det_isUnit g
  rw [he.1] at hd
  exact ⟨Int.isUnit_iff.mp (unit_of_mul_left hd),Int.isUnit_iff.mp (unit_of_mul_right hd),he.2⟩

/-- Literal bad-plane block matrix. -/
def planeMatrix (A : Mat2) (u : Fin 2 → ℤ) : Mat :=
  ![![A 0 0,A 0 1,u 0],![A 1 0,A 1 1,u 1],![0,0,1]]

/-- Literal bad-line block matrix. -/
def lineMatrix (ε : ℤ) (u : Fin 2 → ℤ) (D : Mat2) : Mat :=
  ![![ε,u 0,u 1],![0,D 0 0,D 0 1],![0,D 1 0,D 1 1]]

/-- The lower block fixes the row `(0,1)` modulo three. -/
def GammaEntries (D : Mat2) : Prop := (D 1 0 : ZMod 3) = 0 ∧ (D 1 1 : ZMod 3) = 1

def bbMatrix (ε₀ ε₁ a b c : ℤ) : Mat :=
  ![![ε₀,a,b],![0,ε₁,c],![0,0,1]]

def bgMatrix (ε₀ ε₁ a b k : ℤ) : Mat :=
  ![![ε₀,a,b],![0,ε₁,0],![0,3*k,1]]

theorem det_planeMatrix (A : Mat2) (u : Fin 2 → ℤ) : (planeMatrix A u).det = A.det := by
  rw [Matrix.det_fin_three,Matrix.det_fin_two]
  simp [planeMatrix]

theorem det_lineMatrix (ε : ℤ) (u : Fin 2 → ℤ) (D : Mat2) :
    (lineMatrix ε u D).det = ε*D.det := by
  rw [Matrix.det_fin_three,Matrix.det_fin_two]
  simp [lineMatrix]
  ring

theorem det_bbMatrix (ε₀ ε₁ a b c : ℤ) : (bbMatrix ε₀ ε₁ a b c).det = ε₀*ε₁ := by
  rw [Matrix.det_fin_three]
  simp [bbMatrix]

theorem det_bgMatrix (ε₀ ε₁ a b k : ℤ) : (bgMatrix ε₀ ε₁ a b k).det = ε₀*ε₁ := by
  rw [Matrix.det_fin_three]
  simp [bgMatrix]

end TernaryPoly.RelativeStabilizerMatrices
