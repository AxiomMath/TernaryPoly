module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.Counting
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.LineTransfer

@[expose] public section


/-!
# The plane and line parabolics as `ParabolicData`

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

/-- The units `±1` of `ℚ`. -/
def signs : Subgroup ℚˣ := (Units.map (Int.castRingHom ℚ : ℤ →* ℚ)).range

theorem mem_signs {s : ℚˣ} : s ∈ signs ↔ s = 1 ∨ s = -1 := by
  constructor
  · rintro ⟨ε, rfl⟩
    rcases Int.units_eq_one_or ε with h | h <;> subst h
    · left; exact map_one _
    · right; exact Units.ext (by simp)
  · rintro (h | h) <;> subst h
    · exact ⟨1, map_one _⟩
    · exact ⟨-1, Units.ext (by simp)⟩

theorem planeLevi_mem_Γ {B : GeneralLinearGroup (Fin 2) ℚ} {s : ℚˣ} (hB : B ∈ Γ2)
    (hs : s ∈ signs) : planeLevi B s ∈ Γ := by
  obtain ⟨k, rfl⟩ := hB
  obtain ⟨ε, rfl⟩ := hs
  exact ⟨planeLevi k ε, TernaryPeriodPolynomials.HeckeEigen.planeLevi_map _ k ε⟩

theorem lineLevi_mem_Γ {A : GeneralLinearGroup (Fin 2) ℚ} {d : ℚˣ} (hA : A ∈ Γ2)
    (hd : d ∈ signs) : lineLevi d A ∈ Γ := by
  obtain ⟨k, rfl⟩ := hA
  obtain ⟨ε, rfl⟩ := hd
  exact ⟨lineLevi ε k, TernaryPeriodPolynomials.HeckeEigen.lineLevi_map _ ε k⟩

theorem pU_planeLevi_mem_Γ_iff (u : ℚ × ℚ) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    pU u * planeLevi B s ∈ Γ ↔ u ∈ zLat ∧ (B, s) ∈ Γ2.prod signs := by
  constructor
  · intro h
    obtain ⟨hB, hs⟩ := plane_levi_integral h
    have hs' : s ∈ signs := mem_signs.mpr hs
    have hL := planeLevi_mem_Γ hB hs'
    have hu : pU u ∈ Γ := by
      have := Γ.mul_mem h (Γ.inv_mem hL)
      rwa [mul_inv_cancel_right] at this
    exact ⟨(pU_mem_Γ u).mp hu, hB, hs'⟩
  · rintro ⟨hu, hB, hs⟩
    exact Γ.mul_mem ((pU_mem_Γ u).mpr hu) (planeLevi_mem_Γ hB hs)

/-- A line-parabolic element of `GL₃(ℤ)` has integral Levi part. -/
theorem line_levi_integral {w : ℚ × ℚ} {d : ℚˣ} {A : GeneralLinearGroup (Fin 2) ℚ}
    (h : lU w * lineLevi d A ∈ Γ) : A ∈ Γ2 ∧ (d = 1 ∨ d = -1) := by
  obtain ⟨h1, h2⟩ := (mem_Γ_iff _).mp h
  have hinv : (lU w * lineLevi d A)⁻¹ = lineLevi d⁻¹ A⁻¹ * lU (-w) := by
    rw [_root_.mul_inv_rev, lU_neg]
    congr 1
    exact ((lineLeviHom ℚ).map_inv (d, A)).symm
  rw [hinv] at h2
  refine ⟨(mem_Γ2_iff A).mpr ⟨fun i j => ?_, fun i j => ?_⟩, int_unit_of_int_inv ?_ ?_⟩
  · obtain ⟨z, hz⟩ := h1 i.succ j.succ
    refine ⟨z, ?_⟩
    rw [hz]
    fin_cases i <;> fin_cases j <;>
      simp [lU, lineUnipotent, upperUnipotent, lineLevi_val, Matrix.mul_apply, Fin.sum_univ_three]
  · obtain ⟨z, hz⟩ := h2 i.succ j.succ
    refine ⟨z, ?_⟩
    rw [hz]
    fin_cases i <;> fin_cases j <;>
      simp [lU, lineUnipotent, upperUnipotent, lineLevi_val, Matrix.mul_apply, Fin.sum_univ_three]
  · obtain ⟨z, hz⟩ := h1 0 0
    refine ⟨z, ?_⟩
    rw [hz]
    simp [lU, lineUnipotent, upperUnipotent, lineLevi_val, Matrix.mul_apply, Fin.sum_univ_three]
  · obtain ⟨z, hz⟩ := h2 0 0
    refine ⟨z, ?_⟩
    rw [hz]
    simp [lU, lineUnipotent, upperUnipotent, lineLevi_val, Matrix.mul_apply, Fin.sum_univ_three]

theorem lU_lineLevi_mem_Γ_iff (u : ℚ × ℚ) (A : GeneralLinearGroup (Fin 2) ℚ) (d : ℚˣ) :
    lU u * lineLevi d A ∈ Γ ↔ u ∈ zLat ∧ (A, d) ∈ Γ2.prod signs := by
  constructor
  · intro h
    obtain ⟨hA, hd⟩ := line_levi_integral h
    have hd' : d ∈ signs := mem_signs.mpr hd
    have hL := lineLevi_mem_Γ hA hd'
    have hu : lU u ∈ Γ := by
      have := Γ.mul_mem h (Γ.inv_mem hL)
      rwa [mul_inv_cancel_right] at this
    exact ⟨(lU_mem_Γ u).mp hu, hA, hd'⟩
  · rintro ⟨hu, hA, hd⟩
    exact Γ.mul_mem ((lU_mem_Γ u).mpr hu) (lineLevi_mem_Γ hA hd)

/-- The plane parabolic. -/
def planeData : ParabolicData Γ (GeneralLinearGroup (Fin 2) ℚ × ℚˣ) where
  U := pU
  L := planeLeviHom ℚ
  φ m := matHom ((m.2 : ℚ) • (m.1⁻¹).val)
  ΓM := Γ2.prod signs
  U_add := pU_add
  U_inj a b h := by
    have h1 := congrArg (fun x : RationalGL3 => x.val 0 2) h
    have h2 := congrArg (fun x : RationalGL3 => x.val 1 2) h
    simp [pU, planeUnipotent] at h1 h2
    exact Prod.ext h1 h2
  conj m u := conj_pU m.1 m.2 u
  mem u m := pU_planeLevi_mem_Γ_iff u m.1 m.2

/-- The line parabolic, with Levi coordinates `(A, d)`. -/
def lineData : ParabolicData Γ (GeneralLinearGroup (Fin 2) ℚ × ℚˣ) where
  U := lU
  L := (lineLeviHom ℚ).comp (MulEquiv.prodComm).toMonoidHom
  φ m := matHom (((m.2⁻¹ : ℚˣ) : ℚ) • m.1.valᵀ)
  ΓM := Γ2.prod signs
  U_add := lU_add
  U_inj a b h := by
    have h1 := congrArg (fun x : RationalGL3 => x.val 0 1) h
    have h2 := congrArg (fun x : RationalGL3 => x.val 0 2) h
    simp [lU, lineUnipotent, upperUnipotent] at h1 h2
    exact Prod.ext h1 h2
  conj m u := conj_lU m.2 m.1 u
  mem u m := lU_lineLevi_mem_Γ_iff u m.1 m.2

theorem planeData_L (m : GeneralLinearGroup (Fin 2) ℚ × ℚˣ) : planeData.L m = planeLevi m.1 m.2 :=
  rfl

theorem lineData_L (m : GeneralLinearGroup (Fin 2) ℚ × ℚˣ) : lineData.L m = lineLevi m.2 m.1 :=
  rfl

end TernaryPeriodPolynomials.HeckeEigen.Satake
