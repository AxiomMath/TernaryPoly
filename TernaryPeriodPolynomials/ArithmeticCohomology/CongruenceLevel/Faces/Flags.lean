module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineFaces
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.LocallyInner
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RestrictionComposition

@[expose] public section


/-!
# Complete flags over the line cusps of `Γ(N)`, locally inner classes, and the exclusion of nonmixed components

Formalized by Claude Sonnet 5.5.
Paper: Appendix C, ("It remains to exclude a nonmixed face component ... Choose
a flag in this face. Its stabilizer contains `N_R`, so zero restriction at that flag implies zero restriction to `N_R`.
Exactness puts the face class in the mixed term. The restriction of this term to a flag is its binary cusp restriction").

For the line cusp `Q' = h⁻¹ Q h` of `Γ(N)`, the complete flags over the line correspond to the rational cusps `F · ∞` of the binary Levi
`Γ₂(N)` (the planes containing the line).  `lineFlagStab N h F` is the stabilizer of that flag in the line group `Γ_{Q'}` (the preimage of
the cusp stabilizer `leviCuspStab`), `lineFlagRep` the restriction of `E_n` to it.  The standard flag over the cusp `Q'` is
`h⁻¹ B h`, `B` the upper triangular group: `gammaNBAt N h` is its arithmetic group `Γ(N) ∩ h⁻¹ B h` with coefficient module `flagRep N h n`
(`lineFlagStab_one_iff`).

* `lineFlagStab_contains_radical`, `restriction_radical_eq_zero_of_flag`: the flag stabilizer contains `N_{Q'}`, so zero restriction at a
  flag implies zero restriction to the radical.
* `lineLocallyInner_eq_iInf`: the locally inner classes are those vanishing on every flag stabilizer (vanishing on the radical is automatic).
* `lineFaceCuspidalInH2_eq_locallyInner` / `lineFace_mixed_of_flags_vanish`: **nonmixed components are excluded**: a class with zero
  restriction at every flag lies in the mixed term (the image of `𝒞_{Q'}(E)`), and conversely.
* `lineFace_flag_restriction_edge`: the restriction of a mixed class to a flag is zero iff its binary cusp restriction is zero.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaces

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3S4c

section Standard

/-- The upper triangular elements of `SL₃(ℤ)`. -/
def borelStab : Subgroup SL(3, ℤ) where
  carrier := {γ | (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧ (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
    (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0}
  mul_mem' := by
    rintro γ δ ⟨h0, h1, h2⟩ ⟨k0, k1, k2⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2, k0, k1, k2]
  one_mem' := by simp
  inv_mem' := by
    rintro γ ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, h0, h1, h2]

/-- The flag group `Γ(N) ∩ B(ℤ)`. -/
def gammaNB (N : ℕ) : Subgroup SL(3, ℤ) := gammaN N ⊓ borelStab

/-- The flag group of the standard complete flag over the cusp `h⁻¹ Q h` (equivalently `h⁻¹ P h`): `Γ(N) ∩ h⁻¹ B h`. -/
def gammaNBAt (N : ℕ) (h : SL(3, ℤ)) : Subgroup SL(3, ℤ) := (gammaNB N).comap (MulAut.conj h).toMonoidHom

theorem mem_gammaNBAt {N : ℕ} {h p : SL(3, ℤ)} : p ∈ gammaNBAt N h ↔ h * p * h⁻¹ ∈ gammaNB N := Iff.rfl

/-- **The coefficient module `E_n` restricted to the flag group `Γ(N) ∩ h⁻¹ B h`.** -/
def flagRep (N : ℕ) (h : SL(3, ℤ)) (n : ℕ) : Rep ℂ (gammaNBAt N h) :=
  Rep.of ((ambRep n).comp (gammaNBAt N h).subtype)

theorem gammaNBAt_le_gammaNQAt {N : ℕ} (hN : 3 ≤ N) (h : SL(3, ℤ)) : gammaNBAt N h ≤ gammaNQAt N h := by
  intro p hp
  have hp' : h * p * h⁻¹ ∈ gammaNB N := hp
  exact ⟨hp'.1, mem_lineStab_of_gammaN hN hp'.1 hp'.2.1 hp'.2.2.1⟩

theorem gammaNBAt_le_gammaNPAt {N : ℕ} (hN : 3 ≤ N) (h : SL(3, ℤ)) : gammaNBAt N h ≤ gammaNPAt N h := by
  intro p hp
  have hp' : h * p * h⁻¹ ∈ gammaNB N := hp
  exact ⟨hp'.1, mem_planeStab_of_gammaN hN hp'.1 hp'.2.2.1 hp'.2.2.2⟩

end Standard

section Flags

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ))

/-- **The stabilizer, in the line group of the cusp `h⁻¹ Q h`, of the complete flag attached to the rational cusp of a frame
`F ∈ GL₂(ℚ)`** (the plane through the line given by the cusp `F · ∞` of the binary Levi). -/
def lineFlagStab (F : GL (Fin 2) ℚ) : Subgroup (gammaNQAt N h) :=
  (leviCuspStab (CongruenceSubgroup.Gamma N) F).comap (lineFaceExt N h).rightHom

/-- The coefficient module on the flag stabilizer of the frame `F`. -/
def lineFlagRep (F : GL (Fin 2) ℚ) (n : ℕ) : Rep ℂ (lineFlagStab N h F) :=
  Rep.res (lineFlagStab N h F).subtype (lineFaceRep N h n)

/-- **The locally inner classes of the line cusp `h⁻¹ Q h`**: the classes of `H²(Γ_{h⁻¹Qh}, E_n)` vanishing on the radical and on the
stabilizer of every complete flag over the line. -/
def lineLocallyInner (n : ℕ) : Submodule ℂ (groupCohomology.H2 (lineFaceRep N h n)) :=
  LinearMap.ker (twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n)) ⊓
    ⨅ F : GL (Fin 2) ℚ, LinearMap.ker
      (twoCohomologyRestriction (lineFlagStab N h F).subtype (lineFaceRep N h n))

/-- The radical lies in every flag stabilizer. -/
def lineInlFlag (F : GL (Fin 2) ℚ) : RadicalLattice →* lineFlagStab N h F :=
  (lineFaceExt N h).inl.codRestrict _ (fun r => by
    have : (lineFaceExt N h).rightHom ((lineFaceExt N h).inl r) = 1 := by
      have hk : (lineFaceExt N h).inl r ∈ (lineFaceExt N h).rightHom.ker := by
        rw [← (lineFaceExt N h).range_inl_eq_ker_rightHom]; exact ⟨r, rfl⟩
      exact hk
    show (lineFaceExt N h).rightHom ((lineFaceExt N h).inl r) ∈ leviCuspStab (CongruenceSubgroup.Gamma N) F
    rw [this]; exact one_mem _)

/-- **The flag stabilizer contains the radical `N_{Q'}`**: the radical inclusion factors through it. -/
theorem lineFlagStab_contains_radical (F : GL (Fin 2) ℚ) :
    (lineFaceExt N h).inl = (lineFlagStab N h F).subtype.comp (lineInlFlag N h F) := rfl

/-- **Zero restriction at one flag implies zero restriction to the radical**. -/
theorem restriction_radical_eq_zero_of_flag (n : ℕ) (F : GL (Fin 2) ℚ)
    (y : groupCohomology.H2 (lineFaceRep N h n))
    (hy : twoCohomologyRestriction (lineFlagStab N h F).subtype (lineFaceRep N h n) y = 0) :
    twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n) y = 0 := by
  rw [lineFlagStab_contains_radical, FacePairing.twoCohomologyRestriction_comp, hy, map_zero]

/-- The locally inner classes are the classes vanishing on every flag stabilizer (vanishing on the radical is automatic). -/
theorem lineLocallyInner_eq_iInf (n : ℕ) :
    lineLocallyInner N h n = ⨅ F : GL (Fin 2) ℚ, LinearMap.ker
      (twoCohomologyRestriction (lineFlagStab N h F).subtype (lineFaceRep N h n)) := by
  apply le_antisymm
  · exact inf_le_right
  · intro y hy
    refine ⟨?_, hy⟩
    exact restriction_radical_eq_zero_of_flag N h n 1 y
      (LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hy 1))

/-- **The mixed cuspidal group of the line cusp `h⁻¹ Q h` is the group of locally inner classes.** The image in `H²(Γ_{h⁻¹Qh}, E_n)` of
the group `𝒞_{Q'}(E) ⊂ H¹(Γ₂(N), H¹(N_{Q'}, E))` of classes vanishing at every rational cusp of the binary Levi is exactly the group of
classes vanishing on the stabilizer of every complete flag over the line (Hochschild-Serre). -/
theorem lineFaceCuspidalInH2_eq_locallyInner (n : ℕ) :
    lineFaceCuspidalInH2 N h n = lineLocallyInner N h n := by
  have hB : ∀ (F : GL (Fin 2) ℚ) (V : Rep ℂ ↥(leviCuspStab (CongruenceSubgroup.Gamma N) F))
      (x : groupCohomology.H2 V), x = 0 := fun F V x =>
    LocallyInner.h2_zero_subgroup
      (fun A x => H2_vanish_level (CongruenceSubgroup.Gamma N) A x) _ V x
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have := (LocallyInner.edge_mem_cuspidalFamily_iff (lineFaceSplitting N h) (lineFaceRep N h n)
      (leviCuspStab (CongruenceSubgroup.Gamma N)) hB x.1 x.2).mp hx
    exact Submodule.mem_iInf _ |>.mpr fun F => this F
  · rintro ⟨hy0, hF⟩
    refine ⟨⟨y, hy0⟩, ?_, rfl⟩
    exact (LocallyInner.edge_mem_cuspidalFamily_iff (lineFaceSplitting N h) (lineFaceRep N h n)
      (leviCuspStab (CongruenceSubgroup.Gamma N)) hB y hy0).mpr
      (fun F => LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hF F))

/-- **Exclusion of nonmixed face components**: a class of `H²(Γ_{h⁻¹Qh}, E_n)` with zero restriction at every
complete flag over the line lies in the mixed term, the image of `𝒞_{Q'}(E)`. -/
theorem lineFace_mixed_of_flags_vanish (n : ℕ) (y : groupCohomology.H2 (lineFaceRep N h n))
    (hy : ∀ F : GL (Fin 2) ℚ,
      twoCohomologyRestriction (lineFlagStab N h F).subtype (lineFaceRep N h n) y = 0) :
    y ∈ lineFaceCuspidalInH2 N h n := by
  rw [lineFaceCuspidalInH2_eq_locallyInner, lineLocallyInner_eq_iInf]
  exact (Submodule.mem_iInf _).mpr fun F => LinearMap.mem_ker.mpr (hy F)

/-- Conversely, the mixed term restricts to zero at every flag. -/
theorem lineFace_flags_vanish_of_mixed (n : ℕ) (y : groupCohomology.H2 (lineFaceRep N h n))
    (hy : y ∈ lineFaceCuspidalInH2 N h n) (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (lineFlagStab N h F).subtype (lineFaceRep N h n) y = 0 := by
  rw [lineFaceCuspidalInH2_eq_locallyInner, lineLocallyInner_eq_iInf] at hy
  exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hy F)

/-- **The restriction of a mixed class to a flag is its binary cusp restriction**: for a class `y` with zero
restriction to the radical, `y` restricts to zero at the flag of the frame `F` iff the restriction of its mixed class
(its Hochschild-Serre edge) to the cusp stabilizer `leviCuspStab Γ(N) F` of the binary Levi vanishes. -/
theorem lineFace_flag_restriction_edge (n : ℕ) (y : groupCohomology.H2 (lineFaceRep N h n))
    (hy : twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n) y = 0)
    (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (lineFlagStab N h F).subtype (lineFaceRep N h n) y = 0 ↔
      oneRestriction (leviCuspStab (CongruenceSubgroup.Gamma N) F)
        (lineFaceRadH1 N h n) (lineFaceEdge N h n ⟨y, hy⟩) = 0 := by
  have hB : ∀ (V : Rep ℂ ↥(leviCuspStab (CongruenceSubgroup.Gamma N) F))
      (x : groupCohomology.H2 V), x = 0 := fun V x =>
    LocallyInner.h2_zero_subgroup
      (fun A x => H2_vanish_level (CongruenceSubgroup.Gamma N) A x) _ V x
  have := LocallyInner.edge_mem_cuspidalFamily_iff (lineFaceSplitting N h) (lineFaceRep N h n)
      (fun _ : Unit => leviCuspStab (CongruenceSubgroup.Gamma N) F) (fun _ => hB) y hy
  simp only [cuspidalFamily, Submodule.mem_iInf, LinearMap.mem_ker, forall_const] at this
  exact this.symm

theorem mapGL_entry (A : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL ℚ A : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j =
      (((A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℚ) := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem mem_lineFlagStab_one_iff (p : gammaNQAt N h) :
    p ∈ lineFlagStab N h 1 ↔
      ((h * p.1 * h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := by
  change ((1 : GL (Fin 2) ℚ)⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ (leviBlockQ (h * p.1 * h⁻¹) p.2.2) * 1 :
    GL (Fin 2) ℚ) 1 0 = 0 ↔ _
  rw [inv_one, one_mul, mul_one]
  have hm : ((Matrix.SpecialLinearGroup.mapGL ℚ (leviBlockQ (h * p.1 * h⁻¹) p.2.2) : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) 1 0 = ((((h * p.1 * h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℤ) : ℚ) :=
    mapGL_entry _ 1 0
  rw [hm]
  exact Int.cast_eq_zero

/-- **The flag stabilizer of the standard cusp is the flag group `Γ(N) ∩ h⁻¹ B h`.** -/
theorem lineFlagStab_one_iff (p : gammaNQAt N h) :
    p ∈ lineFlagStab N h 1 ↔ (p : SL(3, ℤ)) ∈ gammaNBAt N h := by
  rw [mem_lineFlagStab_one_iff]
  obtain ⟨hg, hl⟩ := p.2
  constructor
  · intro h21
    exact ⟨hg, hl.2.1, hl.2.2, h21⟩
  · intro hb
    exact hb.2.2.2

end Flags

end TernaryPeriodPolynomials.Argument.GammaNFaces
