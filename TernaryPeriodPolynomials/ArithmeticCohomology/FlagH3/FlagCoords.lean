module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Ext
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisFlag
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Data
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Stab

@[expose] public section


open CategoryTheory MonoidalCategory
open scoped MatrixGroups

/-!
# `H³` of the flag stabilizers of `Γ(6)`: Heisenberg coordinates, the cycle `λ_F`, and the generator `G_F`

Formalized by Claude Sonnet 5.5.

For the flag group `Γ(6) ∩ g⁻¹ B g` (the `gammaNBAt 6 g`, with `flagExt g` and `flagStabEquiv g`) the entries `(01, 12, 02)` of `g γ g⁻¹` are Heisenberg coordinates (`flagCoords`), the elements
`X = g⁻¹ [[1,6,0],[0,1,0],[0,0,1]] g`, `Y = g⁻¹ [[1,0,0],[0,1,6],[0,0,1]] g` have coordinates `(6,0,0)`, `(0,6,0)`, and `flagData g : FlagCohomDatum` is the datum of `FlagH3.Data`
(`dim H³ = 1`, `λ ≠ 0`, `λ[θ] = ∑ z(g) θ(g)` for the explicit seven-term bar cycle `z = heisCycle X Y`).  `flagStabData g` is the same for the stabilizer of `flagOf g` in `Γ(6)`
and `flagStabDataOf F` for an arbitrary complete flag `F`.  `flagLam F`, `flagGen F` are `λ_F` and `G_F` in the form `groupCohomology (Rep.res (stabilizer Γ6 F).subtype (𝟙_ _)) 3`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction
open TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg (flagGroup flag_entries unipMat unipMat_mem)

/-- The conjugate of a flag-group element into the standard Borel subgroup. -/
def conjB (g : SL(3, ℤ)) (p : ↥(gammaNBAt 6 g)) : SL(3, ℤ) := g * p.1 * g⁻¹

theorem conjB_mem (g : SL(3, ℤ)) (p : ↥(gammaNBAt 6 g)) :
    conjB g p ∈ flagGroup 6 := by
  have h : g * p.1 * g⁻¹ ∈ gammaNB 6 := p.2
  exact ⟨h.1, h.2⟩

theorem conjB_mul (g : SL(3, ℤ)) (p q : ↥(gammaNBAt 6 g)) : conjB g (p * q) = conjB g p * conjB g q := by
  simp [conjB, mul_assoc]

theorem ent_mul {γ δ : SL(3, ℤ)} (hγ : γ ∈ flagGroup 6) (hδ : δ ∈ flagGroup 6) :
    (γ * δ : SL(3, ℤ)) 0 1 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 1 + (δ : Matrix (Fin 3) (Fin 3) ℤ) 0 1 ∧
    (γ * δ : SL(3, ℤ)) 1 2 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 2 + (δ : Matrix (Fin 3) (Fin 3) ℤ) 1 2 ∧
    (γ * δ : SL(3, ℤ)) 0 2 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 2 + (δ : Matrix (Fin 3) (Fin 3) ℤ) 0 2 +
      (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 1 * (δ : Matrix (Fin 3) (Fin 3) ℤ) 1 2 := by
  obtain ⟨g00, g11, g22, -⟩ := flag_entries (by norm_num : 3 ≤ 6) hγ
  obtain ⟨d00, d11, d22, -⟩ := flag_entries (by norm_num : 3 ≤ 6) hδ
  obtain ⟨-, g10, g20, g21⟩ := hγ
  obtain ⟨-, d10, d20, d21⟩ := hδ
  refine ⟨?_, ?_, ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_three, g00, d11, d21]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_three, g11, d22, g10]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_three, g00, d22]
    ring


/-- **Heisenberg coordinates on the flag group `Γ(6) ∩ g⁻¹ B g`**: the entries `(01, 12, 02)` of the conjugate `g γ g⁻¹` into the standard Borel subgroup. -/
def flagCoords (g : SL(3, ℤ)) : HeisCoords ↥(gammaNBAt 6 g) where
  a p := (conjB g p : Matrix (Fin 3) (Fin 3) ℤ) 0 1
  b p := (conjB g p : Matrix (Fin 3) (Fin 3) ℤ) 1 2
  c p := (conjB g p : Matrix (Fin 3) (Fin 3) ℤ) 0 2
  a_mul p q := by
    rw [conjB_mul]
    exact (ent_mul (conjB_mem g p) (conjB_mem g q)).1
  b_mul p q := by
    rw [conjB_mul]
    exact (ent_mul (conjB_mem g p) (conjB_mem g q)).2.1
  c_mul p q := by
    rw [conjB_mul]
    exact (ent_mul (conjB_mem g p) (conjB_mem g q)).2.2
  inj p q h1 h2 h3 := by
    obtain ⟨p00, p11, p22, -⟩ := flag_entries (by norm_num : 3 ≤ 6) (conjB_mem g p)
    obtain ⟨-, p10, p20, p21⟩ := conjB_mem g p
    obtain ⟨q00, q11, q22, -⟩ := flag_entries (by norm_num : 3 ≤ 6) (conjB_mem g q)
    obtain ⟨-, q10, q20, q21⟩ := conjB_mem g q
    have hM : conjB g p = conjB g q := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp_all
    apply Subtype.ext
    have := mul_left_cancel (mul_right_cancel hM)
    exact this


/-- The element `g⁻¹ [[1,a,c],[0,1,b],[0,0,1]] g` of the flag group, for `a, b, c` divisible by `6`. -/
def unipElt (g : SL(3, ℤ)) (a b c : ℤ) (ha : (6 : ℤ) ∣ a) (hb : (6 : ℤ) ∣ b) (hc : (6 : ℤ) ∣ c) : ↥(gammaNBAt 6 g) :=
  ⟨g⁻¹ * unipMat a b c * g, by
    have h := unipMat_mem (N := 6) (a := a) (b := b) (c := c) (by exact_mod_cast ha) (by exact_mod_cast hb)
      (by exact_mod_cast hc)
    have h2 : g * (g⁻¹ * unipMat a b c * g) * g⁻¹ = unipMat a b c := by
      have key : ∀ u : SL(3, ℤ), g * (g⁻¹ * u * g) * g⁻¹ = u := fun u => by group
      exact key _
    show g * (g⁻¹ * unipMat a b c * g) * g⁻¹ ∈ gammaNB 6
    rw [h2]
    exact ⟨h.1, h.2⟩⟩

theorem conjB_unipElt (g : SL(3, ℤ)) (a b c : ℤ) (ha : (6 : ℤ) ∣ a) (hb : (6 : ℤ) ∣ b) (hc : (6 : ℤ) ∣ c) :
    conjB g (unipElt g a b c ha hb hc) = unipMat a b c := by
  have key : ∀ u : SL(3, ℤ), g * (g⁻¹ * u * g) * g⁻¹ = u := fun u => by group
  exact key _

theorem flagCoords_unipElt (g : SL(3, ℤ)) (a b c : ℤ) (ha : (6 : ℤ) ∣ a) (hb : (6 : ℤ) ∣ b) (hc : (6 : ℤ) ∣ c) :
    (flagCoords g).a (unipElt g a b c ha hb hc) = a ∧ (flagCoords g).b (unipElt g a b c ha hb hc) = b ∧
      (flagCoords g).c (unipElt g a b c ha hb hc) = c := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [flagCoords, conjB_unipElt, unipMat]


/-- Heisenberg coordinates transported along an isomorphism of groups. -/
def HeisCoords.ofMulEquiv {B B' : Type} [Group B] [Group B'] (H : HeisCoords B) (e : B ≃* B') : HeisCoords B' where
  a x := H.a (e.symm x)
  b x := H.b (e.symm x)
  c x := H.c (e.symm x)
  a_mul x y := by simp [H.a_mul]
  b_mul x y := by simp [H.b_mul]
  c_mul x y := by simp [H.c_mul]
  inj x y h1 h2 h3 := e.symm.injective (H.inj _ _ h1 h2 h3)

/-- The elements `X = g⁻¹ [[1,6,0],[0,1,0],[0,0,1]] g` and `Y = g⁻¹ [[1,0,0],[0,1,6],[0,0,1]] g` of the flag group. -/
def flagX (g : SL(3, ℤ)) : ↥(gammaNBAt 6 g) := unipElt g 6 0 0 (dvd_refl _) (dvd_zero _) (dvd_zero _)

def flagY (g : SL(3, ℤ)) : ↥(gammaNBAt 6 g) := unipElt g 0 6 0 (dvd_zero _) (dvd_refl _) (dvd_zero _)

theorem flagX_coords (g : SL(3, ℤ)) :
    (flagCoords g).a (flagX g) = 6 ∧ (flagCoords g).b (flagX g) = 0 ∧ (flagCoords g).c (flagX g) = 0 :=
  flagCoords_unipElt g 6 0 0 (dvd_refl _) (dvd_zero _) (dvd_zero _)

theorem flagY_coords (g : SL(3, ℤ)) :
    (flagCoords g).a (flagY g) = 0 ∧ (flagCoords g).b (flagY g) = 6 ∧ (flagCoords g).c (flagY g) = 0 :=
  flagCoords_unipElt g 0 6 0 (dvd_zero _) (dvd_refl _) (dvd_zero _)

/-- **The one-dimensionality datum of `H³` of the flag group `Γ(6) ∩ g⁻¹ B g`.** -/
def flagData (g : SL(3, ℤ)) : FlagCohomDatum ↥(gammaNBAt 6 g) :=
  (flagCoords g).flagData (flagExt g) (flagX g) (flagY g) 6 6 (by norm_num) (by norm_num)
    (flagX_coords g).1 (flagX_coords g).2.1 (flagX_coords g).2.2
    (flagY_coords g).1 (flagY_coords g).2.1 (flagY_coords g).2.2

/-- **The same for the stabilizer of the complete flag `flagOf g` in `Γ(6)`.** -/
def flagStabData (g : SL(3, ℤ)) : FlagCohomDatum ↥(MulAction.stabilizer Γ6 (flagOf g)) :=
  ((flagCoords g).ofMulEquiv (flagStabEquiv g)).flagData (flagStabExt g) (flagStabEquiv g (flagX g))
    (flagStabEquiv g (flagY g)) 6 6 (by norm_num) (by norm_num)
    (by simpa [HeisCoords.ofMulEquiv] using (flagX_coords g).1)
    (by simpa [HeisCoords.ofMulEquiv] using (flagX_coords g).2.1)
    (by simpa [HeisCoords.ofMulEquiv] using (flagX_coords g).2.2)
    (by simpa [HeisCoords.ofMulEquiv] using (flagY_coords g).1)
    (by simpa [HeisCoords.ofMulEquiv] using (flagY_coords g).2.1)
    (by simpa [HeisCoords.ofMulEquiv] using (flagY_coords g).2.2)


/-- **The datum for an arbitrary complete flag `F`** (via a chosen `g` with `flagOf g = F`). -/
def flagStabDataOf (F : Flag) : FlagCohomDatum ↥(MulAction.stabilizer Γ6 F) :=
  (Classical.choose_spec (exists_flagOf F)) ▸ flagStabData (Classical.choose (exists_flagOf F))

/-- Cohomology of the restriction of the trivial representation to a subgroup, versus the trivial representation of the subgroup. -/
def resTrivialEquiv (G : Type) [Group G] (S : Subgroup G) (n : ℕ) :
    groupCohomology (Rep.res S.subtype (𝟙_ (Rep.{0} ℚ G))) n ≃ₗ[ℚ] groupCohomology (Rep.trivial ℚ S ℚ) n :=
  (groupCohomology.mapIso (MulEquiv.refl S) (B := Rep.res S.subtype (𝟙_ (Rep.{0} ℚ G))) (A := Rep.trivial ℚ S ℚ)
    (LinearEquiv.refl ℚ ℚ) (fun g => by ext; rfl) n).toLinearEquiv


/-- The evaluation functional `λ_F` on `H³(Stab F, ℚ)`, in the form used by the corner decomposition (`Rep.res` of the monoidal unit). -/
def flagLam (F : Flag) : groupCohomology (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3 →ₗ[ℚ] ℚ :=
  (flagStabDataOf F).lam ∘ₗ (resTrivialEquiv Γ6 (MulAction.stabilizer Γ6 F) 3).toLinearMap

/-- The class `G_F` with `λ_F G_F = 1`. -/
def flagGen (F : Flag) : groupCohomology (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3 :=
  (resTrivialEquiv Γ6 (MulAction.stabilizer Γ6 F) 3).symm (flagStabDataOf F).gen

theorem flagLam_flagGen (F : Flag) : flagLam F (flagGen F) = 1 := by
  simp [flagLam, flagGen, (flagStabDataOf F).lam_gen]

theorem flagLam_ne_zero (F : Flag) : flagLam F ≠ 0 := by
  intro h
  have := congrArg (fun f => f (flagGen F)) h
  simp [flagLam_flagGen] at this

theorem flagLam_injective (F : Flag) : Function.Injective (flagLam F) :=
  (flagStabDataOf F).lam_injective.comp (resTrivialEquiv Γ6 (MulAction.stabilizer Γ6 F) 3).injective

theorem flagLam_eq_smul_flagGen (F : Flag)
    (x : groupCohomology (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3) :
    x = flagLam F x • flagGen F :=
  flagLam_injective F (by rw [map_smul, flagLam_flagGen, smul_eq_mul, mul_one])

theorem finrank_flagCohomology (F : Flag) :
    Module.Finite ℚ (groupCohomology (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3) ∧
      Module.finrank ℚ (groupCohomology (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3) = 1 := by
  have := (flagStabDataOf F).finite
  refine ⟨Module.Finite.equiv (resTrivialEquiv Γ6 (MulAction.stabilizer Γ6 F) 3).symm, ?_⟩
  rw [(resTrivialEquiv Γ6 (MulAction.stabilizer Γ6 F) 3).finrank_eq]
  exact (flagStabDataOf F).finrank_eq_one

end TernaryPeriodPolynomials.Argument.FlagH3
