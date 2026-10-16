module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTBar
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTAlg
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.GeneralReduction

@[expose] public section


/-!
# Normal-form transfer for lines: the flagwise replacement (algebraic form)

Formalized by Claude Sonnet 5.5.

`flagToQ`: the embedding of the stabilizer of a flag over the line of the face `i` into the face group `Q` (inverse of `lineEmb` on the stabilizer).  `zbarG`, `gbarG`: the bar cochains of `d.z` and `γ` at the line, pulled
back to `Q`; `gbarG_dd3T`: `dd3T γ̄ = z̄ ∪ z̄'`.  `nft2_core`: if `z̄ = zx + dκ`, `z̄' = zy + dκ'` for 2-cocycles `zx`, `zy` of `Q` (zero on the radical), there is a normalised primitive `gn` (`dd3T gn = zx ∪ zy`, zero on `inl^3`)
such that for every flag `F` over the line the class of the explicit flag cocycle `lineTheta` equals the class of `(w̄ - κ∘ι) ∪ zy∘ι - gn∘ι`, the primitive `w̄ - κ∘ι` of `zx∘ι`.
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.EquivariantSingularSmall
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section FlagToQ

/-- The stabilizer of a flag over the line `lineOf i.rep` lies in the stabilizer of the line. -/
theorem stab_le_lineStab (i : LineFaces 6) (F : Flag) (hF : flagLineOf F = lineOf i.rep) :
    MulAction.stabilizer Γ6 F ≤ (lineEmb i.rep).range := by
  intro g hg
  rw [lineEmb_range]
  change g • lineOf i.rep = lineOf i.rep
  rw [← hF]
  have h1 : g • F = F := hg
  have := TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant g F
  rw [h1] at this
  exact this.symm

/-- The embedding of the stabilizer of a flag over the line of the face `i` into the face group `Q`. -/
def flagToQ (i : LineFaces 6) (F : Flag) (hF : flagLineOf F = lineOf i.rep) :
    ↥(MulAction.stabilizer Γ6 F) →* ↥(gammaNQAt 6 i.rep) :=
  ((MonoidHom.ofInjective (lineEmb_injective i.rep)).symm : (lineEmb i.rep).range ≃* ↥(gammaNQAt 6 i.rep)).toMonoidHom.comp
    (Subgroup.inclusion (stab_le_lineStab i F hF))

theorem lineEmb_flagToQ (i : LineFaces 6) (F : Flag) (hF : flagLineOf F = lineOf i.rep)
    (s : ↥(MulAction.stabilizer Γ6 F)) : lineEmb i.rep (flagToQ i F hF s) = (s : Γ6) := by
  change lineEmb i.rep ((MonoidHom.ofInjective (lineEmb_injective i.rep)).symm
    (Subgroup.inclusion (stab_le_lineStab i F hF) s)) = _
  exact MonoidHom.apply_ofInjective_symm (lineEmb_injective i.rep) (Subgroup.inclusion (stab_le_lineStab i F hF) s)

end FlagToQ

section Core

open TernaryPeriodPolynomials.Argument.FlagH3

variable {W W' : Rep.{0} ℚ Γ6}

/-- The generic cochain `(a, c) ↦ z̄_d(σ a, σ c)` of the face group `Q` from a line datum (bar cochain at the line `b = lineOf h`). -/
def zbarG (i : LineFaces 6) (d : LineDatum W) (a c : ↥(gammaNQAt 6 i.rep)) : W :=
  barCochain (MulAction.stabilizer Γ6 (lineOf i.rep)) (1 : RationalGL3) (lineOf i.rep) d.z
    (fun j : Fin 2 => if j = 0 then
      faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
        (fun i => lineEmb_range i.rep) i a
     else faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
        (fun i => lineEmb_range i.rep) i c)

theorem lineZbar_eq_zbarG {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
    (ρ₆ : Representation ℂ Γ6 V) (i : LineFaces 6) (d : LineDatum (qRep (MonoidHom.id Γ6) ρ₆)) (a c : ↥(gammaNQAt 6 i.rep)) :
    lineZbar ρ₆ i d a c = zbarG i d a c := by
  unfold lineZbar zbarG
  congr 1
  funext j
  fin_cases j <;> rfl

/-- The bar cochain at the line, evaluated on `σ ∘ ι_F`, is the bar cochain at the flag `F`. -/
theorem bar_flag {W₀ : Rep.{0} ℚ Γ6} {k : ℕ} (i : LineFaces 6) (F : Flag) (hF : flagLineOf F = lineOf i.rep)
    (ι : ↥(MulAction.stabilizer Γ6 F) →* ↥(gammaNQAt 6 i.rep)) (hι : ∀ s, lineEmb i.rep (ι s) = (s : Γ6))
    (θ : (prodComplex Γ6 RationalGL3 Line).X k ⟶ W₀) (x : Fin k → ↥(MulAction.stabilizer Γ6 F)) :
    barCochain (MulAction.stabilizer Γ6 (lineOf i.rep)) (1 : RationalGL3) (lineOf i.rep) θ
      (fun j => faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
        (fun i => lineEmb_range i.rep) i (ι (x j))) =
    barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) (flagLineOf F) θ x := by
  have hle : MulAction.stabilizer Γ6 F ≤ MulAction.stabilizer Γ6 (lineOf i.rep) := by
    intro g hg
    have := stab_le_lineStab i F hF hg
    rwa [lineEmb_range] at this
  rw [barCochain_restrict (MulAction.stabilizer Γ6 F) (MulAction.stabilizer Γ6 (lineOf i.rep)) hle (1 : RationalGL3)
    (flagLineOf F) θ x, hF]
  congr 1
  funext j
  apply Subtype.ext
  exact hι (x j)

theorem dd2_dd1 {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module ℚ M] (ρ : Representation ℚ G M) (κ : G → M) :
    dd2 ρ (dd1 ρ κ) = 0 := by
  funext g h l
  simp only [dd2, dd1, map_mul, Module.End.mul_apply, map_sub, map_add, Pi.zero_apply, mul_assoc]
  abel

theorem dd2_add {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module ℚ M] (ρ : Representation ℚ G M) (a b : G → G → M) :
    dd2 ρ (a + b) = dd2 ρ a + dd2 ρ b := by
  funext g h l
  simp only [dd2, Pi.add_apply, map_add]
  abel

theorem dTwo_eq_dd2T {B : Type} [Group B] (ψ : B → B → ℚ) :
    dTwo (fun g : Fin 2 → B => ψ (g 0) (g 1)) = fun g : Fin 3 → B => dd2T ψ (g 0) (g 1) (g 2) := by
  funext g
  rw [dTwo_apply]
  simp [dd2T]

/-- The cochain `(a, c, e) ↦ γ̄(σ a, σ c, σ e)` of the face group from the bar cochain of `γ` at the line. -/
def gbarG (i : LineFaces 6) (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (a c e : ↥(gammaNQAt 6 i.rep)) : ℚ :=
  barCochain (MulAction.stabilizer Γ6 (lineOf i.rep)) (1 : RationalGL3) (lineOf i.rep) γ
    ![faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i a,
     faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i c,
     faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i e]

variable (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))

/-- **`dd3T γ̄ = z̄ ∪ z̄'` on the face group**, from the cocycle relation of the cut primitive. -/
theorem gbarG_dd3T (i : LineFaces 6) (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) :
    dd3T (gbarG i γ) = cup22 ((W'.ρ).comp (lineEmb i.rep)) (pairOf π) (zbarG i d) (zbarG i e) := by
  funext a c e' f
  have h1 := bar_dd3T (MulAction.stabilizer Γ6 (lineOf i.rep)) (1 : RationalGL3) (lineOf i.rep) (fun g => g.2) γ
    (faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i a)
    (faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i c)
    (faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i e')
    (faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i f)
  have h2 := diag22_bar (MulAction.stabilizer Γ6 (lineOf i.rep)) (1 : RationalGL3) (lineOf i.rep) (fun g => g.2) π d.z e.z
    ![faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i a,
     faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i c,
     faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i e',
     faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i f]
  rw [hγ] at h1
  have e0 : dd3T (gbarG i γ) a c e' f = dd3T (fun a b c => barCochain (MulAction.stabilizer Γ6 (lineOf i.rep)) (1 : RationalGL3)
      (lineOf i.rep) γ ![a, b, c])
      (faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
        (fun i => lineEmb_range i.rep) i a)
      (faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
        (fun i => lineEmb_range i.rep) i c)
      (faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
        (fun i => lineEmb_range i.rep) i e')
      (faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
        (fun i => lineEmb_range i.rep) i f) := by
    simp only [dd3T, gbarG, map_mul]
  rw [e0, h1]
  refine h2.trans ?_
  simp only [cup22, zbarG, MonoidHom.comp_apply, Subgroup.coe_subtype, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, map_mul]
  rfl

theorem zbarG_flag (i : LineFaces 6) (F : Flag) (hF : flagLineOf F = lineOf i.rep)
    (ι : ↥(MulAction.stabilizer Γ6 F) →* ↥(gammaNQAt 6 i.rep)) (hι : ∀ s, lineEmb i.rep (ι s) = (s : Γ6)) (d : LineDatum W)
    (s t : ↥(MulAction.stabilizer Γ6 F)) :
    zbarG i d (ι s) (ι t) =
      barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) (flagLineOf F) d.z (fun j : Fin 2 => if j = 0 then s else t) := by
  rw [← bar_flag i F hF ι hι d.z (fun j : Fin 2 => if j = 0 then s else t)]
  unfold zbarG
  congr 1
  funext j
  by_cases hj : j = 0 <;> simp [hj]

theorem gbarG_flag (i : LineFaces 6) (F : Flag) (hF : flagLineOf F = lineOf i.rep)
    (ι : ↥(MulAction.stabilizer Γ6 F) →* ↥(gammaNQAt 6 i.rep)) (hι : ∀ s, lineEmb i.rep (ι s) = (s : Γ6))
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (a b c : ↥(MulAction.stabilizer Γ6 F)) :
    gbarG i γ (ι a) (ι b) (ι c) =
      barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) (flagLineOf F) γ ![a, b, c] := by
  rw [← bar_flag i F hF ι hι γ ![a, b, c]]
  unfold gbarG
  congr 1
  funext j
  fin_cases j <;> rfl

/-- **NFT-2 (line, algebraic form).**  Let `zx`, `zy` be two-cocycles of the face group `Q` with `z̄ = zx + dκ`, `z̄' = zy + dκ'`.  Then there is a normalised primitive `gn` with `dd3T gn = zx ∪ zy`,
vanishing on `inl^3`, such that for every flag `F` over the line of the face the class `lam_F[Θ_F]` of the explicit flag cocycle `lineTheta` equals the class of `(w̄ - κ) ∪ zy|Stab F - gn|Stab F`
for a primitive `w̄ - κ` of `zx|Stab F`. -/
theorem nft2_core (i : LineFaces 6) (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (zx : ↥(gammaNQAt 6 i.rep) → ↥(gammaNQAt 6 i.rep) → W) (zy : ↥(gammaNQAt 6 i.rep) → ↥(gammaNQAt 6 i.rep) → W')
    (κ : ↥(gammaNQAt 6 i.rep) → W) (κ' : ↥(gammaNQAt 6 i.rep) → W')
    (hzx : dd2 (W.ρ.comp (lineEmb i.rep)) zx = 0) (hzy : dd2 (W'.ρ.comp (lineEmb i.rep)) zy = 0)
    (h1 : zbarG i d = zx + dd1 (W.ρ.comp (lineEmb i.rep)) κ) (h2 : zbarG i e = zy + dd1 (W'.ρ.comp (lineEmb i.rep)) κ')
    (inl : Multiplicative (ℤ × ℤ) →* ↥(gammaNQAt 6 i.rep)) (hinj : Function.Injective inl)
    (hradx : ∀ a b : Multiplicative (ℤ × ℤ), zx (inl a) (inl b) = 0) :
    ∃ gn : ↥(gammaNQAt 6 i.rep) → ↥(gammaNQAt 6 i.rep) → ↥(gammaNQAt 6 i.rep) → ℚ,
      dd3T gn = cup22 (W'.ρ.comp (lineEmb i.rep)) (pairOf π) zx zy ∧
      (∀ a b c : Multiplicative (ℤ × ℤ), gn (inl a) (inl b) (inl c) = 0) ∧
      ∀ (F : Flag) (_ : flagLineOf F = lineOf i.rep) (ι : ↥(MulAction.stabilizer Γ6 F) →* ↥(gammaNQAt 6 i.rep))
        (_ : ∀ s, lineEmb i.rep (ι s) = (s : Γ6)),
        ∃ wn : ↥(MulAction.stabilizer Γ6 F) → W,
          dd1 (W.ρ.comp (MulAction.stabilizer Γ6 F).subtype) wn =
            (fun s t => zx (ι s) (ι t)) ∧
          ∃ hΘ : dThree (fun g : Fin 3 → ↥(MulAction.stabilizer Γ6 F) =>
              cup12 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π) wn
                (fun s t => zy (ι s) (ι t)) (g 0) (g 1) (g 2) -
              gn (ι (g 0)) (ι (g 1)) (ι (g 2))) = 0,
          clsRes (MulAction.stabilizer Γ6 F) (lineTheta π d e γ F) (lineTheta_dThree π d e γ hγ F) =
            clsRes (MulAction.stabilizer Γ6 F) _ hΘ := by
  set ρQ : Representation ℚ ↥(gammaNQAt 6 i.rep) W := W.ρ.comp (lineEmb i.rep) with hρQ
  set ρQ' : Representation ℚ ↥(gammaNQAt 6 i.rep) W' := W'.ρ.comp (lineEmb i.rep) with hρQ'
  have he : ∀ (g : ↥(gammaNQAt 6 i.rep)) (v : W) (w : W'), pairOf π (ρQ g v) (ρQ' g w) = pairOf π v w :=
    fun g v w => pairOf_inv π (lineEmb i.rep g) v w
  have hγb := gbarG_dd3T π i d e γ hγ
  have hzb : dd2 ρQ (zbarG i d) = 0 := by
    rw [h1, dd2_add, hzx, dd2_dd1, add_zero]
  obtain ⟨ε, hε⟩ := nfGamma_exists inl hinj he zx (zbarG i d) zy (zbarG i e) κ κ' (gbarG i γ) hzb hzy h1 h2 hγb hradx
  have hdd := nfGamma0_dd3T he zx (zbarG i d) zy (zbarG i e) κ κ' (gbarG i γ) hzb hzy h1 h2 hγb
  have hgn : dd3T (nfGamma0 ρQ' (pairOf π) (zbarG i d) κ κ' zy (gbarG i γ) - dd2T ε) = cup22 ρQ' (pairOf π) zx zy := by
    rw [dd3T_sub, dd3T_dd2T, hdd, sub_zero]
  refine ⟨nfGamma0 ρQ' (pairOf π) (zbarG i d) κ κ' zy (gbarG i γ) - dd2T ε, hgn, fun a b c => hε a b c, ?_⟩
  intro F hF ι hι
  have hρ : ∀ (s : ↥(MulAction.stabilizer Γ6 F)) (v : W), ρQ (ι s) v = (W.ρ.comp (MulAction.stabilizer Γ6 F).subtype) s v := by
    intro s v
    show W.ρ (lineEmb i.rep (ι s)) v = W.ρ (s : Γ6) v
    rw [hι]
  have hρ' : ∀ (s : ↥(MulAction.stabilizer Γ6 F)) (v : W'), ρQ' (ι s) v = (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) s v := by
    intro s v
    show W'.ρ (lineEmb i.rep (ι s)) v = W'.ρ (s : Γ6) v
    rw [hι]
  have hzF : ∀ g : ↥(MulAction.stabilizer Γ6 F), g • F = F := fun g => g.2
  have hw : dd1 (W.ρ.comp (MulAction.stabilizer Γ6 F).subtype)
      (fun s => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) F d.w (fun _ : Fin 1 => s)) =
      fun s t => zbarG i d (ι s) (ι t) := by
    funext s t
    rw [bar_dd1 (MulAction.stabilizer Γ6 F) W (1 : RationalGL3) F hzF d.w s t, d.hw, barCochain_flagLine, zbarG_flag i F hF ι hι]
  set wb : ↥(MulAction.stabilizer Γ6 F) → W :=
    fun s => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) F d.w (fun _ : Fin 1 => s) with hwb
  have hwn := nf_primitive ι hρ zx (zbarG i d) κ h1 wb hw
  have heH := pull_inv ι hρ hρ' he
  have hΘ := nfTheta_dd3T ι hρ' heH zx zy (nfGamma0 ρQ' (pairOf π) (zbarG i d) κ κ' zy (gbarG i γ) - dd2T ε) hzy hgn
    (wb - fun s => κ (ι s)) hwn
  have hΘ' : dThree (fun g : Fin 3 → ↥(MulAction.stabilizer Γ6 F) =>
      cup12 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π) (wb - fun s => κ (ι s))
        (fun s t => zy (ι s) (ι t)) (g 0) (g 1) (g 2) -
      (nfGamma0 ρQ' (pairOf π) (zbarG i d) κ κ' zy (gbarG i γ) - dd2T ε) (ι (g 0)) (ι (g 1)) (ι (g 2))) = 0 := by
    rw [dThree_eq_dd3T (fun a b c => cup12 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π) (wb - fun s => κ (ι s))
        (fun s t => zy (ι s) (ι t)) a b c -
      (nfGamma0 ρQ' (pairOf π) (zbarG i d) κ κ' zy (gbarG i γ) - dd2T ε) (ι a) (ι b) (ι c))]
    funext g
    exact congrFun (congrFun (congrFun (congrFun hΘ (g 0)) (g 1)) (g 2)) (g 3)
  refine ⟨wb - fun s => κ (ι s), hwn, hΘ', ?_⟩
  have hT := nfTheta_eq ι hρ hρ' he (zbarG i d) zy (zbarG i e) κ κ' (gbarG i γ) ε h2 wb hw
  have hL : lineTheta π d e γ F = fun g : Fin 3 → ↥(MulAction.stabilizer Γ6 F) =>
      cup12 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π) wb (fun s t => zbarG i e (ι s) (ι t)) (g 0) (g 1) (g 2) -
        gbarG i γ (ι (g 0)) (ι (g 1)) (ι (g 2)) := by
    rw [← lineTheta_hfun π d e γ F]
    funext g
    have hg : g = ![g 0, g 1, g 2] := by funext j; fin_cases j <;> rfl
    simp only [hwb]
    congr 1
    · congr 1
      funext s t
      exact (zbarG_flag i F hF ι hι e s t).symm
    · rw [gbarG_flag i F hF ι hι γ (g 0) (g 1) (g 2), ← hg]
  unfold clsRes
  congr 1
  refine cocycleClass_eq_of_dTwo _ _ _ _
    (fun g : Fin 2 → ↥(MulAction.stabilizer Γ6 F) =>
      (-(cup11 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π) wb (fun s => κ' (ι s))) -
        fun s t : ↥(MulAction.stabilizer Γ6 F) => ε (ι s) (ι t)) (g 0) (g 1)) ?_
  rw [dTwo_eq_dd2T, hL]
  funext g
  exact congrFun (congrFun (congrFun hT (g 0)) (g 1)) (g 2)

end Core

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
