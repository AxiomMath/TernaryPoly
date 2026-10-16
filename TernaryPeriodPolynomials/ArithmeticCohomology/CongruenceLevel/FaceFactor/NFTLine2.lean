module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTLineCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.LineSumFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSMixedNormalForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.EdgeToCusp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.LineWiring

@[expose] public section


/-!
# NFT-2 for lines: the normal form of the nerve data and the flagwise replacement

Formalized by Claude Sonnet 5.5.

`nft2_line`: for the nerve data `(ρ, i, x, y, d, e, γ)` of `M3LineC` there are normal-form relative cocycles `z`, `z'` representing the mixed classes `x`, `y` (`z(s a, s b) = 0`, `z(inl r, s l) = 0`, resp. `z'(inl r, s l) = 0`),
a primitive `γ̄` of `z ∪ z'` vanishing on `inl^3`, and primitives `wB c` of `z|Stab(flagAt h (cuspPrim c))` such that the flag cochain of `LetterLift.flagTheta` is a cocycle and has the same class as the explicit
flag cocycle `lineTheta` of the nerve data, for every cusp representative `c`.  These are exactly the hypotheses of `lineSum_can`.  `qRep_comp_emb`, `qRepDual_comp_emb`, `pairOf_eval`, `repRho_flag`, `dualRho_flag`,
`cocycle_dd2'`, `flagTheta_eq_core` are the bookkeeping between the rational transported modules and the complex modules `repAt ρ i`, `dualRepG (repAt ρ i)`.
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open CongruenceSubgroup Matrix
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.EquivariantSingularSmall TernaryPoly.BoundaryFaceResolutionComparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD TernaryPeriodPolynomials.Argument.FlagH3
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section Bridge

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6)

example : Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual) =
    dualRepG (repAt ρ i) := rfl

theorem qRep_comp_emb (g : ↥(gammaNQAt 6 i.rep)) (v : V) :
    ((qRep (MonoidHom.id Γ6) (rep6 ρ)).ρ.comp (lineEmb i.rep)) g v = (repAt ρ i).ρ g v := by
  show rep6 ρ (lineEmb i.rep g) v = ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) g) v
  exact rep6_hρ ρ _ v

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem qRepDual_comp_emb (g : ↥(gammaNQAt 6 i.rep)) (φ : Module.Dual ℂ V) :
    ((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (lineEmb i.rep)) g φ = (dualRepG (repAt ρ i)).ρ g φ := by
  show (rep6 ρ).dual (lineEmb i.rep g) φ = (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) g)) φ
  exact rep6_dual_hρ ρ _ φ

theorem cocycle_dd2' (z : groupCohomology.cocycles₂ (repAt ρ i)) :
    dd2 ((qRep (MonoidHom.id Γ6) (rep6 ρ)).ρ.comp (lineEmb i.rep)) (fun a c => z.1 (a, c)) = 0 := by
  funext g h j
  have := (groupCohomology.mem_cocycles₂_iff z.1).1 z.2 g h j
  simp only [dd2, Pi.zero_apply]
  rw [qRep_comp_emb]
  have e : ((repAt ρ i).ρ g) (z.1 (h, j)) - z.1 (g * h, j) + z.1 (g, h * j) - z.1 (g, h) =
      ((repAt ρ i).ρ g) (z.1 (h, j)) + z.1 (g, h * j) - (z.1 (g * h, j) + z.1 (g, h)) := by abel
  exact e.trans (sub_eq_zero.2 this.symm)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem cocycle_dd2_dual (z : groupCohomology.cocycles₂ (dualRepG (repAt ρ i))) :
    dd2 ((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (lineEmb i.rep)) (fun a c => z.1 (a, c)) = 0 := by
  funext g h j
  have := (groupCohomology.mem_cocycles₂_iff z.1).1 z.2 g h j
  simp only [dd2, Pi.zero_apply]
  rw [qRepDual_comp_emb]
  have e : ((dualRepG (repAt ρ i)).ρ g) (z.1 (h, j)) - z.1 (g * h, j) + z.1 (g, h * j) - z.1 (g, h) =
      ((dualRepG (repAt ρ i)).ρ g) (z.1 (h, j)) + z.1 (g, h * j) - (z.1 (g * h, j) + z.1 (g, h)) := by abel
  exact e.trans (sub_eq_zero.2 this.symm)

theorem pairOf_eval (r : ℂ →ₗ[ℚ] ℚ) (v : V) (φ : Module.Dual ℂ V) :
    pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) v φ = r (φ v) := rfl

theorem repRho_flag (w : Prim2) (b : ↥(MulAction.stabilizer Γ6 (flagAt i.rep w))) (v : V) :
    (repAt ρ i).ρ (flagIota i.rep w b) v = (qRep (MonoidHom.id Γ6) (rep6 ρ)).ρ (b : Γ6) v := by
  rw [← qRep_comp_emb]
  show (qRep (MonoidHom.id Γ6) (rep6 ρ)).ρ (lineEmb i.rep (flagIota i.rep w b)) v = _
  rw [lineEmb_flagIota]

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem dualRho_flag (w : Prim2) (b : ↥(MulAction.stabilizer Γ6 (flagAt i.rep w))) (φ : Module.Dual ℂ V) :
    (dualRepG (repAt ρ i)).ρ (flagIota i.rep w b) φ = (qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ (b : Γ6) φ := by
  rw [← qRepDual_comp_emb]
  show (qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ (lineEmb i.rep (flagIota i.rep w b)) φ = _
  rw [lineEmb_flagIota]

end Bridge

section Main

/-- The cocycle `zx` as a function `Q → Q → W` for the transported module. -/
def zxQ {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
    (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6) (z : groupCohomology.cocycles₂ (repAt ρ i)) :
    ↥(gammaNQAt 6 i.rep) → ↥(gammaNQAt 6 i.rep) → ↑(qRep (MonoidHom.id Γ6) (rep6 ρ)) := fun a c => z.1 (a, c)

/-- The cocycle `zy` as a function `Q → Q → W'` for the transported dual module. -/
def zyQ {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
    (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6) (z : groupCohomology.cocycles₂ (dualRepG (repAt ρ i))) :
    ↥(gammaNQAt 6 i.rep) → ↥(gammaNQAt 6 i.rep) → ↑(qRep (MonoidHom.id Γ6) (rep6 ρ).dual) := fun a c => z.1 (a, c)

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem flagTheta_eq_core (hN : 3 ≤ 6) (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6) (r : ℂ →ₗ[ℚ] ℚ)
    (ρ' : Representation ℚ ↥(gammaNQAt 6 i.rep) (dualRepG (repAt ρ i)))
    (hρ' : ∀ g x, ρ' g x = (dualRepG (repAt ρ i)).ρ g x)
    (eQ : repAt ρ i →ₗ[ℚ] dualRepG (repAt ρ i) →ₗ[ℚ] ℚ)
    (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ (repAt ρ i) x y))
    (z' : groupCohomology.cocycles₂ (dualRepG (repAt ρ i)))
    (gn : ↥(gammaNQAt 6 i.rep) → ↥(gammaNQAt 6 i.rep) → ↥(gammaNQAt 6 i.rep) → ℚ) (c : ↥(cuspReps hN).R)
    (w : ↥(MulAction.stabilizer Γ6 (flagAt i.rep (cuspPrim (c : RationalLine2)))) → ↑(qRep (MonoidHom.id Γ6) (rep6 ρ))) :
    (flagLift i.rep (cuspPrim (c : RationalLine2))
      ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))) (sigma_fix (c : RationalLine2))).flagTheta ρ' eQ w
      (fun a b => z'.val (a, b)) gn =
      fun g : Fin 3 → ↥(MulAction.stabilizer Γ6 (flagAt i.rep (cuspPrim (c : RationalLine2)))) =>
        cup12 ((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (MulAction.stabilizer Γ6 (flagAt i.rep (cuspPrim (c : RationalLine2)))).subtype)
          (pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r)) w
          (fun s t => zyQ ρ i z' (flagIota i.rep (cuspPrim (c : RationalLine2)) s) (flagIota i.rep (cuspPrim (c : RationalLine2)) t))
          (g 0) (g 1) (g 2) -
        gn (flagIota i.rep (cuspPrim (c : RationalLine2)) (g 0)) (flagIota i.rep (cuspPrim (c : RationalLine2)) (g 1))
          (flagIota i.rep (cuspPrim (c : RationalLine2)) (g 2)) := by
  funext g
  unfold LetterLift.flagTheta
  refine congrArg₂ (· - ·) ?_ rfl
  have pair : ∀ v φ, eQ v φ = pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) v φ :=
    fun v φ => (he v φ).trans (pairOf_eval ρ r v φ).symm
  simp only [cup12, zyQ]
  refine (pair _ _).trans ?_
  exact congrArg (pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) _)
    ((hρ' _ _).trans (dualRho_flag ρ i (cuspPrim (c : RationalLine2)) (g 0) _))

omit [FiniteDimensional ℂ V] in
open scoped Classical in
/-- **NFT-2 (lines): the normal form of the nerve data and the flagwise replacement.** -/
theorem nft2_line (hN : 3 ≤ 6) (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6) (x : lineMixedSub ρ i)
    (y : lineMixedSub ρ.dual i)
    (d : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hdc : d.coord (lineFacesEquivOrbits i) =
        faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
          (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
          (fun i => lineEmb_range i.rep) (rep6 ρ) i
          (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x.1))
    (hec : e.coord (lineFacesEquivOrbits i) =
        faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
          (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
          (fun i => lineEmb_range i.rep) (rep6 ρ).dual i
          (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) y.1))
    (r : ℂ →ₗ[ℚ] ℚ)
    (ρ' : Representation ℚ ↥(gammaNQAt 6 i.rep) (dualRepG (repAt ρ i)))
    (hρ' : ∀ g x, ρ' g x = (dualRepG (repAt ρ i)).ρ g x)
    (eQ : repAt ρ i →ₗ[ℚ] dualRepG (repAt ρ i) →ₗ[ℚ] ℚ)
    (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ (repAt ρ i) x y))
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r)) :
    ∃ (z : relativeTwoCocycles (lineFaceExt 6 i.rep).inl (repAt ρ i))
      (z' : relativeTwoCocycles (lineFaceExt 6 i.rep).inl (dualRepG (repAt ρ i))),
      relativeTwoCocycleClass (lineFaceExt 6 i.rep).inl (repAt ρ i) z = ⟨x.1, res_radical_of_lineMixedAt x⟩ ∧
      relativeTwoCocycleClass (lineFaceExt 6 i.rep).inl (dualRepG (repAt ρ i)) z' = ⟨y.1, res_radical_of_lineMixedAt y⟩ ∧
      (∀ a b : Gamma 6, z.val (lineFaceSplitting 6 i.rep a, lineFaceSplitting 6 i.rep b) = 0) ∧
      (∀ (r : RadicalLattice) (l : Gamma 6), z.val ((lineFaceExt 6 i.rep).inl r, lineFaceSplitting 6 i.rep l) = 0) ∧
      (∀ (r : RadicalLattice) (l : Gamma 6), z'.val ((lineFaceExt 6 i.rep).inl r, lineFaceSplitting 6 i.rep l) = 0) ∧
      ∃ (gb : ↥(gammaNQAt 6 i.rep) → ↥(gammaNQAt 6 i.rep) → ↥(gammaNQAt 6 i.rep) → ℚ)
        (_ : ∀ a b c : RadicalLattice, gb ((lineFaceExt 6 i.rep).inl a) ((lineFaceExt 6 i.rep).inl b) ((lineFaceExt 6 i.rep).inl c) = 0)
        (_ : dd3T gb = cup22 ρ' eQ (fun a b => z.val (a, b)) (fun a b => z'.val (a, b)))
        (wB : ∀ c : ↥(cuspReps hN).R, ↥(MulAction.stabilizer Γ6 (flagAt i.rep (cuspPrim (c : RationalLine2)))) → repAt ρ i)
        (_ : ∀ (c : ↥(cuspReps hN).R) b₁ b₂, (repAt ρ i).ρ (flagIota i.rep (cuspPrim (c : RationalLine2)) b₁) (wB c b₂) - wB c (b₁ * b₂) + wB c b₁ =
          z.val (flagIota i.rep (cuspPrim (c : RationalLine2)) b₁, flagIota i.rep (cuspPrim (c : RationalLine2)) b₂))
        (hΘ : ∀ c : ↥(cuspReps hN).R, dThree ((flagLift i.rep (cuspPrim (c : RationalLine2))
          ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))) (sigma_fix (c : RationalLine2))).flagTheta ρ' eQ (wB c)
          (fun a b => z'.val (a, b)) gb) = 0),
        ∀ c : ↥(cuspReps hN).R,
          flagLam (flagAt i.rep (cuspPrim (c : RationalLine2)))
            (clsRes (MulAction.stabilizer Γ6 (flagAt i.rep (cuspPrim (c : RationalLine2)))) (lineTheta (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ
              (flagAt i.rep (cuspPrim (c : RationalLine2)))) (lineTheta_dThree _ d e γ hγ _)) =
          flagLam (flagAt i.rep (cuspPrim (c : RationalLine2)))
            (clsRes (MulAction.stabilizer Γ6 (flagAt i.rep (cuspPrim (c : RationalLine2)))) _ (hΘ c)) := by
  obtain ⟨z, hz, hU, hmix⟩ := exists_normal_form_mixed (lineFaceSplitting 6 i.rep) (repAt ρ i)
    (fun A z => H2_vanish_level (CongruenceSubgroup.Gamma 6) A z) ⟨x.1, res_radical_of_lineMixedAt x⟩
  obtain ⟨z', hz', -, hmix'⟩ := exists_normal_form_mixed (lineFaceSplitting 6 i.rep) (dualRepG (repAt ρ i))
    (fun A z => H2_vanish_level (CongruenceSubgroup.Gamma 6) A z) ⟨y.1, res_radical_of_lineMixedAt y⟩
  have hzx : groupCohomology.H2π _ z.val = x.1 := congrArg Subtype.val hz
  have hzy : groupCohomology.H2π _ z'.val = y.1 := congrArg Subtype.val hz'
  obtain ⟨κ, hκ⟩ := nft1_line_rep6 ρ i x.1 d hdc z.val hzx
  have hzy' : groupCohomology.H2π (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual))
      (z'.val : groupCohomology.cocycles₂ (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual))) = y.1 := hzy
  have t1 := nft1_line_dual ρ i y.1 e hec
  have t2 := t1 (z'.val : groupCohomology.cocycles₂ (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
  have t3 := t2 hzy'
  obtain ⟨κ', hκ'⟩ := t3
  have hrad : ∀ a b : Multiplicative (ℤ × ℤ), z.val.1 ((lineFaceExt 6 i.rep).inl a, (lineFaceExt 6 i.rep).inl b) = 0 :=
    fun a b => z.2 a b
  have h1 : zbarG i d = zxQ ρ i z.val + dd1 ((qRep (MonoidHom.id Γ6) (rep6 ρ)).ρ.comp (lineEmb i.rep)) κ := by
    funext a c
    refine (lineZbar_eq_zbarG (rep6 ρ) i d a c).symm.trans ((hκ a c).trans ?_)
    simp only [Pi.add_apply, dd1, zxQ]
    rw [qRep_comp_emb]
    rfl
  have h2 : zbarG i e = zyQ ρ i z'.val + dd1 ((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (lineEmb i.rep)) κ' := by
    funext a c
    refine (lineZbar_eq_zbarG (rep6 ρ).dual i e a c).symm.trans ((hκ' a c).trans ?_)
    simp only [Pi.add_apply, dd1, zyQ]
    rw [qRepDual_comp_emb]
    rfl
  have hcore := nft2_core (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) i d e γ hγ (zxQ ρ i z.val) (zyQ ρ i z'.val) κ κ'
    (cocycle_dd2' ρ i z.val) (cocycle_dd2_dual ρ i z'.val) h1 h2 (lineFaceExt 6 i.rep).inl
    (lineFaceExt 6 i.rep).inl_injective hrad
  obtain ⟨gn, hdd, hgn0, hF⟩ := hcore
  have pair : ∀ v φ, eQ v φ = pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) v φ :=
    fun v φ => (he v φ).trans (pairOf_eval ρ r v φ).symm
  have hd' : dd3T gn = cup22 ρ' eQ (fun a b => z.val (a, b)) (fun a b => z'.val (a, b)) := by
    refine hdd.trans ?_
    funext a b c e'
    simp only [cup22, zxQ, zyQ]
    refine Eq.trans ?_ (congrArg (fun t => t) (pair _ _)).symm
    exact congrArg (pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) _) ((qRepDual_comp_emb ρ i (a * b) _).trans (hρ' _ _).symm)
  have key := fun c : ↥(cuspReps hN).R => hF (flagAt i.rep (cuspPrim (c : RationalLine2))) (flagLineOf_flagAt i.rep _)
    (flagIota i.rep (cuspPrim (c : RationalLine2))) (lineEmb_flagIota i.rep _)
  choose wB hA hΘ0 hB using key
  have hΘ' : ∀ c : ↥(cuspReps hN).R, dThree ((flagLift i.rep (cuspPrim (c : RationalLine2))
      ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))) (sigma_fix (c : RationalLine2))).flagTheta ρ' eQ (fun b => wB c b)
      (fun a b => z'.val (a, b)) gn) = 0 := fun c =>
    (congrArg dThree (flagTheta_eq_core hN ρ i r ρ' hρ' eQ he z'.val gn c (fun b => wB c b))).trans (hΘ0 c)
  refine ⟨z, z', hz, hz', hU, hmix, hmix', gn, hgn0, hd', fun c => wB c, ?_, hΘ', fun c => ?_⟩
  · intro c b₁ b₂
    have := congrFun (congrFun (hA c) b₁) b₂
    simp only [dd1, zxQ] at this
    have e1 := repRho_flag ρ i (cuspPrim (c : RationalLine2)) b₁ (wB c b₂)
    beta_reduce
    simp only [e1]
    exact this
  · exact congrArg (flagLam (flagAt i.rep (cuspPrim (c : RationalLine2))))
      ((hB c).trans (clsRes_congr _ (flagTheta_eq_core hN ρ i r ρ' hρ' eQ he z'.val gn c (fun b => wB c b)).symm _ _))

end Main

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
