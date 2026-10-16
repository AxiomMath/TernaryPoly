module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.QNat
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ResolutionModel

@[expose] public section


/-!
# Hecke-type naturality of the `Q`-side Hochschild-Serre step

Formalized by Claude Sonnet 5.5.

Let `Q` be a group, `Γ₀ ≤ Q` of finite index, `χ : Γ₀ →* Q`, `Z` a complex of `Q`-modules, `ζ : Res_{Γ₀} Z ⟶ Res_χ Z` a chain
map of complexes of `Γ₀`-modules, and `lam : Res_{Γ₀} X ⟶ Res_χ X` a `Γ₀`-map.

* `hmuC Γ₀ χ Z ζ lam : CxF Z X ⟶ CxF Z X`: the chain map `(Z ⊗ X)_Q → (Z ⊗ X)_Q` which in degree `j` is the coset-sum transfer
  `tX : (Z_j ⊗ X)_Q → (Res Z_j ⊗ Res X)_{Γ₀}` followed by `[n ⊗ x] ↦ [ζ n ⊗ lam x]` (`MX`) and the corestriction `corX` along
  `χ`; on generators `[n ⊗ x] ↦ ∑_{c ∈ Γ₀\Q} [ζ_j(c n) ⊗ lam(c x)]` (`hmuC_f_mk`).
* `hmuC_comm`, `sesHecke`: for `d : P1 ⟶ P0`, `ε : P0 ⟶ 1` and compatible `lam1, lam0` (`lam1 ≫ Res_χ d = Res_{Γ₀} d ≫ lam0`,
  `lam0 ≫ Res_χ ε = Res_{Γ₀} ε`; the trivial module has the identity `lamTriv`) these form a morphism of short complexes
  `sesC Z P1 P0 d ε hdε ⟶ sesC Z P1 P0 d ε hdε`.
* `zetaH`: the map `Res_{Γ₀} (H_n Z) ⟶ Res_χ (H_n Z)` induced by `ζ` on homology (`resHomIso`: `Res` is exact).
  `kappaExp Γ₀ χ Z n ζ X lam` is the Hecke-type endomorphism of `(H_n Z ⊗ X)_Q`; **on generators**
  `[h ⊗ x] ↦ ∑_{c ∈ Γ₀\Q} [zetaH(c h) ⊗ lam(c x)]` (`kappaExp_mk`).
* `hmuC_homology`: for projective `X`, `Res_{Γ₀} X`, `Res_χ X`: `H_n(hmuC) ≫ phiH = phiH ≫ kappaExp`.
* **`hsAmb_hecke`**: `H₃(hmuC … lamTriv) ≫ hsAmb = hsAmb ≫ kappaExp … 2 ζ P1 lam1`.

The proof uses the transfer natural transformation `tX : FX X ⟶ Res ⋙ FX (Res X)` and the corestriction natural transformation
`corX` (`ShortComplex.homologyMap_mapNatTrans`), the comparison `mapHomologyIso_comp` for a composite functor (proved via the
uniqueness of `homologyIso` for two left homology data, `homologyIso_map_comp`), and `phiH_nat`, `phiH_square` over `Γ₀`.
-/

open CategoryTheory MonoidalCategory Representation Representation.Coinvariants Limits
open TernaryPeriodPolynomials.Argument.HeckeHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

variable {Q : Type} [Group Q] (Γ₀ : Subgroup Q) [Γ₀.FiniteIndex] (χ : Γ₀ →* Q)

/-- The transfer `(N ⊗ X)_Q → (Res N ⊗ Res X)_{Γ₀}`, naturally in `N`. -/
def tX (X : Rep.{0} ℚ Q) : FX X ⟶ Rep.resFunctor Γ₀.subtype ⋙ FX (Rep.res Γ₀.subtype X) where
  app N := ModuleCat.ofHom (tMapR Γ₀ (N.ρ.tprod X.ρ))
  naturality _ _ f := (tNatR Γ₀).naturality (f ▷ X)

theorem tX_app_mk (X N : Rep.{0} ℚ Q) (n : N) (x : X) :
    ((tX Γ₀ X).app N).hom (Coinvariants.mk (N.ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)) =
      ∑ c : RC Γ₀, Coinvariants.mk (((N.ρ.tprod X.ρ).comp Γ₀.subtype))
        ((N.ρ.tprod X.ρ) c.out (n ⊗ₜ[ℚ] x)) := by
  exact tSumR_apply Γ₀ (N.ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)

section Cor

variable {H : Type} [Group H] (χ : H →* Q)

/-- Corestriction along `χ`: `(Res_χ N)_H → N_Q`. -/
def corM {V : Type*} [AddCommGroup V] [Module ℚ V] (ρ : Representation ℚ Q V) :
    Coinvariants (ρ.comp χ) →ₗ[ℚ] Coinvariants ρ :=
  Coinvariants.lift _ (Coinvariants.mk ρ) fun h => LinearMap.ext fun v =>
    Coinvariants.mk_self_apply ρ (χ h) v

theorem corM_mk {V : Type*} [AddCommGroup V] [Module ℚ V] (ρ : Representation ℚ Q V) (v : V) :
    corM χ ρ (Coinvariants.mk _ v) = Coinvariants.mk ρ v := rfl

/-- The corestriction natural transformation `(Res_χ N ⊗ Res_χ X)_H → (N ⊗ X)_Q`. -/
def corX (X : Rep.{0} ℚ Q) : Rep.resFunctor χ ⋙ FX (Rep.res χ X) ⟶ FX X where
  app N := ModuleCat.ofHom (corM χ (N.ρ.tprod X.ρ))
  naturality _ _ f := by
    refine ModuleCat.hom_ext (Coinvariants.hom_ext (TensorProduct.ext' fun n x => ?_))
    rfl

end Cor

section Chain

variable {H : Type} [Group H]

/-- The complex of `H`-modules obtained from a complex of `Q`-modules by restriction along `f : H →* Q`. -/
abbrev ResC (f : H →* Q) (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) : ChainComplex (Rep.{0} ℚ H) ℕ :=
  ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z

variable (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) (X : Rep.{0} ℚ Q)

/-- The transfer on the coinvariant complexes: `(Z ⊗ X)_Q → (Res Z ⊗ Res X)_{Γ₀}`. -/
def TX : CxF Z X ⟶ CxF (ResC Γ₀.subtype Z) (Rep.res Γ₀.subtype X) :=
  (NatTrans.mapHomologicalComplex (tX Γ₀ X) (ComplexShape.down ℕ)).app Z

/-- The corestriction on the coinvariant complexes: `(Res_χ Z ⊗ Res_χ X)_{Γ₀} → (Z ⊗ X)_Q`. -/
def KX : CxF (ResC χ Z) (Rep.res χ X) ⟶ CxF Z X :=
  (NatTrans.mapHomologicalComplex (corX χ X) (ComplexShape.down ℕ)).app Z

variable (ζ : ResC Γ₀.subtype Z ⟶ ResC χ Z) {X}
  (lam : Rep.res Γ₀.subtype X ⟶ Rep.res χ X)

/-- The middle map `(Res Z ⊗ Res X)_{Γ₀} → (Res_χ Z ⊗ Res_χ X)_{Γ₀}` induced by `ζ` and `lam`. -/
def MX : CxF (ResC Γ₀.subtype Z) (Rep.res Γ₀.subtype X) ⟶ CxF (ResC χ Z) (Rep.res χ X) :=
  muX ζ (Rep.res Γ₀.subtype X) ≫ CxMap (ResC χ Z) lam

/-- **The Hecke-type endomorphism of the coinvariant complex** `(Z ⊗ X)_Q`: in degree `j`,
`[n ⊗ x] ↦ ∑_{c ∈ Γ₀\Q} [ζ_j (c n) ⊗ lam (c x)]`. -/
def hmuC : CxF Z X ⟶ CxF Z X := TX Γ₀ Z X ≫ MX Γ₀ χ Z ζ lam ≫ KX Γ₀ χ Z X

theorem TX_f_mk (j : ℕ) (n : Z.X j) (x : X) :
    ((TX Γ₀ Z X).f j).hom (Coinvariants.mk ((Z.X j).ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)) =
      ∑ c : RC Γ₀, Coinvariants.mk (((Z.X j).ρ.tprod X.ρ).comp Γ₀.subtype)
        (((Z.X j).ρ.tprod X.ρ) c.out (n ⊗ₜ[ℚ] x)) :=
  tX_app_mk Γ₀ X (Z.X j) n x

theorem hmuC_f_mk (j : ℕ) (n : Z.X j) (x : X) :
    ((hmuC Γ₀ χ Z ζ lam).f j).hom (Coinvariants.mk ((Z.X j).ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)) =
      ∑ c : RC Γ₀, Coinvariants.mk ((Z.X j).ρ.tprod X.ρ)
        ((ζ.f j).hom ((Z.X j).ρ c.out n) ⊗ₜ[ℚ] lam.hom (X.ρ c.out x)) := by
  have e : ((hmuC Γ₀ χ Z ζ lam).f j).hom (Coinvariants.mk ((Z.X j).ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)) =
      ((KX Γ₀ χ Z X).f j).hom (((MX Γ₀ χ Z ζ lam).f j).hom
        (((TX Γ₀ Z X).f j).hom (Coinvariants.mk ((Z.X j).ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)))) := rfl
  rw [e, TX_f_mk]
  erw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun c _ => rfl

theorem hmuC_comm {X Y : Rep.{0} ℚ Q} (φ : X ⟶ Y) (lamX : Rep.res Γ₀.subtype X ⟶ Rep.res χ X)
    (lamY : Rep.res Γ₀.subtype Y ⟶ Rep.res χ Y)
    (h : ∀ x, lamY.hom (φ.hom x) = φ.hom (lamX.hom x)) :
    CxMap Z φ ≫ hmuC Γ₀ χ Z ζ lamY = hmuC Γ₀ χ Z ζ lamX ≫ CxMap Z φ := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  refine ModuleCat.hom_ext (Coinvariants.hom_ext (TensorProduct.ext' fun n x => ?_))
  change ((hmuC Γ₀ χ Z ζ lamY).f j).hom (((CxMap Z φ).f j).hom
      (Coinvariants.mk ((Z.X j).ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x))) =
    ((CxMap Z φ).f j).hom (((hmuC Γ₀ χ Z ζ lamX).f j).hom
      (Coinvariants.mk ((Z.X j).ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)))
  have e1 : ((CxMap Z φ).f j).hom (Coinvariants.mk ((Z.X j).ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)) =
      Coinvariants.mk ((Z.X j).ρ.tprod Y.ρ) (n ⊗ₜ[ℚ] φ.hom x) := FXmap_mk φ n x
  rw [e1, hmuC_f_mk, hmuC_f_mk]
  erw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Eq.trans ?_ (FXmap_mk φ _ _).symm
  rw [← Rep.hom_comm_apply φ c.out x, h]

end Chain

section Comp

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D] [Abelian E]
  (R : C ⥤ D) (F : D ⥤ E) [R.Additive] [F.Additive] (S : ShortComplex C)
  [R.PreservesLeftHomologyOf S] [F.PreservesLeftHomologyOf (S.map R)]
  [(R ⋙ F).PreservesLeftHomologyOf S]

omit [R.PreservesLeftHomologyOf S] [F.PreservesLeftHomologyOf (S.map R)] [(R ⋙ F).PreservesLeftHomologyOf S] in
/-- The two left homology data of `S.map (R ⋙ F)` obtained by applying `R ⋙ F` and by applying `R`, then `F`,
have the same `homologyIso`. -/
theorem homologyIso_map_comp (hl : S.LeftHomologyData) [hl.IsPreservedBy R] [(hl.map R).IsPreservedBy F]
    [hl.IsPreservedBy (R ⋙ F)] :
    (hl.map (R ⋙ F)).homologyIso = ((hl.map R).map F).homologyIso := by
  let γ : ShortComplex.LeftHomologyMapData (𝟙 (S.map (R ⋙ F))) (hl.map (R ⋙ F)) ((hl.map R).map F) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := (Category.id_comp _).trans (Category.comp_id _).symm
      commf' := by
        have a := ShortComplex.LeftHomologyData.map_f' hl (R ⋙ F)
        have b := ShortComplex.LeftHomologyData.map_f' (hl.map R) F
        have c := ShortComplex.LeftHomologyData.map_f' hl R
        refine (Category.comp_id _).trans ?_
        refine a.trans ?_
        refine Eq.trans ?_ (Category.id_comp _).symm
        exact (congrArg F.map c).symm.trans b.symm
      commπ := (Category.comp_id _).trans (Category.id_comp _).symm }
  have h := γ.homologyMap_comm
  rw [ShortComplex.homologyMap_id, Category.id_comp] at h
  exact Iso.ext ((Category.comp_id _).symm.trans h.symm)

/-- The homology comparison for a composite functor. -/
theorem mapHomologyIso_comp :
    S.mapHomologyIso (R ⋙ F) = (S.map R).mapHomologyIso F ≪≫ F.mapIso (S.mapHomologyIso R) := by
  have h1 := ShortComplex.LeftHomologyData.mapHomologyIso_eq (S := S) S.homologyData.left (R ⋙ F)
  have h2 := ShortComplex.LeftHomologyData.mapHomologyIso_eq (S := S.map R) (S.homologyData.left.map R) F
  have h3 := ShortComplex.LeftHomologyData.mapHomologyIso_eq (S := S) S.homologyData.left R
  rw [h1, h2, h3]
  refine Iso.ext ?_
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso]
  have hj : F.map (S.homologyData.left.map R).homologyIso.inv ≫
      F.map ((S.homologyData.left.map R).homologyIso.hom ≫ R.map S.homologyData.left.homologyIso.inv) =
      F.map (R.map S.homologyData.left.homologyIso.inv) := by
    rw [← F.map_comp]
    exact congrArg F.map (Iso.inv_hom_id_assoc _ _)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun w => ((S.homologyData.left.map R).map F).homologyIso.hom ≫ w) hj.symm)
  exact congrArg (fun w => Iso.hom w ≫ F.map (R.map S.homologyData.left.homologyIso.inv))
    (homologyIso_map_comp R F S S.homologyData.left)

end Comp

theorem preservesHomology_comp {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D] [Abelian E]
    (R : C ⥤ D) (F : D ⥤ E) [R.Additive] [F.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [F.PreservesHomology] : (R ⋙ F).PreservesHomology where
  preservesKernels X Y f := by
    have h2 : PreservesLimit (parallelPair (R.map f) 0) F := Functor.PreservesHomology.preservesKernel F (R.map f)
    have e : parallelPair f 0 ⋙ R ≅ parallelPair (R.map f) 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    have h3 : PreservesLimit (parallelPair f 0 ⋙ R) F := preservesLimit_of_iso_diagram F e.symm
    exact comp_preservesLimit (K := parallelPair f 0) R F
  preservesCokernels X Y f := by
    have h2 : PreservesColimit (parallelPair (R.map f) 0) F := Functor.PreservesHomology.preservesCokernel F (R.map f)
    have e : parallelPair f 0 ⋙ R ≅ parallelPair (R.map f) 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    have h3 : PreservesColimit (parallelPair f 0 ⋙ R) F := preservesColimit_of_iso_diagram F e.symm
    exact comp_preservesColimit (K := parallelPair f 0) R F


section Homology

variable {H : Type} [Group H]

variable (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) (n : ℕ)

/-- Restriction of the homology: `Res_f (H_n Z) ≅ H_n (Res_f Z)`. -/
def resHomIso (f : H →* Q) : (ResC f Z).homology n ≅ (Rep.resFunctor f).obj (Z.homology n) :=
  (Z.sc n).mapHomologyIso (Rep.resFunctor f)

variable (ζ : ResC Γ₀.subtype Z ⟶ ResC χ Z)

/-- The map `Res_{Γ₀} (H_n Z) ⟶ Res_χ (H_n Z)` induced on homology by `ζ`. -/
def zetaH : (Rep.resFunctor Γ₀.subtype).obj (Z.homology n) ⟶ (Rep.resFunctor χ).obj (Z.homology n) :=
  (resHomIso Z n Γ₀.subtype).inv ≫ HomologicalComplex.homologyMap ζ n ≫ (resHomIso Z n χ).hom

variable (X : Rep.{0} ℚ Q) (lam : Rep.res Γ₀.subtype X ⟶ Rep.res χ X)

/-- **The Hecke-type map on the ambient space** `(H_n Z ⊗ X)_Q`:
`[h ⊗ x] ↦ ∑_{c ∈ Γ₀\Q} [H_n(ζ)(c h) ⊗ lam (c x)]`. -/
def kappaExp : (FX X).obj (Z.homology n) ⟶ (FX X).obj (Z.homology n) :=
  (tX Γ₀ X).app (Z.homology n) ≫ (FX (Rep.res Γ₀.subtype X)).map (zetaH Γ₀ χ Z n ζ) ≫
    (FXmap lam).app ((Rep.resFunctor χ).obj (Z.homology n)) ≫ (corX χ X).app (Z.homology n)

theorem kappaExp_mk (h : Z.homology n) (x : X) :
    ((kappaExp Γ₀ χ Z n ζ X lam).hom (Coinvariants.mk ((Z.homology n).ρ.tprod X.ρ) (h ⊗ₜ[ℚ] x))) =
      ∑ c : RC Γ₀, Coinvariants.mk ((Z.homology n).ρ.tprod X.ρ)
        ((zetaH Γ₀ χ Z n ζ).hom ((Z.homology n).ρ c.out h) ⊗ₜ[ℚ] lam.hom (X.ρ c.out x)) := by
  have e : (kappaExp Γ₀ χ Z n ζ X lam).hom (Coinvariants.mk ((Z.homology n).ρ.tprod X.ρ) (h ⊗ₜ[ℚ] x)) =
      ((corX χ X).app (Z.homology n)).hom (((FXmap lam).app ((Rep.resFunctor χ).obj (Z.homology n))).hom
        (((FX (Rep.res Γ₀.subtype X)).map (zetaH Γ₀ χ Z n ζ)).hom
          (((tX Γ₀ X).app (Z.homology n)).hom
            (Coinvariants.mk ((Z.homology n).ρ.tprod X.ρ) (h ⊗ₜ[ℚ] x))))) := rfl
  rw [e, tX_app_mk]
  erw [map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun c _ => rfl

theorem trans_inv_hom_aux {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (e : D ≅ C) :
    (f ≫ g ≫ e.inv) ≫ e.hom = f ≫ g := by simp

theorem trans_inv_hom_aux' {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞} (f : A ⟶ B) (e : C ≅ B) :
    (f ≫ e.inv) ≫ e.hom = f := by simp

/-- Pure category theory: the diagram chase of `hmuC_homology`. -/
theorem hecke_chase {𝒞 : Type*} [Category 𝒞] {P Q1 Q2 R0 S1 S2 S3 S4 S5 S6 : 𝒞}
    (HT : P ⟶ Q1) (HM : Q1 ⟶ Q2) (HK : Q2 ⟶ P) (φF : P ⟶ R0) (tx : R0 ⟶ S1) (IGinv : S1 ⟶ Q1)
    (φY : Q1 ⟶ S2) (φY' : Q2 ⟶ S4) (IG'h : Q2 ⟶ S5) (aι : S1 ⟶ S2) (Hz : S2 ⟶ S3) (aχ : S3 ⟶ S6)
    (lamY' : S3 ⟶ S4) (lamR : S6 ⟶ S5) (b : S4 ⟶ S5) (cor : S5 ⟶ R0)
    (hT : HT = φF ≫ tx ≫ IGinv) (hK : HK ≫ φF = IG'h ≫ cor) (hC : IG'h = φY' ≫ b)
    (hM : HM ≫ φY' = φY ≫ Hz ≫ lamY') (hinv : IGinv ≫ φY = aι) (hnat : aχ ≫ lamR = lamY' ≫ b) :
    HT ≫ HM ≫ HK ≫ φF = φF ≫ tx ≫ (aι ≫ Hz ≫ aχ) ≫ lamR ≫ cor := by
  rw [hK, hC, hT]
  simp only [Category.assoc]
  rw [reassoc_of% hM, reassoc_of% hinv, reassoc_of% hnat]

/-- The comparison `H_n (G Z) ≅ G (H_n Z)` for a homology-preserving functor, with `H_n Z` written in `Rep`. -/
def gIso (G : Rep.{0} ℚ Q ⥤ ModuleCat.{0} ℚ) [G.Additive] [G.PreservesHomology] :
    ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Z).homology n ≅ G.obj (Z.homology n) :=
  (Z.sc n).mapHomologyIso G

theorem hmuC_homology [Projective X] [Projective (Rep.res Γ₀.subtype X)] [Projective (Rep.res χ X)] :
    HomologicalComplex.homologyMap (hmuC Γ₀ χ Z ζ lam) n ≫ (phiH Z X n).hom =
      (phiH Z X n).hom ≫ kappaExp Γ₀ χ Z n ζ X lam := by
  have h1 := FX_preservesHomology X
  have h2 := FX_preservesHomology (Rep.res Γ₀.subtype X)
  have h3 := FX_preservesHomology (Rep.res χ X)
  have hG : (Rep.resFunctor Γ₀.subtype ⋙ FX (Rep.res Γ₀.subtype X)).PreservesHomology :=
    preservesHomology_comp _ _
  have hG' : (Rep.resFunctor χ ⋙ FX (Rep.res χ X)).PreservesHomology := preservesHomology_comp _ _
  have hT : HomologicalComplex.homologyMap (TX Γ₀ Z X) n =
      (phiH Z X n).hom ≫ (tX Γ₀ X).app (Z.homology n) ≫
        (gIso Z n (Rep.resFunctor Γ₀.subtype ⋙ FX (Rep.res Γ₀.subtype X))).inv :=
    ShortComplex.homologyMap_mapNatTrans (Z.sc n) (tX Γ₀ X)
  have hK : HomologicalComplex.homologyMap (KX Γ₀ χ Z X) n =
      (gIso Z n (Rep.resFunctor χ ⋙ FX (Rep.res χ X))).hom ≫ (corX χ X).app (Z.homology n) ≫
        (phiH Z X n).inv :=
    ShortComplex.homologyMap_mapNatTrans (Z.sc n) (corX χ X)
  have hM : HomologicalComplex.homologyMap (MX Γ₀ χ Z ζ lam) n ≫
      (phiH (ResC χ Z) (Rep.res χ X) n).hom =
      (phiH (ResC Γ₀.subtype Z) (Rep.res Γ₀.subtype X) n).hom ≫
        (FX (Rep.res Γ₀.subtype X)).map (HomologicalComplex.homologyMap ζ n) ≫
          (FXmap lam).app ((ResC χ Z).homology n) := by
    unfold MX
    rw [HomologicalComplex.homologyMap_comp, Category.assoc, phiH_square (ResC χ Z) _ _ lam n,
      ← Category.assoc (HomologicalComplex.homologyMap (muX ζ (Rep.res Γ₀.subtype X)) n),
      phiH_nat ζ (Rep.res Γ₀.subtype X) n, Category.assoc]
  have hC1 : gIso Z n (Rep.resFunctor Γ₀.subtype ⋙ FX (Rep.res Γ₀.subtype X)) =
      phiH (ResC Γ₀.subtype Z) (Rep.res Γ₀.subtype X) n ≪≫
        (FX (Rep.res Γ₀.subtype X)).mapIso (resHomIso Z n Γ₀.subtype) :=
    mapHomologyIso_comp (Rep.resFunctor Γ₀.subtype) (FX (Rep.res Γ₀.subtype X)) (Z.sc n)
  have hC1' : gIso Z n (Rep.resFunctor χ ⋙ FX (Rep.res χ X)) =
      phiH (ResC χ Z) (Rep.res χ X) n ≪≫ (FX (Rep.res χ X)).mapIso (resHomIso Z n χ) :=
    mapHomologyIso_comp (Rep.resFunctor χ) (FX (Rep.res χ X)) (Z.sc n)
  have hK1 : HomologicalComplex.homologyMap (KX Γ₀ χ Z X) n ≫ (phiH Z X n).hom =
      (gIso Z n (Rep.resFunctor χ ⋙ FX (Rep.res χ X))).hom ≫ (corX χ X).app (Z.homology n) :=
    (congrArg (fun w => w ≫ (phiH Z X n).hom) hK).trans (trans_inv_hom_aux _ _ _)
  have hinvG : (gIso Z n (Rep.resFunctor Γ₀.subtype ⋙ FX (Rep.res Γ₀.subtype X))).inv ≫
      (phiH (ResC Γ₀.subtype Z) (Rep.res Γ₀.subtype X) n).hom =
      (FX (Rep.res Γ₀.subtype X)).map (resHomIso Z n Γ₀.subtype).inv := by
    have e2 : (gIso Z n (Rep.resFunctor Γ₀.subtype ⋙ FX (Rep.res Γ₀.subtype X))).inv =
        (FX (Rep.res Γ₀.subtype X)).map (resHomIso Z n Γ₀.subtype).inv ≫
          (phiH (ResC Γ₀.subtype Z) (Rep.res Γ₀.subtype X) n).inv :=
      congrArg Iso.inv hC1
    exact (congrArg (fun w => w ≫ (phiH (ResC Γ₀.subtype Z) (Rep.res Γ₀.subtype X) n).hom) e2).trans
      (trans_inv_hom_aux' _ _)
  have hnat := (FXmap lam).naturality (resHomIso Z n χ).hom
  rw [hmuC, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  have hfin := hecke_chase (HomologicalComplex.homologyMap (TX Γ₀ Z X) n)
    (HomologicalComplex.homologyMap (MX Γ₀ χ Z ζ lam) n) (HomologicalComplex.homologyMap (KX Γ₀ χ Z X) n)
    (phiH Z X n).hom ((tX Γ₀ X).app (Z.homology n)) (gIso Z n (Rep.resFunctor Γ₀.subtype ⋙ FX (Rep.res Γ₀.subtype X))).inv
    (phiH (ResC Γ₀.subtype Z) (Rep.res Γ₀.subtype X) n).hom (phiH (ResC χ Z) (Rep.res χ X) n).hom
    (gIso Z n (Rep.resFunctor χ ⋙ FX (Rep.res χ X))).hom
    ((FX (Rep.res Γ₀.subtype X)).map (resHomIso Z n Γ₀.subtype).inv)
    ((FX (Rep.res Γ₀.subtype X)).map (HomologicalComplex.homologyMap ζ n))
    ((FX (Rep.res Γ₀.subtype X)).map (resHomIso Z n χ).hom)
    ((FXmap lam).app ((ResC χ Z).homology n))
    ((FXmap lam).app ((Rep.resFunctor χ).obj (Z.homology n)))
    ((FX (Rep.res χ X)).map (resHomIso Z n χ).hom) ((corX χ X).app (Z.homology n))
    hT hK1 (congrArg Iso.hom hC1') hM hinvG hnat
  unfold kappaExp zetaH
  simp only [Functor.map_comp, Category.assoc] at hfin ⊢
  exact hfin

end Homology

section Main

variable (P1 P0 : Rep.{0} ℚ Q) (d : P1 ⟶ P0) (ε : P0 ⟶ Rep.trivial ℚ Q ℚ) (hdε : d ≫ ε = 0)
  (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) (ζ : ResC Γ₀.subtype Z ⟶ ResC χ Z)
  (lam1 : Rep.res Γ₀.subtype P1 ⟶ Rep.res χ P1) (lam0 : Rep.res Γ₀.subtype P0 ⟶ Rep.res χ P0)
  (hd : lam1 ≫ (Rep.resFunctor χ).map d = (Rep.resFunctor Γ₀.subtype).map d ≫ lam0)
  (hε : lam0 ≫ (Rep.resFunctor χ).map ε = (Rep.resFunctor Γ₀.subtype).map ε)

/-- The identity correspondence on the trivial representation. -/
def lamTriv : Rep.res Γ₀.subtype (Rep.trivial ℚ Q ℚ) ⟶ Rep.res χ (Rep.trivial ℚ Q ℚ) :=
  𝟙 (Rep.trivial ℚ ↥Γ₀ ℚ)

/-- **The Hecke-type morphism of the short complex `sesC Z`.** -/
def sesHecke : sesC Z P1 P0 d ε hdε ⟶ sesC Z P1 P0 d ε hdε where
  τ₁ := hmuC Γ₀ χ Z ζ lam1
  τ₂ := hmuC Γ₀ χ Z ζ lam0
  τ₃ := hmuC Γ₀ χ Z ζ (lamTriv Γ₀ χ)
  comm₁₂ := (hmuC_comm Γ₀ χ Z ζ d lam1 lam0 (fun y => by
    have := congrArg (fun t => t.hom y) hd
    exact this.symm)).symm
  comm₂₃ := (hmuC_comm Γ₀ χ Z ζ ε lam0 (lamTriv Γ₀ χ) (fun y => by
    have := congrArg (fun t => t.hom y) hε
    exact this.symm)).symm

theorem hecke_chase_nat {𝒞 : Type*} [Category 𝒞] {A A' B B' C C' : 𝒞} (t3 : A ⟶ A') (δ : A ⟶ B)
    (δ' : A' ⟶ B') (t1 : B ⟶ B') (φ : B ⟶ C) (φ' : B' ⟶ C') (κ : C ⟶ C') (hδ : δ ≫ t1 = t3 ≫ δ')
    (h2 : t1 ≫ φ' = φ ≫ κ) : t3 ≫ δ' ≫ φ' = (δ ≫ φ) ≫ κ := by
  rw [← Category.assoc, ← hδ, Category.assoc, h2, Category.assoc]

include lam0 hd hε in
/-- **Hecke-type naturality of the ambient Hochschild-Serre map** (`hsAmb`): the Hecke-type endomorphism of
`H₃((Z ⊗ 1)_Q)` is intertwined, by the connecting map followed by `phiH`, with the Hecke-type map `kappaExp` on
`(H₂ Z ⊗ P1)_Q`, which is `[h ⊗ x] ↦ ∑_{c ∈ Γ₀\Q} [H₂(ζ)(c h) ⊗ lam1 (c x)]` (`kappaExp_mk`). -/
theorem hsAmb_hecke [Projective P1] [Projective P0] (hZ : ∀ j, Projective (Z.X j))
    (hS : (ShortComplex.mk d ε hdε).ShortExact) [Projective (Rep.res Γ₀.subtype P1)]
    [Projective (Rep.res χ P1)] :
    HomologicalComplex.homologyMap (hmuC Γ₀ χ Z ζ (lamTriv Γ₀ χ)) 3 ≫ hsAmb P1 P0 d ε hdε hS Z hZ =
      hsAmb P1 P0 d ε hdε hS Z hZ ≫ kappaExp Γ₀ χ Z 2 ζ P1 lam1 := by
  have hδ := HomologicalComplex.HomologySequence.δ_naturality (sesHecke Γ₀ χ P1 P0 d ε hdε Z ζ lam1 lam0 hd hε)
    (sesC_shortExact Z P1 P0 d ε hdε hZ hS) (sesC_shortExact Z P1 P0 d ε hdε hZ hS) 3 2 rfl
  have h2 := hmuC_homology Γ₀ χ Z 2 ζ P1 lam1
  unfold hsAmb
  exact hecke_chase_nat _ _ _ _ _ _ _ hδ h2

end Main

end TernaryPeriodPolynomials.Argument.HochschildSerre
