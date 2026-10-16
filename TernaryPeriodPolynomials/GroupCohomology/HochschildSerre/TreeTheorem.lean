module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.QSideNatural
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Inflation

@[expose] public section


/-!
# The Hochschild-Serre step on the image of a tree map

Formalized by Claude Sonnet 5.5.

Setting (as in `QSide`): `P1 → P0 → 1` a short exact sequence of projective `Q`-modules, `Z` a complex of projective
`Q`-modules with `H₃ Z = 0`, `M` a `Q`-module and `Θ3 : M ⊗ P1 ⟶ Z₃`, `Θ2 : M ⊗ P0 ⟶ Z₂` with
`Θ3 ≫ d = (M ◁ d) ≫ Θ2` and `Θ2 ≫ d = 0`.

* `zig` (pure algebra): the zig-zag identity `Σ_j (id ⊗ ε)(u_j) ⊗ c_j = - [Σ m_i ⊗ e_i]` in `(M ⊗ P1)_Q`;
* `piF`, `phiH_cls`: the comparison `phiH` of the homology of the coinvariant complex with the coinvariants of the
  homology, on classes `[(F Θ) y']` coming from a chain map `Θ` with `Θ ≫ d = 0`;
* `delta_cls_gen`: the element-level connecting homomorphism of a short exact sequence of chain complexes of
  `ℚ`-modules;
* `PsiPrime`: the `Q`-morphism `Ψ' : M ⟶ H₂ Z` with `Ψ'(m) = [Θ2(m ⊗ s0)]` (`PsiPrime_spec`: `Ψ' ∘ (id ⊗ ε) = [Θ2]`,
  `PsiPrime_unique`);
* `LamH`: the map `Λ : K_M → H₃((Z ⊗ 1)_Q)`, `x ↦ [Θ3 x ⊗ 1]` on the kernel `K_M` of `(M ⊗ P1)_Q → (M ⊗ P0)_Q`;
* **`thmAEquiv_LamH`**: `thmAEquiv (Λ x) = - (F P1).map Ψ' x`;
* `LamH_bijective`: `Λ` is bijective when `Ψ'` is an isomorphism.
-/


open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

theorem next32 : (ComplexShape.down ℕ).next 3 = 2 :=
  (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 3 2 from rfl)

theorem next21 : (ComplexShape.down ℕ).next 2 = 1 :=
  (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)

section Zig

variable {Q : Type} [Group Q] {M P0 P1 : Type} [AddCommGroup M] [Module ℚ M] [AddCommGroup P0] [Module ℚ P0]
  [AddCommGroup P1] [Module ℚ P1]
  (ρM : Representation ℚ Q M) (ρ0 : Representation ℚ Q P0) (ρ1 : Representation ℚ Q P1)
  (d : P1 →ₗ[ℚ] P0) (ε : P0 →ₗ[ℚ] ℚ)

/-- The `M`-component of an element of `M ⊗ P0`: `(id ⊗ ε)` followed by the unitor. -/
def zM (u : M ⊗[ℚ] P0) : M := TensorProduct.rid ℚ M (LinearMap.lTensor M ε u)

theorem zM_tmul (m : M) (p : P0) : zM ε (m ⊗ₜ[ℚ] p) = ε p • m := by
  simp [zM, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

/-- `u ↦ zM u ⊗ c`. -/
def Zc (c : P1) : M ⊗[ℚ] P0 →ₗ[ℚ] M ⊗[ℚ] P1 :=
  (TensorProduct.mk ℚ M P1).flip c ∘ₗ (TensorProduct.rid ℚ M).toLinearMap ∘ₗ LinearMap.lTensor M ε

theorem Zc_apply (c : P1) (u : M ⊗[ℚ] P0) : Zc ε c u = zM ε u ⊗ₜ[ℚ] c := rfl

variable {ρM ρ0 ρ1 d ε}

theorem zig_exact (hεd : ∀ p, ε (d p) = 0) (hex : ∀ p, ε p = 0 → ∃ p', d p' = p) (s0 : P0)
    (hs0 : ε s0 = 1) : Function.Exact (LinearMap.lTensor M d) (LinearMap.lTensor M ε) := by
  have hfg : Function.Exact d ε := fun p =>
    ⟨fun h => hex p h, fun ⟨p', hp'⟩ => hp' ▸ hεd p'⟩
  exact lTensor_exact M hfg (fun r => ⟨r • s0, by simp [hs0]⟩)

theorem zig_decomp (hεd : ∀ p, ε (d p) = 0) (hex : ∀ p, ε p = 0 → ∃ p', d p' = p) (s0 : P0)
    (hs0 : ε s0 = 1) :
    ∀ u : M ⊗[ℚ] P0, ∃ y : M ⊗[ℚ] P1, u = zM ε u ⊗ₜ[ℚ] s0 + LinearMap.lTensor M d y := by
  have hexact := zig_exact (M := M) hεd hex s0 hs0
  intro u
  have h0 : LinearMap.lTensor M ε (u - zM ε u ⊗ₜ[ℚ] s0) = 0 := by
    apply (TensorProduct.rid ℚ M).injective
    rw [map_sub, map_zero]
    have : TensorProduct.rid ℚ M (LinearMap.lTensor M ε (zM ε u ⊗ₜ[ℚ] s0)) = zM ε u := by
      simp [LinearMap.lTensor_tmul, hs0, TensorProduct.rid_tmul]
    rw [map_sub, this]
    exact sub_self _
  obtain ⟨y, hy⟩ := (hexact _).1 h0
  exact ⟨y, by rw [hy]; abel⟩

theorem zig (hd : ∀ q, d ∘ₗ ρ1 q = ρ0 q ∘ₗ d) (hε : ∀ q, ε ∘ₗ ρ0 q = ε) (hεd : ∀ p, ε (d p) = 0)
    (hinj : Function.Injective d) (hex : ∀ p, ε p = 0 → ∃ p', d p' = p) (s0 : P0) (hs0 : ε s0 = 1)
    (c : Q → P1) (hc : ∀ q, d (c q) = ρ0 q⁻¹ s0 - s0)
    {ι : Type*} (s : Finset ι) (a : ι → ℚ) (q : ι → Q) (u : ι → M ⊗[ℚ] P0) (w : M ⊗[ℚ] P1)
    (hw : LinearMap.lTensor M d w = ∑ i ∈ s, a i • ((ρM.tprod ρ0) (q i) (u i) - u i)) :
    Coinvariants.mk (ρM.tprod ρ1) (∑ i ∈ s, a i • Zc ε (c (q i)) (u i)) = - Coinvariants.mk (ρM.tprod ρ1) w := by
  classical
  have hexact := zig_exact (M := M) hεd hex s0 hs0
  have hDinj : Function.Injective (LinearMap.lTensor M d) :=
    Module.Flat.lTensor_preserves_injective_linearMap d hinj
  have hdec := zig_decomp (M := M) hεd hex s0 hs0
  have hDeq : ∀ (g : Q) (y : M ⊗[ℚ] P1), (ρM.tprod ρ0) g (LinearMap.lTensor M d y) =
      LinearMap.lTensor M d ((ρM.tprod ρ1) g y) := by
    intro g y
    induction y using TensorProduct.inductionOn with
    | tmul m p =>
      simp only [LinearMap.lTensor_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
      exact congrArg (fun z => ρM g m ⊗ₜ[ℚ] z) (LinearMap.congr_fun (hd g) p).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  have hρ0 : ∀ g (p : P0), ρ0 g (ρ0 g⁻¹ p) = p := fun g p => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  choose y hy using hdec
  have key : ∀ (g : Q) (m : M) (yy : M ⊗[ℚ] P1),
      (ρM.tprod ρ0) g (m ⊗ₜ[ℚ] s0 + LinearMap.lTensor M d yy) - (m ⊗ₜ[ℚ] s0 + LinearMap.lTensor M d yy) =
        ((ρM g m - m) ⊗ₜ[ℚ] s0 + ρM g m ⊗ₜ[ℚ] (ρ0 g s0 - s0)) +
          LinearMap.lTensor M d ((ρM.tprod ρ1) g yy - yy) := by
    intro g m yy
    rw [map_add, hDeq, map_sub, Representation.tprod_apply, TensorProduct.map_tmul,
      TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  have hR : ∀ v : M ⊗[ℚ] P0, TensorProduct.rid ℚ M (LinearMap.lTensor M ε v) = zM ε v := fun v => rfl
  have hRD : ∀ v : M ⊗[ℚ] P1, LinearMap.lTensor M ε (LinearMap.lTensor M d v) = 0 := fun v =>
    (hexact _).2 ⟨v, rfl⟩
  have hi : ∀ i, (ρM.tprod ρ0) (q i) (u i) - u i =
      ((ρM (q i) (zM ε (u i)) - zM ε (u i)) ⊗ₜ[ℚ] s0 +
        ρM (q i) (zM ε (u i)) ⊗ₜ[ℚ] (ρ0 (q i) s0 - s0)) +
        LinearMap.lTensor M d ((ρM.tprod ρ1) (q i) (y (u i)) - y (u i)) := by
    intro i
    have := key (q i) (zM ε (u i)) (y (u i))
    rw [← hy (u i)] at this
    exact this
  have hsum : LinearMap.lTensor M d w = ∑ i ∈ s, a i • (((ρM (q i) (zM ε (u i)) - zM ε (u i)) ⊗ₜ[ℚ] s0 +
        ρM (q i) (zM ε (u i)) ⊗ₜ[ℚ] (ρ0 (q i) s0 - s0)) +
        LinearMap.lTensor M d ((ρM.tprod ρ1) (q i) (y (u i)) - y (u i))) := by
    rw [hw]
    exact Finset.sum_congr rfl fun i _ => by rw [hi i]
  let Zl : M ⊗[ℚ] P0 →ₗ[ℚ] M := (TensorProduct.rid ℚ M).toLinearMap ∘ₗ LinearMap.lTensor M ε
  have hZl : ∀ v, zM ε v = Zl v := fun _ => rfl
  have hT : ∑ i ∈ s, a i • (ρM (q i) (zM ε (u i)) - zM ε (u i)) = 0 := by
    have h1 := congrArg Zl hsum
    rw [map_sum] at h1
    have e0 : Zl (LinearMap.lTensor M d w) = 0 := by
      change TensorProduct.rid ℚ M (LinearMap.lTensor M ε (LinearMap.lTensor M d w)) = 0
      rw [hRD, map_zero]
    rw [e0] at h1
    have term : ∀ i, Zl (a i • (((ρM (q i) (zM ε (u i)) - zM ε (u i)) ⊗ₜ[ℚ] s0 +
        ρM (q i) (zM ε (u i)) ⊗ₜ[ℚ] (ρ0 (q i) s0 - s0)) +
        LinearMap.lTensor M d ((ρM.tprod ρ1) (q i) (y (u i)) - y (u i)))) =
        a i • (ρM (q i) (zM ε (u i)) - zM ε (u i)) := by
      intro i
      rw [map_smul, map_add, map_add]
      have eD : Zl (LinearMap.lTensor M d ((ρM.tprod ρ1) (q i) (y (u i)) - y (u i))) = 0 := by
        change TensorProduct.rid ℚ M (LinearMap.lTensor M ε (LinearMap.lTensor M d _)) = 0
        rw [hRD, map_zero]
      have eA : Zl ((ρM (q i) (zM ε (u i)) - zM ε (u i)) ⊗ₜ[ℚ] s0) = ρM (q i) (zM ε (u i)) - zM ε (u i) := by
        rw [← hZl, zM_tmul, hs0, one_smul]
      have eB : Zl (ρM (q i) (zM ε (u i)) ⊗ₜ[ℚ] (ρ0 (q i) s0 - s0)) = 0 := by
        rw [← hZl, zM_tmul, map_sub, show ε (ρ0 (q i) s0) = ε s0 from LinearMap.congr_fun (hε (q i)) s0, sub_self,
          zero_smul]
      rw [eD, eA, eB, add_zero, add_zero]
    rw [Finset.sum_congr rfl fun i _ => term i] at h1
    exact h1.symm
  have hA : ∑ i ∈ s, a i • ((ρM (q i) (zM ε (u i)) - zM ε (u i)) ⊗ₜ[ℚ] s0) = 0 := by
    have : ∑ i ∈ s, a i • ((ρM (q i) (zM ε (u i)) - zM ε (u i)) ⊗ₜ[ℚ] s0) =
        (∑ i ∈ s, a i • (ρM (q i) (zM ε (u i)) - zM ε (u i))) ⊗ₜ[ℚ] s0 := by
      rw [TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul' _ _ _).symm
    rw [this, hT, TensorProduct.zero_tmul]
  have hB : ∀ i, ρM (q i) (zM ε (u i)) ⊗ₜ[ℚ] (ρ0 (q i) s0 - s0) =
      - LinearMap.lTensor M d ((ρM.tprod ρ1) (q i) (Zc ε (c (q i)) (u i))) := by
    intro i
    have h1 : d (ρ1 (q i) (c (q i))) = s0 - ρ0 (q i) s0 := by
      rw [← LinearMap.comp_apply d, hd (q i), LinearMap.comp_apply, hc, map_sub, hρ0]
    rw [Zc_apply, Representation.tprod_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul, h1,
      ← TensorProduct.tmul_neg, neg_sub]
  have hmain : LinearMap.lTensor M d w =
      LinearMap.lTensor M d (- ∑ i ∈ s, a i • (ρM.tprod ρ1) (q i) (Zc ε (c (q i)) (u i)) +
        ∑ i ∈ s, a i • ((ρM.tprod ρ1) (q i) (y (u i)) - y (u i))) := by
    rw [hsum]
    simp only [smul_add, Finset.sum_add_distrib, map_sum, map_smul, map_add, map_neg, hA, zero_add]
    congr 1
    simp only [hB, smul_neg, Finset.sum_neg_distrib]
  have hw' := hDinj hmain
  have hmk := congrArg (Coinvariants.mk (ρM.tprod ρ1)) hw'
  rw [map_add, map_neg, map_sum, map_sum] at hmk
  have e1 : ∀ i, Coinvariants.mk (ρM.tprod ρ1) (a i • (ρM.tprod ρ1) (q i) (Zc ε (c (q i)) (u i))) =
      a i • Coinvariants.mk (ρM.tprod ρ1) (Zc ε (c (q i)) (u i)) := fun i => by
    rw [map_smul, Coinvariants.mk_self_apply]
  have e2 : ∀ i, Coinvariants.mk (ρM.tprod ρ1) (a i • ((ρM.tprod ρ1) (q i) (y (u i)) - y (u i))) = 0 :=
    fun i => by
      rw [map_smul, map_sub, Coinvariants.mk_self_apply, sub_self, smul_zero]
  simp only [e1, e2, Finset.sum_const_zero, add_zero] at hmk
  rw [hmk, map_sum, neg_neg]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _

end Zig

section PiF

theorem piF {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (S : ShortComplex C) [S.HasHomology] [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  have h1 := ShortComplex.LeftHomologyData.mapHomologyIso_eq S.leftHomologyData F
  have h2 := ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom (S.map F) (S.leftHomologyData.map F)
  have h3 := ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom S S.leftHomologyData
  have e : (S.mapHomologyIso F).hom = (S.leftHomologyData.map F).homologyIso.hom ≫
      F.map S.leftHomologyData.homologyIso.inv := congrArg Iso.hom h1
  have hid : S.leftHomologyData.cyclesIso.hom = 𝟙 _ := by
    simp [ShortComplex.LeftHomologyData.cyclesIso]
    rfl
  have h3' : S.homologyπ ≫ S.leftHomologyData.homologyIso.hom = S.leftHomologyData.π :=
    h3.trans (by rw [hid]; exact Category.id_comp _)
  have h4 : S.leftHomologyData.π ≫ S.leftHomologyData.homologyIso.inv = S.homologyπ :=
    (Iso.comp_inv_eq _).2 h3'.symm
  have h5 : (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      ((S.leftHomologyData.map F).cyclesIso.hom ≫ F.map S.leftHomologyData.π) ≫
        F.map S.leftHomologyData.homologyIso.inv := by
    rw [e]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun m => m ≫ F.map S.leftHomologyData.homologyIso.inv) h2)
  refine h5.trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m => (S.leftHomologyData.map F).cyclesIso.hom ≫ m)
    ((F.map_comp S.leftHomologyData.π S.leftHomologyData.homologyIso.inv).symm.trans
      (congrArg F.map h4)))

end PiF

variable {Q : Type} [Group Q]

section PhiCls

variable (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) (X : Rep.{0} ℚ Q) [Projective X]


theorem phiH_cls {N : Rep.{0} ℚ Q} (Θ : N ⟶ Z.X 2) (hΘ : Θ ≫ Z.d 2 1 = 0) (y' : (FX X).obj N)
    (hy : ((CxF Z X).d 2 1).hom (((FX X).map Θ).hom y') = 0) :
    (phiH Z X 2).hom.hom (((CxF Z X).homologyπ 2).hom
        ((CxF Z X).cyclesMk (((FX X).map Θ).hom y') 1 next21 hy)) =
      ((FX X).map (Z.liftCycles Θ 1 next21 hΘ ≫ Z.homologyπ 2)).hom y' := by
  have hpres := FX_preservesHomology X
  have hpi := piF (FX X) (Z.sc 2)
  have hz : (CxF Z X).cyclesMk (((FX X).map Θ).hom y') 1 next21 hy =
      (((Z.sc 2).mapCyclesIso (FX X)).inv).hom (((FX X).map (Z.liftCycles Θ 1 next21 hΘ)).hom y') := by
    have inj : Function.Injective ((CxF Z X).iCycles 2).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    apply inj
    have h1 := ShortComplex.mapCyclesIso_hom_iCycles (S := Z.sc 2) (FX X)
    have h2 : ((Z.sc 2).mapCyclesIso (FX X)).inv ≫ ((Z.sc 2).map (FX X)).iCycles =
        (FX X).map (Z.sc 2).iCycles := (Iso.inv_comp_eq _).2 h1.symm
    have h3 := congrArg (fun t => t.hom (((FX X).map (Z.liftCycles Θ 1 next21 hΘ)).hom y')) h2
    simp only [ModuleCat.hom_comp] at h3
    change ((CxF Z X).iCycles 2).hom ((CxF Z X).cyclesMk (((FX X).map Θ).hom y') 1 next21 hy) =
      ((Z.sc 2).map (FX X)).iCycles.hom ((((Z.sc 2).mapCyclesIso (FX X)).inv).hom
        (((FX X).map (Z.liftCycles Θ 1 next21 hΘ)).hom y'))
    refine Eq.trans ?_ h3.symm
    exact (HomologicalComplex.i_cyclesMk (CxF Z X) _ 1 next21 hy).trans (by
      change _ = ((FX X).map (Z.sc 2).iCycles).hom (((FX X).map (Z.liftCycles Θ 1 next21 hΘ)).hom y')
      have e : (FX X).map Θ = (FX X).map (Z.liftCycles Θ 1 next21 hΘ) ≫ (FX X).map (Z.sc 2).iCycles := by
        exact (congrArg (FX X).map (HomologicalComplex.liftCycles_i Z Θ 1 next21 hΘ).symm).trans
          ((FX X).map_comp _ _)
      exact congrArg (fun t => t.hom y') e)
  rw [hz]
  have h4 := congrArg (fun t => t.hom (((Z.sc 2).mapCyclesIso (FX X)).inv.hom
    (((FX X).map (Z.liftCycles Θ 1 next21 hΘ)).hom y'))) hpi
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h4
  have h5 : (((Z.sc 2).mapCyclesIso (FX X)).hom).hom
      ((((Z.sc 2).mapCyclesIso (FX X)).inv).hom (((FX X).map (Z.liftCycles Θ 1 next21 hΘ)).hom y')) =
      ((FX X).map (Z.liftCycles Θ 1 next21 hΘ)).hom y' := by
    have := congrArg (fun t => t.hom (((FX X).map (Z.liftCycles Θ 1 next21 hΘ)).hom y'))
      (Iso.inv_hom_id ((Z.sc 2).mapCyclesIso (FX X)))
    exact this
  rw [h5] at h4
  refine h4.trans ?_
  rw [(FX X).map_comp]
  rfl

end PhiCls

theorem delta_cls_gen (S : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ)) (hS : S.ShortExact)
    (x₃ : S.X₃.X 3) (hx₃ : (S.X₃.d 3 2).hom x₃ = 0) (x₂ : S.X₂.X 3) (hx₂ : (S.g.f 3).hom x₂ = x₃)
    (x₁ : S.X₁.X 2) (hx₁ : (S.f.f 2).hom x₁ = (S.X₂.d 3 2).hom x₂) (hx₁c : (S.X₁.d 2 1).hom x₁ = 0) :
    (hS.δ 3 2 rfl).hom ((S.X₃.homologyπ 3).hom (S.X₃.cyclesMk x₃ 2 next32 hx₃)) =
      (S.X₁.homologyπ 2).hom (S.X₁.cyclesMk x₁ 1 next21 hx₁c) := by
  let A : ModuleCat.{0} ℚ := ModuleCat.of ℚ ℚ
  let e : ∀ {V : ModuleCat.{0} ℚ} (v : (V : Type)), A ⟶ V := fun {V} v => ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (V : Type) v)
  have h := hS.δ_eq 3 2 rfl (e x₃) (by
      ext; simpa [e] using hx₃) (e x₂) (by ext; simpa [e] using hx₂) (e x₁) (by
      ext; simpa [e] using hx₁) 1 next21
  have h' := congrArg (fun t => t.hom (1 : ℚ)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  have c3 : S.X₃.cyclesMk x₃ 2 next32 hx₃ =
      (S.X₃.liftCycles (e x₃) 2 next32 (by ext; simpa [e] using hx₃)).hom 1 := by
    have inj : Function.Injective (S.X₃.iCycles 3).hom := (ModuleCat.mono_iff_injective _).1 inferInstance
    apply inj
    refine (HomologicalComplex.i_cyclesMk S.X₃ x₃ 2 next32 hx₃).trans ?_
    have hl := HomologicalComplex.liftCycles_i S.X₃ (e x₃) 2 next32 (by ext; simpa [e] using hx₃)
    calc x₃ = (e x₃).hom (1 : ℚ) := (one_smul ℚ x₃).symm
      _ = ((S.X₃.liftCycles (e x₃) 2 next32 (by ext; simpa [e] using hx₃)) ≫ S.X₃.iCycles 3).hom (1 : ℚ) := by
          rw [hl]
      _ = _ := rfl
  have c1 : S.X₁.cyclesMk x₁ 1 next21 hx₁c =
      (S.X₁.liftCycles (e x₁) 1 next21 (by ext; simpa [e] using hx₁c)).hom 1 := by
    have inj : Function.Injective (S.X₁.iCycles 2).hom := (ModuleCat.mono_iff_injective _).1 inferInstance
    apply inj
    refine (HomologicalComplex.i_cyclesMk S.X₁ x₁ 1 next21 hx₁c).trans ?_
    have hl := HomologicalComplex.liftCycles_i S.X₁ (e x₁) 1 next21 (by ext; simpa [e] using hx₁c)
    calc x₁ = (e x₁).hom (1 : ℚ) := (one_smul ℚ x₁).symm
      _ = ((S.X₁.liftCycles (e x₁) 1 next21 (by ext; simpa [e] using hx₁c)) ≫ S.X₁.iCycles 2).hom (1 : ℚ) := by
          rw [hl]
      _ = _ := rfl
  rw [c3, c1]
  exact h'



section Data

variable (P1 P0 : Rep.{0} ℚ Q) (d : P1 ⟶ P0) (ε : P0 ⟶ Rep.trivial ℚ Q ℚ) (hdε : d ≫ ε = 0)
  (hS : (ShortComplex.mk d ε hdε).ShortExact)

include hS in
theorem d_inj : Function.Injective d.hom := (Rep.mono_iff_injective d).1 hS.mono_f

include hS in
theorem ε_surj : Function.Surjective ε.hom := (Rep.epi_iff_surjective ε).1 hS.epi_g

include hS in
theorem ε_ker (p : P0) (hp : ε.hom p = 0) : ∃ p' : P1, d.hom p' = p := by
  have hex : LinearMap.range d.hom.toLinearMap = LinearMap.ker ε.hom.toLinearMap :=
    (hS.exact.map (forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ))).moduleCat_range_eq_ker
  have : p ∈ LinearMap.range d.hom.toLinearMap := by
    rw [hex]; exact hp
  obtain ⟨p', hp'⟩ := this
  exact ⟨p', hp'⟩

include hdε in
theorem ε_d (p : P1) : ε.hom (d.hom p) = 0 := by
  have := congrArg (fun t => t.hom p) hdε
  simpa using this

theorem ε_inv (g : Q) (p : P0) : ε.hom (P0.ρ g p) = ε.hom p := by
  have := Rep.hom_comm_apply ε g p
  exact this

theorem d_eq (g : Q) (p : P1) : d.hom (P1.ρ g p) = P0.ρ g (d.hom p) := Rep.hom_comm_apply d g p

end Data

section Psi

variable (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) (P1 P0 : Rep.{0} ℚ Q) (d : P1 ⟶ P0)
  (ε : P0 ⟶ Rep.trivial ℚ Q ℚ) (hdε : d ≫ ε = 0) (M : Rep.{0} ℚ Q)
  (hS : (ShortComplex.mk d ε hdε).ShortExact)
  (Θ3 : M ⊗ P1 ⟶ Z.X 3) (Θ2 : M ⊗ P0 ⟶ Z.X 2)
  (hθ : Θ3 ≫ Z.d 3 2 = (M ◁ d) ≫ Θ2) (hcyc : Θ2 ≫ Z.d 2 1 = 0)

/-- `Θ2` as a map to the homology. -/
def PsiRaw : M ⊗ P0 ⟶ Z.homology 2 :=
  Z.liftCycles Θ2 1 next21 hcyc ≫ Z.homologyπ 2

include hθ in
theorem comp_PsiRaw : (M ◁ d) ≫ PsiRaw Z P0 M Θ2 hcyc = 0 := by
  have h : (M ◁ d) ≫ Z.liftCycles Θ2 1 next21 hcyc = Θ3 ≫ Z.toCycles 3 2 := by
    rw [← cancel_mono (Z.iCycles 2)]
    simp [hθ]
  rw [PsiRaw, ← Category.assoc, h, Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero]

theorem PsiRaw_whisker (y : M ⊗[ℚ] P1) (h : (M ◁ d) ≫ PsiRaw Z P0 M Θ2 hcyc = 0) :
    (PsiRaw Z P0 M Θ2 hcyc).hom ((M ◁ d).hom y) = 0 := by
  have := congrArg (fun t => t.hom y) h
  simpa using this

/-- A chosen preimage of `1` under `ε`. -/
def sZero : P0 := (ε_surj P1 P0 d ε hdε hS (1 : ℚ)).choose

theorem sZero_spec : ε.hom (sZero P1 P0 d ε hdε hS) = 1 :=
  (ε_surj P1 P0 d ε hdε hS (1 : ℚ)).choose_spec

include hS hθ in
/-- **The map `Ψ' : M ⟶ H₂ Z`**, `Ψ'(m) = [Θ2(m ⊗ s0)]` for `ε s0 = 1`. -/
def PsiPrime : M ⟶ Z.homology 2 :=
  Rep.ofHom ⟨(PsiRaw Z P0 M Θ2 hcyc).hom.toLinearMap ∘ₗ (TensorProduct.mk ℚ M P0).flip (sZero P1 P0 d ε hdε hS),
    fun g => by
      refine LinearMap.ext fun m => ?_
      change (PsiRaw Z P0 M Θ2 hcyc).hom (M.ρ g m ⊗ₜ[ℚ] sZero P1 P0 d ε hdε hS) =
        (Z.homology 2).ρ g ((PsiRaw Z P0 M Θ2 hcyc).hom (m ⊗ₜ[ℚ] sZero P1 P0 d ε hdε hS))
      rw [← Rep.hom_comm_apply (PsiRaw Z P0 M Θ2 hcyc) g (m ⊗ₜ[ℚ] sZero P1 P0 d ε hdε hS)]
      have hs := sZero_spec P1 P0 d ε hdε hS
      obtain ⟨p', hp'⟩ := ε_ker P1 P0 d ε hdε hS (P0.ρ g (sZero P1 P0 d ε hdε hS) - sZero P1 P0 d ε hdε hS) (by
        rw [map_sub, ε_inv, hs]; exact sub_self _)
      have hz := PsiRaw_whisker Z P1 P0 d M Θ2 hcyc (M.ρ g m ⊗ₜ[ℚ] p')
        (comp_PsiRaw Z P1 P0 d M Θ3 Θ2 hθ hcyc)
      have e : (M ◁ d).hom (M.ρ g m ⊗ₜ[ℚ] p') =
          M.ρ g m ⊗ₜ[ℚ] (P0.ρ g (sZero P1 P0 d ε hdε hS)) - M.ρ g m ⊗ₜ[ℚ] sZero P1 P0 d ε hdε hS := by
        change M.ρ g m ⊗ₜ[ℚ] d.hom p' = _
        rw [hp', TensorProduct.tmul_sub]
      rw [e, map_sub, sub_eq_zero] at hz
      exact hz.symm⟩

include hS hθ in
theorem PsiPrime_spec (u : M ⊗[ℚ] P0) :
    (PsiPrime Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc).hom (zM ε.hom.toLinearMap u) =
      (PsiRaw Z P0 M Θ2 hcyc).hom u := by
  obtain ⟨y, hy⟩ := zig_decomp (M := M) (d := d.hom.toLinearMap) (ε := ε.hom.toLinearMap)
    (ε_d P1 P0 d ε hdε) (ε_ker P1 P0 d ε hdε hS) (sZero P1 P0 d ε hdε hS) (sZero_spec P1 P0 d ε hdε hS) u
  have hz := PsiRaw_whisker Z P1 P0 d M Θ2 hcyc y (comp_PsiRaw Z P1 P0 d M Θ3 Θ2 hθ hcyc)
  conv_rhs => rw [hy]
  rw [map_add]
  have : (PsiRaw Z P0 M Θ2 hcyc).hom ((LinearMap.lTensor M d.hom.toLinearMap) y) = 0 := hz
  rw [this, add_zero]
  rfl

include hS hθ in
theorem PsiPrime_unique (Ψ : M ⟶ Z.homology 2)
    (h : ∀ u : M ⊗[ℚ] P0, Ψ.hom (zM ε.hom.toLinearMap u) = (PsiRaw Z P0 M Θ2 hcyc).hom u) :
    Ψ = PsiPrime Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun m => ?_))
  have hs := sZero_spec P1 P0 d ε hdε hS
  have h1 : zM ε.hom.toLinearMap (m ⊗ₜ[ℚ] sZero P1 P0 d ε hdε hS) = m := by
    rw [zM_tmul]
    change ε.hom (sZero P1 P0 d ε hdε hS) • m = m
    rw [hs, one_smul]
  have := h (m ⊗ₜ[ℚ] sZero P1 P0 d ε hdε hS)
  rw [h1] at this
  exact this

end Psi

section Lam

variable (M : Rep.{0} ℚ Q) (Z : ChainComplex (Rep.{0} ℚ Q) ℕ)

/-- `(M ⊗ P)_Q → (Z_n ⊗ 1)_Q` induced by `Θ : M ⊗ P ⟶ Z_n` and the unitor. -/
def Lam (P : Rep.{0} ℚ Q) {n : ℕ} (Θ : M ⊗ P ⟶ Z.X n) :
    (FX P).obj M ⟶ (FX (Rep.trivial ℚ Q ℚ)).obj (Z.X n) :=
  (Rep.coinvariantsFunctor ℚ Q).map Θ ≫ (Rep.coinvariantsFunctor ℚ Q).map (ρ_ (Z.X n)).inv

theorem Lam_mk (P : Rep.{0} ℚ Q) {n : ℕ} (Θ : M ⊗ P ⟶ Z.X n) (w : M ⊗[ℚ] P) :
    (Lam M Z P Θ).hom (Coinvariants.mk (M.ρ.tprod P.ρ) w) =
      Coinvariants.mk ((Z.X n).ρ.tprod (Rep.trivial ℚ Q ℚ).ρ) (Θ.hom w ⊗ₜ[ℚ] (1 : ℚ)) := rfl

theorem CxF_d_mk (X : Rep.{0} ℚ Q) {i j : ℕ} (z : Z.X i ⊗[ℚ] X) :
    ((CxF Z X).d i j).hom (Coinvariants.mk ((Z.X i).ρ.tprod X.ρ) z) =
      Coinvariants.mk ((Z.X j).ρ.tprod X.ρ) ((Z.d i j ▷ X).hom z) := rfl

theorem FXmap_mk_gen {X Y N : Rep.{0} ℚ Q} (φ : X ⟶ Y) (w : N ⊗[ℚ] X) :
    ((FXmap φ).app N).hom (Coinvariants.mk (N.ρ.tprod X.ρ) w) =
      Coinvariants.mk (N.ρ.tprod Y.ρ) ((N ◁ φ).hom w) := rfl

theorem Lam_d_apply (P1 P0 : Rep.{0} ℚ Q) (d : P1 ⟶ P0) (Θ3 : M ⊗ P1 ⟶ Z.X 3) (Θ2 : M ⊗ P0 ⟶ Z.X 2)
    (hθ : Θ3 ≫ Z.d 3 2 = (M ◁ d) ≫ Θ2) (x : (FX P1).obj M) :
    ((CxF Z (Rep.trivial ℚ Q ℚ)).d 3 2).hom ((Lam M Z P1 Θ3).hom x) =
      (Lam M Z P0 Θ2).hom (((FXmap d).app M).hom x) := by
  obtain ⟨w, rfl⟩ := Coinvariants.mk_surjective (M.ρ.tprod P1.ρ) x
  rw [Lam_mk, FXmap_mk_gen, Lam_mk, CxF_d_mk]
  have := congrArg (fun t => t.hom w) hθ
  have e1 : (Z.d 3 2 ▷ Rep.trivial ℚ Q ℚ).hom (Θ3.hom w ⊗ₜ[ℚ] (1 : ℚ)) = (Θ3 ≫ Z.d 3 2).hom w ⊗ₜ[ℚ] (1 : ℚ) := rfl
  rw [e1, hθ]
  rfl

end Lam

section Main

variable (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) (P1 P0 : Rep.{0} ℚ Q) (d : P1 ⟶ P0)
  (ε : P0 ⟶ Rep.trivial ℚ Q ℚ) (hdε : d ≫ ε = 0) (M : Rep.{0} ℚ Q)
  (hS : (ShortComplex.mk d ε hdε).ShortExact)
  (Θ3 : M ⊗ P1 ⟶ Z.X 3) (Θ2 : M ⊗ P0 ⟶ Z.X 2)
  (hθ : Θ3 ≫ Z.d 3 2 = (M ◁ d) ≫ Θ2) (hcyc : Θ2 ≫ Z.d 2 1 = 0)

/-- The kernel `K_M` of `(M ⊗ P1)_Q → (M ⊗ P0)_Q`. -/
abbrev KM : Submodule ℚ ((FX P1).obj M) := LinearMap.ker ((FXmap d).app M).hom

include hθ in
theorem Lam_cycle (x : KM P1 P0 d M) :
    ((CxF Z (Rep.trivial ℚ Q ℚ)).d 3 2).hom ((Lam M Z P1 Θ3).hom x.1) = 0 := by
  rw [Lam_d_apply M Z P1 P0 d Θ3 Θ2 hθ, x.2, map_zero]

include hθ in
/-- **`Λ : K_M → H₃((Z ⊗ 1)_Q)`**. -/
def LamH : KM P1 P0 d M →ₗ[ℚ] (CxF Z (Rep.trivial ℚ Q ℚ)).homology 3 :=
  ((CxF Z (Rep.trivial ℚ Q ℚ)).liftCycles
    (ModuleCat.ofHom ((Lam M Z P1 Θ3).hom ∘ₗ (KM P1 P0 d M).subtype)) 2 next32
    (by refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_); exact Lam_cycle Z P1 P0 d M Θ3 Θ2 hθ x) ≫
      (CxF Z (Rep.trivial ℚ Q ℚ)).homologyπ 3).hom

include hθ in
theorem LamH_apply (x : KM P1 P0 d M) :
    LamH Z P1 P0 d M Θ3 Θ2 hθ x = ((CxF Z (Rep.trivial ℚ Q ℚ)).homologyπ 3).hom
      ((CxF Z (Rep.trivial ℚ Q ℚ)).cyclesMk ((Lam M Z P1 Θ3).hom x.1) 2 next32
        (Lam_cycle Z P1 P0 d M Θ3 Θ2 hθ x)) := by
  have inj : Function.Injective ((CxF Z (Rep.trivial ℚ Q ℚ)).iCycles 3).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hl : (CxF Z (Rep.trivial ℚ Q ℚ)).cyclesMk ((Lam M Z P1 Θ3).hom x.1) 2 next32
        (Lam_cycle Z P1 P0 d M Θ3 Θ2 hθ x) =
      ((CxF Z (Rep.trivial ℚ Q ℚ)).liftCycles
        (ModuleCat.ofHom ((Lam M Z P1 Θ3).hom ∘ₗ (KM P1 P0 d M).subtype)) 2 next32
        (by refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_); exact Lam_cycle Z P1 P0 d M Θ3 Θ2 hθ x)).hom x := by
    apply inj
    refine (HomologicalComplex.i_cyclesMk (CxF Z (Rep.trivial ℚ Q ℚ)) ((Lam M Z P1 Θ3).hom x.1) 2 next32
      (Lam_cycle Z P1 P0 d M Θ3 Θ2 hθ x)).trans ?_
    have := congrArg (fun t => t.hom x) (HomologicalComplex.liftCycles_i (CxF Z (Rep.trivial ℚ Q ℚ))
      (ModuleCat.ofHom ((Lam M Z P1 Θ3).hom ∘ₗ (KM P1 P0 d M).subtype)) 2 next32
        (by refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_); exact Lam_cycle Z P1 P0 d M Θ3 Θ2 hθ x))
    exact this.symm
  rw [hl]
  rfl

/-- The Rep-map `M ⊗ P0 → M`, `(id ⊗ ε)` composed with the unitor. -/
def ERep : M ⊗ P0 ⟶ M := (M ◁ ε) ≫ (ρ_ M).hom

theorem ERep_hom (u : M ⊗[ℚ] P0) : (ERep P0 ε M).hom u = zM ε.hom.toLinearMap u := rfl

include hS hθ in
theorem PsiRaw_eq : PsiRaw Z P0 M Θ2 hcyc =
    ERep P0 ε M ≫ PsiPrime Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun u => ?_))
  exact (PsiPrime_spec Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc u).symm

section Tree

variable [Projective P1] [Projective P0] (hZ : ∀ j, Projective (Z.X j)) (hZ3 : IsZero (Z.homology 3))

include hS hθ hcyc hZ hZ3 in
/-- **The tree theorem**: the Hochschild-Serre step on the image of a tree map. -/
theorem thmAEquiv_LamH (x : KM P1 P0 d M) :
    ((thmAEquiv Z P1 P0 d ε hdε hZ hS hZ3 (LamH Z P1 P0 d M Θ3 Θ2 hθ x) :
        LinearMap.ker ((FXmap d).app (Z.homology 2)).hom) : (FX P1).obj (Z.homology 2)) =
      - ((FX P1).map (PsiPrime Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc)).hom x.1 := by
  obtain ⟨w, hw⟩ := Coinvariants.mk_surjective (M.ρ.tprod P1.ρ) x.1
  have hDw : ((M ◁ d).hom w) ∈ Coinvariants.ker (M.ρ.tprod P0.ρ) := by
    rw [← Coinvariants.mk_eq_zero]
    have h0 : ((FXmap d).app M).hom (Coinvariants.mk (M.ρ.tprod P1.ρ) w) = 0 := by
      rw [hw]; exact x.2
    rw [FXmap_mk_gen] at h0
    exact h0
  obtain ⟨ℓ, hℓ⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hDw
  obtain ⟨s0, hs⟩ : ∃ s0 : P0, ε.hom s0 = 1 := ⟨_, sZero_spec P1 P0 d ε hdε hS⟩
  have hex : ∀ g : Q, ε.hom (P0.ρ g⁻¹ s0 - s0) = 0 := fun g => by
    rw [map_sub, ε_inv, hs]; exact sub_self _
  choose c hc using fun g : Q => ε_ker P1 P0 d ε hdε hS (P0.ρ g⁻¹ s0 - s0) (hex g)
  have hw' : LinearMap.lTensor M d.hom.toLinearMap w =
      ∑ p ∈ ℓ.support, ℓ p • ((M.ρ.tprod P0.ρ) p.1 p.2 - p.2) := by
    exact hℓ.symm
  have hzig := zig (ρM := M.ρ) (ρ0 := P0.ρ) (ρ1 := P1.ρ) (d := d.hom.toLinearMap) (ε := ε.hom.toLinearMap)
    (fun q => LinearMap.ext fun p => d_eq P1 P0 d q p) (fun q => LinearMap.ext fun p => ε_inv P0 ε q p)
    (ε_d P1 P0 d ε hdε) (d_inj P1 P0 d ε hdε hS) (ε_ker P1 P0 d ε hdε hS) s0 hs c hc
    ℓ.support (fun p => ℓ p) (fun p => p.1) (fun p => p.2) w hw'
  -- the elements of the zig-zag
  let y' : (FX P1).obj (M ⊗ P0) := ∑ p ∈ ℓ.support,
    ℓ p • Coinvariants.mk ((M ⊗ P0).ρ.tprod P1.ρ) (p.2 ⊗ₜ[ℚ] c p.1)
  have hx₃ := Lam_cycle Z P1 P0 d M Θ3 Θ2 hθ x
  have hLam : (Lam M Z P1 Θ3).hom x.1 =
      Coinvariants.mk ((Z.X 3).ρ.tprod (Rep.trivial ℚ Q ℚ).ρ) (Θ3.hom w ⊗ₜ[ℚ] (1 : ℚ)) := by
    rw [← hw]; rfl
  let x₂ : (CxF Z P0).X 3 := Coinvariants.mk ((Z.X 3).ρ.tprod P0.ρ) (Θ3.hom w ⊗ₜ[ℚ] s0)
  have hx₂ : ((CxMap Z ε).f 3).hom x₂ = (Lam M Z P1 Θ3).hom x.1 := by
    rw [hLam]
    exact (FXmap_mk ε (Θ3.hom w) s0).trans
      (congrArg (fun r => Coinvariants.mk ((Z.X 3).ρ.tprod (Rep.trivial ℚ Q ℚ).ρ) (Θ3.hom w ⊗ₜ[ℚ] r)) hs)
  let x₁ : (CxF Z P1).X 2 := ((FX P1).map Θ2).hom y'
  have hx₁c : ((CxF Z P1).d 2 1).hom x₁ = 0 := by
    change ((FX P1).map (Z.d 2 1)).hom (((FX P1).map Θ2).hom y') = 0
    have : (FX P1).map Θ2 ≫ (FX P1).map (Z.d 2 1) = 0 := by
      rw [← Functor.map_comp, hcyc, Functor.map_zero]
    have h := congrArg (fun t => t.hom y') this
    exact h
  have hterm : ∀ (g : Q) (u : M ⊗[ℚ] P0),
      Coinvariants.mk ((Z.X 2).ρ.tprod P0.ρ) (Θ2.hom ((M.ρ.tprod P0.ρ) g u - u) ⊗ₜ[ℚ] s0) =
        Coinvariants.mk ((Z.X 2).ρ.tprod P0.ρ) (Θ2.hom u ⊗ₜ[ℚ] (d.hom (c g))) := by
    intro g u
    have h1 : Θ2.hom ((M.ρ.tprod P0.ρ) g u) = (Z.X 2).ρ g (Θ2.hom u) := Rep.hom_comm_apply Θ2 g u
    rw [map_sub, h1, TensorProduct.sub_tmul, map_sub, hc g, TensorProduct.tmul_sub, map_sub,
      Coinvariants.mk_tmul_inv]
  have hx₁ : ((CxMap Z d).f 2).hom x₁ = ((CxF Z P0).d 3 2).hom x₂ := by
    have e1 : (Z.d 3 2 ▷ P0).hom (Θ3.hom w ⊗ₜ[ℚ] s0) = (Z.d 3 2).hom (Θ3.hom w) ⊗ₜ[ℚ] s0 := rfl
    have e2 : (Z.d 3 2).hom (Θ3.hom w) = Θ2.hom ((M ◁ d).hom w) := congrArg (fun t => t.hom w) hθ
    have e3 : ((CxF Z P0).d 3 2).hom x₂ = Coinvariants.mk ((Z.X 2).ρ.tprod P0.ρ)
        (Θ2.hom (∑ p ∈ ℓ.support, ℓ p • ((M.ρ.tprod P0.ρ) p.1 p.2 - p.2)) ⊗ₜ[ℚ] s0) := by
      refine (CxF_d_mk Z P0 (Θ3.hom w ⊗ₜ[ℚ] s0)).trans ?_
      rw [e1, e2]
      exact congrArg (fun v => Coinvariants.mk ((Z.X 2).ρ.tprod P0.ρ) (Θ2.hom v ⊗ₜ[ℚ] s0)) hℓ.symm
    rw [e3]
    change ((FXmap d).app (Z.X 2)).hom (((FX P1).map Θ2).hom y') = _
    simp only [y', map_sum, map_smul, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [FX_map_mk, FXmap_mk, ← hterm p.1 p.2, ← TensorProduct.smul_tmul', map_smul]
  have hG := sesC_shortExact Z P1 P0 d ε hdε hZ hS
  have hδ := delta_cls_gen (sesC Z P1 P0 d ε hdε) hG ((Lam M Z P1 Θ3).hom x.1) hx₃ x₂ hx₂ x₁ hx₁ hx₁c
  rw [thmAEquiv_val, LamH_apply Z P1 P0 d M Θ3 Θ2 hθ x]
  refine (congrArg (phiH Z P1 2).hom.hom hδ).trans ?_
  refine (phiH_cls Z P1 Θ2 hcyc y' hx₁c).trans ?_
  have hE : ((FX P1).map (ERep P0 ε M)).hom y' = Coinvariants.mk (M.ρ.tprod P1.ρ)
      (∑ i ∈ ℓ.support, ℓ i • Zc ε.hom.toLinearMap (c i.1) i.2) := by
    simp only [y', map_sum, map_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [FX_map_mk]
    rfl
  have hPsi : (FX P1).map (Z.liftCycles Θ2 1 next21 hcyc ≫ Z.homologyπ 2) =
      (FX P1).map (ERep P0 ε M) ≫ (FX P1).map (PsiPrime Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc) := by
    rw [← Functor.map_comp]
    exact congrArg (FX P1).map (PsiRaw_eq Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc)
  rw [hPsi]
  change ((FX P1).map (PsiPrime Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc)).hom
    (((FX P1).map (ERep P0 ε M)).hom y') = _
  rw [hE, hzig, map_neg, hw]

include hS hθ hcyc hZ hZ3 in
theorem thmAEquiv_LamH_ker [IsIso (PsiPrime Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc)] (x : KM P1 P0 d M) :
    thmAEquiv Z P1 P0 d ε hdε hZ hS hZ3 (LamH Z P1 P0 d M Θ3 Θ2 hθ x) =
      - (kerNatEquiv (FXmap d) (asIso (PsiPrime Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc)) x) := by
  refine Subtype.ext ?_
  rw [Submodule.coe_neg]
  exact thmAEquiv_LamH Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc hZ hZ3 x

include hS hθ hcyc hZ hZ3 in
/-- **Corollary.** If `Ψ'` is an isomorphism then `Λ : K_M → H₃((Z ⊗ 1)_Q)` is bijective. -/
theorem LamH_bijective [IsIso (PsiPrime Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc)] :
    Function.Bijective (LamH Z P1 P0 d M Θ3 Θ2 hθ) := by
  let e := thmAEquiv Z P1 P0 d ε hdε hZ hS hZ3
  let k := kerNatEquiv (FXmap d) (asIso (PsiPrime Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc))
  have key := thmAEquiv_LamH_ker Z P1 P0 d ε hdε M hS Θ3 Θ2 hθ hcyc hZ hZ3
  have hbij : Function.Bijective (fun x : KM P1 P0 d M => e (LamH Z P1 P0 d M Θ3 Θ2 hθ x)) := by
    have : (fun x : KM P1 P0 d M => e (LamH Z P1 P0 d M Θ3 Θ2 hθ x)) = fun x => - (k x) := funext key
    rw [this]
    exact (neg_involutive.bijective).comp k.bijective
  refine ⟨fun x y hxy => hbij.1 (by simp only [hxy]), fun y => ?_⟩
  obtain ⟨x, hx⟩ := hbij.2 (e y)
  exact ⟨x, e.injective hx⟩

end Tree

end Main

end TernaryPeriodPolynomials.Argument.HochschildSerre
