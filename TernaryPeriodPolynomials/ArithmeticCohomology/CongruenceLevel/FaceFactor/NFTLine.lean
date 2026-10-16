module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Conj
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Dictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Rel
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.PairingLifts
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CupProduct

@[expose] public section


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

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section CochainBridge

open groupCohomology

variable {G : Type} [Group G] (A : Rep.{0} ℚ G)

theorem dTwo_general_apply (f : (Fin 2 → G) → A) (g : Fin 3 → G) :
    (inhomogeneousCochains.d A 2).hom f g =
      A.ρ (g 0) (f ![g 1, g 2]) - f ![g 0 * g 1, g 2] + f ![g 0, g 1 * g 2] - f ![g 0, g 1] := by
  have h0 : Fin.contractNth 0 (fun x1 x2 : G => x1 * x2) g = ![g 0 * g 1, g 2] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h1 : Fin.contractNth 1 (fun x1 x2 : G => x1 * x2) g = ![g 0, g 1 * g 2] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h2 : Fin.contractNth 2 (fun x1 x2 : G => x1 * x2) g = ![g 0, g 1] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h3 : (fun i : Fin 2 => g i.succ) = ![g 1, g 2] := by
    ext i; fin_cases i <;> simp
  simp [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_three, h0, h1, h2, h3]
  norm_num
  abel

/-- A degree-two inhomogeneous cocycle is a `cocycles₂` element with the same class. -/
theorem pi_cocyclesMk_eq_H2π (f : (Fin 2 → G) → A) (hf : (inhomogeneousCochains.d A 2).hom f = 0) :
    ∃ hx : (fun p : G × G => f ![p.1, p.2]) ∈ cocycles₂ A,
      (π A 2).hom (cocyclesMk f hf) = (H2π A).hom ⟨_, hx⟩ := by
  have hx : (fun p : G × G => f ![p.1, p.2]) ∈ cocycles₂ A := by
    rw [mem_cocycles₂_iff]
    intro g h j
    have z : (inhomogeneousCochains.d A 2).hom f ![g, h, j] = 0 := congrFun hf _
    rw [dTwo_general_apply] at z
    change A.ρ g (f ![h, j]) - f ![g * h, j] + f ![g, h * j] - f ![g, h] = 0 at z
    change f ![g * h, j] + f ![g, h] = A.ρ g (f ![h, j]) + f ![g, h * j]
    linear_combination (norm := module) -z
  refine ⟨hx, ?_⟩
  let x : cocycles₂ A := ⟨_, hx⟩
  have hfun : f = (cochainsIso₂ A).inv x.1 := by
    funext g
    have hg : g = ![g 0, g 1] := by
      funext i; fin_cases i <;> rfl
    change f g = f ![g 0, g 1]
    rw [← hg]
  have hd : (inhomogeneousCochains.d A 2).hom ((cochainsIso₂ A).inv x.1) = 0 := by rw [← hfun]; exact hf
  have e := cocyclesMk₂_eq A x
  have e2 : cocyclesMk f hf = cocyclesMk ((cochainsIso₂ A).inv x.1) hd := cocyclesMk_congr hfun hf hd
  rw [e2]
  have e3 : cocyclesMk ((cochainsIso₂ A).inv x.1) hd = (isoCocycles₂ A).inv x := e
  rw [e3]
  rfl

end CochainBridge

section Cobound

open groupCohomology

theorem coboundary_of_H2π_eq {G : Type} [Group G] (A : Rep.{0} ℚ G) (x y : cocycles₂ A)
    (h : (H2π A).hom x = (H2π A).hom y) :
    ∃ κ : G → A, ∀ g h : G, x.1 (g, h) = y.1 (g, h) + (A.ρ g (κ h) - κ (g * h) + κ g) := by
  rw [H2π_eq_iff] at h
  obtain ⟨κ, hκ⟩ := h
  refine ⟨κ, fun g h' => ?_⟩
  have := congrFun hκ (g, h')
  rw [d₁₂_hom_apply] at this
  have h2 : x.1 (g, h') - y.1 (g, h') = A.ρ g (κ h') - κ (g * h') + κ g := this.symm
  rw [← h2]
  abel

end Cobound

section Generic

variable {Z : Type} [MulAction Γ6 Z] {F : Type} (o : F → labelOrbits Γ6 Z) (b : F → Z)
  (hb : ∀ i, b i ∈ labelOrbit Γ6 Z (o i))
  (Grp : F → Type) [∀ i, Group (Grp i)] (emb : ∀ i, Grp i →* Γ6) (hinj : ∀ i, Function.Injective (emb i))
  (hrange : ∀ i, (emb i).range = MulAction.stabilizer Γ6 (b i))

/-- The face group as a subgroup of the stabilizer of `b i`. -/
def faceSigma (i : F) : Grp i →* MulAction.stabilizer Γ6 (b i) :=
  (emb i).codRestrict (MulAction.stabilizer Γ6 (b i)) (fun a => by rw [← hrange i]; exact ⟨a, rfl⟩)

theorem faceSigma_val (i : F) (a : Grp i) : ((faceSigma b Grp emb hrange i a : MulAction.stabilizer Γ6 (b i)) : Γ6) = emb i a := rfl

section Rational

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] (ρ : Representation ℂ Γ6 V)

/-- The identity comparison `Res_σ Res_{Stab b} (qRepG ρ) ⟶ qRepG (ρ ∘ emb)`. -/
def faceQId (i : F) :
    Rep.res (faceSigma b Grp emb hrange i) (Rep.res (MulAction.stabilizer Γ6 (b i)).subtype (qRepG ρ)) ⟶
      qRepG (ρ.comp (emb i)) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

theorem coord_at_b (i : F) (c : (homCochains (prodComplex Γ6 RationalGL3 Z) (qRepG ρ)).homology 2)
    (y : groupCohomology.H2 (Rep.res (emb i) (Rep.of ρ)))
    (hc : (faceCoord (MulAction.stabilizer Γ6 (o i).out) (qRepG ρ) (1 : RationalGL3) (o i).out (fun g => g.2) 2).hom c =
      faceTauQ o b hb Grp emb hinj hrange ρ i y) :
    (groupCohomology.map (faceSigma b Grp emb hrange i) (faceQId b Grp emb hrange ρ i) 2).hom
      ((faceCoord (MulAction.stabilizer Γ6 (b i)) (qRepG ρ) (1 : RationalGL3) (b i) (fun g => g.2) 2).hom c) =
      qH2 (ρ.comp (emb i)) y := by
  have hR : b i = faceG o b hb i • (o i).out := (faceG_smul o b hb i).symm
  have hS : ∀ s : MulAction.stabilizer Γ6 (b i), (s : Γ6) • (faceG o b hb i • (o i).out) = faceG o b hb i • (o i).out :=
    fun s => by rw [faceG_smul o b hb i]; exact s.2
  have hf := conjStabHom_apply (faceG o b hb i) (o i).out (MulAction.stabilizer Γ6 (b i)) hS
  have e := faceCoord_conj_gen vertexAction_free' (MulAction.stabilizer Γ6 (b i)) (qRepG ρ) (1 : RationalGL3) (b i)
    (fun g => g.2) (faceG o b hb i) (o i).out hR
    (conjStabHom (faceG o b hb i) (o i).out (MulAction.stabilizer Γ6 (b i)) hS) hf 2
  have e2 : (faceCoord (MulAction.stabilizer Γ6 (b i)) (qRepG ρ) (1 : RationalGL3) (b i) (fun g => g.2) 2).hom c =
      (groupCohomology.map (conjStabHom (faceG o b hb i) (o i).out (MulAction.stabilizer Γ6 (b i)) hS)
        (conjComparison (qRepG ρ) (faceG o b hb i) (MulAction.stabilizer Γ6 (o i).out) (MulAction.stabilizer Γ6 (b i))
          (conjStabHom (faceG o b hb i) (o i).out (MulAction.stabilizer Γ6 (b i)) hS) hf) 2).hom
        ((faceCoord (MulAction.stabilizer Γ6 (o i).out) (qRepG ρ) (1 : RationalGL3) (o i).out (fun g => g.2) 2).hom c) :=
    congrArg (fun φ => φ.hom c) e
  rw [e2, hc]
  induction y using groupCohomology.H2_induction_on with
  | h z =>
    have t1 : faceTauQ o b hb Grp emb hinj hrange ρ i (groupCohomology.H2π (Rep.res (emb i) (Rep.of ρ)) z) =
        qH2 (ρ.comp (MulAction.stabilizer Γ6 (o i).out).subtype) (EdgeNat.h2Map (faceAlpha o b hb Grp emb hinj hrange i)
          (Rep.res (emb i) (Rep.of ρ)) (Rep.res (MulAction.stabilizer Γ6 (o i).out).subtype (Rep.of ρ)) (ρ (faceG o b hb i)⁻¹)
          (faceTau_hT o b hb Grp emb hinj hrange ρ i) (groupCohomology.H2π _ z)) := rfl
    rw [t1, EdgeNat.h2Map_π, qH2_π, qH2_π]
    erw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply]
    congr 1
    apply Subtype.ext
    funext x
    obtain ⟨a, c⟩ := x
    have hα : ∀ a : Grp i, faceAlpha o b hb Grp emb hinj hrange i
        (conjStabHom (faceG o b hb i) (o i).out (MulAction.stabilizer Γ6 (b i)) hS (faceSigma b Grp emb hrange i a)) = a := by
      intro a
      apply hinj i
      rw [emb_faceAlpha, conjStabHom_apply, faceSigma_val]
      group
    change ρ (faceG o b hb i) (ρ (faceG o b hb i)⁻¹ (z.1 (faceAlpha o b hb Grp emb hinj hrange i
        (conjStabHom (faceG o b hb i) (o i).out (MulAction.stabilizer Γ6 (b i)) hS (faceSigma b Grp emb hrange i a)),
      faceAlpha o b hb Grp emb hinj hrange i
        (conjStabHom (faceG o b hb i) (o i).out (MulAction.stabilizer Γ6 (b i)) hS (faceSigma b Grp emb hrange i c))))) = z.1 (a, c)
    rw [hα a, hα c, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

end Rational

end Generic



section Line

open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ₀ : Representation ℂ (gammaN 6) V) (ρ₆ : Representation ℂ Γ6 V)
  (hρ : ∀ (s : gammaN 6) (v : V), ρ₆ (gammaSixEquiv s) v = ρ₀ s v)

/-- The identity comparison `H²(K, E) → H²(K, ρ₆)` for a representation `ρ₆` of `Γ(6)` agreeing with `ρ₀` under `gammaSixEquiv`. -/
def cmpGen {K : Type} [Group K] (ι : K →* gammaN 6) :
    groupCohomology.H2 (Rep.res ι (Rep.of ρ₀)) →ₗ[ℂ]
      groupCohomology.H2 (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of ρ₆)) :=
  EdgeNat.h2Map (MonoidHom.id K) (Rep.res ι (Rep.of ρ₀))
    (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of ρ₆)) LinearMap.id
    (fun s v => (hρ (ι s) v).symm)

/-- The cochain `(a, c) ↦ z̄_d(σ a, σ c)` of the face group `Q = Γ(6) ∩ h⁻¹Qh` from the bar cochain of `d.z` at the line `b = lineOf h`. -/
def lineZbar (i : LineFaces 6) (d : LineDatum (qRep (MonoidHom.id Γ6) ρ₆)) (a c : ↥(gammaNQAt 6 i.rep)) : V :=
  barCochain (MulAction.stabilizer Γ6 (lineOf i.rep)) (1 : RationalGL3) (lineOf i.rep) d.z
    ![faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i a,
      faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
      (fun i => lineEmb_range i.rep) i c]

theorem lineZbar_cocycle (i : LineFaces 6) (d : LineDatum (qRep (MonoidHom.id Γ6) ρ₆)) :
    (inhomogeneousCochains.d (Rep.res (MulAction.stabilizer Γ6 (lineOf i.rep)).subtype (qRepG ρ₆)) 2).hom
      (fun x => barCochain (MulAction.stabilizer Γ6 (lineOf i.rep)) (1 : RationalGL3) (lineOf i.rep) d.z x) = 0 :=
  barCochain_cocycle (MulAction.stabilizer Γ6 (lineOf i.rep)) (qRepG ρ₆) (1 : RationalGL3) (lineOf i.rep)
    (fun g => g.2) d.z d.hz

/-- **NFT-1**: the bar cochain of `d.z` at the line `b = lineOf h`, pulled back to the face group `Q`, is cohomologous to any cocycle `zx` representing `x`. -/
theorem nft1_line (i : LineFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ₀)))
    (d : LineDatum (qRep (MonoidHom.id Γ6) ρ₆))
    (hdc : d.coord (lineFacesEquivOrbits i) =
      faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
        (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
        (fun i => lineEmb_range i.rep) ρ₆ i
        (cmpGen ρ₀ ρ₆ hρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x))
    (zx : groupCohomology.cocycles₂ (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ₀)))
    (hzx : groupCohomology.H2π _ zx = x) :
    ∃ κ : ↥(gammaNQAt 6 i.rep) → V, ∀ a c : ↥(gammaNQAt 6 i.rep),
      lineZbar ρ₆ i d a c = zx.1 (a, c) +
        (ρ₀ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) a) (κ c) - κ (a * c) + κ a) := by
  have key := coord_at_b (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
    (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
    (fun i => lineEmb_range i.rep) ρ₆ i d.cls (cmpGen ρ₀ ρ₆ hρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x) hdc
  have hc2 : (faceCoord (MulAction.stabilizer Γ6 (lineOf i.rep)) (qRepG ρ₆) (1 : RationalGL3) (lineOf i.rep)
      (fun g => g.2) 2).hom d.cls =
      (groupCohomology.π (Rep.res (MulAction.stabilizer Γ6 (lineOf i.rep)).subtype (qRepG ρ₆)) 2).hom
        (groupCohomology.cocyclesMk (fun x => barCochain (MulAction.stabilizer Γ6 (lineOf i.rep)) (1 : RationalGL3) (lineOf i.rep) d.z x)
          (lineZbar_cocycle ρ₆ i d)) :=
    faceCoord_clsS_eq (MulAction.stabilizer Γ6 (lineOf i.rep)) (qRepG ρ₆) (1 : RationalGL3) (lineOf i.rep)
      (fun g => g.2) (m := 1) d.z d.hz
  rw [hc2] at key
  obtain ⟨hx0, hπ⟩ := pi_cocyclesMk_eq_H2π (Rep.res (MulAction.stabilizer Γ6 (lineOf i.rep)).subtype (qRepG ρ₆))
    (fun x => barCochain (MulAction.stabilizer Γ6 (lineOf i.rep)) (1 : RationalGL3) (lineOf i.rep) d.z x) (lineZbar_cocycle ρ₆ i d)
  rw [hπ, ← hzx] at key
  have hcm : cmpGen ρ₀ ρ₆ hρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp))
      (groupCohomology.H2π (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ₀)) zx) =
      groupCohomology.H2π _ (groupCohomology.mapCocycles₂ (MonoidHom.id _) (EdgeNat.comparison (MonoidHom.id _)
        (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ₀))
        (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)))
          (Rep.of ρ₆)) LinearMap.id (fun s v => (hρ _ v).symm)) zx) :=
    EdgeNat.h2Map_π _ _ _ _ _ zx
  rw [hcm] at key
  have key2 : (groupCohomology.H2π (qRepG (ρ₆.comp (lineEmb i.rep)))).hom
      (groupCohomology.mapCocycles₂ (faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep))
        (fun i => lineEmb i.rep) (fun i => lineEmb_range i.rep) i)
        (faceQId (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
          (fun i => lineEmb_range i.rep) ρ₆ i) ⟨_, hx0⟩) =
      (groupCohomology.H2π (qRepG (ρ₆.comp (lineEmb i.rep)))).hom
        (qCoc (ρ₆.comp (lineEmb i.rep)) (groupCohomology.mapCocycles₂ (MonoidHom.id _) (EdgeNat.comparison (MonoidHom.id _)
          (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ₀))
          (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)))
            (Rep.of ρ₆)) LinearMap.id (fun s v => (hρ _ v).symm)) zx)) := by
    refine Eq.trans ?_ (key.trans (qH2_π _ _))
    exact (groupCohomology.H2π_comp_map_apply _ _ _).symm
  obtain ⟨κ, hκ⟩ := coboundary_of_H2π_eq _ _ _ key2
  refine ⟨κ, fun a c => ?_⟩
  have h1 := hκ a c
  have e1 : (groupCohomology.mapCocycles₂ (faceSigma (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep))
        (fun i => lineEmb i.rep) (fun i => lineEmb_range i.rep) i)
        (faceQId (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
          (fun i => lineEmb_range i.rep) ρ₆ i) ⟨_, hx0⟩).1 (a, c) = lineZbar ρ₆ i d a c := rfl
  have e2 : (qCoc (ρ₆.comp (lineEmb i.rep)) (groupCohomology.mapCocycles₂ (MonoidHom.id _) (EdgeNat.comparison (MonoidHom.id _)
          (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ₀))
          (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)))
            (Rep.of ρ₆)) LinearMap.id (fun s v => (hρ _ v).symm)) zx)).1 (a, c) = zx.1 (a, c) := rfl
  have e3 : ((qRepG (ρ₆.comp (lineEmb i.rep))).ρ a) (κ c) =
      ρ₀ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) a) (κ c) := by
    exact hρ _ _
  rw [e1, e2, e3] at h1
  exact h1

end Line

section Instances

open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem rep6_hρ (s : gammaN 6) (v : V) : rep6 ρ (gammaSixEquiv s) v = ρ s v := by
  change ρ (gammaSixEquiv.symm (gammaSixEquiv s)) v = _
  rw [MulEquiv.symm_apply_apply]

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem rep6_dual_hρ (s : gammaN 6) (v : Module.Dual ℂ V) :
    (rep6 ρ).dual (gammaSixEquiv s) v = ρ.dual s v := by
  simp [Representation.dual_apply, rep6, map_inv]

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
/-- **NFT-1 for the dual datum**: the same statement for the dual representation, in the form of `lineFace_exists_lifts`. -/
theorem nft1_line_dual (i : LineFaces 6)
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (e : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hec : e.coord (lineFacesEquivOrbits i) =
      faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
        (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
        (fun i => lineEmb_range i.rep) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) y))
    (zy : groupCohomology.cocycles₂ (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hzy : groupCohomology.H2π _ zy = y) :
    ∃ κ : gammaNQAt 6 i.rep → Module.Dual ℂ V, ∀ a c, lineZbar (rep6 ρ).dual i e a c = zy.1 (a, c) +
      (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) a) (κ c) - κ (a * c) + κ a) :=
  nft1_line ρ.dual (rep6 ρ).dual (rep6_dual_hρ ρ) i y e hec zy hzy

/-- **NFT-1** for the transported representation `rep6 ρ`, in the form of `lineFace_exists_lifts`. -/
theorem nft1_line_rep6 (i : LineFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (d : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ)))
    (hdc : d.coord (lineFacesEquivOrbits i) =
      faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
        (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
        (fun i => lineEmb_range i.rep) (rep6 ρ) i
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x))
    (zx : groupCohomology.cocycles₂ (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (hzx : groupCohomology.H2π _ zx = x) :
    ∃ κ : gammaNQAt 6 i.rep → V, ∀ a c, lineZbar (rep6 ρ) i d a c = zx.1 (a, c) +
      (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) a) (κ c) - κ (a * c) + κ a) :=
  nft1_line ρ (rep6 ρ) (rep6_hρ ρ) i x d hdc zx hzx

end Instances

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
