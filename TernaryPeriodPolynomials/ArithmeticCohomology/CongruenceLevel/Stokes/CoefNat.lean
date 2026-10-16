module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.CoordNat
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Pairs
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitStokes
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.QComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Dictionary

@[expose] public section


/-!
# Naturality of the Shapiro coordinates in the coefficients, and the scalar action of `ℂ` on data and pairings

Formalized by Claude Sonnet 5.5.

* `homPost g`: postcomposition of Hom cochains with a morphism `g : W ⟶ W'` of coefficient modules; `stabCoord_post`, `faceCoord_post`: the Shapiro coordinates commute with it, the target map
  being `groupCohomology.map (id) (Rep.resMap _ g)` on the cohomology of the stabilizer;
* `LineDatum.map g`, `PlaneDatum.map g`: the image of a datum, with `map_cone` (`cone ≫ g`), `map_isOn`, `map_coord`;
* `mulC`, `mulTriv`: multiplication by a complex scalar `c` on `qRep ι ρ` and on the trivial module `ℂ`; `evalC_mulC_left/right`, `conePairC_mulC_left/right`: the cone pairing is `ℂ`-bilinear
  with respect to them;
* `qH2_smul`, `faceTauQ_smul`: the comparison `qH2` and the face transport `faceTauQ` intertwine the `ℂ`-scalar action with `mulC`.
-/

open CategoryTheory Limits Finsupp
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.EquivariantSingularSmall
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.BoundaryFaceResolutionComparison
open MonoidalCategory
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

section Post

variable {G : Type} [Group G] {W W' : Rep.{0} ℚ G} (C : ChainComplex (Rep ℚ G) ℕ) (g : W ⟶ W')

/-- Postcomposition of Hom cochains with a morphism of coefficients. -/
def homPost : homCochains C W ⟶ homCochains C W' where
  f n := ModuleCat.ofHom
    { toFun := fun c => c ≫ g
      map_add' := fun c c' => Preadditive.add_comp _ _ _ c c' g
      map_smul' := fun r c => Linear.smul_comp _ _ _ r c g }
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (Category.assoc (C.d (i + 1) i) c g).symm

theorem homPost_apply (n : ℕ) (c : C.X n ⟶ W) : (homPost C g).f n c = c ≫ g := rfl

end Post


section StabPost

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] {W W' : Rep.{0} ℚ Γ}
  (S : Subgroup Γ) (v₀ : V) (z : Z) (hz : ∀ g : S, g • z = z) (g : W ⟶ W')

theorem stabCoord_post :
    homPost (prodComplex Γ V Z) g ≫ stabCoord S W' v₀ z hz =
      stabCoord S W v₀ z hz ≫ barChainMap (MonoidHom.id S) (Rep.resMap S.subtype g) := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Rep.free_ext
  intro x
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  have e1 := stabCoord_single S W' v₀ z hz k (c ≫ g) x
  have e2 := stabCoord_single S W v₀ z hz k c (fun i => (MonoidHom.id S) (x i))
  have e3 := barChainMap_apply (MonoidHom.id S) (Rep.resMap S.subtype g) k (((stabCoord S W v₀ z hz).f k).hom c) x
  exact e1.trans ((congrArg (fun t => g.hom t) e2).symm.trans e3.symm)

theorem faceCoord_post (n : ℕ) :
    HomologicalComplex.homologyMap (homPost (prodComplex Γ V Z) g) n ≫ faceCoord S W' v₀ z hz n =
      faceCoord S W v₀ z hz n ≫ groupCohomology.map (MonoidHom.id S) (Rep.resMap S.subtype g) n := by
  rw [faceCoord_eq_homologyMap_stabCoord, faceCoord_eq_homologyMap_stabCoord]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, stabCoord_post]
  rw [HomologicalComplex.homologyMap_comp, Category.assoc, Category.assoc]
  refine congrArg (fun t => HomologicalComplex.homologyMap (stabCoord S W v₀ z hz) n ≫ t) ?_
  exact barChainMap_homology (A := Rep.res S.subtype W) (B := Rep.res S.subtype W') (MonoidHom.id S)
    (Rep.resMap S.subtype g) n

end StabPost

section Datum

variable {W W' : Rep.{0} ℚ Γ6} (g : W ⟶ W')

/-- The image of a line datum under a morphism of coefficient modules. -/
def LineDatum.map (d : LineDatum W) : LineDatum W' where
  z := d.z ≫ g
  hz := by rw [← Category.assoc, d.hz, zero_comp]
  w := d.w ≫ g
  hw := by rw [← Category.assoc, d.hw, Category.assoc]

/-- The image of a plane datum under a morphism of coefficient modules. -/
def PlaneDatum.map (d : PlaneDatum W) : PlaneDatum W' where
  z := d.z ≫ g
  hz := by rw [← Category.assoc, d.hz, zero_comp]
  w := d.w ≫ g
  hw := by rw [← Category.assoc, d.hw, Category.assoc]

theorem LineDatum.map_cone (d : LineDatum W) : (d.map g).cone = d.cone ≫ g :=
  (lineCone_comp g d.w d.z).symm

theorem PlaneDatum.map_cone (d : PlaneDatum W) : (d.map g).cone = d.cone ≫ g :=
  (planeCone_comp g d.w d.z).symm

theorem LineDatum.map_isOn (S : Set Line) (d : LineDatum W) (h : d.IsOn S) : (d.map g).IsOn S :=
  ⟨fun u ℓ hℓ => by
    change g.hom (d.z.hom (MonoidAlgebra.single (u, ℓ) 1)) = 0
    rw [h.1 u ℓ hℓ, map_zero],
   fun u F hF => by
    change g.hom (d.w.hom (MonoidAlgebra.single (u, F) 1)) = 0
    rw [h.2 u F hF, map_zero]⟩

theorem PlaneDatum.map_isOn (S : Set Plane) (d : PlaneDatum W) (h : d.IsOn S) : (d.map g).IsOn S :=
  ⟨fun u ℓ hℓ => by
    change g.hom (d.z.hom (MonoidAlgebra.single (u, ℓ) 1)) = 0
    rw [h.1 u ℓ hℓ, map_zero],
   fun u F hF => by
    change g.hom (d.w.hom (MonoidAlgebra.single (u, F) 1)) = 0
    rw [h.2 u F hF, map_zero]⟩

theorem LineDatum.map_cls (d : LineDatum W) :
    (d.map g).cls = (HomologicalComplex.homologyMap (homPost (prodComplex Γ6 RationalGL3 Line) g) 2).hom d.cls := by
  have hc : ((LineCochains W).d 2 3).hom d.z = 0 := d.hz
  exact (cls2_map (LineCochains W) (homPost (prodComplex Γ6 RationalGL3 Line) g) d.z hc (d.map g).hz).symm

theorem PlaneDatum.map_cls (d : PlaneDatum W) :
    (d.map g).cls = (HomologicalComplex.homologyMap (homPost (prodComplex Γ6 RationalGL3 Plane) g) 2).hom d.cls := by
  have hc : ((PlaneCochains W).d 2 3).hom d.z = 0 := d.hz
  exact (cls2_map (PlaneCochains W) (homPost (prodComplex Γ6 RationalGL3 Plane) g) d.z hc (d.map g).hz).symm

theorem LineDatum.map_coord (o : labelOrbits Γ6 Line) (d : LineDatum W) :
    (d.map g).coord o = (groupCohomology.map (MonoidHom.id (stabilizer Γ6 o.out))
      (Rep.resMap (stabilizer Γ6 o.out).subtype g) 2).hom (d.coord o) := by
  unfold LineDatum.coord
  rw [LineDatum.map_cls]
  have := congrArg (fun m => m.hom d.cls)
    (faceCoord_post (stabilizer Γ6 o.out) (1 : RationalGL3) o.out (fun g => g.2) g 2)
  exact this

theorem PlaneDatum.map_coord (o : labelOrbits Γ6 Plane) (d : PlaneDatum W) :
    (d.map g).coord o = (groupCohomology.map (MonoidHom.id (stabilizer Γ6 o.out))
      (Rep.resMap (stabilizer Γ6 o.out).subtype g) 2).hom (d.coord o) := by
  unfold PlaneDatum.coord
  rw [PlaneDatum.map_cls]
  have := congrArg (fun m => m.hom d.cls)
    (faceCoord_post (stabilizer Γ6 o.out) (1 : RationalGL3) o.out (fun g => g.2) g 2)
  exact this

end Datum

section Scalar

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  {G : Type} [Group G] (ι : Γ6 →* G) (ρ : Representation ℂ G V)

/-- Multiplication by a complex scalar, as an endomorphism of the rational module underlying a complex representation. -/
def mulC (c : ℂ) : qRep ι ρ ⟶ qRep ι ρ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((c • LinearMap.id : V →ₗ[ℂ] V).restrictScalars ℚ)
    (fun g v => by
      change c • (ρ (ι g)) v = (ρ (ι g)) (c • v)
      rw [map_smul]))

/-- Multiplication by a complex scalar on the trivial module `ℂ`. -/
def mulTriv (c : ℂ) : Rep.trivial ℚ Γ6 ℂ ⟶ Rep.trivial ℚ Γ6 ℂ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ (Representation.trivial ℚ Γ6 ℂ)
    ((c • LinearMap.id : ℂ →ₗ[ℂ] ℂ).restrictScalars ℚ) (fun _ _ => rfl))

theorem evalC_mulC_left (c : ℂ) :
    (mulC ι ρ c ⊗ₘ 𝟙 (qRep ι ρ.dual)) ≫ evalC ι ρ = evalC ι ρ ≫ mulTriv c := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro v f
  change (evalC ι ρ).hom (((mulC ι ρ c ⊗ₘ 𝟙 (qRep ι ρ.dual))).hom (v ⊗ₜ[ℚ] f)) =
    c • (evalC ι ρ).hom (v ⊗ₜ[ℚ] f)
  rw [tensorHom_hom_tmul]
  change (show Module.Dual ℂ V from f) (c • (show V from v)) = c • (show Module.Dual ℂ V from f) (show V from v)
  rw [map_smul]

theorem evalC_mulC_right (c : ℂ) :
    (𝟙 (qRep ι ρ) ⊗ₘ mulC ι ρ.dual c) ≫ evalC ι ρ = evalC ι ρ ≫ mulTriv c := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro v f
  change (evalC ι ρ).hom (((𝟙 (qRep ι ρ) ⊗ₘ mulC ι ρ.dual c)).hom (v ⊗ₜ[ℚ] f)) =
    c • (evalC ι ρ).hom (v ⊗ₜ[ℚ] f)
  rw [tensorHom_hom_tmul]
  change (c • (show Module.Dual ℂ V from f)) v = c • (show Module.Dual ℂ V from f) v
  rfl

theorem conePairC_mulC_left (v : coneR.X 4) (X : coneR.X 2 ⟶ qRep ι ρ) (Y : coneR.X 2 ⟶ qRep ι ρ.dual) (c : ℂ) :
    conePairC (evalC ι ρ) v (X ≫ mulC ι ρ c) Y = c * conePairC (evalC ι ρ) v X Y := by
  unfold conePairC
  have h : (X ≫ mulC ι ρ c) ⊗ₘ Y = (X ⊗ₘ Y) ≫ (mulC ι ρ c ⊗ₘ 𝟙 (qRep ι ρ.dual)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  rw [h]
  simp only [Category.assoc]
  rw [evalC_mulC_left]
  rfl

theorem conePairC_mulC_right (v : coneR.X 4) (X : coneR.X 2 ⟶ qRep ι ρ) (Y : coneR.X 2 ⟶ qRep ι ρ.dual) (c : ℂ) :
    conePairC (evalC ι ρ) v X (Y ≫ mulC ι ρ.dual c) = c * conePairC (evalC ι ρ) v X Y := by
  unfold conePairC
  have h : X ⊗ₘ (Y ≫ mulC ι ρ.dual c) = (X ⊗ₘ Y) ≫ (𝟙 (qRep ι ρ) ⊗ₘ mulC ι ρ.dual c) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  rw [h]
  simp only [Category.assoc]
  rw [evalC_mulC_right]
  rfl

end Scalar

section QSmul

variable {H : Type} [Group H] {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ' : Representation ℂ H V) (c : ℂ)

/-- **The comparison `qH2` intertwines the complex scalar action with the rational module map "multiplication by `c`".** -/
theorem qH2_smul (φ : Rep.res (MonoidHom.id H) (qRepG ρ') ⟶ qRepG ρ') (hφ : ∀ v : V, φ.hom v = c • v)
    (y : groupCohomology.H2 (Rep.of ρ')) :
    qH2 ρ' (c • y) = (groupCohomology.map (MonoidHom.id H) φ 2).hom (qH2 ρ' y) := by
  induction y using groupCohomology.H2_induction_on with
  | h z =>
    have h1 : c • groupCohomology.H2π (Rep.of ρ') z = groupCohomology.H2π (Rep.of ρ') (c • z) :=
      (map_smul (groupCohomology.H2π (Rep.of ρ')).hom c z).symm
    rw [h1, qH2_π, qH2_π, groupCohomology.H2π_comp_map_apply]
    congr 1
    apply Subtype.ext
    funext x
    exact (hφ _).symm

end QSmul

section FaceSmul

variable {Z : Type} [MulAction Γ6 Z] {F : Type} (o : F → labelOrbits Γ6 Z) (b : F → Z)
  (hb : ∀ i, b i ∈ labelOrbit Γ6 Z (o i))
  (Grp : F → Type) [∀ i, Group (Grp i)] (emb : ∀ i, Grp i →* Γ6) (hinj : ∀ i, Function.Injective (emb i))
  (hrange : ∀ i, (emb i).range = MulAction.stabilizer Γ6 (b i))
  {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] (σ : Representation ℂ Γ6 V)

/-- **The rational transport `faceTauQ` intertwines the scalar action of `ℂ` with the coefficient map "multiplication by `c`".** -/
theorem faceTauQ_smul (i : F) (c : ℂ) (x : groupCohomology.H2 (Rep.res (emb i) (Rep.of σ))) :
    faceTauQ o b hb Grp emb hinj hrange σ i (c • x) =
      (groupCohomology.map (MonoidHom.id (MulAction.stabilizer Γ6 (o i).out))
        (Rep.resMap (MulAction.stabilizer Γ6 (o i).out).subtype (mulC (MonoidHom.id Γ6) σ c)) 2).hom
        (faceTauQ o b hb Grp emb hinj hrange σ i x) := by
  unfold faceTauQ
  change qH2 _ (faceTau o b hb Grp emb hinj hrange σ i (c • x)) = _
  rw [map_smul]
  exact qH2_smul (σ.comp (MulAction.stabilizer Γ6 (o i).out).subtype) c
    (Rep.resMap (MulAction.stabilizer Γ6 (o i).out).subtype (mulC (MonoidHom.id Γ6) σ c)) (fun v => rfl) _

end FaceSmul

end TernaryPeriodPolynomials.Argument.GammaNStokes
