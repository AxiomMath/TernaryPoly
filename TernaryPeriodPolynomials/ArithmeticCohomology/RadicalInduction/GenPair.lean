module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenCompat
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadIsoFace

@[expose] public section


/-!
# From the extension of `K` to the extension of `S = K ∩ Γ(6)` and back: the canonical face pairing

Formalized by Claude Sonnet 5.5.

`extSK`, `splSK`, `hdetSK`: the extension of `S` transported from `extK` along `eSK : S ≃ K`.  `pairing_K_S`: the canonical face pairing at `K` of the edges of two classes equals the canonical face pairing at `S`
of the edges of their images under `isoKer` for `α = eSK`; `isoKer_toKgen`: the image of `toKgen y` is `y`.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction
open CategoryTheory

section SK

variable (K : Subgroup SL(3, ℤ)) (hK : K ≤ gammaN 6)
  (extK : GroupExtension RadicalLattice ↥K ↥(CongruenceSubgroup.Gamma 6)) (sK : extK.Splitting)

/-- The extension of `S = K ∩ Γ(6)` transported from `extK`. -/
def extSK : GroupExtension RadicalLattice ↥(SK K) ↥(CongruenceSubgroup.Gamma 6) :=
  FaceTransport.pullbackExt extK (eSK K hK)

/-- Its Levi splitting. -/
def splSK : (extSK K hK extK).Splitting :=
  FaceTransport.splitting (FaceTransport.pullbackEquiv extK (eSK K hK)) sK

theorem hdetSK (hdetK : ∀ A, radDet (splitRadicalInput sK A) = 1) (A : ↥(CongruenceSubgroup.Gamma 6)) :
    radDet (splitRadicalInput (splSK K hK extK sK) A) = 1 := by
  have e : ∀ r, splitRadicalInput (splSK K hK extK sK) A r = splitRadicalInput sK A r := fun r =>
    FaceTransport.radicalInput_eq (FaceTransport.pullbackEquiv extK (eSK K hK)) sK A r
  have := hdetK A
  unfold radDet at this ⊢
  rw [e rl1, e rl2]
  exact this

theorem hinl_SK (r : RadicalLattice) : (eSK K hK).toMonoidHom ((extSK K hK extK).inl r) = extK.inl r :=
  FaceTransport.equiv_inl (FaceTransport.pullbackEquiv extK (eSK K hK)) r

theorem hsplit_SK (m : ↥(CongruenceSubgroup.Gamma 6)) : (eSK K hK).toMonoidHom (splSK K hK extK sK m) = sK m :=
  FaceTransport.equiv_splitting (FaceTransport.pullbackEquiv extK (eSK K hK)) sK m

variable (σ : Rep ℂ ↥(gammaN 6))

theorem isoKer_toKgen_val (y : groupCohomology.H2 (Rep.res (SK K).subtype σ)) :
    EdgeNat.h2Map (eSK K hK).toMonoidHom (Rep.res (inclK K hK) σ) (Rep.res (SK K).subtype σ) LinearMap.id
      (fun _ _ => rfl) (toKgen K hK σ y) = y := by
  unfold toKgen
  refine (h2Map_comp (eSK K hK).symm.toMonoidHom (eSK K hK).toMonoidHom (Rep.res (SK K).subtype σ)
    (Rep.res (inclK K hK) σ) (Rep.res (SK K).subtype σ) LinearMap.id (fun g v => toKgen_hT K hK σ g v) LinearMap.id
    (fun _ _ => rfl) y).trans ?_
  have key : EdgeNat.h2Map (MonoidHom.id ↥(SK K)) (Rep.res (SK K).subtype σ) (Rep.res (SK K).subtype σ)
      (𝟙 (Rep.res (SK K).subtype σ) : Rep.res (SK K).subtype σ ⟶ Rep.res (SK K).subtype σ).hom.toLinearMap
      (fun g v => Rep.hom_comm_apply (𝟙 (Rep.res (SK K).subtype σ) : Rep.res (SK K).subtype σ ⟶ Rep.res (SK K).subtype σ) g v) y = y :=
    (h2Hom_eq_h2Map _ _ (𝟙 (Rep.res (SK K).subtype σ)) y).symm.trans (h2Hom_id y)
  exact (h2Map_congr (MonoidHom.ext fun x => (eSK K hK).symm_apply_apply x) _ _ _ _ (LinearMap.ext fun v => rfl) y).trans key

variable [FiniteDimensional ℂ σ] (hdetK : ∀ A, radDet (splitRadicalInput sK A) = 1)

/-- The `K`-world to `S`-world map of classes with vanishing radical restriction. -/
def isoKerK : (twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) σ)).ker →ₗ[ℂ]
    (twoCohomologyRestriction (extSK K hK extK).inl (Rep.res (SK K).subtype σ)).ker :=
  isoKer (ext' := extSK K hK extK) (eSK K hK).toMonoidHom (hinl_SK K hK extK) (W₁ := Rep.res (inclK K hK) σ)
    (W₂ := Rep.res (SK K).subtype σ) LinearMap.id (fun _ _ => rfl)

/-- The same for the contragredient coefficients. -/
def isoKerKD : (twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) σ))).ker →ₗ[ℂ]
    (twoCohomologyRestriction (extSK K hK extK).inl (dualRepG (Rep.res (SK K).subtype σ))).ker :=
  isoKerD (ext' := extSK K hK extK) (eSK K hK).toMonoidHom (hinl_SK K hK extK) (W₁ := Rep.res (inclK K hK) σ)
    (W₂ := Rep.res (SK K).subtype σ) LinearMap.id (fun _ _ => rfl)

omit [FiniteDimensional ℂ σ] in
theorem isoKerK_val (z : (twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) σ)).ker) :
    (isoKerK K hK extK σ z).1 = EdgeNat.h2Map (eSK K hK).toMonoidHom (Rep.res (inclK K hK) σ) (Rep.res (SK K).subtype σ)
      LinearMap.id (fun _ _ => rfl) z.1 := rfl

omit [FiniteDimensional ℂ σ] in
theorem isoKerKD_val (z : (twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) σ))).ker) :
    (isoKerKD K hK extK σ z).1 = EdgeNat.h2Map (eSK K hK).toMonoidHom (dualRepG (Rep.res (inclK K hK) σ))
      (dualRepG (Rep.res (SK K).subtype σ)) LinearMap.id (fun _ _ => rfl) z.1 := rfl

omit [FiniteDimensional ℂ σ] in
theorem isoKerK_edge_mem
    (z : (twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) σ)).ker)
    (hz : splitCohomologyEdge sK (Rep.res (inclK K hK) σ) z ∈
      SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma 6) (splitRadicalH1Representation sK (Rep.res (inclK K hK) σ))) :
    splitCohomologyEdge (splSK K hK extK sK) (Rep.res (SK K).subtype σ) (isoKerK K hK extK σ z) ∈
      SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma 6) (splitRadicalH1Representation (splSK K hK extK sK) (Rep.res (SK K).subtype σ)) := by
  have : Fact (3 ≤ 6) := ⟨by norm_num⟩
  exact isoKer_edge_mem (s := sK) (s' := splSK K hK extK sK) (ext' := extSK K hK extK) (eSK K hK).toMonoidHom
    (hinl_SK K hK extK) (hsplit_SK K hK extK sK) (W₁ := Rep.res (inclK K hK) σ) (W₂ := Rep.res (SK K).subtype σ)
    LinearMap.id (fun _ _ => rfl) z hz

omit [FiniteDimensional ℂ σ] in
theorem isoKerKD_edge_mem
    (z : (twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) σ))).ker)
    (hz : splitCohomologyEdge sK (dualRepG (Rep.res (inclK K hK) σ)) z ∈
      SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma 6) (splitRadicalH1Representation sK (dualRepG (Rep.res (inclK K hK) σ)))) :
    splitCohomologyEdge (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ)) (isoKerKD K hK extK σ z) ∈
      SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma 6)
        (splitRadicalH1Representation (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ))) := by
  have : Fact (3 ≤ 6) := ⟨by norm_num⟩
  exact isoKerD_edge_mem (s := sK) (s' := splSK K hK extK sK) (ext' := extSK K hK extK) (eSK K hK).toMonoidHom
    (hinl_SK K hK extK) (hsplit_SK K hK extK sK) (W₁ := Rep.res (inclK K hK) σ) (W₂ := Rep.res (SK K).subtype σ)
    LinearMap.id (fun _ _ => rfl) z hz

include hdetK in
/-- **The canonical face pairing at `K` equals that at `S`** (edges of corresponding classes). -/
theorem pairing_K_S
    (z : (twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) σ)).ker)
    (z' : (twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) σ))).ker)
    (hz : splitCohomologyEdge sK (Rep.res (inclK K hK) σ) z ∈
      SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma 6) (splitRadicalH1Representation sK (Rep.res (inclK K hK) σ)))
    (hz' : splitCohomologyEdge sK (dualRepG (Rep.res (inclK K hK) σ)) z' ∈
      SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma 6) (splitRadicalH1Representation sK (dualRepG (Rep.res (inclK K hK) σ))))
    (h1 : splitCohomologyEdge (splSK K hK extK sK) (Rep.res (SK K).subtype σ) (isoKerK K hK extK σ z) ∈
      SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma 6) (splitRadicalH1Representation (splSK K hK extK sK) (Rep.res (SK K).subtype σ)))
    (h2 : splitCohomologyEdge (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ)) (isoKerKD K hK extK σ z') ∈
      SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma 6)
        (splitRadicalH1Representation (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ)))) :
    facePairingCan (by norm_num : 3 ≤ 6) sK hdetK (Rep.res (inclK K hK) σ) ⟨splitCohomologyEdge sK (Rep.res (inclK K hK) σ) z, hz⟩
        ⟨splitCohomologyEdge sK (dualRepG (Rep.res (inclK K hK) σ)) z', hz'⟩ =
      facePairingCan (by norm_num : 3 ≤ 6) (splSK K hK extK sK) (hdetSK K hK extK sK hdetK) (Rep.res (SK K).subtype σ)
        ⟨splitCohomologyEdge (splSK K hK extK sK) (Rep.res (SK K).subtype σ) (isoKerK K hK extK σ z), h1⟩
        ⟨splitCohomologyEdge (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ)) (isoKerKD K hK extK σ z'), h2⟩ := by
  have : Fact (3 ≤ 6) := ⟨by norm_num⟩
  exact facePairingCan_iso_edge (s := sK) (s' := splSK K hK extK sK) (ext' := extSK K hK extK) (eSK K hK).toMonoidHom
    (hinl_SK K hK extK) (hsplit_SK K hK extK sK) (W₁ := Rep.res (inclK K hK) σ) (W₂ := Rep.res (SK K).subtype σ)
    LinearMap.id LinearMap.id (fun _ _ => rfl) (fun _ _ => rfl) (fun a b => rfl) hdetK (hdetSK K hK extK sK hdetK) z z' hz hz' h1 h2

end SK

section CompatGenThm

variable {M : ℕ} [NeZero M] (K K' : Subgroup SL(3, ℤ)) (hK : K ≤ gammaN 6) (hK' : K' ≤ gammaN M) (u : ↥(gammaN 6))
  (hmem : ∀ s : ↥(SK K), (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaN M →
    (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ K')
  (hback : ∀ p : ↥K', (u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ ∈ K) (h6 : 6 ∣ M)
  (extK : GroupExtension RadicalLattice ↥K ↥(CongruenceSubgroup.Gamma 6)) (sK : extK.Splitting)
  (ext' : GroupExtension RadicalLattice ↥K' ↥(CongruenceSubgroup.Gamma M)) (s' : ext'.Splitting)

/-- The extension of the stabilizer, transported from `ext'` along `μ`. -/
def extStabGen : GroupExtension RadicalLattice ↥(StabK (M := M) K u) ↥(CongruenceSubgroup.Gamma M) :=
  FaceTransport.pullbackExt ext' (muEquivGen K K' hK' u hmem hback h6)

/-- Its Levi splitting. -/
def splStabGen : (extStabGen K K' hK' u hmem hback h6 ext').Splitting :=
  FaceTransport.splitting (FaceTransport.pullbackEquiv ext' (muEquivGen K K' hK' u hmem hback h6)) s'

omit [NeZero M] in
theorem hdetStabGen (hdet' : ∀ A, radDet (splitRadicalInput s' A) = 1) (A : ↥(CongruenceSubgroup.Gamma M)) :
    radDet (splitRadicalInput (splStabGen K K' hK' u hmem hback h6 ext' s') A) = 1 := by
  have e : ∀ r, splitRadicalInput (splStabGen K K' hK' u hmem hback h6 ext' s') A r = splitRadicalInput s' A r := fun r =>
    FaceTransport.radicalInput_eq (FaceTransport.pullbackEquiv ext' (muEquivGen K K' hK' u hmem hback h6)) s' A r
  have := hdet' A
  unfold radDet at this ⊢
  rw [e rl1, e rl2]
  exact this

omit [NeZero M] in
/-- **`Compat` for an arbitrary face group, at the frame `h u`.** -/
theorem compat_gen (hdetK : ∀ A, radDet (splitRadicalInput sK A) = 1)
    (hinl : ∀ r : RadicalLattice, (u : SL(3, ℤ)) * ((ext'.inl r : ↥K') : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ =
      ((extK.inl (r ^ (M / 6)) : ↥K) : SL(3, ℤ)))
    (hspl : ∀ m : ↥(CongruenceSubgroup.Gamma M), (u : SL(3, ℤ)) * ((s' m : ↥K') : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ =
      ((sK (Subgroup.inclusion (gamma_le_of_dvd h6) m) : ↥K) : SL(3, ℤ))) :
    Compat (extSK K hK extK) (splSK K hK extK sK) (StabK (M := M) K u) (StabK (M := M) K u).subtype
      (extStabGen K K' hK' u hmem hback h6 ext') (splStabGen K K' hK' u hmem hback h6 ext' s')
      (Subgroup.inclusion (gamma_le_of_dvd h6)) (M / 6) where
  range_eq := Subgroup.range_subtype _
  inl_eq r := by
    apply Subtype.ext
    apply Subtype.ext
    change ((((muEquivGen K K' hK' u hmem hback h6).symm (ext'.inl r) : ↥(StabK (M := M) K u)) : ↥(SK K)) : ↥(gammaN 6)).1 =
      ((extK.inl (r ^ (M / 6)) : ↥K) : SL(3, ℤ))
    rw [muEquivGen_symm_val]
    exact hinl r
  split_eq m := by
    apply Subtype.ext
    apply Subtype.ext
    change ((((muEquivGen K K' hK' u hmem hback h6).symm (s' m) : ↥(StabK (M := M) K u)) : ↥(SK K)) : ↥(gammaN 6)).1 =
      ((sK (Subgroup.inclusion (gamma_le_of_dvd h6) m) : ↥K) : SL(3, ℤ))
    rw [muEquivGen_symm_val]
    exact hspl m
  inj := Subgroup.inclusion_injective _
  det := hdetSK K hK extK sK hdetK

end CompatGenThm

end TernaryPeriodPolynomials.Argument.RadicalInduction
