module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenComp
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenPair
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.MackeyComp

@[expose] public section


/-!
# The orbit identity for an arbitrary face group (Step 2 of the literal Stokes lemma at `Γ(N)`)

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

**`orbit_ident_gen`**: let `K ≤ Γ(6)`, `K' ≤ Γ(M)` be subgroups of `SL₃(ℤ)` with split extensions `extK`, `ext'` over `Γ(6)`, `Γ(M)` (radical `ℤ²`), `u ∈ Γ(6)` with `u K' u⁻¹ ⊆ K`,
`u⁻¹ (K ∩ uΓ(M)u⁻¹) u ⊆ K'`, `u · inl'(r) · u⁻¹ = inl(r^{M/6})`, `u · s'(m) · u⁻¹ = s(m)`.  For an induced class `c_V` of a class `c₀` of `Γ(M)` (and likewise for the contragredient)
the canonical face pairing at `K` (level 6) of the edges of the orbit components `h2E e_O (res_K c_V)`, `h2E e_Oᵀ (res_K c'_V)` equals the canonical face pairing at `K'` (level `M`) of the edges of the restrictions
`res_{K'} c₀`, `res_{K'} c'₀`, with constant exactly `1` (the Koszul renormalisation `m₀²` cancels the orbit size).
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
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section Defs

variable {M : ℕ} (K : Subgroup SL(3, ℤ)) (hK : K ≤ gammaN 6) {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (o : orbitRel.Quotient ↥(SK K) (↥(gammaN 6) ⧸ Δ6 M))

/-- The `S`-world component class `h2E e_O (res_S c_V)`. -/
def yS (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M)))) :
    groupCohomology.H2 (Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M)))) :=
  h2E (Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M)))) (eO (Δ6 M) (SK K) o)
    (fun k v => eO_equivariant ρ (Δ6 M) (SK K) o k v)
    (twoCohomologyRestriction (SK K).subtype (Rep.of (permRep ρ (Δ6 M))) cV)

/-- The `K`-world component class (the first component of S5's `lineTermX`/`planeTermX`). -/
def zK (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M)))) :
    groupCohomology.H2 (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) :=
  h2E (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) (eO (Δ6 M) (SK K) o)
    (fun k v => eO_equivariant ρ (Δ6 M) (SK K) o ((eSK K hK).symm k) v)
    (twoCohomologyRestriction (inclK K hK) (Rep.of (permRep ρ (Δ6 M))) cV)

variable [Fintype (↥(gammaN 6) ⧸ Δ6 M)]

/-- The `S`-world component class for the contragredient. -/
def ySd (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M)))) :
    groupCohomology.H2 (Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M)).dual)) :=
  h2E (Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M)).dual)) (eO (Δ6 M) (SK K) o).dualMap
    (fun k v => eO_dual_equivariant ρ (Δ6 M) (SK K) o k v)
    (twoCohomologyRestriction (SK K).subtype (Rep.of (permRep ρ (Δ6 M)).dual) (h2Hom (dualRepHom ρ (Δ6 M)) cVd))

/-- The `K`-world component class for the contragredient (the first component of `lineTermY`/`planeTermY`). -/
def zKd (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M)))) :
    groupCohomology.H2 (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)).dual)) :=
  h2E (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)).dual)) (eO (Δ6 M) (SK K) o).dualMap
    (fun k v => eO_dual_equivariant ρ (Δ6 M) (SK K) o ((eSK K hK).symm k) v)
    (twoCohomologyRestriction (inclK K hK) (Rep.of (permRep ρ (Δ6 M)).dual) (h2Hom (dualRepHom ρ (Δ6 M)) cVd))

omit [Fintype (↥(gammaN 6) ⧸ Δ6 M)] in
theorem zK_eq (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M)))) :
    zK K hK ρ o cV = toKgen K hK (Rep.of (permRep ρ (Δ6 M))) (yS K ρ o cV) := by
  unfold zK yS
  rw [toKgen_res K hK]
  exact toKgen_h2E K hK (Rep.of (permRep ρ (Δ6 M))) (eO (Δ6 M) (SK K) o) _ _ _

theorem zKd_eq (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M)))) :
    zKd K hK ρ o cVd = toKgen K hK (Rep.of (permRep ρ (Δ6 M)).dual) (ySd K ρ o cVd) := by
  unfold zKd ySd
  rw [toKgen_res K hK]
  exact toKgen_h2E K hK (Rep.of (permRep ρ (Δ6 M)).dual) (eO (Δ6 M) (SK K) o).dualMap _ _ _

theorem ySd_eq (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M)))) :
    ySd K ρ o cVd = dualPushG ρ (Δ6 M) (SK K) (yS K ρ.dual o cVd) := by
  unfold ySd yS
  rw [res_h2Hom_eq]
  exact h2E_dualPushG ρ (Δ6 M) (SK K) o _ _

end Defs

section Main

variable {M : ℕ} [NeZero M] (hM : 3 ≤ M) (h6 : 6 ∣ M)
  (K K' : Subgroup SL(3, ℤ)) (hK : K ≤ gammaN 6) (hK' : K' ≤ gammaN M) (u : ↥(gammaN 6))
  (hmem : ∀ s : ↥(SK K), (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaN M →
    (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ K')
  (hback : ∀ p : ↥K', (u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ ∈ K)
  (extK : GroupExtension RadicalLattice ↥K ↥(CongruenceSubgroup.Gamma 6)) (sK : extK.Splitting)
  (hdetK : ∀ A, radDet (splitRadicalInput sK A) = 1)
  (ext' : GroupExtension RadicalLattice ↥K' ↥(CongruenceSubgroup.Gamma M)) (s' : ext'.Splitting)
  (hdet' : ∀ A, radDet (splitRadicalInput s' A) = 1)
  (hinl : ∀ r : RadicalLattice, (u : SL(3, ℤ)) * ((ext'.inl r : ↥K') : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ =
    ((extK.inl (r ^ (M / 6)) : ↥K) : SL(3, ℤ)))
  (hspl : ∀ m : ↥(CongruenceSubgroup.Gamma M), (u : SL(3, ℤ)) * ((s' m : ↥K') : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ =
    ((sK (Subgroup.inclusion (gamma_le_of_dvd h6) m) : ↥K) : SL(3, ℤ)))
  {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)
  (o : orbitRel.Quotient ↥(SK K) (↥(gammaN 6) ⧸ Δ6 M)) (hu : (u : ↥(gammaN 6) ⧸ Δ6 M) = Quotient.out o)

/-- The orbit projection of the `S`-world class of `z`. -/
def aCls (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M))))
    (hz : twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) (zK K hK ρ o cV) = 0) :
    (twoCohomologyRestriction (extSK K hK extK).inl
      (WI (extSK K hK extK) (stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)) (ρ.comp (SK K).subtype))).ker :=
  qKer ρ (SK K) (u : ↥(gammaN 6) ⧸ Δ6 M) (extSK K hK extK)
    (isoKerK K hK extK (Rep.of (permRep ρ (Δ6 M))) ⟨zK K hK ρ o cV, hz⟩)

/-- The transposed orbit inclusion of the `S`-world class of `z'`. -/
def bCls (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M))))
    (hz' : twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))) (zKd K hK ρ o cVd) = 0) :
    (twoCohomologyRestriction (extSK K hK extK).inl
      (dualRepG (WI (extSK K hK extK) (stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)) (ρ.comp (SK K).subtype)))).ker :=
  jKerD ρ (SK K) (u : ↥(gammaN 6) ⧸ Δ6 M) (extSK K hK extK)
    (isoKerKD K hK extK (Rep.of (permRep ρ (Δ6 M))) ⟨zKd K hK ρ o cVd, hz'⟩)

include hM h6 hK hK' hmem hback hdetK hdet' hinl hspl hu in
/-- **Parts A-D**: the canonical face pairing at `K` of the component classes equals the canonical face pairing at the
stabilizer of the `Stab`-level classes obtained from the orbit components. -/
theorem partA
    (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M)))) (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M))))
    (hz : twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) (zK K hK ρ o cV) = 0)
    (hzc : splitCohomologyEdge sK (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) ⟨zK K hK ρ o cV, hz⟩ ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma 6) (splitRadicalH1Representation sK (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))))
    (hz' : twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))) (zKd K hK ρ o cVd) = 0)
    (hzc' : splitCohomologyEdge sK (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))) ⟨zKd K hK ρ o cVd, hz'⟩ ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma 6)
        (splitRadicalH1Representation sK (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))))))
    (m1 : splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))
        (kerMapW (compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl) (ρ.comp (SK K).subtype)
          (aCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cV hz)) ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))))
    (m2 : splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))
        (kerMapWD (compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl) (ρ.comp (SK K).subtype)
          (bCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cVd hz')) ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))))) :
    facePairingCan (by norm_num : 3 ≤ 6) sK hdetK (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))
        ⟨splitCohomologyEdge sK (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) ⟨zK K hK ρ o cV, hz⟩, hzc⟩
        ⟨splitCohomologyEdge sK (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))) ⟨zKd K hK ρ o cVd, hz'⟩, hzc'⟩ =
      facePairingCan hM (splStabGen K K' hK' u hmem hback h6 ext' s') (hdetStabGen K K' hK' u hmem hback h6 ext' s' hdet')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))
        ⟨splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
          (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))
          (kerMapW (compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl) (ρ.comp (SK K).subtype)
            (aCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cV hz)), m1⟩
        ⟨splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
          (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))
          (kerMapWD (compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl) (ρ.comp (SK K).subtype)
            (bCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cVd hz')), m2⟩ := by
  classical
  have : Fact (3 ≤ 6) := ⟨by norm_num⟩
  have : NeZero (M / 6) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h6) (by norm_num)).ne'⟩
  have : Fintype (↥(SK K) ⧸ stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)) := Fintype.ofFinite _
  have hNorm : (CongruenceSubgroup.Gamma M).Normal := CongruenceSubgroup.Gamma_normal M
  have hfi : (subM 6 M).FiniteIndex :=
    ⟨ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero
      (Subgroup.relIndex_dvd_index_of_normal (CongruenceSubgroup.Gamma M) (CongruenceSubgroup.Gamma 6))⟩
  have : Fintype (CongruenceSubgroup.Gamma 6 ⧸ subM 6 M) := Fintype.ofFinite _
  have hc := compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl
  have hdetStab := hdetStabGen K K' hK' u hmem hback h6 ext' s' hdet'
  let σ := Rep.of (permRep ρ (Δ6 M))
  let x : ↥(gammaN 6) ⧸ Δ6 M := (u : ↥(gammaN 6) ⧸ Δ6 M)
  let z : (twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) σ)).ker := ⟨zK K hK ρ o cV, hz⟩
  let zd : (twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) σ))).ker := ⟨zKd K hK ρ o cVd, hz'⟩
  have h1 := isoKerK_edge_mem K hK extK sK σ z hzc
  have h2 := isoKerKD_edge_mem K hK extK sK σ zd hzc'
  have hA := pairing_K_S K hK extK sK σ hdetK z zd hzc hzc' h1 h2
  have hy1 : (isoKerK K hK extK σ z).1 = yS K ρ o cV := by
    rw [isoKerK_val]
    change EdgeNat.h2Map (eSK K hK).toMonoidHom (Rep.res (inclK K hK) σ) (Rep.res (SK K).subtype σ) LinearMap.id
      (fun g v => rfl) (zK K hK ρ o cV) = _
    rw [zK_eq K hK ρ o cV]
    exact isoKer_toKgen_val K hK σ _
  have hy2 : (isoKerKD K hK extK σ zd).1 = ySd K ρ o cVd := by
    rw [isoKerKD_val]
    change EdgeNat.h2Map (eSK K hK).toMonoidHom (dualRepG (Rep.res (inclK K hK) σ)) (dualRepG (Rep.res (SK K).subtype σ))
      LinearMap.id (fun g v => rfl) (zKd K hK ρ o cVd) = _
    rw [zKd_eq K hK ρ o cVd]
    exact isoKer_toKgen_val K hK (Rep.of (permRep ρ (Δ6 M)).dual) _
  let ŷ := isoKerK K hK extK σ z
  let ŷ' := isoKerKD K hK extK σ zd
  have hx : x = Quotient.out o := hu
  have hqj : ∀ w, h2Hom (qRep ρ (SK K) x) (h2Hom (jRep ρ (SK K) x) w) = w := fun w => by
    rw [← h2Hom_comp, jRep_qRep, h2Hom_id]
  have hyS : yS K ρ o cV = h2Hom (jRep ρ (SK K) x) (h2Hom (qRep ρ (SK K) x)
      (twoCohomologyRestriction (SK K).subtype σ cV)) :=
    h2E_eO_eq ρ (Δ6 M) (SK K) o x hx _
  have hmark : ŷ.1 = h2Hom (jRep ρ (SK K) x) (h2Hom (qRep ρ (SK K) x) ŷ.1) := by
    rw [hy1]
    conv_rhs => rw [hyS, hqj]
    exact hyS
  have hS : ∀ (k : ↥(SK K)) (v : Module.Dual ℂ ((↥(gammaN 6) ⧸ Δ6 M) → E)),
      (eO (Δ6 M) (SK K) o).dualMap ((Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M)).dual)).ρ k v) =
        (Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M)).dual)).ρ k ((eO (Δ6 M) (SK K) o).dualMap v) :=
    fun k v => eO_dual_equivariant ρ (Δ6 M) (SK K) o k v
  have hidem' : ∀ f : Module.Dual ℂ ((↥(gammaN 6) ⧸ Δ6 M) → E),
      (eO (Δ6 M) (SK K) o).dualMap ((eO (Δ6 M) (SK K) o).dualMap f) = (eO (Δ6 M) (SK K) o).dualMap f :=
    fun f => LinearMap.ext fun v => by
      change f (eO (Δ6 M) (SK K) o (eO (Δ6 M) (SK K) o v)) = f (eO (Δ6 M) (SK K) o v)
      rw [eO_idem]
  have hmark' : ŷ'.1 = h2E (Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M)).dual)) (eO (Δ6 M) (SK K) o).dualMap hS ŷ'.1 := by
    rw [hy2]
    unfold ySd
    exact (h2E_idem _ _ _ hidem' _).symm
  let a := qKer ρ (SK K) x (extSK K hK extK) ŷ
  let b := jKerD ρ (SK K) x (extSK K hK extK) ŷ'
  have ha := qKer_edge_mem ρ (SK K) x (ext := extSK K hK extK) (s := splSK K hK extK sK) ŷ h1
  have hb := jKerD_edge_mem ρ (SK K) x (ext := extSK K hK extK) (s := splSK K hK extK sK) ŷ' h2
  have hJ : jKer ρ (SK K) x (extSK K hK extK) a = ŷ := jKer_qKer ρ (SK K) x ŷ hmark
  have hQ : qKerD ρ (SK K) x (extSK K hK extK) b = ŷ' := qKerD_jKerD ρ (SK K) x o hx ŷ' hS hmark'
  have h1' : splitCohomologyEdge (splSK K hK extK sK) (Rep.res (SK K).subtype σ)
      (jKer ρ (SK K) x (extSK K hK extK) a) ∈ cuspidalSubspace (CongruenceSubgroup.Gamma 6)
      (splitRadicalH1Representation (splSK K hK extK sK) (Rep.res (SK K).subtype σ)) := by
    rw [hJ]; exact h1
  have h2' : splitCohomologyEdge (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ))
      (qKerD ρ (SK K) x (extSK K hK extK) b) ∈ cuspidalSubspace (CongruenceSubgroup.Gamma 6)
      (splitRadicalH1Representation (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ))) := by
    rw [hQ]; exact h2
  have e1 : (⟨splitCohomologyEdge (splSK K hK extK sK) (Rep.res (SK K).subtype σ) (jKer ρ (SK K) x (extSK K hK extK) a), h1'⟩ :
      cuspidalSubspace (CongruenceSubgroup.Gamma 6)
        (splitRadicalH1Representation (splSK K hK extK sK) (Rep.res (SK K).subtype σ))) =
      ⟨splitCohomologyEdge (splSK K hK extK sK) (Rep.res (SK K).subtype σ) ŷ, h1⟩ :=
    Subtype.ext (congrArg (fun w => splitCohomologyEdge (splSK K hK extK sK) (Rep.res (SK K).subtype σ) w) hJ)
  have e2 : (⟨splitCohomologyEdge (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ))
        (qKerD ρ (SK K) x (extSK K hK extK) b), h2'⟩ :
      cuspidalSubspace (CongruenceSubgroup.Gamma 6)
        (splitRadicalH1Representation (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ)))) =
      ⟨splitCohomologyEdge (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ)) ŷ', h2⟩ :=
    Subtype.ext (congrArg (fun w => splitCohomologyEdge (splSK K hK extK sK) (dualRepG (Rep.res (SK K).subtype σ)) w) hQ)
  have hA' := congrArg₂ (fun p q => facePairingCan (by norm_num : 3 ≤ 6) (splSK K hK extK sK) (hdetSK K hK extK sK hdetK)
      (Rep.res (SK K).subtype σ) p q) e1.symm e2.symm
  have hD := mackey_edge (ext := extSK K hK extK) (s := splSK K hK extK sK)
    (ext' := extStabGen K K' hK' u hmem hback h6 ext') (s' := splStabGen K K' hK' u hmem hback h6 ext' s')
    (hle := gamma_le_of_dvd h6) (m0 := M / 6) (N := 6) (M := M) ρ (SK K) x hM hc hdetStab a b ha hb h1' h2'
  exact hA.trans (hA'.trans hD)

omit [NeZero M] [FiniteDimensional ℂ E] in
theorem isoKerK_zK_val (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M))))
    (hz : twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) (zK K hK ρ o cV) = 0) :
    (isoKerK K hK extK (Rep.of (permRep ρ (Δ6 M))) ⟨zK K hK ρ o cV, hz⟩).1 = yS K ρ o cV := by
  rw [isoKerK_val]
  change EdgeNat.h2Map (eSK K hK).toMonoidHom (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))
    (Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M)))) LinearMap.id (fun g v => rfl) (zK K hK ρ o cV) = _
  rw [zK_eq K hK ρ o cV]
  exact isoKer_toKgen_val K hK (Rep.of (permRep ρ (Δ6 M))) _

omit [FiniteDimensional ℂ E] in
theorem isoKerKD_zKd_val (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M))))
    (hz' : twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))) (zKd K hK ρ o cVd) = 0) :
    (isoKerKD K hK extK (Rep.of (permRep ρ (Δ6 M))) ⟨zKd K hK ρ o cVd, hz'⟩).1 = ySd K ρ o cVd := by
  rw [isoKerKD_val]
  change EdgeNat.h2Map (eSK K hK).toMonoidHom (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))))
    (dualRepG (Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M))))) LinearMap.id (fun g v => rfl) (zKd K hK ρ o cVd) = _
  rw [zKd_eq K hK ρ o cVd]
  exact isoKer_toKgen_val K hK (Rep.of (permRep ρ (Δ6 M)).dual) _

/-- `μ` on the classes with vanishing radical restriction, coefficients `E`. -/
def muKer :
    (twoCohomologyRestriction ext'.inl (WK K' ρM hK')).ker →ₗ[ℂ]
      (twoCohomologyRestriction (extStabGen K K' hK' u hmem hback h6 ext').inl
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))).ker :=
  isoKer (ext' := extStabGen K K' hK' u hmem hback h6 ext') (muEquivGen K K' hK' u hmem hback h6).toMonoidHom
    (fun r => FaceTransport.equiv_inl (FaceTransport.pullbackEquiv ext' (muEquivGen K K' hK' u hmem hback h6)) r)
    (W₁ := WK K' ρM hK') (W₂ := AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)) (ρ (u : ↥(gammaN 6)))
    (fun g v => hTgen K K' u hmem ρ ρM hρ hK' g v)

/-- `μ` on the classes with vanishing radical restriction, dual coefficients. -/
def muKerD :
    (twoCohomologyRestriction ext'.inl (dualRepG (WK K' ρM hK'))).ker →ₗ[ℂ]
      (twoCohomologyRestriction (extStabGen K K' hK' u hmem hback h6 ext').inl
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))).ker :=
  isoKerD (ext' := extStabGen K K' hK' u hmem hback h6 ext') (muEquivGen K K' hK' u hmem hback h6).toMonoidHom
    (fun r => FaceTransport.equiv_inl (FaceTransport.pullbackEquiv ext' (muEquivGen K K' hK' u hmem hback h6)) r)
    (W₁ := WK K' ρM hK') (W₂ := AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)) (ρ.dual (u : ↥(gammaN 6)))
    (fun g f => hTgen K K' u hmem ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) hK' g f)

/-- The Mackey coordinate: the pull-back of the restriction of `c₀` to `K'` along `μ`. -/
def cStab (c₀ : groupCohomology.H2 (Rep.of ρM)) :
    groupCohomology.H2 (Rep.of (rhoStab ρ (Δ6 M) (SK K) u)) :=
  EdgeNat.h2Map (muGen K K' u hmem) (WK K' ρM hK') (Rep.of (rhoStab ρ (Δ6 M) (SK K) u))
    (ρ (u : ↥(gammaN 6))) (hTgen K K' u hmem ρ ρM hρ hK')
    (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀)

/-- The Mackey coordinate for the contragredient. -/
def cStabD (c₀' : groupCohomology.H2 (Rep.of ρM.dual)) :
    groupCohomology.H2 (Rep.of (rhoStab ρ.dual (Δ6 M) (SK K) u)) :=
  EdgeNat.h2Map (muGen K K' u hmem) (WK K' ρM.dual hK') (Rep.of (rhoStab ρ.dual (Δ6 M) (SK K) u))
    (ρ.dual (u : ↥(gammaN 6))) (hTgen K K' u hmem ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) hK')
    (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM.dual) c₀')

omit [NeZero M] [FiniteDimensional ℂ E] in
include hK hK' hmem hρ hu in
theorem partF_a
    (c₀ : groupCohomology.H2 (Rep.of ρM)) (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M))))
    (hcV : PhiH ρ (Δ6 M) cV = transportΔ M ρ ρM hρ c₀)
    (hz : twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) (zK K hK ρ o cV) = 0) :
    (aCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cV hz).1 =
      shapiroEquiv ρ (Δ6 M) (SK K) u (cStab K K' hK' u hmem ρ ρM hρ c₀) := by
  classical
  let x : ↥(gammaN 6) ⧸ Δ6 M := (u : ↥(gammaN 6) ⧸ Δ6 M)
  have hqj : ∀ w, h2Hom (qRep ρ (SK K) x) (h2Hom (jRep ρ (SK K) x) w) = w := fun w => by
    rw [← h2Hom_comp, jRep_qRep, h2Hom_id]
  have hcomp : yS K ρ o cV = Theta ρ (Δ6 M) (SK K) u (WK K' ρM hK') (muGen K K' u hmem) (ρ (u : ↥(gammaN 6)))
      (hTgen K K' u hmem ρ ρM hρ hK') (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀) :=
    comp_eq_gen K K' u hmem ρ ρM hρ hK' o hu c₀ cV hcV
  have h0 : (aCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cV hz).1 =
      h2Hom (qRep ρ (SK K) x) (isoKerK K hK extK (Rep.of (permRep ρ (Δ6 M))) ⟨zK K hK ρ o cV, hz⟩).1 := rfl
  rw [h0, isoKerK_zK_val, hcomp]
  exact hqj (shapiroEquiv ρ (Δ6 M) (SK K) u (cStab K K' hK' u hmem ρ ρM hρ c₀))

omit [FiniteDimensional ℂ E] in
include hK hK' hmem hρ hu in
theorem partF_b [Fintype (↥(SK K) ⧸ stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M))]
    (c₀' : groupCohomology.H2 (Rep.of ρM.dual)) (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M))))
    (hcVd : PhiH ρ.dual (Δ6 M) cVd = transportΔ M ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) c₀')
    (hz' : twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))) (zKd K hK ρ o cVd) = 0) :
    (bCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cVd hz').1 =
      h2Hom (dualRepHom (ρ.comp (SK K).subtype) (stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)))
        (shapiroEquiv ρ.dual (Δ6 M) (SK K) u (cStabD K K' hK' u hmem ρ ρM hρ c₀')) := by
  classical
  let x : ↥(gammaN 6) ⧸ Δ6 M := (u : ↥(gammaN 6) ⧸ Δ6 M)
  have hcompd : yS K ρ.dual o cVd = Theta ρ.dual (Δ6 M) (SK K) u (WK K' ρM.dual hK') (muGen K K' u hmem)
      (ρ.dual (u : ↥(gammaN 6))) (hTgen K K' u hmem ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) hK')
      (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM.dual) c₀') :=
    comp_eq_gen K K' u hmem ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) hK' o hu c₀' cVd hcVd
  have h0 : (bCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cVd hz').1 =
      EdgeNat.h2Map (MonoidHom.id ↥(SK K)) (dualRepG (Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M)))))
        (dualRepG (WI (extSK K hK extK) (stabilizer ↥(SK K) x) (ρ.comp (SK K).subtype))) (jDual (SK K) x)
        (fun g f => jDual_equivariant' ρ (SK K) x g f)
        (isoKerKD K hK extK (Rep.of (permRep ρ (Δ6 M))) ⟨zKd K hK ρ o cVd, hz'⟩).1 := rfl
  rw [h0, isoKerKD_zKd_val, ySd_eq, hcompd]
  exact jDual_dualPush ρ (SK K) x (shapiroEquiv ρ.dual (Δ6 M) (SK K) u (cStabD K K' hK' u hmem ρ ρM hρ c₀'))

omit [NeZero M] [FiniteDimensional ℂ E] in
include h6 hK hK' hmem hback hdetK hinl hspl hρ hu in
theorem partF1
    (c₀ : groupCohomology.H2 (Rep.of ρM)) (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M))))
    (hcV : PhiH ρ (Δ6 M) cV = transportΔ M ρ ρM hρ c₀)
    (hz : twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) (zK K hK ρ o cV) = 0)
    (hε : twoCohomologyRestriction ext'.inl (WK K' ρM hK')
      (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀) = 0) :
    kerMapW (compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl) (ρ.comp (SK K).subtype)
        (aCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cV hz) =
      muKer (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6) (ρ := ρ) (ρM := ρM)
        (hρ := hρ) (ext' := ext')
        ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀, hε⟩ := by
  classical
  apply Subtype.ext
  exact (h2Map_stab_eq_PhiH ρ (SK K) (u : ↥(gammaN 6) ⧸ Δ6 M) _).trans
    ((congrArg (PhiH (ρ.comp (SK K).subtype) (stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)))
      (partF_a (K := K) (K' := K') (hK := hK) (hK' := hK') (u := u) (hmem := hmem) (extK := extK) (ρ := ρ) (ρM := ρM)
        (hρ := hρ) (o := o) (hu := hu) c₀ cV hcV hz)).trans
      (PhiH_shapiroEquiv ρ (Δ6 M) (SK K) u (cStab K K' hK' u hmem ρ ρM hρ c₀)))

omit [FiniteDimensional ℂ E] in
include h6 hK hK' hmem hback hdetK hinl hspl hρ hu in
theorem partF2 [Fintype (↥(SK K) ⧸ stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M))]
    (c₀' : groupCohomology.H2 (Rep.of ρM.dual)) (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M))))
    (hcVd : PhiH ρ.dual (Δ6 M) cVd = transportΔ M ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) c₀')
    (hz' : twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))) (zKd K hK ρ o cVd) = 0)
    (hε' : twoCohomologyRestriction ext'.inl (dualRepG (WK K' ρM hK'))
      (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM.dual) c₀') = 0) :
    kerMapWD (compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl) (ρ.comp (SK K).subtype)
        (bCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cVd hz') =
      muKerD (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6) (ρ := ρ) (ρM := ρM)
        (hρ := hρ) (ext' := ext')
        ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM.dual) c₀', hε'⟩ := by
  classical
  apply Subtype.ext
  have hb := partF_b (K := K) (K' := K') (hK := hK) (hK' := hK') (u := u) (hmem := hmem) (extK := extK) (ρ := ρ)
    (ρM := ρM) (hρ := hρ) (o := o) (hu := hu) c₀' cVd hcVd hz'
  exact (congrArg (fun w => EdgeNat.h2Map (stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)).subtype
      (dualRepG (WI (extSK K hK extK) (stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)) (ρ.comp (SK K).subtype)))
      (dualRepG (AS (stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)).subtype (ρ.comp (SK K).subtype)))
      (evTD (extSK K hK extK) (stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)) (stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)).subtype
        (ρ.comp (SK K).subtype))
      (evTD_hT (fun g => g.2) (ρ.comp (SK K).subtype)) w) hb).trans
    ((h2Map_stab_dual_eq_PhiH ρ (SK K) (u : ↥(gammaN 6) ⧸ Δ6 M) _).trans
      (PhiH_shapiroEquiv ρ.dual (Δ6 M) (SK K) u (cStabD K K' hK' u hmem ρ ρM hρ c₀')))

omit [NeZero M] [FiniteDimensional ℂ E] in
include hM h6 hK' hmem hback hρ in
theorem muKer_edge_mem
    (z : (twoCohomologyRestriction ext'.inl (WK K' ρM hK')).ker)
    (hz : splitCohomologyEdge s' (WK K' ρM hK') z ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation s' (WK K' ρM hK'))) :
    splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))
        (muKer (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6) (ρ := ρ) (ρM := ρM)
          (hρ := hρ) (ext' := ext') z) ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))) := by
  have : Fact (3 ≤ M) := ⟨hM⟩
  exact isoKer_edge_mem (s := s') (s' := splStabGen K K' hK' u hmem hback h6 ext' s')
    (ext' := extStabGen K K' hK' u hmem hback h6 ext') (muEquivGen K K' hK' u hmem hback h6).toMonoidHom
    (fun r => FaceTransport.equiv_inl (FaceTransport.pullbackEquiv ext' (muEquivGen K K' hK' u hmem hback h6)) r)
    (fun m => FaceTransport.equiv_splitting (FaceTransport.pullbackEquiv ext' (muEquivGen K K' hK' u hmem hback h6)) s' m)
    (W₁ := WK K' ρM hK') (W₂ := AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)) (ρ (u : ↥(gammaN 6)))
    (fun g v => hTgen K K' u hmem ρ ρM hρ hK' g v) z hz

omit [NeZero M] [FiniteDimensional ℂ E] in
include hM h6 hK' hmem hback hρ in
theorem muKerD_edge_mem
    (z : (twoCohomologyRestriction ext'.inl (dualRepG (WK K' ρM hK'))).ker)
    (hz : splitCohomologyEdge s' (dualRepG (WK K' ρM hK')) z ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation s' (dualRepG (WK K' ρM hK')))) :
    splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))
        (muKerD (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6) (ρ := ρ) (ρM := ρM)
          (hρ := hρ) (ext' := ext') z) ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))) := by
  have : Fact (3 ≤ M) := ⟨hM⟩
  exact isoKerD_edge_mem (s := s') (s' := splStabGen K K' hK' u hmem hback h6 ext' s')
    (ext' := extStabGen K K' hK' u hmem hback h6 ext') (muEquivGen K K' hK' u hmem hback h6).toMonoidHom
    (fun r => FaceTransport.equiv_inl (FaceTransport.pullbackEquiv ext' (muEquivGen K K' hK' u hmem hback h6)) r)
    (fun m => FaceTransport.equiv_splitting (FaceTransport.pullbackEquiv ext' (muEquivGen K K' hK' u hmem hback h6)) s' m)
    (W₁ := WK K' ρM hK') (W₂ := AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)) (ρ.dual (u : ↥(gammaN 6)))
    (fun g f => hTgen K K' u hmem ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) hK' g f) z hz

omit [NeZero M] in
include hM h6 hK' hmem hback hρ in
/-- **Part E**: the canonical face pairing at `K'` of two classes equals the canonical face pairing at the stabilizer of
their `μ`-transports (an isometric comparison, constant `1`). -/
theorem partE (hdet' : ∀ A, radDet (splitRadicalInput s' A) = 1)
    (z : (twoCohomologyRestriction ext'.inl (WK K' ρM hK')).ker)
    (z' : (twoCohomologyRestriction ext'.inl (dualRepG (WK K' ρM hK'))).ker)
    (hz : splitCohomologyEdge s' (WK K' ρM hK') z ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation s' (WK K' ρM hK')))
    (hz' : splitCohomologyEdge s' (dualRepG (WK K' ρM hK')) z' ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation s' (dualRepG (WK K' ρM hK'))))
    (h3 : splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))
        (muKer (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6) (ρ := ρ) (ρM := ρM)
          (hρ := hρ) (ext' := ext') z) ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))))
    (h4 : splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))
        (muKerD (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6) (ρ := ρ) (ρM := ρM)
          (hρ := hρ) (ext' := ext') z') ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))))) :
    facePairingCan hM s' hdet' (WK K' ρM hK') ⟨splitCohomologyEdge s' (WK K' ρM hK') z, hz⟩
        ⟨splitCohomologyEdge s' (dualRepG (WK K' ρM hK')) z', hz'⟩ =
      facePairingCan hM (splStabGen K K' hK' u hmem hback h6 ext' s') (hdetStabGen K K' hK' u hmem hback h6 ext' s' hdet')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))
        ⟨splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
          (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))
          (muKer (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6) (ρ := ρ)
            (ρM := ρM) (hρ := hρ) (ext' := ext') z), h3⟩
        ⟨splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
          (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))
          (muKerD (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6) (ρ := ρ)
            (ρM := ρM) (hρ := hρ) (ext' := ext') z'), h4⟩ := by
  have : Fact (3 ≤ M) := ⟨hM⟩
  exact facePairingCan_iso_edge (s := s') (s' := splStabGen K K' hK' u hmem hback h6 ext' s')
    (ext' := extStabGen K K' hK' u hmem hback h6 ext') (muEquivGen K K' hK' u hmem hback h6).toMonoidHom
    (fun r => FaceTransport.equiv_inl (FaceTransport.pullbackEquiv ext' (muEquivGen K K' hK' u hmem hback h6)) r)
    (fun m => FaceTransport.equiv_splitting (FaceTransport.pullbackEquiv ext' (muEquivGen K K' hK' u hmem hback h6)) s' m)
    (W₁ := WK K' ρM hK') (W₂ := AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)) (ρ (u : ↥(gammaN 6)))
    (ρ.dual (u : ↥(gammaN 6)))
    (fun g v => hTgen K K' u hmem ρ ρM hρ hK' g v)
    (fun g f => hTgen K K' u hmem ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) hK' g f)
    (fun a b => by
      change (ρ.dual (u : ↥(gammaN 6)) b) (ρ (u : ↥(gammaN 6)) a) = b a
      show b ((ρ (u : ↥(gammaN 6))⁻¹) (ρ (u : ↥(gammaN 6)) a)) = b a
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl)
    (hdet') (hdetStabGen K K' hK' u hmem hback h6 ext' s' hdet') z z' hz hz' h3 h4

include hM h6 hK hK' hmem hback hdetK hdet' hinl hspl hρ hu in
/-- **The generic orbit identification.**  The canonical face pairing at `K` of the orbit components of the induced
classes equals the canonical face pairing at `K'` of the restrictions of the base classes `c₀`, `c₀'`; the constant is
exactly `1` (the Koszul factor `m0^2` of `altForm_gen` cancels the size `m0^2` of the radical-lattice orbits). -/
theorem orbit_ident_gen
    (c₀ : groupCohomology.H2 (Rep.of ρM)) (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M))))
    (hcV : PhiH ρ (Δ6 M) cV = transportΔ M ρ ρM hρ c₀)
    (c₀' : groupCohomology.H2 (Rep.of ρM.dual)) (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M))))
    (hcVd : PhiH ρ.dual (Δ6 M) cVd = transportΔ M ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) c₀')
    (hz : twoCohomologyRestriction extK.inl (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) (zK K hK ρ o cV) = 0)
    (hzc : splitCohomologyEdge sK (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) ⟨zK K hK ρ o cV, hz⟩ ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma 6) (splitRadicalH1Representation sK (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))))
    (hz' : twoCohomologyRestriction extK.inl (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))) (zKd K hK ρ o cVd) = 0)
    (hzc' : splitCohomologyEdge sK (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))) ⟨zKd K hK ρ o cVd, hz'⟩ ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma 6)
        (splitRadicalH1Representation sK (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))))))
    (hε : twoCohomologyRestriction ext'.inl (WK K' ρM hK')
      (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀) = 0)
    (hεc : splitCohomologyEdge s' (WK K' ρM hK') ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀, hε⟩ ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation s' (WK K' ρM hK')))
    (hε' : twoCohomologyRestriction ext'.inl (dualRepG (WK K' ρM hK'))
      (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM.dual) c₀') = 0)
    (hεc' : splitCohomologyEdge s' (dualRepG (WK K' ρM hK'))
        ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM.dual) c₀', hε'⟩ ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation s' (dualRepG (WK K' ρM hK')))) :
    facePairingCan (by norm_num : 3 ≤ 6) sK hdetK (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))
        ⟨splitCohomologyEdge sK (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M)))) ⟨zK K hK ρ o cV, hz⟩, hzc⟩
        ⟨splitCohomologyEdge sK (dualRepG (Rep.res (inclK K hK) (Rep.of (permRep ρ (Δ6 M))))) ⟨zKd K hK ρ o cVd, hz'⟩, hzc'⟩ =
      facePairingCan hM s' hdet' (WK K' ρM hK')
        ⟨splitCohomologyEdge s' (WK K' ρM hK') ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀, hε⟩, hεc⟩
        ⟨splitCohomologyEdge s' (dualRepG (WK K' ρM hK'))
          ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM.dual) c₀', hε'⟩, hεc'⟩ := by
  classical
  have : Fintype (↥(SK K) ⧸ stabilizer ↥(SK K) (u : ↥(gammaN 6) ⧸ Δ6 M)) := Fintype.ofFinite _
  have f1 := partF1 (K := K) (K' := K') (hK := hK) (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6)
    (extK := extK) (sK := sK) (hdetK := hdetK) (ext' := ext') (s' := s') (hinl := hinl) (hspl := hspl) (ρ := ρ)
    (ρM := ρM) (hρ := hρ) (o := o) (hu := hu) c₀ cV hcV hz hε
  have f2 := partF2 (K := K) (K' := K') (hK := hK) (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6)
    (extK := extK) (sK := sK) (hdetK := hdetK) (ext' := ext') (s' := s') (hinl := hinl) (hspl := hspl) (ρ := ρ)
    (ρM := ρM) (hρ := hρ) (o := o) (hu := hu) c₀' cVd hcVd hz' hε'
  have h3 := muKer_edge_mem (hM := hM) (h6 := h6) (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (ext' := ext') (s' := s') (ρ := ρ) (ρM := ρM) (hρ := hρ)
    ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀, hε⟩ hεc
  have h4 := muKerD_edge_mem (hM := hM) (h6 := h6) (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (ext' := ext') (s' := s') (ρ := ρ) (ρM := ρM) (hρ := hρ)
    ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM.dual) c₀', hε'⟩ hεc'
  have m1 : splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))
        (kerMapW (compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl) (ρ.comp (SK K).subtype)
          (aCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cV hz)) ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))) := by
    rw [f1]; exact h3
  have m2 : splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))
        (kerMapWD (compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl) (ρ.comp (SK K).subtype)
          (bCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cVd hz')) ∈
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))) := by
    rw [f2]; exact h4
  have hA := partA (hM := hM) (h6 := h6) (K := K) (K' := K') (hK := hK) (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (extK := extK) (sK := sK) (hdetK := hdetK) (ext' := ext') (s' := s') (hdet' := hdet') (hinl := hinl) (hspl := hspl) (ρ := ρ) (o := o) (hu := hu) cV cVd hz hzc hz' hzc' m1 m2
  have hE := partE (hM := hM) (h6 := h6) (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (ext' := ext') (s' := s') (ρ := ρ) (ρM := ρM) (hρ := hρ) hdet'
    ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀, hε⟩
    ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM.dual) c₀', hε'⟩ hεc hεc' h3 h4
  have e1 : (⟨splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))
        (kerMapW (compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl) (ρ.comp (SK K).subtype)
          (aCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cV hz)), m1⟩ :
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))) =
      ⟨splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))
        (muKer (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6) (ρ := ρ)
          (ρM := ρM) (hρ := hρ) (ext' := ext')
          ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀, hε⟩), h3⟩ :=
    Subtype.ext (congrArg (fun w => splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
      (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)) w) f1)
  have e2 : (⟨splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))
        (kerMapWD (compat_gen K K' hK hK' u hmem hback h6 extK sK ext' s' hdetK hinl hspl) (ρ.comp (SK K).subtype)
          (bCls (K := K) (hK := hK) (extK := extK) (ρ := ρ) (o := o) (u := u) cVd hz')), m2⟩ :
      cuspidalSubspace (CongruenceSubgroup.Gamma M) (splitRadicalH1Representation (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))))) =
      ⟨splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
        (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)))
        (muKerD (K := K) (K' := K') (hK' := hK') (u := u) (hmem := hmem) (hback := hback) (h6 := h6) (ρ := ρ)
          (ρM := ρM) (hρ := hρ) (ext' := ext')
          ⟨twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM.dual) c₀', hε'⟩), h4⟩ :=
    Subtype.ext (congrArg (fun w => splitCohomologyEdge (splStabGen K K' hK' u hmem hback h6 ext' s')
      (dualRepG (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype))) w) f2)
  have hB := congrArg₂ (fun p q => facePairingCan hM (splStabGen K K' hK' u hmem hback h6 ext' s')
      (hdetStabGen K K' hK' u hmem hback h6 ext' s' hdet') (AS (StabK (M := M) K u).subtype (ρ.comp (SK K).subtype)) p q) e1 e2
  exact (hA.trans hB).trans hE.symm

end Main

end TernaryPeriodPolynomials.Argument.RadicalInduction
