module

public import TernaryPeriodPolynomials.GroupCohomology.Koszul.Alg
public import TernaryPeriodPolynomials.GroupCohomology.Koszul.PermHom
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.PermProjective
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

@[expose] public section


/-!
# The Koszul resolution of `ℤ²` and the group homology of `ℤ²` in degrees `2` and `≥ 3`

Formalized by Claude Sonnet 5.5.

`U2 = Multiplicative (Fin 2 → ℤ)`.  The complex `0 → ℚ[U2] → ℚ[U2]^2 → ℚ[U2] → ℚ → 0` with
`d₁[(i, v)] = [v + e_i] - [v]` and `d₂[v] = -[(0, v + e_1)] + [(0, v)] + [(1, v + e_0)] - [(1, v)]` is a projective resolution of the
trivial representation (`kResolution`).  Exactness is proved by the explicit `ℚ`-linear contraction `H0, H1, Sig` assembled from the
one-variable contractions of `KoszulAlg` (`K_contract0`, `K_contract1`, `K_contract2`).

Consequences, with trivial `ℚ`-coefficients: `Hₙ(ℤ², M) = 0` for `n ≥ 3` (`isZero_groupHomology_U2`, any `M`) and
`dim H₂(ℤ², ℚ) ≤ 1` (`rank_groupHomology_U2_two`).  Together with the cycle `[e₁|e₂] - [e₂|e₁]` (later files) this identifies `H₂(ℤ², ℚ)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomologyDescent

open CategoryTheory Representation Rep
open scoped MonoidAlgebra

/-! ### The Koszul complex of `ℤ²` as a complex of `U₂`-representations -/


abbrev T2 := Fin 2 → ℤ
abbrev U2 := Multiplicative T2

/-- Index set of the middle term. -/
abbrev KI := Fin 2 × T2

instance : MulAction U2 KI where
  smul u p := (p.1, Multiplicative.toAdd u + p.2)
  one_smul p := by
    show (p.1, Multiplicative.toAdd (1 : U2) + p.2) = p
    simp
  mul_smul u w p := by
    show (p.1, Multiplicative.toAdd (u * w) + p.2) = (p.1, Multiplicative.toAdd u + (Multiplicative.toAdd w + p.2))
    simp [add_assoc]

theorem KI_smul (u : U2) (i : Fin 2) (v : T2) : u • ((i, v) : KI) = (i, Multiplicative.toAdd u + v) := rfl

theorem T2_smul (u : U2) (v : T2) : u • v = Multiplicative.toAdd u + v := rfl

/-- `ℚ[ℤ²]` as a finitely supported function. -/
abbrev Q1 := KI →₀ ℚ

/-- Inclusion of the `i`-th summand. -/
def iota (i : Fin 2) : R →ₗ[ℚ] Q1 := Finsupp.lmapDomain ℚ ℚ (fun v => ((i, v) : KI))

/-- Projection to the `i`-th summand. -/
def proj (i : Fin 2) : Q1 →ₗ[ℚ] R :=
  Finsupp.lsum ℚ fun p : KI => if p.1 = i then Finsupp.lsingle p.2 else 0

theorem iota_single (i : Fin 2) (v : T2) (r : ℚ) :
    iota i (Finsupp.single v r) = Finsupp.single ((i, v) : KI) r := by
  simp [iota]

theorem proj_single (i : Fin 2) (j : Fin 2) (v : T2) (r : ℚ) :
    proj i (Finsupp.single ((j, v) : KI) r) = if j = i then Finsupp.single v r else 0 := by
  simp [proj]
  split_ifs <;> simp

theorem proj_iota (i j : Fin 2) (f : R) : proj i (iota j f) = if j = i then f else 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]; split_ifs <;> try simp
  | single v r => rw [iota_single, proj_single]

theorem iota_proj_add (ξ : Q1) : iota 0 (proj 0 ξ) + iota 1 (proj 1 ξ) = ξ := by
  induction ξ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, add_add_add_comm, ha, hb]
  | single p r =>
    obtain ⟨j, v⟩ := p
    rw [proj_single, proj_single]
    fin_cases j <;> simp [iota_single]

/-- The boundary `d₁`: `[(i, v)] ↦ [v + e_i] - [v]`. -/
def D1 : Q1 →ₗ[ℚ] R := Finsupp.lsum ℚ fun p : KI => LinearMap.toSpanSingleton ℚ R
    (Finsupp.single (p.2 + Pi.single p.1 1) 1 - Finsupp.single p.2 1)

/-- `t_i - 1` as a linear map. -/
def DlL (i : Fin 2) : R →ₗ[ℚ] R := Tm i - LinearMap.id

theorem DlL_apply (i : Fin 2) (f : R) : DlL i f = Tm i f - f := rfl

/-- The boundary `d₂`. -/
def D2 : R →ₗ[ℚ] Q1 := -(iota 0 ∘ₗ DlL 1) + iota 1 ∘ₗ DlL 0

theorem D2_apply (z : R) : D2 z = -iota 0 (Tm 1 z - z) + iota 1 (Tm 0 z - z) := rfl

/-- The contraction in degree `0`. -/
def H0 : R →ₗ[ℚ] Q1 := iota 0 ∘ₗ sh 0 + iota 1 ∘ₗ sh 1 ∘ₗ epsi 0

/-- The contraction in degree `1`. -/
def H1 : Q1 →ₗ[ℚ] R := sh 0 ∘ₗ proj 1

/-- The base point. -/
def Sig : ℚ →ₗ[ℚ] R := LinearMap.toSpanSingleton ℚ R (Finsupp.single 0 1)

theorem D1_single (i : Fin 2) (v : T2) (r : ℚ) :
    D1 (Finsupp.single ((i, v) : KI) r) = Tm i (Finsupp.single v r) - Finsupp.single v r := by
  simp [D1, Tm_single, Finsupp.smul_single, smul_sub]

theorem D1_iota (i : Fin 2) (f : R) : D1 (iota i f) = Tm i f - f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]; abel
  | single v r => rw [iota_single, D1_single]

theorem Tm_comm (i j : Fin 2) (f : R) : Tm i (Tm j f) = Tm j (Tm i f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | single v r => rw [Tm_single, Tm_single, Tm_single, Tm_single, add_right_comm]

theorem D1_D2 (z : R) : D1 (D2 z) = 0 := by
  rw [D2_apply, map_add, map_neg, D1_iota, D1_iota, map_sub, map_sub, Tm_comm 0 1 z]
  abel

theorem K_eps_sig : aug (Sig 1) = 1 := by
  simp [Sig, aug_single]

theorem K_contract0 (w : R) : D1 (H0 w) + Sig (aug w) = w := by
  have h1 := Tm_sub_sh 0 w
  have h2 := Tm_sub_sh 1 (epsi 0 w)
  have h3 := epsi_one_epsi_zero w
  simp only [H0, LinearMap.add_apply, LinearMap.comp_apply, map_add, D1_iota, Sig, LinearMap.toSpanSingleton_apply]
  rw [h1, h2, h3]
  abel

theorem K_contract1_iota0 (x : R) : H0 (D1 (iota 0 x)) + D2 (H1 (iota 0 x)) = iota 0 x := by
  have e3 : proj 1 (iota 0 x) = 0 := by rw [proj_iota]; simp
  have e1 : sh 0 (Tm 0 x - x) = x := sh_Tm_sub 0 x
  have e2 : epsi 0 (Tm 0 x - x) = 0 := epsi_Tm_sub 0 x
  rw [D1_iota]
  simp only [H0, H1, LinearMap.add_apply, LinearMap.comp_apply, e3, e1, e2, map_zero, add_zero]

theorem K_contract1_iota1 (y : R) : H0 (D1 (iota 1 y)) + D2 (H1 (iota 1 y)) = iota 1 y := by
  have e1 : sh 0 (Tm 1 y - y) = Tm 1 (sh 0 y) - sh 0 y := by
    rw [map_sub, sh_Tm_comm 0 1 (by decide)]
  have e2 : epsi 0 (Tm 1 y - y) = Tm 1 (epsi 0 y) - epsi 0 y := by
    rw [map_sub, epsi_Tm_comm 0 1 (by decide)]
  have e3 : proj 1 (iota 1 y) = y := by rw [proj_iota]; simp
  have e4 : sh 1 (Tm 1 (epsi 0 y) - epsi 0 y) = epsi 0 y := sh_Tm_sub 1 _
  have e5 := Tm_sub_sh 0 y
  have hH : H0 (D1 (iota 1 y)) = iota 0 (Tm 1 (sh 0 y) - sh 0 y) + iota 1 (epsi 0 y) := by
    rw [D1_iota]
    simp only [H0, LinearMap.add_apply, LinearMap.comp_apply, e1, e2, e4]
  have hD : D2 (H1 (iota 1 y)) = -iota 0 (Tm 1 (sh 0 y) - sh 0 y) + iota 1 (y - epsi 0 y) := by
    simp only [H1, LinearMap.comp_apply, e3, D2_apply, e5]
  rw [hH, hD]
  simp only [map_sub]
  abel
theorem K_contract1 (ξ : Q1) : H0 (D1 ξ) + D2 (H1 ξ) = ξ := by
  have h := iota_proj_add ξ
  have a0 := K_contract1_iota0 (proj 0 ξ)
  have a1 := K_contract1_iota1 (proj 1 ξ)
  calc H0 (D1 ξ) + D2 (H1 ξ)
      = H0 (D1 (iota 0 (proj 0 ξ) + iota 1 (proj 1 ξ))) + D2 (H1 (iota 0 (proj 0 ξ) + iota 1 (proj 1 ξ))) := by
        rw [h]
    _ = (H0 (D1 (iota 0 (proj 0 ξ))) + D2 (H1 (iota 0 (proj 0 ξ)))) +
          (H0 (D1 (iota 1 (proj 1 ξ))) + D2 (H1 (iota 1 (proj 1 ξ)))) := by
        simp only [map_add]; abel
    _ = iota 0 (proj 0 ξ) + iota 1 (proj 1 ξ) := by rw [a0, a1]
    _ = ξ := h

theorem K_contract2 (z : R) : H1 (D2 z) = z := by
  have e3 : proj 1 (iota 0 (Tm 1 z - z)) = 0 := by rw [proj_iota]; simp
  have e4 : proj 1 (iota 1 (Tm 0 z - z)) = Tm 0 z - z := by rw [proj_iota]; simp
  rw [D2_apply]
  simp only [H1, LinearMap.comp_apply, map_add, map_neg, e3, e4, map_zero, neg_zero, zero_add]
  exact sh_Tm_sub 0 z




/-! ### The Koszul complex as a complex of representations -/

section KosRep

theorem lift_eq {X : Type} {M : Type} [AddCommGroup M] [Module ℚ M] (L : (X →₀ ℚ) →ₗ[ℚ] M) :
    Finsupp.lift M ℚ X (fun x => L (Finsupp.single x 1)) = L := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp

theorem permHom_hom_apply {G : Type} [Group G] {X Y : Type} [MulAction G X] [MulAction G Y]
    (L : (X →₀ ℚ) →ₗ[ℚ] (Y →₀ ℚ))
    (hc : ∀ (g : G) (x : X), L (Finsupp.single (g • x) 1) =
      Finsupp.mapDomain (fun y => g • y) (L (Finsupp.single x 1))) (f : ℚ[X]) :
    (permHom (fun x => L (Finsupp.single x 1)) hc).hom f =
      (MonoidAlgebra.coeffLinearEquiv ℚ).symm (L (MonoidAlgebra.coeffLinearEquiv ℚ f)) := by
  change permLin (fun x => L (Finsupp.single x 1)) f = _
  simp [permLin, lift_eq]

abbrev X0 : Rep ℚ U2 := Rep.ofMulAction ℚ U2 T2
abbrev X1 : Rep ℚ U2 := Rep.ofMulAction ℚ U2 KI

theorem mapDomain_single' {α β : Type} (f : α → β) (a : α) (r : ℚ) :
    Finsupp.mapDomain f (Finsupp.single a r) = Finsupp.single (f a) r := Finsupp.mapDomain_single

theorem md_sub {α β : Type} (f : α → β) (a b : α →₀ ℚ) :
    Finsupp.mapDomain f (a - b) = Finsupp.mapDomain f a - Finsupp.mapDomain f b :=
  (Finsupp.mapDomain.addMonoidHom f).map_sub a b

theorem md_neg {α β : Type} (f : α → β) (a : α →₀ ℚ) :
    Finsupp.mapDomain f (-a) = -Finsupp.mapDomain f a :=
  (Finsupp.mapDomain.addMonoidHom f).map_neg a

theorem md_add {α β : Type} (f : α → β) (a b : α →₀ ℚ) :
    Finsupp.mapDomain f (a + b) = Finsupp.mapDomain f a + Finsupp.mapDomain f b :=
  Finsupp.mapDomain_add

theorem hD1 (g : U2) (p : KI) :
    D1 (Finsupp.single (g • p) 1) = Finsupp.mapDomain (fun y : T2 => g • y) (D1 (Finsupp.single p 1)) := by
  obtain ⟨i, v⟩ := p
  rw [KI_smul, D1_single, D1_single, Tm_single, Tm_single, md_sub, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single]
  simp only [T2_smul]
  rw [add_assoc]

theorem hD2 (g : U2) (v : T2) :
    D2 (Finsupp.single (g • v) 1) = Finsupp.mapDomain (fun y : KI => g • y) (D2 (Finsupp.single v 1)) := by
  rw [D2_apply, D2_apply]
  simp only [Tm_single, map_sub, iota_single, md_add, md_neg, md_sub, Finsupp.mapDomain_single, KI_smul,
    T2_smul, add_assoc]

/-- The Koszul differential `X1 → X0`. -/
def kd1 : X1 ⟶ X0 := permHom (fun p => D1 (Finsupp.single p 1)) hD1

/-- The Koszul differential `X0 → X1`. -/
def kd2 : X0 ⟶ X1 := permHom (fun v => D2 (Finsupp.single v 1)) hD2

theorem kd1_apply (f : ℚ[KI]) :
    kd1.hom f = (MonoidAlgebra.coeffLinearEquiv ℚ).symm (D1 (MonoidAlgebra.coeffLinearEquiv ℚ f)) :=
  permHom_hom_apply D1 hD1 f

theorem kd2_apply (f : ℚ[T2]) :
    kd2.hom f = (MonoidAlgebra.coeffLinearEquiv ℚ).symm (D2 (MonoidAlgebra.coeffLinearEquiv ℚ f)) :=
  permHom_hom_apply D2 hD2 f

end KosRep


/-! ### Resolution -/

section Res

open ZeroObject CategoryTheory.Limits

theorem aug_D1 (ξ : Q1) : aug (D1 ξ) = 0 := by
  induction ξ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | single p r =>
    obtain ⟨i, v⟩ := p
    rw [D1_single, map_sub, Tm_single, aug_single, aug_single, sub_self]

/-- The augmentation `ℚ[ℤ²] → ℚ`. -/
def kEps : X0 ⟶ Rep.trivial ℚ U2 ℚ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := X0.ρ) (σ := (Rep.trivial ℚ U2 ℚ).ρ)
    (aug ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
    (fun g v => by
      have key : (aug ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ∘ₗ
          (Representation.ofMulAction ℚ U2 T2 g) = aug ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap := by
        refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
        simp [Representation.ofMulAction_single, aug_single]
      exact LinearMap.congr_fun key v))

theorem kEps_apply (f : ℚ[T2]) : kEps.hom f = aug (MonoidAlgebra.coeffLinearEquiv ℚ f) := rfl

theorem kd2_kd1 : kd2 ≫ kd1 = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change kd1.hom (kd2.hom f) = 0
  rw [kd2_apply, kd1_apply]
  simp [D1_D2]

theorem kd1_kEps : kd1 ≫ kEps = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change kEps.hom (kd1.hom f) = 0
  rw [kd1_apply, kEps_apply]
  simp [aug_D1]

/-- The terms of the Koszul complex. -/
def kX : ℕ → Rep ℚ U2
  | 0 => X0
  | 1 => X1
  | 2 => X0
  | _ + 3 => 0

/-- The differentials of the Koszul complex. -/
def kD : ∀ n : ℕ, kX (n + 1) ⟶ kX n
  | 0 => kd1
  | 1 => kd2
  | _ + 2 => 0

/-- The Koszul complex of `ℤ²`. -/
def kComplex : ChainComplex (Rep ℚ U2) ℕ :=
  ChainComplex.of kX kD (fun n => by
    match n with
    | 0 => exact kd2_kd1
    | 1 => exact zero_comp
    | _ + 2 => exact zero_comp)


open TernaryPeriodPolynomials.Argument.BinaryDuality (ofMulAction_projective)

theorem T2_stab_subsingleton (v : T2) : Subsingleton (MulAction.stabilizer U2 v) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  have ha : (a : U2) • v = v := MulAction.mem_stabilizer_iff.mp a.2
  have hb : (b : U2) • v = v := MulAction.mem_stabilizer_iff.mp b.2
  rw [T2_smul] at ha hb
  have : Multiplicative.toAdd (a : U2) = Multiplicative.toAdd (b : U2) := by
    have := ha.trans hb.symm
    exact add_right_cancel this
  exact Multiplicative.toAdd.injective this

theorem KI_stab_subsingleton (p : KI) : Subsingleton (MulAction.stabilizer U2 p) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  have ha : (a : U2) • p = p := MulAction.mem_stabilizer_iff.mp a.2
  have hb : (b : U2) • p = p := MulAction.mem_stabilizer_iff.mp b.2
  obtain ⟨i, v⟩ := p
  rw [KI_smul] at ha hb
  have ha' := congrArg Prod.snd ha
  have hb' := congrArg Prod.snd hb
  have : Multiplicative.toAdd (a : U2) = Multiplicative.toAdd (b : U2) := by
    have := ha'.trans hb'.symm
    exact add_right_cancel this
  exact Multiplicative.toAdd.injective this

instance X0_projective : Projective X0 :=
  ofMulAction_projective (fun v => haveI := T2_stab_subsingleton v; inferInstance)

instance X1_projective : Projective X1 :=
  ofMulAction_projective (fun p => haveI := KI_stab_subsingleton p; inferInstance)

instance kProjective (n : ℕ) : Projective (kComplex.X n) := by
  change Projective (kX n)
  match n with
  | 0 => exact X0_projective
  | 1 => exact X1_projective
  | 2 => exact X0_projective
  | n + 3 => exact (isZero_zero (Rep ℚ U2)).projective

/-- The augmentation of the Koszul complex. -/
def kPi : kComplex ⟶ (ChainComplex.single₀ (Rep ℚ U2)).obj (Rep.trivial ℚ U2 ℚ) :=
  ((ChainComplex.toSingle₀Equiv kComplex _)).symm ⟨kEps, by
    simp only [kComplex]
    exact kd1_kEps⟩


theorem k_exact0 (f : ℚ[T2]) (hf : kEps.hom f = 0) : ∃ ξ : ℚ[KI], kd1.hom ξ = f := by
  set w := MonoidAlgebra.coeffLinearEquiv ℚ f with hw
  refine ⟨(MonoidAlgebra.coeffLinearEquiv ℚ).symm (H0 w), ?_⟩
  rw [kd1_apply, LinearEquiv.apply_symm_apply]
  have h := K_contract0 w
  have haug : aug w = 0 := by rw [← kEps_apply] at *; exact hf
  rw [haug, map_zero, add_zero] at h
  rw [h, hw]
  exact LinearEquiv.symm_apply_apply _ _

theorem k_exact1 (ξ : ℚ[KI]) (hξ : kd1.hom ξ = 0) : ∃ z : ℚ[T2], kd2.hom z = ξ := by
  set x := MonoidAlgebra.coeffLinearEquiv ℚ ξ with hx
  have h0 : D1 x = 0 := by
    rw [kd1_apply] at hξ
    have := (MonoidAlgebra.coeffLinearEquiv ℚ).symm.injective (a₂ := 0) (by simpa using hξ)
    simpa [hx] using this
  refine ⟨(MonoidAlgebra.coeffLinearEquiv ℚ).symm (H1 x), ?_⟩
  rw [kd2_apply, LinearEquiv.apply_symm_apply]
  have h := K_contract1 x
  rw [h0, map_zero, zero_add] at h
  rw [h, hx]
  exact LinearEquiv.symm_apply_apply _ _

theorem kd2_injective : Function.Injective kd2.hom := by
  intro a b hab
  rw [kd2_apply, kd2_apply] at hab
  have := (MonoidAlgebra.coeffLinearEquiv ℚ).symm.injective hab
  have h2 := congrArg H1 this
  rw [K_contract2, K_contract2] at h2
  exact (MonoidAlgebra.coeffLinearEquiv ℚ).injective h2

theorem kEps_surjective : Function.Surjective kEps.hom := by
  intro r
  refine ⟨MonoidAlgebra.single (0 : T2) r, ?_⟩
  rw [kEps_apply]
  have : (MonoidAlgebra.coeffLinearEquiv ℚ) (MonoidAlgebra.single (0 : T2) r) = Finsupp.single 0 r := rfl
  rw [this, aug_single]

theorem kPi_quasiIso : QuasiIso kPi where
  quasiIsoAt m := by
    induction m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      constructor
      · apply (forget₂ _ (ModuleCat ℚ)).reflects_exact_of_faithful
        rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        ext c
        change c ∈ LinearMap.range kd1.hom.toLinearMap ↔ c ∈ LinearMap.ker kEps.hom.toLinearMap
        constructor
        · rintro ⟨a, rfl⟩
          have h : kEps.hom (kd1.hom a) = 0 := by simpa using congrArg (fun φ => φ.hom a) kd1_kEps
          exact h
        · intro hc
          exact k_exact0 c hc
      · rw [Rep.epi_iff_surjective]
        exact kEps_surjective
    | succ m _ =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
      cases m with
      | zero =>
        apply (forget₂ _ (ModuleCat ℚ)).reflects_exact_of_faithful
        rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        ext c
        change c ∈ LinearMap.range kd2.hom.toLinearMap ↔ c ∈ LinearMap.ker kd1.hom.toLinearMap
        constructor
        · rintro ⟨a, rfl⟩
          have h : kd1.hom (kd2.hom a) = 0 := by simpa using congrArg (fun φ => φ.hom a) kd2_kd1
          exact h
        · intro hc
          exact k_exact1 c hc
      | succ m =>
        cases m with
        | zero =>
          have h21 : (HomologicalComplex.sc' kComplex (1 + 2) (1 + 1) 1).f = 0 :=
            ChainComplex.of_d kX kD 2
          rw [ShortComplex.exact_iff_mono _ h21]
          change Mono (kComplex.d 2 1)
          have h10 : kComplex.d 2 1 = kd2 := ChainComplex.of_d kX kD 1
          rw [h10]
          exact (Rep.mono_iff_injective kd2).mpr kd2_injective
        | succ m =>
          apply ShortComplex.exact_of_isZero_X₂
          exact isZero_zero (Rep ℚ U2)

/-- The Koszul complex as a projective resolution of the trivial representation of `ℤ²`. -/
def kResolution : ProjectiveResolution (Rep.trivial ℚ U2 ℚ) where
  complex := kComplex
  projective := kProjective
  π := kPi
  quasiIso := kPi_quasiIso


/-! ### Group homology of `ℤ²` in degrees `2` and `≥ 3` -/

/-- Group homology of `ℤ²` computed by the Koszul complex. -/
def groupHomologyKoszul (M : Rep ℚ U2) (n : ℕ) :
    groupHomology M n ≅ (kResolution.complex.coinvariantsTensorObj M).homology n :=
  groupHomologyIso M n kResolution

theorem isZero_groupHomology_U2 (M : Rep ℚ U2) (n : ℕ) : IsZero (groupHomology M (n + 3)) := by
  refine IsZero.of_iso ?_ (groupHomologyKoszul M (n + 3))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 4) (n + 3) (n + 2) (by simp) (by simp)]
  apply ShortComplex.exact_of_isZero_X₂
  exact Functor.map_isZero ((Rep.coinvariantsTensor ℚ U2).obj M) (isZero_zero (Rep ℚ U2))


/-- The generator of `(1 ⊗ ℚ[ℤ²])_{ℤ²}`. -/
def kf : ℚ →ₗ[ℚ] ↑(((Rep.coinvariantsTensor ℚ U2).obj (Rep.trivial ℚ U2 ℚ)).obj X0) :=
  (Rep.coinvariantsTensorMk (Rep.trivial ℚ U2 ℚ) X0 (1 : ℚ)) ∘ₗ MonoidAlgebra.lsingle (0 : T2)

theorem kf_surjective : Function.Surjective kf := by
  have key : ∀ w : TensorProduct ℚ (Rep.trivial ℚ U2 ℚ) X0,
      Coinvariants.mk ((Rep.trivial ℚ U2 ℚ).ρ.tprod X0.ρ) w ∈ LinearMap.range kf := by
    intro w
    induction w using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul a x =>
      induction x using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add]; exact Submodule.add_mem _ hx hy
      | single v s =>
        have h := Coinvariants.mk_self_apply ((Rep.trivial ℚ U2 ℚ).ρ.tprod X0.ρ)
          (Multiplicative.ofAdd (-v) : U2) (a ⊗ₜ[ℚ] MonoidAlgebra.single v s)
        rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.ofMulAction_single] at h
        have e : (Multiplicative.ofAdd (-v) : U2) • v = (0 : T2) := by
          rw [T2_smul]; simp
        rw [e] at h
        refine ⟨a * s, ?_⟩
        have h' : Coinvariants.mk ((Rep.trivial ℚ U2 ℚ).ρ.tprod X0.ρ)
            (a ⊗ₜ[ℚ] MonoidAlgebra.single (0 : T2) s) =
            Coinvariants.mk ((Rep.trivial ℚ U2 ℚ).ρ.tprod X0.ρ) (a ⊗ₜ[ℚ] MonoidAlgebra.single v s) := by
          rw [← h]; rfl
        rw [← h']
        change Rep.coinvariantsTensorMk (Rep.trivial ℚ U2 ℚ) X0 (1 : ℚ)
          (MonoidAlgebra.single (0 : T2) (a * s)) = _
        have : MonoidAlgebra.single (0 : T2) (a * s) = a • MonoidAlgebra.single (0 : T2) s := by
          rw [MonoidAlgebra.smul_single']
        rw [this, map_smul]
        change a • Coinvariants.mk ((Rep.trivial ℚ U2 ℚ).ρ.tprod X0.ρ)
          ((1 : ℚ) ⊗ₜ[ℚ] MonoidAlgebra.single (0 : T2) s) = _
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  intro z
  obtain ⟨w, rfl⟩ := Coinvariants.mk_surjective _ z
  exact key w


theorem rank_coinv_X0 :
    Module.rank ℚ ↑(((Rep.coinvariantsTensor ℚ U2).obj (Rep.trivial ℚ U2 ℚ)).obj X0) ≤ 1 := by
  calc Module.rank ℚ ↑(((Rep.coinvariantsTensor ℚ U2).obj (Rep.trivial ℚ U2 ℚ)).obj X0)
      ≤ Module.rank ℚ ℚ := LinearMap.rank_le_of_surjective kf kf_surjective
    _ = 1 := Module.rank_self ℚ

theorem rank_groupHomology_U2_two : Module.rank ℚ (groupHomology (Rep.trivial ℚ U2 ℚ) 2) ≤ 1 := by
  have e := (groupHomologyKoszul (Rep.trivial ℚ U2 ℚ) 2)
  let C := kResolution.complex.coinvariantsTensorObj (Rep.trivial ℚ U2 ℚ)
  set S := C.sc 2 with hS
  have h1 : Module.rank ℚ S.X₂ ≤ 1 := rank_coinv_X0
  have h2 : Module.rank ℚ S.cycles ≤ Module.rank ℚ S.X₂ :=
    LinearMap.rank_le_of_injective S.iCycles.hom
      ((ModuleCat.mono_iff_injective S.iCycles).mp inferInstance)
  have h3 : Module.rank ℚ S.homology ≤ Module.rank ℚ S.cycles :=
    LinearMap.rank_le_of_surjective S.homologyπ.hom ((ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance)
  have h4 : Module.rank ℚ (groupHomology (Rep.trivial ℚ U2 ℚ) 2) =
      Module.rank ℚ S.homology :=
    LinearEquiv.rank_eq (e.toLinearEquiv)
  rw [h4]
  exact h3.trans (h2.trans h1)

end Res


end TernaryPeriodPolynomials.Argument.GroupHomologyDescent
