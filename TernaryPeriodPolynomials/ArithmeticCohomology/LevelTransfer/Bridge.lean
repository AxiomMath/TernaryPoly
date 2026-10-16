module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InhomogeneousResolution
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.AmbientResolution
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Transfer
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Order.Fin.SuccAboveOrderIso

@[expose] public section


/-!
# Bridge from the homogeneous-cochain model to Mathlib's `groupCohomology` (degree two)

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LevelTransfer

open CategoryTheory GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

section Inhom

variable {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ Γ V)

theorem mem_inhom_iff (f : Γ → Γ → V) :
    f ∈ inhomogeneousTwoCycles σ ↔ (fun p : Γ × Γ => f p.1 p.2) ∈ groupCohomology.cocycles₂ (Rep.of σ) := by
  rw [groupCohomology.mem_cocycles₂_iff]
  constructor
  · intro h g h' j
    have := h g h' j
    change f (g * h') j + f g h' = σ g (f h' j) + f g (h' * j)
    rw [← sub_eq_zero]
    rw [show f (g * h') j + f g h' - (σ g (f h' j) + f g (h' * j)) =
      -(σ g (f h' j) - f (g * h') j + f g (h' * j) - f g h') by abel, this, neg_zero]
  · intro h g h' j
    have := h g h' j
    change f (g * h') j + f g h' = σ g (f h' j) + f g (h' * j) at this
    show σ g (f h' j) - f (g * h') j + f g (h' * j) - f g h' = 0
    rw [show σ g (f h' j) - f (g * h') j + f g (h' * j) - f g h' =
      -(f (g * h') j + f g h' - (σ g (f h' j) + f g (h' * j))) by abel, this, sub_self, neg_zero]

/-- Uncurrying identifies the inhomogeneous two-cocycles of the model with Mathlib's `cocycles₂`. -/
def toCocycles₂ : inhomogeneousTwoCycles σ ≃ₗ[ℂ] groupCohomology.cocycles₂ (Rep.of σ) where
  toFun f := ⟨fun p => f.val p.1 p.2, (mem_inhom_iff σ f.val).mp f.property⟩
  invFun f := ⟨fun a b => f.val (a, b), (mem_inhom_iff σ _).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The class in Mathlib's `H²` of an inhomogeneous two-cocycle. -/
def inhomToH2 : inhomogeneousTwoCycles σ →ₗ[ℂ] groupCohomology.H2 (Rep.of σ) :=
  (groupCohomology.H2π (Rep.of σ)).hom ∘ₗ (toCocycles₂ σ).toLinearMap

theorem inhomToH2_eq_zero_iff (x : inhomogeneousTwoCycles σ) :
    inhomToH2 σ x = 0 ↔ x ∈ inhomogeneousBoundaries σ := by
  change groupCohomology.H2π (Rep.of σ) (toCocycles₂ σ x) = 0 ↔ _
  rw [groupCohomology.H2π_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨fun g => u g, ?_⟩
    apply Subtype.ext
    funext a b
    have := congrFun hu (a, b)
    exact this
  · rintro ⟨u, hu⟩
    refine ⟨fun g => u g, ?_⟩
    funext p
    have := congrFun (congrArg Subtype.val hu) p.1
    exact congrFun this p.2

theorem inhomToH2_surjective : Function.Surjective (inhomToH2 σ) := by
  intro y
  induction y using groupCohomology.H2_induction_on with
  | h x => exact ⟨(toCocycles₂ σ).symm x, by simp [inhomToH2]⟩

/-- `InhomogeneousH2 σ ≃ H²(Γ, σ)` (Mathlib's group cohomology). -/
def inhomEquivH2 : InhomogeneousH2 σ ≃ₗ[ℂ] groupCohomology.H2 (Rep.of σ) :=
  LinearEquiv.ofBijective
    (Submodule.liftQ (inhomogeneousBoundaries σ) (inhomToH2 σ) (fun x hx =>
      LinearMap.mem_ker.mpr ((inhomToH2_eq_zero_iff σ x).mpr hx)))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.Quotient.mk_eq_zero]
      exact (inhomToH2_eq_zero_iff σ x).mp hq,
     by
      intro y
      obtain ⟨x, hx⟩ := inhomToH2_surjective σ y
      exact ⟨Submodule.Quotient.mk x, hx⟩⟩

theorem inhomEquivH2_mk (x : inhomogeneousTwoCycles σ) :
    inhomEquivH2 σ (Submodule.Quotient.mk x) = inhomToH2 σ x := rfl

end Inhom

section Prism

/-- The base-point change identity for a homogeneous two-cocycle (prism formula). -/
theorem prism_identity {G V : Type} [AddCommGroup V] (F : (Fin 3 → G) → V)
    (hz : ∀ x : Fin 4 → G, F ![x 1, x 2, x 3] - F ![x 0, x 2, x 3] + F ![x 0, x 1, x 3] -
      F ![x 0, x 1, x 2] = 0)
    (x0 x1 x2 y0 y1 y2 : G) (a b : V)
    (ha : F ![x1, x2, y2] = a) (hb : F ![x1, y1, y2] = b) :
    F ![y0, y1, y2] - F ![x0, x1, x2] =
      -a + b + F ![x0, x2, y2] - F ![x0, y0, y2] - F ![x0, x1, y1] + F ![x0, y0, y1] := by
  have t1 := hz ![x0, x1, x2, y2]
  have t2 := hz ![x0, x1, y1, y2]
  have t3 := hz ![x0, y0, y1, y2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at t1 t2 t3
  rw [ha] at t1
  rw [hb] at t2
  rw [← sub_eq_zero]
  have : F ![y0, y1, y2] - F ![x0, x1, x2] -
      (-a + b + F ![x0, x2, y2] - F ![x0, y0, y2] - F ![x0, x1, y1] + F ![x0, y0, y1]) =
      (F ![y0, y1, y2] - F ![x0, y1, y2] + F ![x0, y0, y2] - F ![x0, y0, y1]) -
      (b - F ![x0, y1, y2] + F ![x0, x1, y2] - F ![x0, x1, y1]) +
      (a - F ![x0, x2, y2] + F ![x0, x1, y2] - F ![x0, x1, x2]) := by abel
  rw [this, t1, t2, t3]
  simp

end Prism

section Bridge

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  (Γ : Subgroup G)

/-- **The bridge** `H²_{hom}(Γ, ρ) ≃ H²(Γ, ρ|Γ)` between the homogeneous-cochain model on ambient
vertices and Mathlib's group cohomology (inhomogeneous cochains), degree two.  It sends the class of a
cocycle `F` to the class of `(a, b) ↦ F(1, a, ab)`. -/
def bridge : H2 Γ ρ ≃ₗ[ℂ] groupCohomology.H2 (Rep.of (ρ.comp Γ.subtype)) :=
  (ambientResolutionH2Equiv Γ ρ).trans
    ((fullInhomogeneousH2Equiv (ρ.comp Γ.subtype)).trans (inhomEquivH2 (ρ.comp Γ.subtype)))

/-- The cocycle `(a, b) ↦ F(1, a, ab)` in Mathlib's `cocycles₂`. -/
def bridgeCocycle (z : cocycles Γ ρ) : groupCohomology.cocycles₂ (Rep.of (ρ.comp Γ.subtype)) :=
  toCocycles₂ (ρ.comp Γ.subtype)
    (fullInhomogeneousCycleEquiv (ρ.comp Γ.subtype)
      (ambientRestrictionCycles Γ ρ z))

theorem bridgeCocycle_apply (z : cocycles Γ ρ) (a b : Γ) :
    (bridgeCocycle ρ Γ z : Γ × Γ → V) (a, b) =
      z.val.val ![1, (a : G), ((a * b : Γ) : G)] := by
  change z.val.val (fun i => ((![1, a, a * b] : Fin 3 → Γ) i : G)) = _
  have e : (fun i : Fin 3 => ((![1, a, a * b] : Fin 3 → Γ) i : G)) =
      ![1, (a : G), ((a * b : Γ) : G)] := by
    funext i; fin_cases i <;> rfl
  rw [e]

theorem bridge_mk (z : cocycles Γ ρ) :
    bridge ρ Γ (Submodule.Quotient.mk z) = (groupCohomology.H2π (Rep.of (ρ.comp Γ.subtype))).hom
      (bridgeCocycle ρ Γ z) := rfl

variable {Γ} {Γ' : Subgroup G}

/-- The identity intertwiner `Res_{Γ'} (ρ|Γ) → ρ|Γ'`. -/
def resRep (h : Γ' ≤ Γ) :
    Rep.res (Subgroup.inclusion h) (Rep.of (ρ.comp Γ.subtype)) ⟶ Rep.of (ρ.comp Γ'.subtype) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- **Naturality in the subgroup**: the bridge intertwines the model restriction `resH2` with
Mathlib's restriction `groupCohomology.map`. -/
theorem bridge_res (h : Γ' ≤ Γ) (x : H2 Γ ρ) :
    (groupCohomology.map (Subgroup.inclusion h) (resRep ρ h) 2).hom (bridge ρ Γ x) =
      bridge ρ Γ' (resH2 ρ h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [bridge_mk]
  have h1 : resH2 ρ h (Submodule.Quotient.mk z) = Submodule.Quotient.mk (cocyclesRes ρ h z) := rfl
  rw [h1, bridge_mk]
  have h2 := congrArg (fun t => t.hom (bridgeCocycle ρ Γ z))
    (groupCohomology.H2π_comp_map (Subgroup.inclusion h) (resRep ρ h))
  change (groupCohomology.map (Subgroup.inclusion h) (resRep ρ h) 2).hom
      ((groupCohomology.H2π (Rep.of (ρ.comp Γ.subtype))).hom (bridgeCocycle ρ Γ z)) = _ at h2
  rw [h2]
  have e : groupCohomology.mapCocycles₂ (Subgroup.inclusion h) (resRep ρ h) (bridgeCocycle ρ Γ z) =
      bridgeCocycle ρ Γ' (cocyclesRes ρ h z) := by
    apply Subtype.ext
    funext p
    change (bridgeCocycle ρ Γ z : Γ × Γ → V) (Subgroup.inclusion h p.1, Subgroup.inclusion h p.2) =
      (bridgeCocycle ρ Γ' (cocyclesRes ρ h z) : Γ' × Γ' → V) (p.1, p.2)
    rw [bridgeCocycle_apply, bridgeCocycle_apply]
    rfl
  exact congrArg (groupCohomology.H2π (Rep.of (ρ.comp Γ'.subtype))).hom e

end Bridge

section Conj

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  {Δ Δ' : Subgroup G} (g : G)

/-- `Δ' = g Δ g⁻¹`. -/
def IsConj (Δ Δ' : Subgroup G) (g : G) : Prop := ∀ x, x ∈ Δ' ↔ g⁻¹ * x * g ∈ Δ

theorem IsEq.act_conj {k : ℕ} {f : FunSpace G V k} (hf : IsEq ρ Δ f) (hg : IsConj Δ Δ' g) :
    IsEq ρ Δ' (actFun ρ g f) := by
  intro γ hγ x
  simp only [actFun_apply]
  have h1 : (fun i => g⁻¹ * (γ * x i)) = fun i => (g⁻¹ * γ * g) * (g⁻¹ * x i) := by
    funext i; group
  rw [h1, hf _ ((hg γ).mp hγ), ← Module.End.mul_apply, ← map_mul]
  have : g * (g⁻¹ * γ * g) = γ * g := by group
  rw [this, map_mul, Module.End.mul_apply]

/-- Conjugation of cocycles by `g`, from `Δ` to `Δ' = gΔg⁻¹`. -/
def actCocycleConj (hg : IsConj Δ Δ' g) : cocycles Δ ρ →ₗ[ℂ] cocycles Δ' ρ where
  toFun z := ⟨⟨actFun ρ g z.val.val,
      (mem_cochains_iff ρ Δ' 2 _).mpr (IsEq.act_conj ρ g ((mem_cochains_iff ρ Δ 2 _).mp z.val.2) hg)⟩, by
    have h := z.property
    change differentialTwo Δ ρ z.val = 0 at h
    rw [differentialTwo_eq] at h
    change differentialTwo Δ' ρ _ = 0
    rw [differentialTwo_eq]
    change rd2 (actFun ρ g z.val.val) = 0
    rw [← actFun_rd2, h, map_zero]⟩
  map_add' z w := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
  map_smul' a z := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _

/-- The action of `g` on `H²`: `H²(Δ, ρ) → H²(gΔg⁻¹, ρ)`. -/
def actH2Conj (hg : IsConj Δ Δ' g) : H2 Δ ρ →ₗ[ℂ] H2 Δ' ρ :=
  Submodule.mapQ _ _ (actCocycleConj ρ g hg) (by
    rintro _ ⟨c, rfl⟩
    refine ⟨⟨actFun ρ g c.val,
      (mem_cochains_iff ρ Δ' 1 _).mpr (IsEq.act_conj ρ g ((mem_cochains_iff ρ Δ 1 _).mp c.2) hg)⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    exact (actFun_rd1 ρ g c.val).symm)

/-- Conjugation `γ ↦ g γ g⁻¹`, `Δ → Δ'`. -/
def conjHom (hg : IsConj Δ Δ' g) : Δ →* Δ' where
  toFun γ := ⟨g * γ.val * g⁻¹, (hg _).mpr (by simp [mul_assoc])⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

/-- The intertwiner `ρ(g⁻¹)` for the conjugation map. -/
def conjRep (hg : IsConj Δ Δ' g) :
    Rep.res (conjHom g hg) (Rep.of (ρ.comp Δ'.subtype)) ⟶ Rep.of (ρ.comp Δ.subtype) :=
  Rep.ofHom ⟨ρ g⁻¹, fun γ => by
    ext v
    change ρ g⁻¹ (ρ (g * γ.val * g⁻¹) v) = ρ γ.val (ρ g⁻¹ v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group⟩

/-- **Naturality in conjugation**: Mathlib's conjugation map on `H²` is inverse to the model action. -/
theorem bridge_conj (hg : IsConj Δ Δ' g) (x : H2 Δ ρ) :
    (groupCohomology.map (conjHom g hg) (conjRep ρ g hg) 2).hom
        (bridge ρ Δ' (actH2Conj ρ g hg x)) = bridge ρ Δ x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : actH2Conj ρ g hg (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (actCocycleConj ρ g hg z) := rfl
  rw [h0, bridge_mk, bridge_mk]
  have h2 := congrArg (fun t => t.hom (bridgeCocycle ρ Δ' (actCocycleConj ρ g hg z)))
    (groupCohomology.H2π_comp_map (conjHom g hg) (conjRep ρ g hg))
  change (groupCohomology.map (conjHom g hg) (conjRep ρ g hg) 2).hom
      ((groupCohomology.H2π (Rep.of (ρ.comp Δ'.subtype))).hom
        (bridgeCocycle ρ Δ' (actCocycleConj ρ g hg z))) = _ at h2
  rw [h2]
  change groupCohomology.H2π (Rep.of (ρ.comp Δ.subtype))
      (groupCohomology.mapCocycles₂ (conjHom g hg) (conjRep ρ g hg)
        (bridgeCocycle ρ Δ' (actCocycleConj ρ g hg z))) =
    groupCohomology.H2π (Rep.of (ρ.comp Δ.subtype)) (bridgeCocycle ρ Δ z)
  rw [← sub_eq_zero, ← map_sub, groupCohomology.H2π_eq_zero_iff]
  set F := z.val.val with hFdef
  have hz : ∀ x : Fin 4 → G, F ![x 1, x 2, x 3] - F ![x 0, x 2, x 3] + F ![x 0, x 1, x 3] -
      F ![x 0, x 1, x 2] = 0 := by
    intro x
    have h := z.property
    change differentialTwo Δ ρ z.val = 0 at h
    rw [differentialTwo_eq] at h
    exact congrFun h x
  have hF : ∀ γ ∈ Δ, ∀ x, F (fun i => γ * x i) = ρ γ (F x) :=
    (mem_cochains_iff ρ Δ 2 F).mp z.val.2
  refine ⟨fun δ => -(F ![1, δ.val, δ.val * g⁻¹] - F ![1, g⁻¹, δ.val * g⁻¹]), ?_⟩
  funext p
  obtain ⟨γ, δ⟩ := p
  have e1 : F ![γ.val, γ.val * δ.val, γ.val * δ.val * g⁻¹] =
      ρ γ.val (F ![1, δ.val, δ.val * g⁻¹]) := by
    have := hF γ.val γ.2 ![1, δ.val, δ.val * g⁻¹]
    have e : (fun i => γ.val * (![1, δ.val, δ.val * g⁻¹] : Fin 3 → G) i) =
        ![γ.val, γ.val * δ.val, γ.val * δ.val * g⁻¹] := by
      funext i; fin_cases i <;> simp [mul_assoc]
    rw [e] at this
    exact this
  have e2 : F ![γ.val, γ.val * g⁻¹, γ.val * δ.val * g⁻¹] =
      ρ γ.val (F ![1, g⁻¹, δ.val * g⁻¹]) := by
    have := hF γ.val γ.2 ![1, g⁻¹, δ.val * g⁻¹]
    have e : (fun i => γ.val * (![1, g⁻¹, δ.val * g⁻¹] : Fin 3 → G) i) =
        ![γ.val, γ.val * g⁻¹, γ.val * δ.val * g⁻¹] := by
      funext i; fin_cases i <;> simp [mul_assoc]
    rw [e] at this
    exact this
  have key := prism_identity F hz 1 γ.val (γ.val * δ.val) g⁻¹ (γ.val * g⁻¹) (γ.val * δ.val * g⁻¹)
    _ _ e1 e2
  have hM : ((groupCohomology.mapCocycles₂ (conjHom g hg) (conjRep ρ g hg))
      (bridgeCocycle ρ Δ' (actCocycleConj ρ g hg z)) : Δ × Δ → V) (γ, δ) =
      F ![g⁻¹, γ.val * g⁻¹, γ.val * δ.val * g⁻¹] := by
    change ρ g⁻¹ ((bridgeCocycle ρ Δ' (actCocycleConj ρ g hg z) : Δ' × Δ' → V)
      (conjHom g hg γ, conjHom g hg δ)) = _
    rw [bridgeCocycle_apply]
    change ρ g⁻¹ (actFun ρ g F ![1, g * γ.val * g⁻¹, g * γ.val * g⁻¹ * (g * δ.val * g⁻¹)]) = _
    rw [actFun_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
    congr 1
    funext i
    fin_cases i <;> simp [mul_assoc]
  rw [groupCohomology.d₁₂_hom_apply]
  change _ = ((groupCohomology.mapCocycles₂ (conjHom g hg) (conjRep ρ g hg))
      (bridgeCocycle ρ Δ' (actCocycleConj ρ g hg z)) : Δ × Δ → V) (γ, δ) -
    (bridgeCocycle ρ Δ z : Δ × Δ → V) (γ, δ)
  rw [hM, bridgeCocycle_apply]
  simp only [map_neg, map_sub]
  change _ = _ - F ![1, γ.val, γ.val * δ.val]
  have e3 : F ![1, γ.val * δ.val, γ.val * δ.val * g⁻¹] = F ![1, (γ * δ).val, (γ * δ).val * g⁻¹] := rfl
  have e4 : F ![1, g⁻¹, γ.val * δ.val * g⁻¹] = F ![1, g⁻¹, (γ * δ).val * g⁻¹] := rfl
  rw [key, ← e3, ← e4]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  abel

end Conj

section Invariants

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  {N S : Subgroup G} [Fintype (S ⧸ N.subgroupOf S)]

omit [Fintype (S ⧸ N.subgroupOf S)] in
theorem isConj_of_normalizes (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) {s : G} (hs : s ∈ S) :
    IsConj N N s := by
  intro x
  constructor
  · exact hnorm s hs x
  · intro h
    have := hnorm s⁻¹ (S.inv_mem hs) _ h
    simpa [mul_assoc] using this

omit [Fintype (S ⧸ N.subgroupOf S)] in
theorem actH2_eq_actH2Conj {s : G} (hs : ∀ n ∈ N, s⁻¹ * n * s ∈ N) (hg : IsConj N N s)
    (x : H2 N ρ) : actH2 ρ s hs x = actH2Conj ρ s hg x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

omit [Fintype (S ⧸ N.subgroupOf S)] in
theorem actH2Conj_inv_actH2Conj {g : G} {Δ Δ' : Subgroup G} (hg : IsConj Δ Δ' g)
    (hg' : IsConj Δ' Δ g⁻¹) (x : H2 Δ ρ) : actH2Conj ρ g⁻¹ hg' (actH2Conj ρ g hg x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk z
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  change actFun ρ g⁻¹ (actFun ρ g z.val.val) = z.val.val
  rw [← actFun_mul, inv_mul_cancel, actFun_one]

/-- Mathlib's restriction `H²(S, ρ|S) → H²(N, ρ|N)`. -/
def resMathlib (hNS : N ≤ S) :
    groupCohomology.H2 (Rep.of (ρ.comp S.subtype)) →ₗ[ℂ] groupCohomology.H2 (Rep.of (ρ.comp N.subtype)) :=
  (groupCohomology.map (Subgroup.inclusion hNS) (resRep ρ hNS) 2).hom

/-- Mathlib's conjugation action of `s ∈ S` on `H²(N, ρ|N)`. -/
def conjAct (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) {s : G} (hs : s ∈ S) :
    groupCohomology.H2 (Rep.of (ρ.comp N.subtype)) →ₗ[ℂ] groupCohomology.H2 (Rep.of (ρ.comp N.subtype)) :=
  (groupCohomology.map (conjHom s (isConj_of_normalizes hnorm hs))
    (conjRep ρ s (isConj_of_normalizes hnorm hs)) 2).hom

/-- **Level transfer on Mathlib's `groupCohomology`** (degree two): the image of the restriction
`H²(S, ρ|S) → H²(N, ρ|N)` is exactly the classes fixed by Mathlib's conjugation action of `S`. -/
theorem mem_range_resMathlib_iff (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N)
    (y : groupCohomology.H2 (Rep.of (ρ.comp N.subtype))) :
    y ∈ LinearMap.range (resMathlib ρ hNS) ↔ ∀ (s : G) (hs : s ∈ S), conjAct ρ hnorm hs y = y := by
  obtain ⟨x, rfl⟩ := (bridge ρ N).surjective y
  constructor
  · rintro ⟨w, hw⟩ s hs
    obtain ⟨v, rfl⟩ := (bridge ρ S).surjective w
    have h1 : resMathlib ρ hNS (bridge ρ S v) = bridge ρ N (resH2 ρ hNS v) := bridge_res ρ hNS v
    have h2 : resH2 ρ hNS v = x := (bridge ρ N).injective (h1.symm.trans hw)
    have h3 : actH2Conj ρ s (isConj_of_normalizes hnorm hs) x = x := by
      rw [← actH2_eq_actH2Conj ρ (hnorm s hs) (isConj_of_normalizes hnorm hs)]
      exact (mem_range_resH2_iff ρ hNS hnorm x).mp ⟨v, h2⟩ s hs
    have h4 := bridge_conj ρ s (isConj_of_normalizes hnorm hs) x
    calc conjAct ρ hnorm hs (bridge ρ N x)
        = (groupCohomology.map _ _ 2).hom (bridge ρ N (actH2Conj ρ s (isConj_of_normalizes hnorm hs) x)) := by
          rw [h3]; rfl
      _ = bridge ρ N x := h4
  · intro h
    have hx : x ∈ LinearMap.range (resH2 ρ hNS) := by
      rw [mem_range_resH2_iff ρ hNS hnorm]
      intro s hs
      rw [actH2_eq_actH2Conj ρ (hnorm s hs) (isConj_of_normalizes hnorm hs)]
      have hs' : s⁻¹ ∈ S := S.inv_mem hs
      have h1 := bridge_conj ρ s⁻¹ (isConj_of_normalizes hnorm hs')
        (actH2Conj ρ s (isConj_of_normalizes hnorm hs) x)
      rw [actH2Conj_inv_actH2Conj ρ (isConj_of_normalizes hnorm hs)
        (isConj_of_normalizes hnorm hs')] at h1
      have h2 := h s⁻¹ hs'
      have h3 : bridge ρ N (actH2Conj ρ s (isConj_of_normalizes hnorm hs) x) = bridge ρ N x := by
        rw [← h1]
        exact h2
      exact (bridge ρ N).injective h3
    obtain ⟨v, hv⟩ := hx
    refine ⟨bridge ρ S v, ?_⟩
    change (groupCohomology.map _ _ 2).hom (bridge ρ S v) = _
    rw [bridge_res ρ hNS v, hv]

end Invariants

end TernaryPeriodPolynomials.Argument.LevelTransfer
