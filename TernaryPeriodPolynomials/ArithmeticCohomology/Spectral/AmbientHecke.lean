module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.HeckeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientGroupH2

@[expose] public section


/-!
# Local Hecke operators in inhomogeneous coordinates

Let `Λ ≤ G` and let `S` be a local correspondence of `Λ` (finitely many disjoint cosets `sΛ`, permuted
by left multiplication by `Λ`) with `S ∩ Λ = ∅`. The local Hecke operator of `LocalHecke` acts on the
ambient homogeneous cocycles `C ↦ (x ↦ ∑_{s ∈ S} ρ(s) C(s⁻¹ x))`. Restricting to `Λ`-vertices
(`ambientCocycleToGroup`) turns it into the inhomogeneous formula
`(T c)(g, h) = ∑_s ρ(s) c(δ_s(g), δ_{s'}(h))`, `δ_s(g) = s⁻¹ g s'` with `s⁻¹ g ∈ Λ s'⁻¹`
(`ambientHecke_class`): the ambient cocycle is cohomologous to the lift of its restriction along a
`Λ`-equivariant retraction `G → Λ` sending every `s⁻¹` to `1`.

The right cosets `Λ s⁻¹` form `HeckeH1.RightCosets` data (`toRightCosets`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.AmbientHecke

open LocalHecke HeckeH1

variable {G : Type} [Group G] {Λ : Subgroup G}

/-! ### Right cosets `Λ s⁻¹` -/

/-- The next index: `s⁻¹ g ∈ Λ (next g s)⁻¹`. -/
def nextRep (S : LocalCorrespondence Λ) (g : Λ) (s : S.representatives) : S.representatives :=
  representativeMap S g s

theorem nextRep_mem (S : LocalCorrespondence Λ) (g : Λ) (s : S.representatives) :
    s.val⁻¹ * g.val * (nextRep S g s).val ∈ Λ := by
  have h := Λ.inv_mem (representativeMap_mem S g s)
  simpa [nextRep, mul_assoc] using h

/-- The next index is characterized by `s⁻¹ g t ∈ Λ`. -/
theorem nextRep_unique (S : LocalCorrespondence Λ) (g : Λ) (s t : S.representatives)
    (h : s.val⁻¹ * g.val * t.val ∈ Λ) : nextRep S g s = t := by
  apply Subtype.ext
  apply S.disjoint _ (nextRep S g s).property _ t.property
  have := Λ.mul_mem (Λ.inv_mem (nextRep_mem S g s)) h
  simpa [mul_assoc] using this

/-- The transition `δ_s(g) = s⁻¹ g (next g s)`. -/
def deltaRep (S : LocalCorrespondence Λ) (g : Λ) (s : S.representatives) : Λ :=
  ⟨s.val⁻¹ * g.val * (nextRep S g s).val, nextRep_mem S g s⟩

theorem deltaRep_val (S : LocalCorrespondence Λ) (g : Λ) (s : S.representatives) :
    (deltaRep S g s).val = s.val⁻¹ * g.val * (nextRep S g s).val := rfl

/-- **The right cosets `Λ s⁻¹` as `RightCosets` data.** -/
def toRightCosets (S : LocalCorrespondence Λ) : RightCosets Λ.subtype where
  index := S.representatives
  fintype := inferInstance
  rep s := s.val⁻¹
  next := nextRep S
  delta := deltaRep S
  delta_spec g s := by
    change s.val⁻¹ * g.val * (nextRep S g s).val = s.val⁻¹ * g.val * ((nextRep S g s).val⁻¹)⁻¹
    rw [inv_inv]
  disjoint i j g h := by
    apply Subtype.ext
    apply S.disjoint i.val i.property j.val j.property
    change g.val = i.val⁻¹ * (j.val⁻¹)⁻¹ at h
    rw [inv_inv] at h
    rw [← h]
    exact g.property

/-! ### A retraction `G → Λ` adapted to `S` -/

variable (S : LocalCorrespondence Λ)

open Classical in
/-- Coset representatives of `Λ \ G`, equal to `1` on `Λ` and to `s⁻¹` on `Λ s⁻¹`. -/
def cosetRep (q : Quotient (QuotientGroup.rightRel Λ)) : G :=
  if q = Quotient.mk _ 1 then 1
  else if h : ∃ s ∈ S.representatives, Quotient.mk _ s⁻¹ = q then h.choose⁻¹
  else Quotient.out q

theorem cosetRep_mk (q : Quotient (QuotientGroup.rightRel Λ)) :
    Quotient.mk (QuotientGroup.rightRel Λ) (cosetRep S q) = q := by
  classical
  unfold cosetRep
  split_ifs with h1 h2
  · exact h1.symm
  · exact h2.choose_spec.2
  · exact Quotient.out_eq q

theorem mk_eq_mk_iff (x y : G) :
    Quotient.mk (QuotientGroup.rightRel Λ) x = Quotient.mk _ y ↔ y * x⁻¹ ∈ Λ := by
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply

/-- The retraction `π(x) = x · rep(Λx)⁻¹`. -/
def retract (x : G) : G := x * (cosetRep S (Quotient.mk _ x))⁻¹

theorem retract_mem (x : G) : retract S x ∈ Λ := by
  have h := cosetRep_mk S (Quotient.mk _ x)
  rw [mk_eq_mk_iff] at h
  exact h

theorem retract_mul {g : G} (hg : g ∈ Λ) (x : G) : retract S (g * x) = g * retract S x := by
  have hq : Quotient.mk (QuotientGroup.rightRel Λ) (g * x) = Quotient.mk _ x := by
    rw [mk_eq_mk_iff]
    simpa [mul_assoc] using Λ.inv_mem hg
  simp only [retract, hq, mul_assoc]

theorem retract_one : retract S 1 = 1 := by
  simp [retract, cosetRep]

theorem retract_of_mem {g : G} (hg : g ∈ Λ) : retract S g = g := by
  have := retract_mul S hg 1
  rw [mul_one, retract_one, mul_one] at this
  exact this

variable (hS : ∀ s ∈ S.representatives, s ∉ Λ)

include hS in
theorem retract_inv_rep {s : G} (hs : s ∈ S.representatives) : retract S s⁻¹ = 1 := by
  classical
  have hne : Quotient.mk (QuotientGroup.rightRel Λ) s⁻¹ ≠ Quotient.mk _ 1 := by
    rw [Ne, mk_eq_mk_iff, inv_inv, one_mul]
    exact hS s hs
  have hex : ∃ s' ∈ S.representatives, Quotient.mk (QuotientGroup.rightRel Λ) s'⁻¹ =
      Quotient.mk _ s⁻¹ := ⟨s, hs, rfl⟩
  have hrep : cosetRep S (Quotient.mk _ s⁻¹) = s⁻¹ := by
    unfold cosetRep
    rw [ite_eq_right hne, dite_eq_left hex]
    have hspec := hex.choose_spec
    rw [mk_eq_mk_iff, inv_inv] at hspec
    have := S.disjoint s hs hex.choose hspec.1 hspec.2
    rw [← this]
  simp [retract, hrep]

/-! ### Lifting inhomogeneous cocycles -/

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The homogeneous form `(a, b, d) ↦ ρ(a) c(a⁻¹b, b⁻¹d)` of an inhomogeneous cocycle. -/
def liftAux (c : groupCohomology.cocycles₂ (subgroupCoefficientRep Λ ρ)) (a b d : Λ) :
    subgroupCoefficientRep Λ ρ :=
  (subgroupCoefficientRep Λ ρ).ρ a (c (a⁻¹ * b, b⁻¹ * d))

theorem liftAux_mul (c : groupCohomology.cocycles₂ (subgroupCoefficientRep Λ ρ)) (γ a b d : Λ) :
    liftAux ρ c (γ * a) (γ * b) (γ * d) = (subgroupCoefficientRep Λ ρ).ρ γ (liftAux ρ c a b d) := by
  have h1 : (γ * a)⁻¹ * (γ * b) = a⁻¹ * b := by group
  have h2 : (γ * b)⁻¹ * (γ * d) = b⁻¹ * d := by group
  simp only [liftAux, h1, h2, map_mul, Module.End.mul_apply]

theorem liftAux_cocycle (c : groupCohomology.cocycles₂ (subgroupCoefficientRep Λ ρ)) (a b d e : Λ) :
    liftAux ρ c b d e - liftAux ρ c a d e + liftAux ρ c a b e - liftAux ρ c a b d = 0 := by
  have key := (groupCohomology.mem_cocycles₂_iff _).mp c.property (a⁻¹ * b) (b⁻¹ * d) (d⁻¹ * e)
  have e1 : a⁻¹ * b * (b⁻¹ * d) = a⁻¹ * d := by group
  have e2 : b⁻¹ * d * (d⁻¹ * e) = b⁻¹ * e := by group
  rw [e1, e2] at key
  simp only [groupCohomology.cocycles₂.val_eq_coe] at key
  have hb : b = a * (a⁻¹ * b) := by group
  unfold liftAux
  rw [hb, map_mul, Module.End.mul_apply, ← hb, ← map_sub, ← map_add, ← map_sub]
  set A := (subgroupCoefficientRep Λ ρ).ρ (a⁻¹ * b) (c (b⁻¹ * d, d⁻¹ * e))
  set B := c (a⁻¹ * d, d⁻¹ * e)
  set C := c (a⁻¹ * b, b⁻¹ * e)
  set D := c (a⁻¹ * b, b⁻¹ * d)
  have : A - B + C - D = 0 := by
    rw [show A - B + C - D = (A + C) - (B + D) by abel, ← key, sub_self]
  rw [this, map_zero]

/-- The retraction as a map to `Λ`. -/
def retractΛ (x : G) : Λ := ⟨retract S x, retract_mem S x⟩

theorem retractΛ_mul (γ : Λ) (x : G) : retractΛ S (γ.val * x) = γ * retractΛ S x :=
  Subtype.ext (retract_mul S γ.property x)

/-- The ambient lift `C(x) = ρ(πx₀) c(πx₀⁻¹ πx₁, πx₁⁻¹ πx₂)`. -/
def liftFun (c : groupCohomology.cocycles₂ (subgroupCoefficientRep Λ ρ)) (x : Fin 3 → G) : V :=
  liftAux ρ c (retractΛ S (x 0)) (retractΛ S (x 1)) (retractΛ S (x 2))

theorem liftFun_mem (c : groupCohomology.cocycles₂ (subgroupCoefficientRep Λ ρ)) :
    liftFun S ρ c ∈ cochains Λ ρ 2 := by
  intro γ x
  simp only [liftFun, retractΛ_mul, liftAux_mul]
  rfl

/-- The ambient lift of an inhomogeneous cocycle. -/
def liftCocycle (c : groupCohomology.cocycles₂ (subgroupCoefficientRep Λ ρ)) : cocycles Λ ρ :=
  ⟨⟨liftFun S ρ c, liftFun_mem S ρ c⟩, by
    funext x
    change liftFun S ρ c ![x 1, x 2, x 3] - liftFun S ρ c ![x 0, x 2, x 3] +
      liftFun S ρ c ![x 0, x 1, x 3] - liftFun S ρ c ![x 0, x 1, x 2] = 0
    exact liftAux_cocycle ρ c _ _ _ _⟩

theorem liftCocycle_apply (c : groupCohomology.cocycles₂ (subgroupCoefficientRep Λ ρ))
    (x : Fin 3 → G) : (liftCocycle S ρ c).val.val x = liftFun S ρ c x := rfl

/-- The lift restricts to the original cocycle. -/
theorem ambientCocycleToGroup_lift (c : groupCohomology.cocycles₂ (subgroupCoefficientRep Λ ρ)) :
    ambientCocycleToGroup Λ ρ (liftCocycle S ρ c) = c := by
  apply groupCohomology.cocycles₂_ext
  intro g h
  rw [ambientCocycleToGroup_apply, liftCocycle_apply]
  have h0 : retractΛ S 1 = 1 := Subtype.ext (retract_one S)
  have h1 : retractΛ S g.val = g := Subtype.ext (retract_of_mem S g.property)
  have h2 : retractΛ S (g.val * h.val) = g * h :=
    Subtype.ext (retract_of_mem S (Λ.mul_mem g.property h.property))
  simp only [liftFun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, h0, h1, h2, liftAux, inv_one, one_mul,
    map_one, inv_mul_cancel_left]
  rfl

/-! ### The local Hecke operator in inhomogeneous coordinates -/

include hS in
/-- **Cocycle formula.** On the lift of `c`, the local Hecke operator restricts to
`(g, h) ↦ ∑_s ρ(s) c(δ_s(g), δ_{s'}(h))`. -/
theorem ambientHecke_lift (c : groupCohomology.cocycles₂ (subgroupCoefficientRep Λ ρ)) (g h : Λ) :
    ambientCocycleToGroup Λ ρ (cocycleAction ρ S (liftCocycle S ρ c)) (g, h) =
      ∑ s : S.representatives, ρ s.val (c (deltaRep S g s, deltaRep S h (nextRep S g s))) := by
  rw [ambientCocycleToGroup_apply]
  change (cochainAction ρ S 2 (liftCocycle S ρ c).val).val ![1, g.val, g.val * h.val] = _
  rw [cochainAction_apply, ← Finset.sum_coe_sort S.representatives]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [liftCocycle_apply]
  have hs : retractΛ S s.val⁻¹ = 1 := Subtype.ext (retract_inv_rep S hS s.property)
  have hg : s.val⁻¹ * g.val = (deltaRep S g s).val * (nextRep S g s).val⁻¹ := by
    simp [deltaRep, mul_assoc]
  have hgh : s.val⁻¹ * (g.val * h.val) = (deltaRep S g s).val * (deltaRep S h (nextRep S g s)).val *
      (nextRep S h (nextRep S g s)).val⁻¹ := by
    simp [deltaRep, mul_assoc]
  have ht : ∀ t : S.representatives, retractΛ S t.val⁻¹ = 1 :=
    fun t => Subtype.ext (retract_inv_rep S hS t.property)
  have h1 : retractΛ S (s.val⁻¹ * g.val) = deltaRep S g s := by
    rw [hg, retractΛ_mul, ht, mul_one]
  have h2 : retractΛ S (s.val⁻¹ * (g.val * h.val)) =
      deltaRep S g s * deltaRep S h (nextRep S g s) := by
    rw [hgh, mul_assoc, retractΛ_mul, retractΛ_mul, ht, mul_one]
  simp only [liftFun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [mul_one, hs, h1, h2, liftAux, inv_one, one_mul, map_one, inv_mul_cancel_left]
  rfl

/-- **The class of the local Hecke image is computed by the lift of the restriction.** -/
theorem ambientHecke_class (C : cocycles Λ ρ) :
    groupCohomology.H2π (subgroupCoefficientRep Λ ρ)
        (ambientCocycleToGroup Λ ρ (cocycleAction ρ S C)) =
      groupCohomology.H2π (subgroupCoefficientRep Λ ρ)
        (ambientCocycleToGroup Λ ρ (cocycleAction ρ S (liftCocycle S ρ (ambientCocycleToGroup Λ ρ C)))) := by
  set D := C - liftCocycle S ρ (ambientCocycleToGroup Λ ρ C) with hDdef
  have hD : groupCohomology.H2π (subgroupCoefficientRep Λ ρ) (ambientCocycleToGroup Λ ρ D) = 0 := by
    rw [hDdef, map_sub, ambientCocycleToGroup_lift, sub_self, map_zero]
  obtain ⟨P, hP⟩ := (ambientCocycle_H2_zero_iff Λ ρ D).mp hD
  have hTD : cocycleAction ρ S D = boundaryMap Λ ρ (cochainAction ρ S 1 P) := by
    apply Subtype.ext
    change cochainAction ρ S 2 D.val = differentialOne Λ ρ (cochainAction ρ S 1 P)
    rw [differentialOne_action, hP]
  have hzero : groupCohomology.H2π (subgroupCoefficientRep Λ ρ)
      (ambientCocycleToGroup Λ ρ (cocycleAction ρ S D)) = 0 := by
    apply (ambientCocycle_H2_zero_iff Λ ρ _).mpr
    exact ⟨cochainAction ρ S 1 P, by rw [hTD]; rfl⟩
  rw [hDdef, map_sub, map_sub, map_sub, sub_eq_zero] at hzero
  exact hzero

/-- **The local Hecke image respects cohomology classes of restrictions.** -/
theorem ambientHecke_congr (C C' : cocycles Λ ρ)
    (h : groupCohomology.H2π (subgroupCoefficientRep Λ ρ) (ambientCocycleToGroup Λ ρ C) =
      groupCohomology.H2π (subgroupCoefficientRep Λ ρ) (ambientCocycleToGroup Λ ρ C')) :
    groupCohomology.H2π (subgroupCoefficientRep Λ ρ)
        (ambientCocycleToGroup Λ ρ (cocycleAction ρ S C)) =
      groupCohomology.H2π (subgroupCoefficientRep Λ ρ)
        (ambientCocycleToGroup Λ ρ (cocycleAction ρ S C')) := by
  have hD : groupCohomology.H2π (subgroupCoefficientRep Λ ρ) (ambientCocycleToGroup Λ ρ (C - C')) = 0 := by
    rw [map_sub, map_sub, h, sub_self]
  obtain ⟨P, hP⟩ := (ambientCocycle_H2_zero_iff Λ ρ (C - C')).mp hD
  have hTD : cocycleAction ρ S (C - C') = boundaryMap Λ ρ (cochainAction ρ S 1 P) := by
    apply Subtype.ext
    change cochainAction ρ S 2 (C - C').val = differentialOne Λ ρ (cochainAction ρ S 1 P)
    rw [differentialOne_action, hP]
  have hzero : groupCohomology.H2π (subgroupCoefficientRep Λ ρ)
      (ambientCocycleToGroup Λ ρ (cocycleAction ρ S (C - C'))) = 0 := by
    apply (ambientCocycle_H2_zero_iff Λ ρ _).mpr
    exact ⟨cochainAction ρ S 1 P, by rw [hTD]; rfl⟩
  rw [map_sub, map_sub, map_sub, sub_eq_zero] at hzero
  exact hzero

end TernaryPeriodPolynomials.Spectral.AmbientHecke
