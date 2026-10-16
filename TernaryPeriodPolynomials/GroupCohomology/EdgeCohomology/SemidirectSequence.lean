module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.OneInflation
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.OneTransport
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.Inflation

@[expose] public section


/-!
# The low-degree inflation-restriction sequence for `N ⋊ ℤ`, in degree one

Formalized by Claude Sonnet 5.5.

For a semidirect product `G = N ⋊[φ] Q` (`TernaryPoly.LowDegreeHochschildSerre.G`) and a rational representation `A` of `G`:

* `infl : H¹(Q, A^N) → H¹(G, A)` is injective (`infl_injective`);
* `ker (resp) = range (infl)` (`ker_resp_eq_range_infl`), where `resp : H¹(G, A) → H¹(N, A)`;
* for `Q = Multiplicative ℤ` the image of `resp` is exactly the `Q`-invariants of `H¹(N, A)` (`mem_range_resp_iff`), i.e.
  `0 → H¹(ℤ, A^N) → H¹(G, A) → H¹(N, A)^ℤ → 0` is exact.

The surjectivity onto the invariants is `exists_extension`: a radical cocycle whose class is fixed by the generator of `ℤ` extends
to `G`.  The proof uses the universal properties of the semidirect product: the cocycle `z` on `N` and a cocycle `s` of `ℤ`
(`exists_cocycle_cyclic`: a cocycle on the free group on one generator with a prescribed value at the generator) give
homomorphisms into `A ⋊ G` (`homOfCocycle`), they are compatible as soon as they are at the generator (`compat_of_generator`),
and `SemidirectProduct.lift` assembles a section whose left component is the extension.  Everything is built on
`TernaryPoly.LowDegreeHochschildSerre` (`restrictOne`, `quotientOne`, `one_value_quotient`, `restrictOne_class_invariant`).
-/

open TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EdgeCohomology

open CategoryTheory groupCohomology

section Section

variable {Γ : Type} [Group Γ] (V : Rep.{0} ℚ Γ)

/-- The automorphism of the additive group of `V` by `g`, as an automorphism of `Multiplicative V`. -/
def repAut (g : Γ) : MulAut (Multiplicative V) where
  toFun v := Multiplicative.ofAdd (V.ρ g (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd (V.ρ g⁻¹ (Multiplicative.toAdd v))
  left_inv v := by
    change Multiplicative.ofAdd (V.ρ g⁻¹ (V.ρ g (Multiplicative.toAdd v))) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    change Multiplicative.ofAdd (V.ρ g (V.ρ g⁻¹ (Multiplicative.toAdd v))) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_mul' a b := by
    change Multiplicative.ofAdd (V.ρ g (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
    rw [map_add]
    rfl

def repHom : Γ →* MulAut (Multiplicative V) where
  toFun := repAut V
  map_one' := by
    ext v
    change Multiplicative.ofAdd (V.ρ 1 (Multiplicative.toAdd v)) = v
    rw [map_one]; rfl
  map_mul' g h := by
    ext v
    change Multiplicative.ofAdd (V.ρ (g * h) (Multiplicative.toAdd v)) =
      Multiplicative.ofAdd (V.ρ g (V.ρ h (Multiplicative.toAdd v)))
    rw [map_mul]; rfl

/-- The semidirect product `V ⋊ Γ` of a representation. -/
abbrev RepSD := Multiplicative V ⋊[repHom V] Γ

theorem cocycle_mul (c : cocycles₁ V) (g h : Γ) :
    (c (g * h) : V) = V.ρ g (c h) + c g :=
  (mem_cocycles₁_iff _).mp c.property g h

/-- A one-cocycle gives a homomorphic section `Γ → V ⋊ Γ`. -/
def sectionHom (c : cocycles₁ V) : Γ →* RepSD V where
  toFun g := ⟨Multiplicative.ofAdd (c g : V), g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (c 1 : V) = 1
      rw [cocycles₁_map_one]; rfl
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (c (g * h) : V) =
        Multiplicative.ofAdd (c g : V) * repHom V g (Multiplicative.ofAdd (c h : V))
      rw [cocycle_mul]
      change _ = Multiplicative.ofAdd ((c g : V) + V.ρ g (c h))
      rw [add_comm]
    · rfl

/-- A homomorphic section `Γ → V ⋊ Γ` gives a one-cocycle. -/
def cocycleOfSection (F : Γ →* RepSD V) (hF : ∀ g, (F g).right = g) : cocycles₁ V :=
  ⟨fun g => Multiplicative.toAdd (F g).left, (mem_cocycles₁_iff _).mpr (fun g h => by
    have h1 := congrArg SemidirectProduct.left (map_mul F g h)
    rw [SemidirectProduct.mul_left, hF] at h1
    change Multiplicative.toAdd (F (g * h)).left = _
    rw [h1]
    change (Multiplicative.toAdd (F g).left + V.ρ g (Multiplicative.toAdd (F h).left)) = _
    rw [add_comm])⟩

@[simp] theorem cocycleOfSection_apply (F : Γ →* RepSD V) (hF : ∀ g, (F g).right = g) (g : Γ) :
    (cocycleOfSection V F hF g : V) = Multiplicative.toAdd (F g).left := rfl

end Section




section Cyclic

variable (W : Rep.{0} ℚ (Multiplicative ℤ))

/-- A cocycle on the infinite cyclic group is determined by its value at the generator. -/
theorem cocycle_ext_cyclic (c d : cocycles₁ W) (h : (c (Multiplicative.ofAdd 1) : W) = d (Multiplicative.ofAdd 1)) :
    c = d := by
  have hs : sectionHom W c = sectionHom W d := by
    apply (zpowersHom (RepSD W)).symm.injective
    change (sectionHom W c) (Multiplicative.ofAdd 1) = (sectionHom W d) (Multiplicative.ofAdd 1)
    change (⟨Multiplicative.ofAdd (c (Multiplicative.ofAdd 1) : W), Multiplicative.ofAdd 1⟩ : RepSD W) =
      ⟨Multiplicative.ofAdd (d (Multiplicative.ofAdd 1) : W), Multiplicative.ofAdd 1⟩
    rw [h]
  apply Subtype.ext
  funext g
  have := congrArg (fun F : Multiplicative ℤ →* RepSD W => (F g).left) hs
  exact congrArg Multiplicative.toAdd this

/-- Every value at the generator is the value of a cocycle on the infinite cyclic group. -/
theorem exists_cocycle_cyclic (w : W) : ∃ c : cocycles₁ W, (c (Multiplicative.ofAdd 1) : W) = w := by
  let F : Multiplicative ℤ →* RepSD W :=
    zpowersHom (RepSD W) ⟨Multiplicative.ofAdd w, Multiplicative.ofAdd 1⟩
  have hF : ∀ g, (F g).right = g := by
    have h : (SemidirectProduct.rightHom).comp F = MonoidHom.id (Multiplicative ℤ) := by
      apply (zpowersHom (Multiplicative ℤ)).symm.injective
      change SemidirectProduct.rightHom (F (Multiplicative.ofAdd 1)) = Multiplicative.ofAdd 1
      simp [F]
    intro g
    exact DFunLike.congr_fun h g
  refine ⟨cocycleOfSection W F hF, ?_⟩
  change Multiplicative.toAdd (F (Multiplicative.ofAdd 1)).left = w
  simp [F]

end Cyclic



section Extension

open TernaryPoly.LowDegreeHochschildSerre

variable {Δ Γ : Type} [Group Δ] [Group Γ] (V : Rep.{0} ℚ Γ)

/-- A cocycle on a subgroup (or any group mapping to `Γ`) gives a homomorphism into `V ⋊ Γ`. -/
def homOfCocycle (ι : Δ →* Γ) (c : cocycles₁ (Rep.res ι V)) : Δ →* RepSD V where
  toFun d := ⟨Multiplicative.ofAdd (c d : V), ι d⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (c 1 : V) = 1
      rw [cocycles₁_map_one]; rfl
    · exact map_one ι
  map_mul' d e := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (c (d * e) : V) =
        Multiplicative.ofAdd (c d : V) * repHom V (ι d) (Multiplicative.ofAdd (c e : V))
      have h := (mem_cocycles₁_iff _).mp c.property d e
      change (c (d * e) : V) = V.ρ (ι d) (c e) + c d at h
      rw [h]
      change _ = Multiplicative.ofAdd ((c d : V) + V.ρ (ι d) (c e))
      rw [add_comm]
    · exact map_mul ι d e

@[simp] theorem homOfCocycle_left (ι : Δ →* Γ) (c : cocycles₁ (Rep.res ι V)) (d : Δ) :
    (homOfCocycle V ι c d).left = Multiplicative.ofAdd (c d : V) := rfl

@[simp] theorem homOfCocycle_right (ι : Δ →* Γ) (c : cocycles₁ (Rep.res ι V)) (d : Δ) :
    (homOfCocycle V ι c d).right = ι d := rfl

end Extension



section Surj

open TernaryPoly.LowDegreeHochschildSerre

variable {N : Type} [Group N] (φ : Multiplicative ℤ →* MulAut N) (A : Rep.{0} ℚ (G φ))
  (z : cocycles₁ (radicalRep φ A)) (s : cocycles₁ (Rep.res (qIn φ) A))

/-- The two homomorphisms into `A ⋊ G` assembled from a radical cocycle and a quotient cocycle. -/
def compatProp (q : Multiplicative ℤ) : Prop :=
  ∀ n : N, homOfCocycle A (nIn φ) z (φ q n) =
    homOfCocycle A (qIn φ) s q * homOfCocycle A (nIn φ) z n * (homOfCocycle A (qIn φ) s q)⁻¹

theorem compat_one : compatProp φ A z s 1 := by
  intro n
  simp

theorem compat_mul {q r : Multiplicative ℤ} (hq : compatProp φ A z s q) (hr : compatProp φ A z s r) :
    compatProp φ A z s (q * r) := by
  intro n
  rw [map_mul, MulAut.mul_apply, hq, hr, map_mul]
  simp [mul_assoc]

theorem compat_inv {q : Multiplicative ℤ} (hq : compatProp φ A z s q) :
    compatProp φ A z s q⁻¹ := by
  intro n
  have h := hq (φ q⁻¹ n)
  rw [show φ q (φ q⁻¹ n) = n by rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl] at h
  rw [map_inv, h]
  simp [mul_assoc]

theorem compat_of_generator (hgen : compatProp φ A z s (Multiplicative.ofAdd 1)) (q : Multiplicative ℤ) :
    compatProp φ A z s q := by
  have hq : q = (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd q) := by
    rw [← ofAdd_zsmul]; simp
  rw [hq]
  generalize Multiplicative.toAdd q = k
  induction k using Int.induction_on with
  | zero => simpa using compat_one φ A z s
  | succ k ih =>
    rw [zpow_add_one]
    exact compat_mul φ A z s ih hgen
  | pred k ih =>
    rw [zpow_sub_one]
    exact compat_mul φ A z s ih (compat_inv φ A z s hgen)

theorem compat_generator (v : A)
    (hv : ∀ n : N, A.ρ (qIn φ (Multiplicative.ofAdd 1)) (z (φ (Multiplicative.ofAdd 1)⁻¹ n)) - z n =
      A.ρ (nIn φ n) v - v)
    (hs : (s (Multiplicative.ofAdd 1) : A) = v) :
    compatProp φ A z s (Multiplicative.ofAdd 1) := by
  intro n
  set t : Multiplicative ℤ := Multiplicative.ofAdd 1 with ht
  have hn := hv (φ t n)
  rw [show φ t⁻¹ (φ t n) = n by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl] at hn
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
      homOfCocycle_left, homOfCocycle_right]
    apply Multiplicative.toAdd.injective
    have hconj : (qIn φ t * nIn φ n) * (qIn φ t)⁻¹ = nIn φ (φ t n) := by
      rw [← map_inv]; exact (SemidirectProduct.inl_aut _ _).symm
    change (z (φ t n) : A) = _
    simp only [toAdd_mul, toAdd_ofAdd]
    change (z (φ t n) : A) = (s t : A) + A.ρ (qIn φ t) (z n) +
      A.ρ (qIn φ t * nIn φ n) (A.ρ (qIn φ t)⁻¹ (-(s t : A)))
    rw [← Module.End.mul_apply, ← map_mul, mul_assoc, hconj] at *
    rw [hs, map_neg]
    have h2 : (z (φ t n) : A) = A.ρ (qIn φ t) (z n) - (A.ρ (nIn φ (φ t n)) v - v) := by
      rw [← hn]; abel
    rw [h2]; abel
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, homOfCocycle_right]
    rw [← map_inv]; exact SemidirectProduct.inl_aut _ _

/-- Extension of a radical cocycle whose class is fixed by the generator of the infinite cyclic quotient. -/
theorem exists_extension (v : A)
    (hv : ∀ n : N, A.ρ (qIn φ (Multiplicative.ofAdd 1)) (z (φ (Multiplicative.ofAdd 1)⁻¹ n)) - z n =
      A.ρ (nIn φ n) v - v) :
    ∃ c : cocycles₁ A, (∀ n : N, (c (nIn φ n) : A) = z n) ∧
      (c (qIn φ (Multiplicative.ofAdd 1)) : A) = v := by
  obtain ⟨s, hs⟩ := exists_cocycle_cyclic (Rep.res (qIn φ) A) v
  have hcompat := compat_of_generator φ A z s (compat_generator φ A z s v hv hs)
  let F : G φ →* RepSD A := SemidirectProduct.lift (homOfCocycle A (nIn φ) z) (homOfCocycle A (qIn φ) s)
    (fun q => MonoidHom.ext fun n => hcompat q n)
  have hF : ∀ g, (F g).right = g := by
    have h : (SemidirectProduct.rightHom : RepSD A →* G φ).comp F = MonoidHom.id (G φ) := by
      apply SemidirectProduct.hom_ext
      · exact MonoidHom.ext fun n => by
          change (F (nIn φ n)).right = nIn φ n
          simp [F]
      · exact MonoidHom.ext fun q => by
          change (F (qIn φ q)).right = qIn φ q
          simp [F]
    intro g
    exact DFunLike.congr_fun h g
  refine ⟨cocycleOfSection A F hF, fun n => ?_, ?_⟩
  · change Multiplicative.toAdd (F (nIn φ n)).left = _
    simp [F]
  · change Multiplicative.toAdd (F (qIn φ (Multiplicative.ofAdd 1))).left = v
    simp [F, hs]

end Surj

section Sequence

open TernaryPoly.LowDegreeHochschildSerre

variable {N Q : Type} [Group N] [Group Q] (φ : Q →* MulAut N) (A : Rep.{0} ℚ (G φ))

/-- The inclusion of the radical invariants into `A`, equivariant for `G` acting through `Q`. -/
def inflCoeff : Rep.res (SemidirectProduct.rightHom : G φ →* Q) (invariantsRep φ A) ⟶ A :=
  Rep.ofHom ⟨(radicalRep φ A).ρ.invariants.subtype, by
    intro g
    apply LinearMap.ext
    intro v
    exact (action_invariant φ A v g).symm⟩

/-- Inflation `H¹(Q, A^N) → H¹(G, A)`. -/
def infl : groupCohomology (invariantsRep φ A) 1 ⟶ groupCohomology A 1 :=
  groupCohomology.map SemidirectProduct.rightHom (inflCoeff φ A) 1

/-- Restriction `H¹(G, A) → H¹(N, A)`. -/
def resp : groupCohomology A 1 ⟶ groupCohomology (radicalRep φ A) 1 :=
  groupCohomology.map (nIn φ) (𝟙 (radicalRep φ A)) 1

theorem resp_H1π (c : cocycles₁ A) :
    resp φ A (H1π A c) = H1π (radicalRep φ A) (restrictOne φ A c) := by
  rw [resp, H1π_comp_map_apply]
  rfl

/-- The inflated cocycle. -/
def inflCocycle (b : cocycles₁ (invariantsRep φ A)) : cocycles₁ A :=
  mapCocycles₁ SemidirectProduct.rightHom (inflCoeff φ A) b

@[simp] theorem inflCocycle_apply (b : cocycles₁ (invariantsRep φ A)) (g : G φ) :
    (inflCocycle φ A b g : A) = ((b g.right : (radicalRep φ A).ρ.invariants) : A) := rfl

theorem infl_H1π (b : cocycles₁ (invariantsRep φ A)) :
    infl φ A (H1π _ b) = H1π A (inflCocycle φ A b) := by
  rw [infl, H1π_comp_map_apply]
  rfl


theorem infl_injective : Function.Injective (infl φ A).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H1_induction_on with | h b => ?_
  have h0 : H1π A (inflCocycle φ A b) = 0 := by
    rw [← infl_H1π]; exact hx
  obtain ⟨u, hu⟩ := (H1π_eq_zero_iff _).mp h0
  have hinv : u ∈ (radicalRep φ A).ρ.invariants := by
    rw [Representation.mem_invariants]
    intro n
    have h1 := congrFun hu (nIn φ n)
    change A.ρ (nIn φ n) u - u = _ at h1
    rw [inflCocycle_apply] at h1
    have h2 : ((b ((nIn φ n).right) : (radicalRep φ A).ρ.invariants) : A) = 0 := by
      rw [SemidirectProduct.right_inl, cocycles₁_map_one]; rfl
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  rw [H1π_eq_zero_iff]
  refine ⟨⟨u, hinv⟩, ?_⟩
  funext q
  apply Subtype.ext
  have h1 := congrFun hu (qIn φ q)
  change A.ρ (qIn φ q) u - u = _ at h1
  rw [inflCocycle_apply, SemidirectProduct.right_inr] at h1
  exact h1

theorem resp_infl (b : cocycles₁ (invariantsRep φ A)) :
    restrictOne φ A (inflCocycle φ A b) = 0 := by
  apply Subtype.ext
  funext n
  change ((b ((nIn φ n).right) : (radicalRep φ A).ρ.invariants) : A) = 0
  rw [SemidirectProduct.right_inl, cocycles₁_map_one]; rfl

theorem ker_resp_eq_range_infl :
    LinearMap.ker (resp φ A).hom = LinearMap.range (infl φ A).hom := by
  ext x
  constructor
  · intro hx
    induction x using H1_induction_on with | h c => ?_
    have h0 : H1π (radicalRep φ A) (restrictOne φ A c) = 0 := by
      rw [← resp_H1π]; exact hx
    obtain ⟨u, hu⟩ := (H1π_eq_zero_iff _).mp h0
    let c' : cocycles₁ A := c - ⟨d₀₁ A u, d₀₁_apply_mem_cocycles₁ (A := A) u⟩
    have hc' : ∀ n, c' (nIn φ n) = 0 := by
      intro n
      have h1 := congrFun hu n
      change A.ρ (nIn φ n) u - u = c (nIn φ n) at h1
      change c (nIn φ n) - (A.ρ (nIn φ n) u - u) = 0
      rw [h1, sub_self]
    refine ⟨H1π _ (quotientOne φ A c' hc'), ?_⟩
    change infl φ A (H1π _ (quotientOne φ A c' hc')) = _
    rw [infl_H1π]
    have hinf : inflCocycle φ A (quotientOne φ A c' hc') = c' := by
      apply Subtype.ext
      funext g
      exact (one_value_quotient φ A c' hc' g).symm
    rw [hinf]
    have hdiff : H1π A c' = H1π A c := by
      rw [H1π_eq_iff]
      refine ⟨-u, ?_⟩
      funext g
      change (d₀₁ A (-u)) g = (c g - (d₀₁ A u) g) - c g
      rw [map_neg]
      change -(d₀₁ A u g) = _
      abel
    exact hdiff
  · rintro ⟨y, rfl⟩
    induction y using H1_induction_on with | h b => ?_
    change resp φ A (infl φ A (H1π _ b)) = 0
    rw [infl_H1π, resp_H1π, resp_infl]
    exact map_zero (H1π (radicalRep φ A)).hom

/-- Invariance under the generator of `ℤ` is invariance under the whole quotient. -/
theorem invariant_of_generator {N : Type} [Group N] (φ : Multiplicative ℤ →* MulAut N) (A : Rep.{0} ℚ (G φ))
    (x : groupCohomology (radicalRep φ A) 1)
    (hx : (cohomologyRep φ A 1).ρ (Multiplicative.ofAdd 1) x = x) (q : Multiplicative ℤ) :
    (cohomologyRep φ A 1).ρ q x = x := by
  have hinv : (cohomologyRep φ A 1).ρ (Multiplicative.ofAdd 1)⁻¹ x = x := by
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hq : q = (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd q) := by
    rw [← ofAdd_zsmul]; simp
  rw [hq]
  generalize Multiplicative.toAdd q = k
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, map_mul, Module.End.mul_apply, hx, ih]
  | pred k ih =>
    rw [zpow_sub_one, map_mul, Module.End.mul_apply, hinv, ih]

/-- For an infinite cyclic quotient the image of the restriction is exactly the space of vectors of
`H¹(N, A)` fixed by the generator (equivalently, by the whole quotient). -/
theorem mem_range_resp_iff {N : Type} [Group N] (φ : Multiplicative ℤ →* MulAut N) (A : Rep.{0} ℚ (G φ))
    (x : groupCohomology (radicalRep φ A) 1) :
    x ∈ LinearMap.range (resp φ A).hom ↔
      (cohomologyRep φ A 1).ρ (Multiplicative.ofAdd 1) x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    induction y using H1_induction_on with | h c => ?_
    change (cohomologyRep φ A 1).ρ _ (resp φ A (H1π A c)) = resp φ A (H1π A c)
    rw [resp_H1π]
    exact restrictOne_class_invariant φ A c _
  · intro ht
    induction x using H1_induction_on with | h z => ?_
    rw [H1π_action, H1π_eq_iff] at ht
    obtain ⟨v, hv⟩ := ht
    obtain ⟨c, hc, -⟩ := exists_extension φ A z v (fun n => by
      have h1 := congrFun hv n
      change A.ρ (nIn φ n) v - v = _ at h1
      rw [h1]
      rfl)
    refine ⟨H1π A c, ?_⟩
    change resp φ A (H1π A c) = _
    rw [resp_H1π]
    congr 1
    exact Subtype.ext (funext hc)

end Sequence

end TernaryPeriodPolynomials.Argument.EdgeCohomology
