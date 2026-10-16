module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AwayGood
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.SumRearrange

@[expose] public section


/-!
# Commutativity of the away-from-three Hecke operators

Any realization of the literal double-coset Hecke action on degree-two
cohomology of `rationalLevel` satisfies `T s ∘ T t = T t ∘ T s` whenever the
defining matrices of `s` and `t` are `Good` (in particular for `AwayThree`
correspondences).  Consequently `awayThreeHeckeAlgebra D hecke` is commutative
for every actual boundary Hecke action.

Proof: both compositions are given on cochains by double sums
`∑_{r, r'} ρ(r r') c((r r')⁻¹ x)` whose summand depends only on `r r' Γ`; the
multiplicities are the Hecke structure constants, which are symmetric by
Gelfand's trick with the involution `x ↦ w xᵀ w⁻¹`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.HeckeCommutativity

theorem isReps_of_correspondence (t : HeckeCorrespondence) :
    IsReps rationalLevel t.representatives t.g := by
  refine ⟨?_, ?_, t.disjoint⟩
  · intro r hr
    obtain ⟨a, b, rfl⟩ := t.inDoubleCoset r hr
    exact ⟨a.val, a.2, b.val, b.2, rfl⟩
  · rintro y ⟨h₁, hh₁, h₂, hh₂, rfl⟩
    exact t.complete ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩

theorem heckeCount_comm_good {a b : RationalGL3} (ha : Good a) (hb : Good b) (c : RationalGL3) :
    heckeCount rationalLevel a b c = heckeCount rationalLevel b a c :=
  heckeCount_comm_of_pred rationalLevel ι ι_mul ι_ι (fun _ hh => ι_mem_rationalLevel hh) Good
    (fun _ _ hx hy => good_mul hx hy) (fun _ hh => good_of_mem hh)
    (fun _ hx => ι_mem_dcoset_of_good hx) ha hb c

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Double Hecke sums commute whenever the structure constants are symmetric. -/
theorem heckeCochain_comm_of_count (ρ : Representation ℂ RationalGL3 V)
    {s t : HeckeCorrespondence}
    (hcount : ∀ c, heckeCount rationalLevel s.g t.g c = heckeCount rationalLevel t.g s.g c)
    (c : cochains rationalLevel ρ 2)
    (zt : cochains rationalLevel ρ 2) (hzt : ∀ x, zt.val x = heckeCochain ρ t c x)
    (zs : cochains rationalLevel ρ 2) (hzs : ∀ x, zs.val x = heckeCochain ρ s c x)
    (x : Fin 3 → RationalGL3) :
    heckeCochain ρ s zt x = heckeCochain ρ t zs x := by
  let F : RationalGL3 → V := fun y => ρ y (c.val (fun i => y⁻¹ * x i))
  have hF : ∀ y h, h ∈ rationalLevel → F (y * h) = F y := by
    intro y h hh
    simp only [F]
    have e : (fun i => (y * h)⁻¹ * x i) = fun i => h⁻¹ * (y⁻¹ * x i) := by
      funext i; group
    rw [e, c.property ⟨h⁻¹, inv_mem hh⟩ (fun i => y⁻¹ * x i)]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
  have expand : ∀ (u w : HeckeCorrespondence) (z : cochains rationalLevel ρ 2),
      (∀ x, z.val x = heckeCochain ρ w c x) →
      heckeCochain ρ u z x = ∑ r ∈ u.representatives, ∑ r' ∈ w.representatives, F (r * r') := by
    intro u w z hz
    unfold heckeCochain
    apply Finset.sum_congr rfl
    intro r _
    rw [hz]
    unfold heckeCochain
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r' _
    simp only [F]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev]
    congr 2
    simp only [mul_assoc]
  rw [expand s t zt hzt, expand t s zs hzs]
  exact sum_pairs_comm rationalLevel F hF (isReps_of_correspondence s)
    (isReps_of_correspondence t) hcount

theorem heckeCochain_comm (ρ : Representation ℂ RationalGL3 V) {s t : HeckeCorrespondence}
    (hs : Good s.g) (ht : Good t.g) (c : cochains rationalLevel ρ 2)
    (zt : cochains rationalLevel ρ 2) (hzt : ∀ x, zt.val x = heckeCochain ρ t c x)
    (zs : cochains rationalLevel ρ 2) (hzs : ∀ x, zs.val x = heckeCochain ρ s c x)
    (x : Fin 3 → RationalGL3) :
    heckeCochain ρ s zt x = heckeCochain ρ t zs x :=
  heckeCochain_comm_of_count ρ (heckeCount_comm_good hs ht) c zt hzt zs hzs x

/-- Realized Hecke operators commute whenever the structure constants are symmetric. -/
theorem realizesHecke_comm_of_count (ρ : Representation ℂ RationalGL3 V)
    (T : HeckeCorrespondence → Module.End ℂ (H2 rationalLevel ρ)) (hT : RealizesHecke ρ T)
    {s t : HeckeCorrespondence}
    (hcount : ∀ c, heckeCount rationalLevel s.g t.g c = heckeCount rationalLevel t.g s.g c) :
    T s * T t = T t * T s := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ ξ
  obtain ⟨zt, hzt, hTt⟩ := hT t c
  obtain ⟨zs, hzs, hTs⟩ := hT s c
  obtain ⟨zst, hzst, hTst⟩ := hT s zt
  obtain ⟨zts, hzts, hTts⟩ := hT t zs
  change T s (T t (classOf rationalLevel ρ c)) = T t (T s (classOf rationalLevel ρ c))
  rw [hTt, hTst, hTs, hTts]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [hzst, hzts]
  exact heckeCochain_comm_of_count ρ hcount c.val zt.val hzt zs.val hzs x

/-- **Commutativity** of realized Hecke operators with `Good` defining matrices. -/
theorem realizesHecke_comm (ρ : Representation ℂ RationalGL3 V)
    (T : HeckeCorrespondence → Module.End ℂ (H2 rationalLevel ρ)) (hT : RealizesHecke ρ T)
    {s t : HeckeCorrespondence} (hs : Good s.g) (ht : Good t.g) :
    T s * T t = T t * T s :=
  realizesHecke_comm_of_count ρ T hT (heckeCount_comm_good hs ht)

/-- The away-from-three pair Hecke operators commute. -/
theorem pairHecke_comm {n : ℕ} (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) {s t : HeckeCorrespondence}
    (hs : AwayThree s) (ht : AwayThree t) :
    Commute (pairHecke D hecke s) (pairHecke D hecke t) := by
  have hp : hecke .plane s * hecke .plane t = hecke .plane t * hecke .plane s :=
    realizesHecke_comm (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
      (hecke .plane) (hhecke .plane) (good_of_awayThree hs) (good_of_awayThree ht)
  have hl : hecke .line s * hecke .line t = hecke .line t * hecke .line s :=
    realizesHecke_comm (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
      (hecke .line) (hhecke .line) (good_of_awayThree hs) (good_of_awayThree ht)
  unfold Commute SemiconjBy
  refine LinearMap.ext fun v => ?_
  have ha : hecke .plane s (hecke .plane t v.1) = hecke .plane t (hecke .plane s v.1) := by
    rw [← Module.End.mul_apply, hp, Module.End.mul_apply]
  have hb : hecke .line s (hecke .line t v.2) = hecke .line t (hecke .line s v.2) := by
    rw [← Module.End.mul_apply, hl, Module.End.mul_apply]
  exact Prod.ext ha hb

/-- **The away-from-three Hecke algebra is commutative.** -/
theorem awayThreeHeckeAlgebra_commute {n : ℕ} (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) {A B : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hA : A ∈ awayThreeHeckeAlgebra D hecke) (hB : B ∈ awayThreeHeckeAlgebra D hecke) :
    Commute A B := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hB
  rintro _ ⟨t, ht, rfl⟩
  apply Commute.symm
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hA
  rintro _ ⟨s, hs, rfl⟩
  exact pairHecke_comm D hecke hhecke ht hs

end TernaryPeriodPolynomials.HeckeCommutativity
