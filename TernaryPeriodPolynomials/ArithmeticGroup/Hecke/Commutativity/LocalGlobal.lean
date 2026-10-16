module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.LocalLevel

@[expose] public section


/-!
# Elements of the adelic level with prescribed local components; local–global

* `ofLocal M h`: for rational matrices `M v` in the local level at each place
  `v`, the element of `GL₃(Ẑ)` whose `v`-component is `M v`; its image lies in
  `finiteLevel` (`ofLocal_mem`).
* `mem_rationalLevel_of_locK`: a rational matrix in the local level at every
  place lies in `rationalLevel`.
* `mem_dcoset_of_local`: if `y = K₁ v · x · K₂ v` for every place `v`, with
  `K₁ v, K₂ v` in the local level at `v`, then `y ∈ Γ x Γ`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix IsDedekindDomain
open TernaryPeriodPolynomials.HeckeStability

namespace TernaryPeriodPolynomials.HeckeCommutativity

/-- Entrywise local lift of a family of rational matrices. -/
def localMat (M : FinitePlace → Matrix (Fin 3) (Fin 3) ℚ) (h : ∀ v i j, IntAt v (M v i j)) :
    Matrix (Fin 3) (Fin 3) IntegralAdeles :=
  fun i j v => ⟨algebraMap ℚ (v.adicCompletion ℚ) (M v i j), h v i j⟩

theorem localMat_apply (M : FinitePlace → Matrix (Fin 3) (Fin 3) ℚ) (h : ∀ v i j, IntAt v (M v i j))
    (i j : Fin 3) (v : FinitePlace) :
    ((localMat M h i j v : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
      algebraMap ℚ (v.adicCompletion ℚ) (M v i j) := rfl

theorem localMat_mul (M N : FinitePlace → Matrix (Fin 3) (Fin 3) ℚ)
    (hM : ∀ v i j, IntAt v (M v i j)) (hN : ∀ v i j, IntAt v (N v i j))
    (hMN : ∀ v i j, IntAt v ((M v * N v) i j)) :
    localMat M hM * localMat N hN = localMat (fun v => M v * N v) hMN := by
  apply Matrix.ext
  intro i j
  funext v
  apply Subtype.ext
  rw [localMat_apply, Matrix.mul_apply, Matrix.mul_apply, map_sum, Finset.sum_apply]
  rw [AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Pi.mul_apply, MulMemClass.coe_mul, localMat_apply, localMat_apply, map_mul]

theorem localMat_eq_one (M : FinitePlace → Matrix (Fin 3) (Fin 3) ℚ)
    (hM : ∀ v i j, IntAt v (M v i j)) (h1 : ∀ v, M v = 1) : localMat M hM = 1 := by
  apply Matrix.ext
  intro i j
  funext v
  apply Subtype.ext
  rw [localMat_apply, h1 v, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- The element of `GL₃(Ẑ)` with prescribed local components. -/
def ofLocalInt (M : FinitePlace → RationalGL3) (h : ∀ v, LocK (M v) v) :
    GeneralLinearGroup (Fin 3) IntegralAdeles where
  val := localMat (fun v => (M v).val) (fun v => (h v).1)
  inv := localMat (fun v => ((M v)⁻¹).val) (fun v => (h v).2.1)
  val_inv := by
    rw [localMat_mul _ _ _ _ (fun v => by rw [Units.mul_inv]; exact (locK_one v).1)]
    exact localMat_eq_one _ _ (fun v => Units.mul_inv _)
  inv_val := by
    rw [localMat_mul _ _ _ _ (fun v => by rw [Units.inv_mul]; exact (locK_one v).1)]
    exact localMat_eq_one _ _ (fun v => Units.inv_mul _)

/-- Its image in `GL₃(𝔸_f)`. -/
def ofLocal (M : FinitePlace → RationalGL3) (h : ∀ v, LocK (M v) v) : FiniteGL :=
  GeneralLinearGroup.map integralEmbedding (ofLocalInt M h)

theorem reduction_eq_of_intAt (x : IntegralAdeles) (q : ℚ) (c : ℤ)
    (hx : ((x placeThree : placeThree.adicCompletionIntegers ℚ) : placeThree.adicCompletion ℚ) =
      algebraMap ℚ _ q)
    (h : IntAt placeThree ((q - c) / 3)) : integralReduction x = c := by
  let w : placeThree.adicCompletionIntegers ℚ := ⟨_, h⟩
  have hdec : x placeThree = (c : placeThree.adicCompletionIntegers ℚ) + 3 * w := by
    apply Subtype.ext
    rw [hx]
    simp only [w, AddMemClass.coe_add, MulMemClass.coe_mul]
    have e1 : q = (c : ℚ) + 3 * ((q - c) / 3) := by ring
    conv_lhs => rw [e1]
    rw [map_add, map_mul, map_intCast, map_ofNat]
    have h3c : ((3 : placeThree.adicCompletionIntegers ℚ) : placeThree.adicCompletion ℚ) = 3 := by
      rfl
    rw [h3c]
    simp
  change PadicInt.toZMod (threeIntegralEquiv (x placeThree)) = c
  rw [hdec, map_add, map_mul, map_add, map_mul, map_intCast, map_intCast]
  have : PadicInt.toZMod (threeIntegralEquiv (3 : placeThree.adicCompletionIntegers ℚ)) = 0 := by
    rw [map_ofNat, map_ofNat]
    rfl
  rw [this, zero_mul, add_zero]

theorem ofLocal_mem (M : FinitePlace → RationalGL3) (h : ∀ v, LocK (M v) v) :
    ofLocal M h ∈ finiteLevel := by
  refine Subgroup.mem_map.mpr ⟨ofLocalInt M h, ?_, rfl⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction (ofLocalInt M h)).val = lastRow
  have e : ∀ i j, (GeneralLinearGroup.map integralReduction (ofLocalInt M h)).val i j =
      integralReduction ((ofLocalInt M h).val i j) := fun _ _ => rfl
  have hrow : ∀ j, integralReduction ((ofLocalInt M h).val 2 j) = if j = 2 then 1 else 0 := by
    intro j
    have := reduction_eq_of_intAt ((ofLocalInt M h).val 2 j) ((M placeThree).val 2 j)
      (if j = 2 then 1 else 0) rfl (by
        have h3 := (h placeThree).2.2 rfl j
        split_ifs at h3 ⊢ <;> simpa using h3)
    rw [this]
    split_ifs <;> simp
  funext j
  simp only [vecMul, dotProduct, lastRow, Fin.sum_univ_three, Pi.single_apply, e, hrow]
  fin_cases j <;> simp

/-- Equality of finite-adelic matrices is checked place by place. -/
theorem finiteMat_ext {A B : Matrix (Fin 3) (Fin 3) FiniteAdeles}
    (h : ∀ v, (finiteEvaluation v).mapMatrix A = (finiteEvaluation v).mapMatrix B) : A = B := by
  apply Matrix.ext
  intro i j
  apply RestrictedProduct.ext
  intro v
  have := congrArg (fun X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) => X i j) (h v)
  exact this

theorem ofLocal_eval (M : FinitePlace → RationalGL3) (h : ∀ v, LocK (M v) v) (v : FinitePlace) :
    (finiteEvaluation v).mapMatrix (ofLocal M h).val =
      (algebraMap ℚ (v.adicCompletion ℚ)).mapMatrix (M v).val := by
  apply Matrix.ext
  intro i j
  rfl

theorem rationalFinite_eval (x : RationalGL3) (v : FinitePlace) :
    (finiteEvaluation v).mapMatrix (rationalFinite x).val =
      (algebraMap ℚ (v.adicCompletion ℚ)).mapMatrix x.val := by
  apply Matrix.ext
  intro i j
  simp [rationalFinite, GeneralLinearGroup.map]

/-- A rational matrix in the local level everywhere lies in the arithmetic level. -/
theorem mem_rationalLevel_of_locK {x : RationalGL3} (h : ∀ v, LocK x v) : x ∈ rationalLevel := by
  apply (rationalFinite_mem_finiteLevel_iff x).mp
  have : rationalFinite x = ofLocal (fun _ => x) h := by
    apply Units.ext
    apply finiteMat_ext
    intro v
    rw [rationalFinite_eval, ofLocal_eval]
  rw [this]
  exact ofLocal_mem _ h

/-- **Local–global principle for double cosets.** -/
theorem mem_dcoset_of_finite {x y : RationalGL3} {k k' : FiniteGL} (hk : k ∈ finiteLevel)
    (hk' : k' ∈ finiteLevel) (h : rationalFinite y = k * rationalFinite x * k') :
    y ∈ dcoset rationalLevel x := by
  obtain ⟨γ, hγ, -, hu⟩ := CosetDecomposition.cosetDecomposition_all x k hk
  set u := (rationalFinite x)⁻¹ * ((rationalFinite γ)⁻¹ * k) * rationalFinite x with hudef
  have hδ : rationalFinite (x⁻¹ * γ⁻¹ * y) ∈ finiteLevel := by
    have e : rationalFinite (x⁻¹ * γ⁻¹ * y) = u * k' := by
      rw [map_mul, map_mul, map_inv, map_inv, h, hudef]
      group
    rw [e]
    exact mul_mem hu hk'
  have hδ' := (rationalFinite_mem_finiteLevel_iff _).mp hδ
  refine ⟨γ, hγ, x⁻¹ * γ⁻¹ * y, hδ', ?_⟩
  group

/-- Local version of the local–global principle. -/
theorem mem_dcoset_of_local {x y : RationalGL3} (K₁ K₂ : FinitePlace → RationalGL3)
    (h₁ : ∀ v, LocK (K₁ v) v) (h₂ : ∀ v, LocK (K₂ v) v) (h : ∀ v, y = K₁ v * x * K₂ v) :
    y ∈ dcoset rationalLevel x := by
  apply mem_dcoset_of_finite (ofLocal_mem K₁ h₁) (ofLocal_mem K₂ h₂)
  apply Units.ext
  apply finiteMat_ext
  intro v
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul, rationalFinite_eval, rationalFinite_eval,
    ofLocal_eval, ofLocal_eval, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, ← h v]

end TernaryPeriodPolynomials.HeckeCommutativity
