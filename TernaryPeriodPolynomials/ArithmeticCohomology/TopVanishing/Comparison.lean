module

public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Lift

@[expose] public section


/-!
# Comparison of free resolutions

For complexes of permutation modules, a free complex maps equivariantly to an exact one,
extending the identity of the augmentation point; a chain endomorphism of a free exact complex
that is the identity on the augmentation point is homotopic to the identity. Combining the two for
the homogeneous complex `C` and a free resolution `X` of length `N`: since `X` has no cells in
index `N + 2`, the composite `C → X → C` kills the boundaries in index `N + 1`, and the homotopy
`s` satisfies `d s d = d` there.
-/

noncomputable section

namespace TernaryPeriodPolynomials.TopVanishing

variable {Λ : Type} [Group Λ]

theorem PermutationComplex.d_d_apply (C : PermutationComplex Λ) (k : ℕ)
    (v : C.cell (k + 1 + 1) →₀ ℂ) : C.d k (C.d (k + 1) v) = 0 :=
  LinearMap.congr_fun (C.d_comp_d k) v

attribute [instance] FreeResolution.point

/-- The map collapsing chains onto the augmentation point. -/
def pointMap (S T : Type) [Unique T] : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (fun _ => default)

theorem pointMap_single (S T : Type) [Unique T] (s : S) (a : ℂ) :
    pointMap S T (Finsupp.single s a) = Finsupp.single default a :=
  Finsupp.mapDomain_single

theorem pointMap_equivariant (S T : Type) [MulAction Λ S] [MulAction Λ T] [Unique T] :
    Equivariant Λ (pointMap S T) :=
  equivariant_of_single fun γ s => by
    rw [pointMap_single, pointMap_single, chainAct_single,
      Subsingleton.elim (γ • (default : T)) default]

theorem pointMap_comp_pointMap (S T : Type) [Unique S] [Unique T] :
    pointMap T S ∘ₗ pointMap S T = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro s a
  rw [LinearMap.comp_apply, pointMap_single, pointMap_single, LinearMap.id_apply,
    Subsingleton.elim (default : S) s]

section ChainMap

variable {P Q : PermutationComplex Λ} (hP : P.Free) (hQ : Q.Exact) [Unique (Q.cell 0)]

omit [Unique (Q.cell 0)] in
/-- A map in index `k + 1` commuting with the boundaries kills the boundaries of index `k + 2`
after one more boundary. -/
theorem cycle_of_comm {k : ℕ} {m : (P.cell k →₀ ℂ) →ₗ[ℂ] (Q.cell k →₀ ℂ)}
    {m' : (P.cell (k + 1) →₀ ℂ) →ₗ[ℂ] (Q.cell (k + 1) →₀ ℂ)}
    (h : Q.d k ∘ₗ m' = m ∘ₗ P.d k) : Q.d k ∘ₗ m' ∘ₗ P.d (k + 1) = 0 :=
  LinearMap.ext fun v => by
    have e : Q.d k (m' (P.d (k + 1) v)) = m (P.d k (P.d (k + 1) v)) :=
      LinearMap.congr_fun h (P.d (k + 1) v)
    show Q.d k (m' (P.d (k + 1) v)) = 0
    rw [e, P.d_d_apply k v, map_zero]

include hP hQ in
theorem exists_chainMap_zero :
    ∃ m : (P.cell (0 + 1) →₀ ℂ) →ₗ[ℂ] (Q.cell (0 + 1) →₀ ℂ),
      Equivariant Λ m ∧ Q.d 0 ∘ₗ m = pointMap (P.cell 0) (Q.cell 0) ∘ₗ P.d 0 :=
  exists_equivariant_lift (hP 0) _ ((pointMap_equivariant _ _).comp (P.equivariant 0)) (Q.d 0)
    (Q.equivariant 0) fun _ => by
      rw [hQ.1]
      exact Submodule.mem_top

omit [Unique (Q.cell 0)] in
include hP hQ in
theorem exists_chainMap_succ (k : ℕ) (m : (P.cell (k + 1) →₀ ℂ) →ₗ[ℂ] (Q.cell (k + 1) →₀ ℂ))
    (hm : Equivariant Λ m) (cycle : Q.d k ∘ₗ m ∘ₗ P.d (k + 1) = 0) :
    ∃ m' : (P.cell (k + 1 + 1) →₀ ℂ) →ₗ[ℂ] (Q.cell (k + 1 + 1) →₀ ℂ),
      Equivariant Λ m' ∧ Q.d (k + 1) ∘ₗ m' = m ∘ₗ P.d (k + 1) :=
  exists_equivariant_lift (hP (k + 1)) _ (hm.comp (P.equivariant (k + 1))) (Q.d (k + 1))
    (Q.equivariant (k + 1)) fun s => hQ.2 k (by
      rw [LinearMap.mem_ker]
      exact LinearMap.congr_fun cycle (Finsupp.single s 1))

/-- The chain map in positive indices, with its equivariance and the cycle condition. -/
def chainMapAux : (k : ℕ) → {m : (P.cell (k + 1) →₀ ℂ) →ₗ[ℂ] (Q.cell (k + 1) →₀ ℂ) //
    Equivariant Λ m ∧ Q.d k ∘ₗ m ∘ₗ P.d (k + 1) = 0}
  | 0 => ⟨(exists_chainMap_zero hP hQ).choose, (exists_chainMap_zero hP hQ).choose_spec.1,
      cycle_of_comm (exists_chainMap_zero hP hQ).choose_spec.2⟩
  | k + 1 =>
    ⟨(exists_chainMap_succ hP hQ k (chainMapAux k).1 (chainMapAux k).2.1
        (chainMapAux k).2.2).choose,
      (exists_chainMap_succ hP hQ k (chainMapAux k).1 (chainMapAux k).2.1
        (chainMapAux k).2.2).choose_spec.1,
      cycle_of_comm (exists_chainMap_succ hP hQ k (chainMapAux k).1 (chainMapAux k).2.1
        (chainMapAux k).2.2).choose_spec.2⟩

/-- An equivariant chain map from a free complex to an exact complex, extending the identity of
the augmentation point. -/
def chainMap : (k : ℕ) → (P.cell k →₀ ℂ) →ₗ[ℂ] (Q.cell k →₀ ℂ)
  | 0 => pointMap (P.cell 0) (Q.cell 0)
  | k + 1 => (chainMapAux hP hQ k).1

theorem chainMap_zero : chainMap hP hQ 0 = pointMap (P.cell 0) (Q.cell 0) := rfl

theorem chainMap_succ (k : ℕ) : chainMap hP hQ (k + 1) = (chainMapAux hP hQ k).1 := rfl

theorem chainMap_equivariant : ∀ k, Equivariant Λ (chainMap hP hQ k)
  | 0 => pointMap_equivariant _ _
  | k + 1 => (chainMapAux hP hQ k).2.1

theorem chainMap_comm : ∀ k, Q.d k ∘ₗ chainMap hP hQ (k + 1) = chainMap hP hQ k ∘ₗ P.d k
  | 0 => (exists_chainMap_zero hP hQ).choose_spec.2
  | k + 1 => (exists_chainMap_succ hP hQ k (chainMapAux hP hQ k).1 (chainMapAux hP hQ k).2.1
      (chainMapAux hP hQ k).2.2).choose_spec.2

theorem chainMap_comm_apply (k : ℕ) (v : P.cell (k + 1) →₀ ℂ) :
    Q.d k (chainMap hP hQ (k + 1) v) = chainMap hP hQ k (P.d k v) :=
  LinearMap.congr_fun (chainMap_comm hP hQ k) v

end ChainMap

section Homotopy

variable {C : PermutationComplex Λ} (hC : C.Free) (hCe : C.Exact)
  (φ : (k : ℕ) → (C.cell k →₀ ℂ) →ₗ[ℂ] (C.cell k →₀ ℂ))
  (hφ : ∀ k, Equivariant Λ (φ k)) (comm : ∀ k, C.d k ∘ₗ φ (k + 1) = φ k ∘ₗ C.d k)
  (zero : φ 0 = LinearMap.id)

include hC hCe hφ comm in
theorem exists_homotopy_succ (k : ℕ) (s : (C.cell k →₀ ℂ) →ₗ[ℂ] (C.cell (k + 1) →₀ ℂ))
    (hs : Equivariant Λ s) (h : C.d k ∘ₗ s ∘ₗ C.d k = C.d k - φ k ∘ₗ C.d k) :
    ∃ s' : (C.cell (k + 1) →₀ ℂ) →ₗ[ℂ] (C.cell (k + 1 + 1) →₀ ℂ),
      Equivariant Λ s' ∧ C.d (k + 1) ∘ₗ s' = LinearMap.id - φ (k + 1) - s ∘ₗ C.d k :=
  exists_equivariant_lift (hC k) _ ((equivariant_id.sub (hφ (k + 1))).sub
      (hs.comp (C.equivariant k))) (C.d (k + 1)) (C.equivariant (k + 1)) fun x => hCe.2 k (by
    have e1 : C.d k (φ (k + 1) (Finsupp.single x 1)) = φ k (C.d k (Finsupp.single x 1)) :=
      LinearMap.congr_fun (comm k) (Finsupp.single x 1)
    have e2 : C.d k (s (C.d k (Finsupp.single x 1))) =
        C.d k (Finsupp.single x 1) - φ k (C.d k (Finsupp.single x 1)) :=
      LinearMap.congr_fun h (Finsupp.single x 1)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, map_sub, map_sub, e1, e2, sub_self])

/-- The homotopy `s` with `d s + s d = 1 - φ`, recorded through its composite with `d`. -/
def homotopyAux : (k : ℕ) → {s : (C.cell k →₀ ℂ) →ₗ[ℂ] (C.cell (k + 1) →₀ ℂ) //
    Equivariant Λ s ∧ C.d k ∘ₗ s ∘ₗ C.d k = C.d k - φ k ∘ₗ C.d k}
  | 0 => ⟨0, equivariant_zero, LinearMap.ext fun v => by simp [zero]⟩
  | k + 1 =>
    ⟨(exists_homotopy_succ hC hCe φ hφ comm k (homotopyAux k).1 (homotopyAux k).2.1
        (homotopyAux k).2.2).choose,
      (exists_homotopy_succ hC hCe φ hφ comm k (homotopyAux k).1 (homotopyAux k).2.1
        (homotopyAux k).2.2).choose_spec.1,
      LinearMap.ext fun v => by
        have e : C.d (k + 1) ((exists_homotopy_succ hC hCe φ hφ comm k (homotopyAux k).1
            (homotopyAux k).2.1 (homotopyAux k).2.2).choose (C.d (k + 1) v)) =
            C.d (k + 1) v - φ (k + 1) (C.d (k + 1) v) -
              (homotopyAux k).1 (C.d k (C.d (k + 1) v)) :=
          LinearMap.congr_fun (exists_homotopy_succ hC hCe φ hφ comm k (homotopyAux k).1
            (homotopyAux k).2.1 (homotopyAux k).2.2).choose_spec.2 (C.d (k + 1) v)
        show C.d (k + 1) ((exists_homotopy_succ hC hCe φ hφ comm k (homotopyAux k).1
            (homotopyAux k).2.1 (homotopyAux k).2.2).choose (C.d (k + 1) v)) =
          C.d (k + 1) v - φ (k + 1) (C.d (k + 1) v)
        rw [e, C.d_d_apply k v, map_zero, sub_zero]⟩

end Homotopy

/-- Comparison with a free resolution of length `N`: a free exact complex `C` with a single
augmentation point has an equivariant `s` with `d s d = d` on index `N + 2`. -/
theorem exists_splitting {N : ℕ} (X : FreeResolution Λ N) {C : PermutationComplex Λ}
    (hC : C.Free) (hCe : C.Exact) [Unique (C.cell 0)] :
    ∃ s : (C.cell (N + 1) →₀ ℂ) →ₗ[ℂ] (C.cell (N + 1 + 1) →₀ ℂ),
      Equivariant Λ s ∧ C.d (N + 1) ∘ₗ s ∘ₗ C.d (N + 1) = C.d (N + 1) := by
  have comm : ∀ k, C.d k ∘ₗ (chainMap X.free hCe (k + 1) ∘ₗ chainMap hC X.exact (k + 1)) =
      (chainMap X.free hCe k ∘ₗ chainMap hC X.exact k) ∘ₗ C.d k := fun k =>
    LinearMap.ext fun v => by
      show C.d k (chainMap X.free hCe (k + 1) (chainMap hC X.exact (k + 1) v)) =
        chainMap X.free hCe k (chainMap hC X.exact k (C.d k v))
      rw [chainMap_comm_apply, chainMap_comm_apply]
  have zero : chainMap X.free hCe 0 ∘ₗ chainMap hC X.exact 0 = LinearMap.id :=
    pointMap_comp_pointMap _ _
  have top : ∀ v : C.cell (N + 1 + 1) →₀ ℂ, chainMap hC X.exact (N + 1) (C.d (N + 1) v) = 0 := by
    intro v
    have cycle : chainMap hC X.exact (N + 1) (C.d (N + 1) v) ∈ LinearMap.ker (X.d N) := by
      rw [LinearMap.mem_ker, chainMap_comm_apply, C.d_d_apply N v, map_zero]
    obtain ⟨u, hu⟩ := X.exact.2 N cycle
    have hu0 : u = 0 := Finsupp.ext fun t => (X.top.false t).elim
    rw [← hu, hu0, map_zero]
  let S := homotopyAux hC hCe (fun k => chainMap X.free hCe k ∘ₗ chainMap hC X.exact k)
    (fun k => (chainMap_equivariant X.free hCe k).comp (chainMap_equivariant hC X.exact k))
    comm zero (N + 1)
  refine ⟨S.1, S.2.1, LinearMap.ext fun v => ?_⟩
  have e : C.d (N + 1) (S.1 (C.d (N + 1) v)) = C.d (N + 1) v -
      chainMap X.free hCe (N + 1) (chainMap hC X.exact (N + 1) (C.d (N + 1) v)) :=
    LinearMap.congr_fun S.2.2 v
  show C.d (N + 1) (S.1 (C.d (N + 1) v)) = C.d (N + 1) v
  rw [e, top v, map_zero, sub_zero]

end TernaryPeriodPolynomials.TopVanishing
