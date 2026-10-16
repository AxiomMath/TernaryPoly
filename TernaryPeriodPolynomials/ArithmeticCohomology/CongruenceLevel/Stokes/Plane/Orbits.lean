module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Orbits
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaces

@[expose] public section


/-!
# The `Γ(6)`-orbits of rational planes are the faces of type `P` of `Γ(6)`

Formalized by Claude Sonnet 5.5.  The plane analogue of `LineOrbits`: the plane `π_h = h⁻¹ ⟨e₁, e₂⟩`, `planeFacesEquivOrbits`,
`mem_stabilizer_planeOf_iff`.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPoly.IntegralGL3Congruence
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.OrdinaryFullAction (lineAction planeAction subspaceAction vectorAction)

section Planes

/-- The second basis vector of rational three-space. -/
def e1 : Fin 3 → ℚ := Pi.single 1 1

theorem finrank_stdSpan : Module.finrank ℚ (Submodule.span ℚ {e0, e1}) = 2 := by
  have hli : LinearIndependent ℚ ![e0, e1] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [e0, e1] at h0 h1
    exact ⟨h0, h1⟩
  have := finrank_span_eq_card hli
  rw [show Set.range ![e0, e1] = {e0, e1} from by ext x; simp [or_comm]] at this
  simpa using this

/-- The standard plane `⟨e₁, e₂⟩`. -/
def stdPlane : Plane :=
  ⟨Submodule.span ℚ {e0, e1}, finrank_stdSpan,
    ⟨stdLine, (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span (by simp))⟩⟩

theorem planeAction_val (g : GL (Fin 3) ℚ) (P : Plane) :
    (planeAction g P).val = P.val.map (vectorAction g).toLinearMap := rfl

theorem planeAction_mul (g h : GL (Fin 3) ℚ) (P : Plane) :
    planeAction (g * h) P = planeAction g (planeAction h P) :=
  Subtype.ext (TernaryPoly.OrdinaryFullAction.subspaceAction_mul g h P.val)

theorem planeAction_one (P : Plane) : planeAction 1 P = P :=
  Subtype.ext (TernaryPoly.OrdinaryFullAction.subspaceAction_one P.val)

theorem mulVec_mapGL (q : SL(3, ℤ)) (x : Fin 3 → ℚ) (i : Fin 3) :
    ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec x i =
      ∑ j, ((q : Matrix (Fin 3) (Fin 3) ℤ) i j : ℚ) * x j := by
  simp [Matrix.mulVec, dotProduct, Matrix.SpecialLinearGroup.mapGL]

/-- The plane `h⁻¹ ⟨e₁, e₂⟩` of an integral change of basis. -/
def planeOf (h : SL(3, ℤ)) : Plane := planeAction (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) stdPlane

theorem mulVec_e1 (q : SL(3, ℤ)) (i : Fin 3) :
    ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e1 i =
      ((q : Matrix (Fin 3) (Fin 3) ℤ) i 1 : ℚ) := by
  simp [e1, Matrix.mulVec, dotProduct, Matrix.SpecialLinearGroup.mapGL, Pi.single_apply]

theorem planeAction_mapGL_stdPlane_val (q : SL(3, ℤ)) :
    (planeAction (Matrix.SpecialLinearGroup.mapGL ℚ q) stdPlane).val =
      Submodule.span ℚ {((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0,
        ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e1} := by
  rw [planeAction_val, stdPlane, Submodule.map_span, Set.image_pair]
  have h0 : (vectorAction (Matrix.SpecialLinearGroup.mapGL ℚ q)).toLinearMap e0 =
      ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 :=
    vectorAction_apply _ _
  have h1 : (vectorAction (Matrix.SpecialLinearGroup.mapGL ℚ q)).toLinearMap e1 =
      ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e1 :=
    vectorAction_apply _ _
  rw [h0, h1]

/-- A vector with vanishing last coordinate lies in `⟨e₁, e₂⟩`. -/
theorem mem_stdSpan_of_last (x : Fin 3 → ℚ) (h : x 2 = 0) : x ∈ Submodule.span ℚ {e0, e1} := by
  refine Submodule.mem_span_pair.2 ⟨x 0, x 1, ?_⟩
  funext i
  fin_cases i
  · simp [e0, e1]
  · simp [e0, e1]
  · simp [e0, e1, h]

theorem last_of_mem_stdSpan (x : Fin 3 → ℚ) (h : x ∈ Submodule.span ℚ {e0, e1}) : x 2 = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 h
  simp [e0, e1]

/-- The stabilizer of the standard plane in `SL₃(ℤ)` is `planeBorel` (last row `(0, 0, *)`). -/
theorem planeAction_stdPlane_eq_iff (q : SL(3, ℤ)) :
    planeAction (Matrix.SpecialLinearGroup.mapGL ℚ q) stdPlane = stdPlane ↔ q ∈ planeBorel := by
  have hval := planeAction_mapGL_stdPlane_val q
  constructor
  · intro h
    have h0 : ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 ∈
        Submodule.span ℚ {e0, e1} := by
      have : ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 ∈
          (planeAction (Matrix.SpecialLinearGroup.mapGL ℚ q) stdPlane).val := by
        rw [hval]; exact Submodule.subset_span (by simp)
      rw [h] at this
      exact this
    have h1 : ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e1 ∈
        Submodule.span ℚ {e0, e1} := by
      have : ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e1 ∈
          (planeAction (Matrix.SpecialLinearGroup.mapGL ℚ q) stdPlane).val := by
        rw [hval]; exact Submodule.subset_span (by simp)
      rw [h] at this
      exact this
    refine ⟨?_, ?_⟩
    · have := last_of_mem_stdSpan _ h0
      rw [mulVec_e0] at this
      exact_mod_cast this
    · have := last_of_mem_stdSpan _ h1
      rw [mulVec_e1] at this
      exact_mod_cast this
  · rintro ⟨h0, h1⟩
    apply Subtype.ext
    rw [hval]
    have hle : Submodule.span ℚ {((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0,
        ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e1} ≤
        Submodule.span ℚ {e0, e1} := by
      rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact mem_stdSpan_of_last _ (by rw [mulVec_e0]; exact_mod_cast h0)
      · exact mem_stdSpan_of_last _ (by rw [mulVec_e1]; exact_mod_cast h1)
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [← hval]
    have := (planeAction (Matrix.SpecialLinearGroup.mapGL ℚ q) stdPlane).2.1
    rw [this]
    exact finrank_stdSpan.symm


theorem planeOf_eq_iff (h h' : SL(3, ℤ)) : planeOf h = planeOf h' ↔ h' * h⁻¹ ∈ planeBorel := by
  rw [← planeAction_stdPlane_eq_iff]
  have e1 : planeAction (Matrix.SpecialLinearGroup.mapGL ℚ (h' * h⁻¹)) stdPlane =
      planeAction (Matrix.SpecialLinearGroup.mapGL ℚ h') (planeOf h) := by
    rw [planeOf, ← planeAction_mul, ← map_mul]
  have e2 : planeAction (Matrix.SpecialLinearGroup.mapGL ℚ h') (planeOf h') = stdPlane := by
    rw [planeOf, ← planeAction_mul, ← map_mul, mul_inv_cancel, map_one, planeAction_one]
  rw [e1]
  constructor
  · intro heq
    rw [heq, e2]
  · intro heq
    apply (planeAction (Matrix.SpecialLinearGroup.mapGL ℚ h')).injective
    rw [heq, e2]

/-- The action of `γ ∈ Γ(6)` on the planes `π_h`. -/
theorem smul_planeOf (p : gammaN 6) (h : SL(3, ℤ)) :
    gammaSixEquiv p • planeOf h = planeOf (h * p.1⁻¹) := by
  have key : gammaSixEquiv p • planeOf h =
      planeAction (Matrix.SpecialLinearGroup.mapGL ℚ p.1) (planeOf h) := by
    change planeAction (TernaryPoly.OrdinaryFullAction.integral (gammaSixEquiv p).val) (planeOf h) = _
    have : TernaryPoly.OrdinaryFullAction.integral (gammaSixEquiv p).val =
        Matrix.SpecialLinearGroup.mapGL ℚ p.1 := iotaQ_gammaSix p
    rw [this]
  rw [key, planeOf, planeOf, ← planeAction_mul, ← map_mul]
  congr 3
  group

/-- Every rational plane is `π_h` for an integral change of basis `h ∈ SL₃(ℤ)`. -/
theorem exists_planeOf (P : Plane) : ∃ h : SL(3, ℤ), planeOf h = P := by
  have hne : P.val ≠ ⊤ := by
    intro htop
    have h3 : Module.finrank ℚ P.val = 3 := by
      rw [htop, finrank_top]; simp
    rw [P.2.1] at h3
    omega
  obtain ⟨f, hf0, hPf⟩ := Submodule.exists_le_ker_of_lt_top P.val (lt_top_iff_ne_top.2 hne)
  set a : Fin 3 → ℚ := fun i => f (fun j => if i = j then 1 else 0) with ha
  have hfx : ∀ x : Fin 3 → ℚ, f x = ∑ i, x i * a i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp [ha, smul_eq_mul]
  have ha0 : a ≠ 0 := by
    intro h0
    apply hf0
    apply LinearMap.ext
    intro x
    rw [hfx, h0]
    simp
  obtain ⟨r, hprim, c, hc, hrc⟩ := exists_primitive_row a ha0
  obtain ⟨H, h0, h1, h2⟩ := exists_SL3_bottom_row (r 0) (r 1) (r 2) hprim
  have hHrow : ∀ j, ((H : Matrix (Fin 3) (Fin 3) ℤ) 2 j : ℚ) = c * a j := by
    intro j
    rw [← hrc j]
    fin_cases j
    · simp [h0]
    · simp [h1]
    · simp [h2]
  refine ⟨H, Subtype.ext ?_⟩
  -- `H P ⊆ ⟨e₁, e₂⟩`, hence `P = H⁻¹ ⟨e₁, e₂⟩` by dimension
  have hmap : ∀ x ∈ P.val, (((Matrix.SpecialLinearGroup.mapGL ℚ H : GL (Fin 3) ℚ) :
      Matrix (Fin 3) (Fin 3) ℚ).mulVec x) ∈ Submodule.span ℚ {e0, e1} := by
    intro x hx
    apply mem_stdSpan_of_last
    have hfx0 : f x = 0 := hPf hx
    rw [hfx] at hfx0
    rw [mulVec_mapGL]
    calc ∑ j, ((H : Matrix (Fin 3) (Fin 3) ℤ) 2 j : ℚ) * x j = ∑ j, c * (x j * a j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hHrow j]; ring
      _ = c * ∑ j, x j * a j := by rw [Finset.mul_sum]
      _ = 0 := by rw [hfx0, mul_zero]
  have hle : P.val ≤ (planeOf H).val := by
    intro x hx
    refine ⟨_, hmap x hx, ?_⟩
    change (vectorAction (Matrix.SpecialLinearGroup.mapGL ℚ H⁻¹)) ((vectorAction (Matrix.SpecialLinearGroup.mapGL ℚ H)) x) = x
    rw [← LinearEquiv.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    rfl
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [P.2.1, (planeOf H).2.1])).symm


theorem planeOf_rel {h h' : SL(3, ℤ)} (hr : (planeFaceSetoid 6).r h h') :
    (Quotient.mk'' (planeOf h') : labelOrbits Γ6 Plane) = Quotient.mk'' (planeOf h) := by
  obtain ⟨q, hq, γ, hγ, rfl⟩ := hr
  have h1 : planeOf (q * h * γ) = planeOf (h * γ) := by
    symm
    rw [planeOf_eq_iff]
    simpa [mul_assoc] using hq
  have h2 : planeOf (h * γ) = gammaSixEquiv ⟨γ⁻¹, (gammaN 6).inv_mem hγ⟩ • planeOf h := by
    rw [smul_planeOf]
    simp
  rw [h1, h2]
  exact MulAction.orbitRel.Quotient.quotient_smul_eq

/-- The map from the faces of type `P` of `Γ(6)` to the `Γ(6)`-orbits of rational planes. -/
def planeFaceToOrbit : PlaneFaces 6 → labelOrbits Γ6 Plane :=
  Quotient.lift (fun h => (Quotient.mk'' (planeOf h) : labelOrbits Γ6 Plane)) (fun _ _ hr => (planeOf_rel hr).symm)

theorem planeFaceToOrbit_mk (h : SL(3, ℤ)) :
    planeFaceToOrbit (Quotient.mk (planeFaceSetoid 6) h) = Quotient.mk'' (planeOf h) := rfl

theorem planeFaceToOrbit_surjective : Function.Surjective planeFaceToOrbit := by
  intro o
  induction o using Quotient.inductionOn' with
  | h P =>
    obtain ⟨h, rfl⟩ := exists_planeOf P
    exact ⟨Quotient.mk (planeFaceSetoid 6) h, rfl⟩

theorem planeFaceToOrbit_injective : Function.Injective planeFaceToOrbit := by
  intro i j hij
  induction i using Quotient.inductionOn with
  | h h =>
    induction j using Quotient.inductionOn with
    | h h' =>
      have heq : (Quotient.mk'' (planeOf h) : labelOrbits Γ6 Plane) = Quotient.mk'' (planeOf h') := hij
      have hrel := Quotient.exact heq
      obtain ⟨g, hg⟩ := (MulAction.orbitRel_apply).1 hrel
      obtain ⟨p, rfl⟩ := gammaSixEquiv.surjective g
      have hg' : planeOf (h' * p.1⁻¹) = planeOf h := by
        rw [← smul_planeOf]; exact hg
      rw [planeOf_eq_iff] at hg'
      apply Quotient.sound
      refine ⟨(h * (h' * p.1⁻¹)⁻¹)⁻¹, planeBorel.inv_mem hg', p.1, p.2, ?_⟩
      group

/-- **The faces of type `P` of `Γ(6)` are the `Γ(6)`-orbits of rational planes.** -/
def planeFacesEquivOrbits : PlaneFaces 6 ≃ labelOrbits Γ6 Plane :=
  Equiv.ofBijective planeFaceToOrbit ⟨planeFaceToOrbit_injective, planeFaceToOrbit_surjective⟩

/-- **The stabilizer of the plane `π_h` in `Γ(6)` is the plane group `gammaNPAt 6 h`.** -/
theorem mem_stabilizer_planeOf_iff (p : gammaN 6) (h : SL(3, ℤ)) :
    gammaSixEquiv p ∈ MulAction.stabilizer Γ6 (planeOf h) ↔ p.1 ∈ gammaNPAt 6 h := by
  rw [MulAction.mem_stabilizer_iff, smul_planeOf, planeOf_eq_iff]
  have e : h * (h * p.1⁻¹)⁻¹ = h * p.1 * h⁻¹ := by group
  rw [e]
  constructor
  · intro hq
    have hmem : h * p.1 * h⁻¹ ∈ gammaN 6 := by
      have := (gammaN_normal 6).conj_mem _ p.2 h
      simpa [mul_assoc] using this
    exact ⟨hmem, mem_planeStab_of_gammaN (by norm_num) hmem hq.1 hq.2⟩
  · intro hq
    exact ⟨hq.2.1, hq.2.2.1⟩

end Planes

end TernaryPeriodPolynomials.Argument.GammaNStokes
