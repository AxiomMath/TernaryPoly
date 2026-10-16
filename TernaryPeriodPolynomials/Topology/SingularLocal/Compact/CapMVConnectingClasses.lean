module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVPairing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.BoundaryClasses

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex
open SingularLocalCap SingularLocalCap.BoundaryClasses SingularLocalCompactCap.Algebra

/-- The scalar family of a literal cycle is a categorical cycle in the same actual complex. -/
theorem elementCycle_condition {s : ComplexShape ℕ} (K : HomologicalComplex (ModuleCat.{0} ℚ) s)
    (i j k : ℕ) (x : Homology.Cycles (K.sc' i j k)) :
    elementMap (x.val : K.X j) ≫ K.d j k = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change K.d j k ((r : ℚ) • (x.val : K.X j)) = 0
  have hz : K.d j k x.val = 0 := x.property
  exact (map_smul (K.d j k).hom (r : ℚ) (x.val : K.X j)).trans
    ((congrArg (fun v : K.X k => (r : ℚ) • v) hz).trans (smul_zero (r : ℚ)))

/-- The cycle-family construction and the quotient-cycle class describe the same
actual homology element. -/
theorem representedFamily {s : ComplexShape ℕ} (K : HomologicalComplex (ModuleCat.{0} ℚ) s)
    (i j k : ℕ) (hi : s.prev j = i) (hk : s.next j = k) (x : Homology.Cycles (K.sc' i j k)) :
    K.liftCycles (elementMap (x.val : K.X j)) k hk (elementCycle_condition K i j k x) ≫ K.homologyπ j =
      elementMap ((K.homologyIsoSc' i j k hi hk).inv (Homology.cycleClass _ x)) := by
  apply (cancel_mono (K.homologyι j)).mp
  rw [Category.assoc,HomologicalComplex.homology_π_ι,← Category.assoc]
  erw [HomologicalComplex.liftCycles_i]
  erw [elementMap_comp,elementMap_comp,represented_opcycles]

/-- The connecting map of a genuine short exact complex sequence sends a represented cycle
to the class of its literal lifted differential. -/
theorem connecting_representatives {s : ComplexShape ℕ}
    (S : ShortComplex (HomologicalComplex (ModuleCat.{0} ℚ) s)) (hS : S.ShortExact)
    (p i j k : ℕ) (hij : s.Rel i j) (hp : s.prev i = p) (hk : s.next j = k)
    (x₃ : Homology.Cycles (S.X₃.sc' p i j)) (x₂ : S.X₂.X i)
    (x₁ : Homology.Cycles (S.X₁.sc' i j k))
    (h₂ : S.g.f i x₂ = x₃.val) (h₁ : S.f.f j x₁.val = S.X₂.d i j x₂) :
    hS.δ i j hij ((S.X₃.homologyIsoSc' p i j hp (s.next_eq' hij)).inv (Homology.cycleClass _ x₃)) =
      (S.X₁.homologyIsoSc' i j k (s.prev_eq' hij) hk).inv (Homology.cycleClass _ x₁) := by
  have h₂' : elementMap x₂ ≫ S.g.f i = elementMap (x₃.val : S.X₃.X i) := by
    exact (elementMap_comp x₂ (S.g.f i)).trans (congrArg elementMap h₂)
  have h₁' : elementMap (x₁.val : S.X₁.X j) ≫ S.f.f j = elementMap x₂ ≫ S.X₂.d i j := by
    exact (elementMap_comp (x₁.val : S.X₁.X j) (S.f.f j)).trans
      ((congrArg elementMap h₁).trans (elementMap_comp x₂ (S.X₂.d i j)).symm)
  have he := hS.δ_eq i j hij (elementMap (x₃.val : S.X₃.X i)) (elementCycle_condition S.X₃ p i j x₃)
    (elementMap x₂) h₂' (elementMap (x₁.val : S.X₁.X j)) h₁' k hk
  rw [← Category.assoc,representedFamily S.X₃ p i j hp (s.next_eq' hij) x₃,
    representedFamily S.X₁ i j k (s.prev_eq' hij) hk x₁,elementMap_comp] at he
  have hh := congrArg (fun f => f 1) he
  have em (x : S.X₁.homology j) : elementMap x (1 : ℚ) = x := one_smul ℚ x
  erw [em,em] at hh
  exact hh

/-- The actual cohomology connecting map uses the positive differential of a lifted cochain. -/
theorem cochainConnecting_representatives
    (S : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℕ)) (hS : S.ShortExact) (a : ℕ)
    (x₃ : Homology.Cycles (S.X₃.sc' (a-1) a (a+1))) (x₂ : S.X₂.X a)
    (x₁ : Homology.Cycles (S.X₁.sc' a (a+1) (a+2)))
    (h₂ : S.g.f a x₂ = x₃.val) (h₁ : S.f.f (a+1) x₁.val = S.X₂.d a (a+1) x₂) :
    hS.δ a (a+1) rfl (Descent.cochainClass S.X₃ a x₃) = Descent.cochainClass S.X₁ (a+1) x₁ :=
  connecting_representatives S hS (a-1) a (a+1) (a+2) rfl (up_prev a) (up_next (a+1)) x₃ x₂ x₁ h₂ h₁

/-- The actual homology connecting map uses the positive differential of a lifted chain. -/
theorem chainConnecting_representatives
    (S : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ)) (hS : S.ShortExact) (b : ℕ)
    (x₃ : Homology.Cycles (S.X₃.sc' (b+2) (b+1) b)) (x₂ : S.X₂.X (b+1))
    (x₁ : Homology.Cycles (S.X₁.sc' (b+1) b (b-1)))
    (h₂ : S.g.f (b+1) x₂ = x₃.val) (h₁ : S.f.f b x₁.val = S.X₂.d (b+1) b x₂) :
    hS.δ (b+1) b rfl (Descent.chainClass S.X₃ (b+1) x₃) = Descent.chainClass S.X₁ b x₁ :=
  connecting_representatives S hS (b+2) (b+1) b (b-1) rfl (down_prev (b+1)) (down_next b) x₃ x₂ x₁ h₂ h₁

end TernaryPoly.SingularLocalCompactCapMV
