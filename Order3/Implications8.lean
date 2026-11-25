import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation8_167_359_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h167 : Equation167 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h8 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 2]; rw [← h359 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h8 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation159_325_implies_Equation26 (G : Type*) [Magma G] (h159 : Equation159 G) (h325 : Equation325 G) : Equation26 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h325 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h159 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation159_325_implies_Equation209 (G : Type*) [Magma G] (h159 : Equation159 G) (h325 : Equation325 G) : Equation209 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h325 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h159 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1, 1]; rw [h325 x y]

theorem Equation159_385_implies_Equation16 (G : Type*) [Magma G] (h159 : Equation159 G) (h385 : Equation385 G) : Equation16 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h385 X1 X0]
    conv => enter [1]; rw [← h385 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h159 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation159_385_implies_Equation117 (G : Type*) [Magma G] (h159 : Equation159 G) (h385 : Equation385 G) : Equation117 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h385 X1 X0]
    conv => enter [1]; rw [← h385 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h159 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 2]; rw [h385 y x]

theorem Equation159_323_implies_Equation25 (G : Type*) [Magma G] (h159 : Equation159 G) (h323 : Equation323 G) : Equation25 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h159 X0 X1]
    conv => enter [1]; rw [← h323 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation159_378_implies_Equation10 (G : Type*) [Magma G] (h159 : Equation159 G) (h378 : Equation378 G) : Equation10 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h159 X0 X1]
    conv => enter [1]; rw [← h378 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation159_309_implies_Equation153 (G : Type*) [Magma G] (h159 : Equation159 G) (h309 : Equation309 G) : Equation153 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h309 X0 X1]
    conv => enter [1, 1]; rw [h309 X0 X1]
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h309 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h159 X0 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation159_361_implies_Equation156 (G : Type*) [Magma G] (h159 : Equation159 G) (h361 : Equation361 G) : Equation156 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h361 X0 X1]
    conv => enter [1, 2]; rw [h361 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h361 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h159 X0 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation159_206_209_326_implies_Equation24 (G : Type*) [Magma G] (h159 : Equation159 G) (h206 : Equation206 G) (h209 : Equation209 G) (h326 : Equation326 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h326 X0 X1]
    conv => enter [1]; rw [← h159 X0 (X1 ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← h206 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l5 X0 (X1 ◇ X0)]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h206 X0 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 1]; rw [← l9 X0 X2]
    conv => enter [1]; rw [l3 X1 (X0 ◇ X2)]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l9 X0 X2]
    conv => enter [1]; rw [← h326 X1 (X0 ◇ X2)]
  have l12 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X1 := by
    intro X1 X0 X2
    conv => enter [1]; rw [l11 (X1 ◇ (X0 ◇ X2)) X0 X1]
    conv => enter [1]; rw [l10 X1 X0 X2]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l11 X1 X0 X1]
    conv => enter [1]; rw [l12 X1 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h206 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l0 X0 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1]; rw [← l11 (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) X1 X0]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 1]; rw [← l11 ((X0 ◇ X1) ◇ X1) X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l13 X0 X1]
    conv => enter [1]; rw [← l16 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  intro x y
  conv => enter [1]; rw [← l17 x y]

theorem Equation117_124_159_375_implies_Equation13 (G : Type*) [Magma G] (h117 : Equation117 G) (h124 : Equation124 G) (h159 : Equation159 G) (h375 : Equation375 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h375 X1 X0]
    conv => enter [1]; rw [← h159 X0 (X1 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← h124 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← l5 (X0 ◇ X1) X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h124 X0 (X1 ◇ X0)]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l7 X1 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 1, 2]; rw [← l9 X2 X0]
    conv => enter [1]; rw [l3 X1 (X2 ◇ X0)]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l9 X2 X0]
    conv => enter [1]; rw [← h375 (X2 ◇ X0) X1]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ ((X2 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X2 X1
    conv => enter [1]; rw [l11 X0 ((X2 ◇ X0) ◇ X1) X1]
    conv => enter [1]; rw [l10 X1 X0 X2]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l11 X0 X1 X0]
    conv => enter [1]; rw [l12 X0 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1]; rw [← l11 X1 ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1, 2]; rw [← l11 X0 (X1 ◇ (X1 ◇ X0)) X1]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l13 X1 X0]
    conv => enter [1]; rw [← l16 X1 X0]
    conv => enter [1]; rw [l13 X1 X0]
  intro x y
  conv => enter [1]; rw [← l17 y x]

theorem Equation159_308_326_implies_Equation152 (G : Type*) [Magma G] (h159 : Equation159 G) (h308 : Equation308 G) (h326 : Equation326 G) : Equation152 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h159 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h308 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X1) ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h308 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation159_364_375_implies_Equation166 (G : Type*) [Magma G] (h159 : Equation159 G) (h364 : Equation364 G) (h375 : Equation375 G) : Equation166 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h364 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [← h159 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h364 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation156_326_implies_Equation25 (G : Type*) [Magma G] (h156 : Equation156 G) (h326 : Equation326 G) : Equation25 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h326 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h156 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation153_375_implies_Equation10 (G : Type*) [Magma G] (h153 : Equation153 G) (h375 : Equation375 G) : Equation10 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h153 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation23_156_325_implies_Equation24 (G : Type*) [Magma G] (h23 : Equation23 G) (h156 : Equation156 G) (h325 : Equation325 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h156 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h156 X0 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h156 X0 X1]
    conv => enter [1]; rw [← h325 (X0 ◇ X0) (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h23 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h156 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l5 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h156 X0 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [l8 X0 (X0 ◇ X0)]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l8 X0 X2]
  intro x y
  conv => enter [1]; rw [← l10 x x y]

theorem Equation8_153_385_implies_Equation13 (G : Type*) [Magma G] (h8 : Equation8 G) (h153 : Equation153 G) (h385 : Equation385 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h153 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h153 X0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h153 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h8 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h153 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X0) X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l5 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h153 X0 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [l8 (X0 ◇ X0) X0]
  have l10 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = X0 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l8 X2 X0]
  intro x y
  conv => enter [1]; rw [← l10 y x x]

theorem Equation156_323_implies_Equation25 (G : Type*) [Magma G] (h156 : Equation156 G) (h323 : Equation323 G) : Equation25 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h156 X0 X1]
    conv => enter [1]; rw [← h323 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1]; rw [← h156 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation153_378_implies_Equation10 (G : Type*) [Magma G] (h153 : Equation153 G) (h378 : Equation378 G) : Equation10 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h153 X0 X1]
    conv => enter [1]; rw [← h378 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [← h153 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation156_308_309_implies_Equation24 (G : Type*) [Magma G] (h156 : Equation156 G) (h308 : Equation308 G) (h309 : Equation309 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h156 X0 X1]
    conv => enter [1]; rw [← h308 (X0 ◇ X1) (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h308 X0 X1]
    conv => enter [1]; rw [← h309 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h156 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h308 X0 X1]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h156 X0 X0]
  intro x y
  conv => enter [1]; rw [← l6 x y]

theorem Equation153_361_364_implies_Equation13 (G : Type*) [Magma G] (h153 : Equation153 G) (h361 : Equation361 G) (h364 : Equation364 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h153 X0 X1]
    conv => enter [1]; rw [← h364 (X1 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h364 X0 X1]
    conv => enter [1]; rw [← h361 (X1 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h153 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h364 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h153 X0 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation153_326_implies_Equation309 (G : Type*) [Magma G] (h153 : Equation153 G) (h326 : Equation326 G) : Equation309 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h153 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h326 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h153 X1 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation156_375_implies_Equation361 (G : Type*) [Magma G] (h156 : Equation156 G) (h375 : Equation375 G) : Equation361 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h156 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h375 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h156 X1 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation153_325_implies_Equation24 (G : Type*) [Magma G] (h153 : Equation153 G) (h325 : Equation325 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h153 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h153 X0 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l1 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h153 X0 (X1 ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation156_385_implies_Equation13 (G : Type*) [Magma G] (h156 : Equation156 G) (h385 : Equation385 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h156 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h156 X0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h156 X0 ((X0 ◇ X0) ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation153_212_implies_Equation24 (G : Type*) [Magma G] (h153 : Equation153 G) (h212 : Equation212 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h212 X0 X1]
    conv => enter [1]; rw [← h153 X1 (X0 ◇ (X1 ◇ X1))]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation127_156_implies_Equation13 (G : Type*) [Magma G] (h127 : Equation127 G) (h156 : Equation156 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h127 X0 X1]
    conv => enter [1]; rw [← h156 X1 ((X1 ◇ X1) ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation153_209_implies_Equation24 (G : Type*) [Magma G] (h153 : Equation153 G) (h209 : Equation209 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h153 X1 (X0 ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation117_156_implies_Equation13 (G : Type*) [Magma G] (h117 : Equation117 G) (h156 : Equation156 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h156 X1 ((X0 ◇ X1) ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation153_206_implies_Equation24 (G : Type*) [Magma G] (h153 : Equation153 G) (h206 : Equation206 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h153 X1 (X0 ◇ (X0 ◇ X1))]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation124_156_implies_Equation13 (G : Type*) [Magma G] (h124 : Equation124 G) (h156 : Equation156 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h156 X1 ((X1 ◇ X0) ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation153_308_309_implies_Equation152 (G : Type*) [Magma G] (h153 : Equation153 G) (h308 : Equation308 G) (h309 : Equation309 G) : Equation152 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h153 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h308 X0 X1]
    conv => enter [1, 1]; rw [h308 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h308 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h153 X0 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation156_361_364_implies_Equation166 (G : Type*) [Magma G] (h156 : Equation156 G) (h361 : Equation361 G) (h364 : Equation364 G) : Equation166 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h156 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h364 X0 X1]
    conv => enter [1, 2]; rw [h364 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h364 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h156 X0 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation23_162_implies_Equation25 (G : Type*) [Magma G] (h23 : Equation23 G) (h162 : Equation162 G) : Equation25 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h23 X0]
    conv => enter [1]; rw [← h162 X0 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation8_162_implies_Equation10 (G : Type*) [Magma G] (h8 : Equation8 G) (h162 : Equation162 G) : Equation10 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h162 X0 (X0 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation152_212_325_implies_Equation308 (G : Type*) [Magma G] (h152 : Equation152 G) (h212 : Equation212 G) (h325 : Equation325 G) : Equation308 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h152 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h152 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h152 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation127_166_385_implies_Equation364 (G : Type*) [Magma G] (h127 : Equation127 G) (h166 : Equation166 G) (h385 : Equation385 G) : Equation364 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h166 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h166 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h166 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation152_209_326_implies_Equation308 (G : Type*) [Magma G] (h152 : Equation152 G) (h209 : Equation209 G) (h326 : Equation326 G) : Equation308 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h152 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X1) ◇ X0) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h152 X0 X1]
    conv => enter [1, 2, 2]; rw [← h152 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X1)) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1, 2, 2]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation117_166_375_implies_Equation364 (G : Type*) [Magma G] (h117 : Equation117 G) (h166 : Equation166 G) (h375 : Equation375 G) : Equation364 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h166 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h166 X0 X1]
    conv => enter [1, 1, 1]; rw [← h166 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [l4 X1 X0]
    conv => enter [1, 1, 1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l5 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation23_152_206_implies_Equation24 (G : Type*) [Magma G] (h23 : Equation23 G) (h152 : Equation152 G) (h206 : Equation206 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h152 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h23 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation8_124_166_implies_Equation13 (G : Type*) [Magma G] (h8 : Equation8 G) (h124 : Equation124 G) (h166 : Equation166 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h124 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h166 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h8 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation152_205_309_implies_Equation308 (G : Type*) [Magma G] (h152 : Equation152 G) (h205 : Equation205 G) (h309 : Equation309 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h309 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h152 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [l1 X0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation104_166_361_implies_Equation364 (G : Type*) [Magma G] (h104 : Equation104 G) (h166 : Equation166 G) (h361 : Equation361 G) : Equation364 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h166 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h361 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h166 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [l1 (X1 ◇ X0) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation152_159_326_implies_Equation308 (G : Type*) [Magma G] (h152 : Equation152 G) (h159 : Equation159 G) (h326 : Equation326 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h326 X0 X1]
    conv => enter [1]; rw [← h159 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h152 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h326 ((X0 ◇ X1) ◇ (X0 ◇ X1)) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation159_166_375_implies_Equation364 (G : Type*) [Magma G] (h159 : Equation159 G) (h166 : Equation166 G) (h375 : Equation375 G) : Equation364 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h375 X1 X0]
    conv => enter [1]; rw [← h159 X0 (X1 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h166 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h166 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h375 X0 ((X1 ◇ X0) ◇ (X1 ◇ X0))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [← l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation152_159_208_implies_Equation205 (G : Type*) [Magma G] (h152 : Equation152 G) (h159 : Equation159 G) (h208 : Equation208 G) : Equation205 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h159 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h152 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h208 X0 ((X0 ◇ X1) ◇ (X0 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation101_159_166_implies_Equation104 (G : Type*) [Magma G] (h101 : Equation101 G) (h159 : Equation159 G) (h166 : Equation166 G) : Equation104 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h166 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h101 X0 ((X0 ◇ X0) ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation152_156_208_implies_Equation205 (G : Type*) [Magma G] (h152 : Equation152 G) (h156 : Equation156 G) (h208 : Equation208 G) : Equation205 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h156 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h208 X0 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation101_153_166_implies_Equation104 (G : Type*) [Magma G] (h101 : Equation101 G) (h153 : Equation153 G) (h166 : Equation166 G) : Equation104 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h166 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h153 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h101 X0 ((X1 ◇ X0) ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation152_153_208_implies_Equation205 (G : Type*) [Magma G] (h152 : Equation152 G) (h153 : Equation153 G) (h208 : Equation208 G) : Equation205 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h153 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h152 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h208 X0 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation101_156_166_implies_Equation104 (G : Type*) [Magma G] (h101 : Equation101 G) (h156 : Equation156 G) (h166 : Equation166 G) : Equation104 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h156 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h166 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h101 X0 ((X1 ◇ X0) ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation47_218_231_implies_Equation5 (G : Type*) [Magma G] (h47 : Equation47 G) (h218 : Equation218 G) (h231 : Equation231 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h218 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1, 2]; rw [← h231 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1, 1]; rw [← h47 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h47 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h231 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation100_108_255_implies_Equation4 (G : Type*) [Magma G] (h100 : Equation100 G) (h108 : Equation108 G) (h255 : Equation255 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h100 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h108 ((X0 ◇ X0) ◇ X0) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1, 2]; rw [← h255 X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h255 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h108 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation47_208_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h208 : Equation208 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h208 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [← h47 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 1]; rw [← h208 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h47 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation101_255_implies_Equation3 (G : Type*) [Magma G] (h101 : Equation101 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h101 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h255 X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 2]; rw [← h101 X0 X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h255 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h255 X0]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation23_65_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h65 : Equation65 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h23 X0]
    conv => enter [1]; rw [← h65 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h65 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 2]; rw [← h23 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h23 X0]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation8_261_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h261 : Equation261 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h261 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h261 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 1]; rw [← h8 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h8 X0]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation63_203_implies_Equation3 (G : Type*) [Magma G] (h63 : Equation63 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h63 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h203 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h203 X0]
    conv => enter [1]; rw [← l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h63 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation99_271_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h271 : Equation271 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h271 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h99 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h99 X0]
    conv => enter [1]; rw [← l0 X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h271 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation63_75_implies_Equation26 (G : Type*) [Magma G] (h63 : Equation63 G) (h75 : Equation75 G) : Equation26 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation264_271_implies_Equation16 (G : Type*) [Magma G] (h264 : Equation264 G) (h271 : Equation271 G) : Equation16 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation56_218_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h218 : Equation218 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h218 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [← h56 (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h56 (X0 ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h56 X1 X0]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation100_283_implies_Equation2 (G : Type*) [Magma G] (h100 : Equation100 G) (h283 : Equation283 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h100 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [← h283 ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h283 ((X0 ◇ X0) ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h283 X1 X0]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation23_53_63_implies_Equation26 (G : Type*) [Magma G] (h23 : Equation23 G) (h53 : Equation53 G) (h63 : Equation63 G) : Equation26 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h53 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h23 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h63 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h53 X1 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ (X0 ◇ X1)) (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l2 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 2]; rw [← l5 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l5 X1 (X0 ◇ X0)]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1]; rw [← h23 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X1 ◇ (X0 ◇ X1)) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l14 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ (X0 ◇ X1)) X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 2]; rw [l3 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l3 X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l3 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [← l10 X1 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 1]; rw [← l5 X1 X0]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l19 X0 X1]
    conv => enter [1]; rw [← l12 X1 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 1, 2]; rw [l3 X1 X0]
  have l22 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1, 2]; rw [← h63 X0 (X1 ◇ X1)]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l20 X1 X0]
    conv => enter [1]; rw [l20 X1 X2]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← h53 X0 X1]
  have l25 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← l20 X1 (X0 ◇ (X0 ◇ X1))]
  have l26 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l5 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 2]; rw [l3 X1 X0]
  have l27 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X1)) = ((X0 ◇ X2) ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l23 X1 (X2 ◇ (X2 ◇ X0)) (X0 ◇ X2)]
    conv => enter [1, 2]; rw [l3 X2 X0]
  have l28 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l23 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l29 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l28 X1 X0 X2]
    conv => enter [1]; rw [← h53 X1 X0]
  have l30 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X2)) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l7 X1 ((X2 ◇ (X0 ◇ X2)) ◇ X1)]
    conv => enter [1, 1, 1, 2]; rw [l29 X1 X2 X0]
  have l31 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l19 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l3 X1 X0]
    conv => enter [1, 2, 2]; rw [l3 X1 X0]
  have l32 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l22 X0 X1]
    conv => enter [1]; rw [l5 X1 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1, 1, 2]; rw [← l22 X0 X1]
  have l33 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l32 X1 X0]
  have l34 : ∀ X1 X0 : G, ((((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l14 X1 X0]
    conv => enter [1]; rw [l3 ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) X1]
  have l35 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))]
    conv => enter [1, 2]; rw [l14 X1 X0]
  have l36 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l33 X0 X1]
    conv => enter [1]; rw [l33 X0 X2]
  have l37 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l33 X0 X1]
    conv => enter [1]; rw [l20 X0 X2]
  have l38 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X1 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l33 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1]; rw [l29 (X0 ◇ (X1 ◇ X0)) X0 X1]
  have l39 : ∀ X1 X0 X2 : G, (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2)) = (X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l16 ((X1 ◇ (X0 ◇ X1)) ◇ X2) X2]
    conv => enter [1, 1]; rw [l29 X2 X1 X0]
  have l40 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l16 X0 X1]
    conv => enter [1]; rw [l5 ((X0 ◇ (X0 ◇ X1)) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l16 X0 X1]
  have l41 : ∀ X1 X0 X2 : G, (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l17 X0 X1]
    conv => enter [1]; rw [← l37 (X0 ◇ (X0 ◇ X1)) X2 ((X1 ◇ X0) ◇ X1)]
  have l42 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))]
    conv => enter [1, 1, 1]; rw [l14 X1 X0]
  have l43 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l15 (X1 ◇ X2) X2]
    conv => enter [1, 1, 1]; rw [l23 X2 X1 X0]
  have l44 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 (X0 ◇ X1) X1]
    conv => enter [1, 1, 1]; rw [← l20 X0 X1]
  have l45 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [l36 ((X1 ◇ X0) ◇ X1) (X0 ◇ (X0 ◇ X1)) X2]
  have l46 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X2)) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l45 X0 X1 ((X2 ◇ (X0 ◇ X2)) ◇ X1)]
    conv => enter [1]; rw [← l30 X2 X0 X1]
  have l47 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l44 X0 X1]
    conv => enter [1, 2]; rw [l31 (X0 ◇ X1) X1]
  have l48 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l43 X1 X2 X0]
    conv => enter [1, 2]; rw [l31 (X1 ◇ X2) X2]
  have l49 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l42 X1 X0]
    conv => enter [1, 1]; rw [← h63 (X1 ◇ (X1 ◇ X0)) X0]
  have l50 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l47 X0 X1]
    conv => enter [1, 1]; rw [← l46 X0 X1 X0]
  have l51 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l33 (X1 ◇ (X1 ◇ X0)) (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))))]
    conv => enter [1]; rw [← l49 X1 X0]
  have l52 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l50 X0 X1]
    conv => enter [1]; rw [← l41 X1 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X1)]
  have l53 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l27 (X1 ◇ (X1 ◇ X0)) X1 X0]
    conv => enter [1]; rw [l51 X1 X0]
  have l54 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l26 X1 X0]
    conv => enter [1]; rw [← l52 X0 X1]
  have l55 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l35 X1 X0]
    conv => enter [1, 1]; rw [← l53 X0 X1]
  have l56 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l54 X2 X1]
    conv => enter [1]; rw [l48 X1 X2 X0]
  have l57 : ∀ X2 X1 X0 : G, ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ (((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) ◇ X2)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l54 X2 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l39 X1 X0 X2]
    conv => enter [1, 2, 1]; rw [← l54 X2 (X1 ◇ (X0 ◇ X1))]
  have l58 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l55 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  have l59 : ∀ X0 X1 : G, (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l55 X1 X0]
    conv => enter [1, 1, 1]; rw [← l55 X1 X0]
    conv => enter [1]; rw [l34 X1 X0]
  have l60 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l53 X0 X1]
    conv => enter [1, 2, 2]; rw [l55 X1 X0]
  have l61 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l58 X0 X2]
    conv => enter [1]; rw [l23 X2 (((X0 ◇ X2) ◇ X0) ◇ X0) X1]
  have l62 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1, 2, 1, 2]; rw [← l58 X0 X2]
    conv => enter [1]; rw [l29 X1 X2 (((X0 ◇ X2) ◇ X0) ◇ X0)]
  have l63 : ∀ X1 X0 : G, (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [l21 X0 X1]
    conv => enter [1]; rw [← l24 (X0 ◇ X1) (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))]
  have l64 : ∀ X1 X0 : G, (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l63 X1 X0]
    conv => enter [1]; rw [l62 (X0 ◇ X1) X0 X1]
  have l65 : ∀ X1 X0 : G, ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l40 X1 X0]
    conv => enter [1]; rw [l64 X1 X0]
  have l66 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l40 X0 X1]
    conv => enter [1]; rw [l65 X0 X1]
  have l67 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1, 1, 2]; rw [← l58 X0 X1]
    conv => enter [1]; rw [l38 X1 (((X0 ◇ X1) ◇ X0) ◇ X0) X2]
  have l68 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ X2) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l56 X2 X1 X0]
    conv => enter [1]; rw [l67 (X0 ◇ (X1 ◇ X0)) X2 ((X2 ◇ (X1 ◇ X2)) ◇ X2)]
  have l69 : ∀ X2 X1 X0 : G, ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ ((X2 ◇ X0) ◇ X2)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l57 X2 X1 X0]
    conv => enter [1, 2]; rw [← l68 X2 X0 X1]
  have l70 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l25 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 2]; rw [l25 X1 X0]
  have l71 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l70 X1 X0]
    conv => enter [1]; rw [l69 (X1 ◇ (X1 ◇ X0)) X0 X0]
  have l72 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l71 X1 X0]
    conv => enter [1, 2]; rw [l66 X1 X0]
  have l73 : ∀ X0 X1 : G, (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l72 X0 X1]
    conv => enter [1]; rw [l59 X0 X1]
  have l74 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l60 X0 X1]
    conv => enter [1, 2]; rw [← l72 X0 X1]
  have l75 : ∀ X0 X1 : G, ((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l74 X0 ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l73 X0 X1]
  have l76 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l61 X1 X0 X0]
    conv => enter [1]; rw [l75 X0 X1]
  intro x y
  conv => enter [1]; rw [← l76 x y]

theorem Equation23_53_63_implies_Equation31 (G : Type*) [Magma G] (h23 : Equation23 G) (h53 : Equation53 G) (h63 : Equation63 G) : Equation31 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h53 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h23 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h63 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ (X0 ◇ X1)) (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l2 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 2]; rw [← l4 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l4 X1 (X0 ◇ X0)]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← h23 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X1 ◇ (X0 ◇ X1)) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2]; rw [← l8 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [← l4 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l13 X0 X1]
    conv => enter [1]; rw [← l10 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1, 2]; rw [← h63 X0 (X1 ◇ X1)]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l14 X1 X0]
    conv => enter [1]; rw [l14 X1 X2]
  have l17 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [l16 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l18 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l17 X1 X0 X2]
    conv => enter [1]; rw [← h53 X1 X0]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l15 X0 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1, 1, 2]; rw [← l15 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l19 X1 X0]
  have l21 : ∀ X2 X0 X1 : G, ((X2 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l20 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1]; rw [l18 (X2 ◇ X2) X0 X1]
  have l22 : ∀ X2 X1 : G, ((X2 ◇ X2) ◇ X1) = X1 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l18 (X2 ◇ (X1 ◇ X2)) X2 X1]
    conv => enter [1]; rw [l21 X2 X2 X1]
  intro x y
  conv => enter [1]; rw [← l22 y x]

theorem Equation23_53_63_implies_Equation75 (G : Type*) [Magma G] (h23 : Equation23 G) (h53 : Equation53 G) (h63 : Equation63 G) : Equation75 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h53 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h23 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h63 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h53 X1 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ (X0 ◇ X1)) (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l2 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 2]; rw [← l5 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l5 X1 (X0 ◇ X0)]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1]; rw [← h23 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X1 ◇ (X0 ◇ X1)) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l14 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ (X0 ◇ X1)) X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 2]; rw [l3 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l3 X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l3 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [← l10 X1 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 1]; rw [← l5 X1 X0]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l19 X0 X1]
    conv => enter [1]; rw [← l12 X1 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 1, 2]; rw [l3 X1 X0]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 ((X1 ◇ (X1 ◇ X0)) ◇ X1) X0]
    conv => enter [1, 2, 1, 2]; rw [l4 X0 X1]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1, 2]; rw [← h23 X0]
  have l24 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1, 2]; rw [← h63 X0 (X1 ◇ X1)]
  have l25 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l20 X1 X0]
    conv => enter [1]; rw [l20 X1 X2]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← h53 X0 X1]
  have l27 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← l20 X1 (X0 ◇ (X0 ◇ X1))]
  have l28 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l5 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 2]; rw [l3 X1 X0]
  have l29 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X1)) = ((X0 ◇ X2) ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l25 X1 (X2 ◇ (X2 ◇ X0)) (X0 ◇ X2)]
    conv => enter [1, 2]; rw [l3 X2 X0]
  have l30 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l25 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l31 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l30 X1 X0 X2]
    conv => enter [1]; rw [← h53 X1 X0]
  have l32 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X2)) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l7 X1 ((X2 ◇ (X0 ◇ X2)) ◇ X1)]
    conv => enter [1, 1, 1, 2]; rw [l31 X1 X2 X0]
  have l33 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l19 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l3 X1 X0]
    conv => enter [1, 2, 2]; rw [l3 X1 X0]
  have l34 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l24 X0 X1]
    conv => enter [1]; rw [l5 X1 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1, 1, 2]; rw [← l24 X0 X1]
  have l35 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l34 X1 X0]
  have l36 : ∀ X1 X0 : G, ((((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l14 X1 X0]
    conv => enter [1]; rw [l3 ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) X1]
  have l37 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))]
    conv => enter [1, 2]; rw [l14 X1 X0]
  have l38 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l35 X0 X1]
    conv => enter [1]; rw [l35 X0 X2]
  have l39 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l35 X0 X1]
    conv => enter [1]; rw [l20 X0 X2]
  have l40 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X1 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l35 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1]; rw [l31 (X0 ◇ (X1 ◇ X0)) X0 X1]
  have l41 : ∀ X1 X0 X2 : G, (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2)) = (X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l16 ((X1 ◇ (X0 ◇ X1)) ◇ X2) X2]
    conv => enter [1, 1]; rw [l31 X2 X1 X0]
  have l42 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l16 X0 X1]
    conv => enter [1]; rw [l5 ((X0 ◇ (X0 ◇ X1)) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l16 X0 X1]
  have l43 : ∀ X1 X0 X2 : G, (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l17 X0 X1]
    conv => enter [1]; rw [← l39 (X0 ◇ (X0 ◇ X1)) X2 ((X1 ◇ X0) ◇ X1)]
  have l44 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))]
    conv => enter [1, 1, 1]; rw [l14 X1 X0]
  have l45 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l15 (X1 ◇ X2) X2]
    conv => enter [1, 1, 1]; rw [l25 X2 X1 X0]
  have l46 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 (X0 ◇ X1) X1]
    conv => enter [1, 1, 1]; rw [← l20 X0 X1]
  have l47 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [l38 ((X1 ◇ X0) ◇ X1) (X0 ◇ (X0 ◇ X1)) X2]
  have l48 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X2)) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l47 X0 X1 ((X2 ◇ (X0 ◇ X2)) ◇ X1)]
    conv => enter [1]; rw [← l32 X2 X0 X1]
  have l49 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l46 X0 X1]
    conv => enter [1, 2]; rw [l33 (X0 ◇ X1) X1]
  have l50 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l45 X1 X2 X0]
    conv => enter [1, 2]; rw [l33 (X1 ◇ X2) X2]
  have l51 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l44 X1 X0]
    conv => enter [1, 1]; rw [← h63 (X1 ◇ (X1 ◇ X0)) X0]
  have l52 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l49 X0 X1]
    conv => enter [1, 1]; rw [← l48 X0 X1 X0]
  have l53 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l35 (X1 ◇ (X1 ◇ X0)) (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))))]
    conv => enter [1]; rw [← l51 X1 X0]
  have l54 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l52 X0 X1]
    conv => enter [1]; rw [← l43 X1 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X1)]
  have l55 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l29 (X1 ◇ (X1 ◇ X0)) X1 X0]
    conv => enter [1]; rw [l53 X1 X0]
  have l56 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X0]
    conv => enter [1]; rw [← l54 X0 X1]
  have l57 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1, 1]; rw [← l55 X0 X1]
  have l58 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l56 X2 X1]
    conv => enter [1]; rw [l50 X1 X2 X0]
  have l59 : ∀ X2 X1 X0 : G, ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ (((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) ◇ X2)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l56 X2 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l41 X1 X0 X2]
    conv => enter [1, 2, 1]; rw [← l56 X2 (X1 ◇ (X0 ◇ X1))]
  have l60 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l57 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  have l61 : ∀ X0 X1 : G, (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l57 X1 X0]
    conv => enter [1, 1, 1]; rw [← l57 X1 X0]
    conv => enter [1]; rw [l36 X1 X0]
  have l62 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l55 X0 X1]
    conv => enter [1, 2, 2]; rw [l57 X1 X0]
  have l63 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l60 X0 X2]
    conv => enter [1]; rw [l25 X2 (((X0 ◇ X2) ◇ X0) ◇ X0) X1]
  have l64 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1, 2, 1, 2]; rw [← l60 X0 X2]
    conv => enter [1]; rw [l31 X1 X2 (((X0 ◇ X2) ◇ X0) ◇ X0)]
  have l65 : ∀ X1 X0 : G, (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [l21 X0 X1]
    conv => enter [1]; rw [← l26 (X0 ◇ X1) (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))]
  have l66 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l26 ((X0 ◇ (X0 ◇ X1)) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← l23 X0 X1]
  have l67 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← l66 X0 X1]
  have l68 : ∀ X1 X0 : G, (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l65 X1 X0]
    conv => enter [1]; rw [l64 (X0 ◇ X1) X0 X1]
  have l69 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l67 X1 X0]
    conv => enter [1]; rw [l64 ((X0 ◇ (X0 ◇ X1)) ◇ X0) (X0 ◇ (X0 ◇ X1)) X0]
  have l70 : ∀ X1 X0 : G, ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l42 X1 X0]
    conv => enter [1]; rw [l68 X1 X0]
  have l71 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l69 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l72 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l42 X0 X1]
    conv => enter [1]; rw [l70 X0 X1]
  have l73 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1, 1, 2]; rw [← l60 X0 X1]
    conv => enter [1]; rw [l40 X1 (((X0 ◇ X1) ◇ X0) ◇ X0) X2]
  have l74 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ X2) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l58 X2 X1 X0]
    conv => enter [1]; rw [l73 (X0 ◇ (X1 ◇ X0)) X2 ((X2 ◇ (X1 ◇ X2)) ◇ X2)]
  have l75 : ∀ X2 X1 X0 : G, ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ ((X2 ◇ X0) ◇ X2)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l59 X2 X1 X0]
    conv => enter [1, 2]; rw [← l74 X2 X0 X1]
  have l76 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l27 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 2]; rw [l27 X1 X0]
  have l77 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l76 X1 X0]
    conv => enter [1]; rw [l75 (X1 ◇ (X1 ◇ X0)) X0 X0]
  have l78 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l77 X1 X0]
    conv => enter [1, 2]; rw [l72 X1 X0]
  have l79 : ∀ X0 X1 : G, (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l78 X0 X1]
    conv => enter [1]; rw [l61 X0 X1]
  have l80 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l62 X0 X1]
    conv => enter [1, 2]; rw [← l78 X0 X1]
  have l81 : ∀ X0 X1 : G, ((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l80 X0 ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l79 X0 X1]
  have l82 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l63 X1 X0 X0]
    conv => enter [1]; rw [l81 X0 X1]
  have l83 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l82 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l71 X0 X1]
  intro x y
  conv => enter [1]; rw [← l83 y x]

theorem Equation8_271_273_implies_Equation16 (G : Type*) [Magma G] (h8 : Equation8 G) (h271 : Equation271 G) (h273 : Equation273 G) : Equation16 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h273 (X0 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h8 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h271 X0 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h273 X1 ((X1 ◇ X0) ◇ X0)]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [l2 X1 ((X1 ◇ X0) ◇ X0)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l0 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h271 ((X1 ◇ X0) ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 1]; rw [← l5 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l5 X1 (X0 ◇ X0)]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← h8 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 ((X1 ◇ X0) ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [l3 ((X1 ◇ X0) ◇ X0) X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h271 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l3 X1 X0]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h273 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l3 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 1]; rw [← l10 X1 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 2]; rw [← l5 X1 X0]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l19 X0 X1]
    conv => enter [1]; rw [← l12 X1 X0]
  have l21 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2, 1]; rw [l3 X1 X0]
  have l22 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 (((X1 ◇ X1) ◇ X0) ◇ X0)]
    conv => enter [1, 1]; rw [← h271 X0 (X1 ◇ X1)]
  have l23 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l20 X1 X0]
    conv => enter [1]; rw [l20 X1 X2]
  have l24 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [← h273 X0 X1]
  have l25 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← l20 X1 ((X1 ◇ X0) ◇ X0)]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
  have l27 : ∀ X1 X0 X2 : G, ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) = (X0 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l23 X1 ((X0 ◇ X2) ◇ X2) (X2 ◇ X0)]
    conv => enter [1, 1]; rw [l3 X2 X0]
  have l28 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l23 X1 ((X0 ◇ X1) ◇ X0) X2]
  have l29 : ∀ X2 X0 X1 : G, ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l28 X0 X1 X2]
    conv => enter [1]; rw [← h273 X1 X0]
  have l30 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l7 (X1 ◇ ((X2 ◇ X0) ◇ X2)) X1]
    conv => enter [1, 2, 2, 1]; rw [l29 X1 X2 X0]
  have l31 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
    conv => enter [1, 1, 1]; rw [l3 X1 X0]
  have l32 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l22 X0 X1]
    conv => enter [1]; rw [l5 X1 (((X0 ◇ X0) ◇ X1) ◇ X1)]
    conv => enter [1, 2, 1]; rw [← l22 X0 X1]
  have l33 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← l32 X0 X1]
  have l34 : ∀ X0 X1 : G, ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l14 X1 X0]
    conv => enter [1]; rw [l3 ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) X1]
  have l35 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))]
    conv => enter [1, 1]; rw [l14 X1 X0]
  have l36 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l33 X0 X1]
    conv => enter [1]; rw [l33 X0 X2]
  have l37 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X0) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l33 X0 X1]
    conv => enter [1]; rw [l20 X0 X2]
  have l38 : ∀ X2 X0 X1 : G, ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l33 ((X0 ◇ X1) ◇ X0) X2]
    conv => enter [1]; rw [l29 ((X0 ◇ X1) ◇ X0) X0 X1]
  have l39 : ∀ X2 X1 X0 : G, ((X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = ((X2 ◇ ((X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X0) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l16 X2 (X2 ◇ ((X1 ◇ X0) ◇ X1))]
    conv => enter [1, 2]; rw [l29 X2 X1 X0]
  have l40 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l16 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ ((X1 ◇ X0) ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← l16 X1 X0]
  have l41 : ∀ X1 X0 X2 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = ((X2 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1, 1]; rw [l17 X1 X0]
    conv => enter [1]; rw [← l37 X2 ((X1 ◇ X0) ◇ X0) (X1 ◇ (X0 ◇ X1))]
  have l42 : ∀ X0 X1 : G, ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) = ((((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [l14 X1 X0]
  have l43 : ∀ X2 X1 X0 : G, ((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = ((((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l15 X2 (X2 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l23 X2 X1 X0]
  have l44 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l20 X0 X1]
  have l45 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [l36 ((X1 ◇ X0) ◇ X0) (X1 ◇ (X0 ◇ X1)) X2]
  have l46 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l45 X1 X0 (X1 ◇ ((X2 ◇ X0) ◇ X2))]
    conv => enter [1]; rw [← l30 X1 X2 X0]
  have l47 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l44 X1 X0]
    conv => enter [1, 1]; rw [l31 X1 (X1 ◇ X0)]
  have l48 : ∀ X2 X1 X0 : G, ((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = (((X2 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l43 X2 X1 X0]
    conv => enter [1, 1]; rw [l31 X2 (X2 ◇ X1)]
  have l49 : ∀ X0 X1 : G, ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) = ((((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l42 X0 X1]
    conv => enter [1, 2]; rw [← h271 ((X0 ◇ X1) ◇ X1) X0]
  have l50 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l47 X1 X0]
    conv => enter [1, 2]; rw [← l46 X1 X0 X0]
  have l51 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l33 ((X0 ◇ X1) ◇ X1) ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← l49 X0 X1]
  have l52 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l50 X1 X0]
    conv => enter [1]; rw [← l41 X1 X0 (X1 ◇ ((X1 ◇ X0) ◇ X1))]
  have l53 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l27 ((X0 ◇ X1) ◇ X1) X0 X1]
    conv => enter [1]; rw [l51 X0 X1]
  have l54 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l26 X1 X0]
    conv => enter [1]; rw [← l52 X1 X0]
  have l55 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l35 X0 X1]
    conv => enter [1, 2]; rw [← l53 X0 X1]
  have l56 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (((X2 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l54 X2 X1]
    conv => enter [1]; rw [l48 X2 X1 X0]
  have l57 : ∀ X2 X1 X0 : G, (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = ((X2 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) ◇ X0) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l54 X2 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l39 X2 X1 X0]
    conv => enter [1, 1, 2]; rw [← l54 X2 ((X1 ◇ X0) ◇ X1)]
  have l58 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l55 X1 X0]
    conv => enter [1]; rw [l14 X0 X1]
  have l59 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l55 X0 X1]
    conv => enter [1, 2, 2]; rw [← l55 X0 X1]
    conv => enter [1]; rw [l34 X0 X1]
  have l60 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l53 X0 X1]
    conv => enter [1, 1, 1]; rw [l55 X0 X1]
  have l61 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l58 X2 X0]
    conv => enter [1]; rw [l23 X2 (X0 ◇ (X0 ◇ (X2 ◇ X0))) X1]
  have l62 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X2)) ◇ X1) = (X0 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1, 1, 2, 1]; rw [← l58 X2 X0]
    conv => enter [1]; rw [l29 X1 X2 (X0 ◇ (X0 ◇ (X2 ◇ X0)))]
  have l63 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l21 X1 X0]
    conv => enter [1]; rw [← l24 (X1 ◇ X0) (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))]
  have l64 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l63 X1 X0]
    conv => enter [1]; rw [l62 (X1 ◇ X0) X1 X0]
  have l65 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l40 X0 X1]
    conv => enter [1]; rw [l64 X1 X0]
  have l66 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l40 X1 X0]
    conv => enter [1]; rw [l65 X0 X1]
  have l67 : ∀ X2 X0 X1 : G, ((X2 ◇ X2) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1, 2, 1]; rw [← l58 X1 X0]
    conv => enter [1]; rw [l38 X2 X1 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l68 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l56 X2 X1 X0]
    conv => enter [1]; rw [l67 (X2 ◇ ((X2 ◇ X1) ◇ X2)) X2 ((X0 ◇ X1) ◇ X0)]
  have l69 : ∀ X2 X1 X0 : G, (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ X0) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l57 X2 X1 X0]
    conv => enter [1, 1]; rw [← l68 X2 X0 X1]
  have l70 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l25 ((X0 ◇ X1) ◇ X1) X1]
    conv => enter [1, 2, 1]; rw [l25 X1 X0]
  have l71 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l70 X1 X0]
    conv => enter [1]; rw [l69 ((X0 ◇ X1) ◇ X1) X0 X0]
  have l72 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l71 X1 X0]
    conv => enter [1, 1]; rw [l66 X0 X1]
  have l73 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l72 X0 X1]
    conv => enter [1]; rw [l59 X0 X1]
  have l74 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l60 X0 X1]
    conv => enter [1, 1]; rw [← l72 X0 X1]
  have l75 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l74 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l73 X0 X1]
  have l76 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l61 X0 X1 X0]
    conv => enter [1]; rw [l75 X0 X1]
  intro x y
  conv => enter [1]; rw [← l76 y x]

theorem Equation8_271_273_implies_Equation11 (G : Type*) [Magma G] (h8 : Equation8 G) (h271 : Equation271 G) (h273 : Equation273 G) : Equation11 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h273 (X0 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h8 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h271 X0 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l0 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h271 ((X1 ◇ X0) ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 1]; rw [← l4 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l4 X1 (X0 ◇ X0)]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h8 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 ((X1 ◇ X0) ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 1]; rw [← l8 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [← l4 X1 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← l10 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 (((X1 ◇ X1) ◇ X0) ◇ X0)]
    conv => enter [1, 1]; rw [← h271 X0 (X1 ◇ X1)]
  have l16 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l14 X1 X0]
    conv => enter [1]; rw [l14 X1 X2]
  have l17 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l16 X1 ((X0 ◇ X1) ◇ X0) X2]
  have l18 : ∀ X2 X0 X1 : G, ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l17 X0 X1 X2]
    conv => enter [1]; rw [← h273 X1 X0]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l15 X0 X1]
    conv => enter [1]; rw [l4 X1 (((X0 ◇ X0) ◇ X1) ◇ X1)]
    conv => enter [1, 2, 1]; rw [← l15 X0 X1]
  have l20 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← l19 X0 X1]
  have l21 : ∀ X0 X1 X2 : G, (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ X2)) = X1 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l20 ((X0 ◇ X1) ◇ X0) X2]
    conv => enter [1]; rw [l18 (X2 ◇ X2) X0 X1]
  have l22 : ∀ X1 X2 : G, (X1 ◇ (X2 ◇ X2)) = X1 := by
    intro X1 X2
    conv => enter [1, 1]; rw [← l18 ((X1 ◇ X1) ◇ X1) X1 X1]
    conv => enter [1]; rw [l21 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [← l22 x y]

theorem Equation8_271_273_implies_Equation264 (G : Type*) [Magma G] (h8 : Equation8 G) (h271 : Equation271 G) (h273 : Equation273 G) : Equation264 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h273 (X0 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h8 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h271 X0 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h273 X1 ((X1 ◇ X0) ◇ X0)]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [l2 X1 ((X1 ◇ X0) ◇ X0)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l0 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h271 ((X1 ◇ X0) ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 1]; rw [← l5 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l5 X1 (X0 ◇ X0)]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← h8 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 ((X1 ◇ X0) ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [l3 ((X1 ◇ X0) ◇ X0) X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h271 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l3 X1 X0]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h273 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l3 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 1]; rw [← l10 X1 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 2]; rw [← l5 X1 X0]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l19 X0 X1]
    conv => enter [1]; rw [← l12 X1 X0]
  have l21 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2, 1]; rw [l3 X1 X0]
  have l22 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 (X1 ◇ ((X0 ◇ X1) ◇ X1))]
    conv => enter [1, 1, 2, 1]; rw [l4 X1 X0]
  have l23 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1, 1]; rw [← h8 X0]
  have l24 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 (((X1 ◇ X1) ◇ X0) ◇ X0)]
    conv => enter [1, 1]; rw [← h271 X0 (X1 ◇ X1)]
  have l25 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l20 X1 X0]
    conv => enter [1]; rw [l20 X1 X2]
  have l26 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [← h273 X0 X1]
  have l27 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← l20 X1 ((X1 ◇ X0) ◇ X0)]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
  have l29 : ∀ X1 X0 X2 : G, ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) = (X0 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l25 X1 ((X0 ◇ X2) ◇ X2) (X2 ◇ X0)]
    conv => enter [1, 1]; rw [l3 X2 X0]
  have l30 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l25 X1 ((X0 ◇ X1) ◇ X0) X2]
  have l31 : ∀ X2 X0 X1 : G, ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l30 X0 X1 X2]
    conv => enter [1]; rw [← h273 X1 X0]
  have l32 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l7 (X1 ◇ ((X2 ◇ X0) ◇ X2)) X1]
    conv => enter [1, 2, 2, 1]; rw [l31 X1 X2 X0]
  have l33 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
    conv => enter [1, 1, 1]; rw [l3 X1 X0]
  have l34 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l24 X0 X1]
    conv => enter [1]; rw [l5 X1 (((X0 ◇ X0) ◇ X1) ◇ X1)]
    conv => enter [1, 2, 1]; rw [← l24 X0 X1]
  have l35 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← l34 X0 X1]
  have l36 : ∀ X0 X1 : G, ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l14 X1 X0]
    conv => enter [1]; rw [l3 ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) X1]
  have l37 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))]
    conv => enter [1, 1]; rw [l14 X1 X0]
  have l38 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l35 X0 X1]
    conv => enter [1]; rw [l35 X0 X2]
  have l39 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X0) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l35 X0 X1]
    conv => enter [1]; rw [l20 X0 X2]
  have l40 : ∀ X2 X0 X1 : G, ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l35 ((X0 ◇ X1) ◇ X0) X2]
    conv => enter [1]; rw [l31 ((X0 ◇ X1) ◇ X0) X0 X1]
  have l41 : ∀ X2 X1 X0 : G, ((X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = ((X2 ◇ ((X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X0) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l16 X2 (X2 ◇ ((X1 ◇ X0) ◇ X1))]
    conv => enter [1, 2]; rw [l31 X2 X1 X0]
  have l42 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l16 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ ((X1 ◇ X0) ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← l16 X1 X0]
  have l43 : ∀ X1 X0 X2 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = ((X2 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1, 1]; rw [l17 X1 X0]
    conv => enter [1]; rw [← l39 X2 ((X1 ◇ X0) ◇ X0) (X1 ◇ (X0 ◇ X1))]
  have l44 : ∀ X0 X1 : G, ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) = ((((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [l14 X1 X0]
  have l45 : ∀ X2 X1 X0 : G, ((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = ((((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l15 X2 (X2 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l25 X2 X1 X0]
  have l46 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l20 X0 X1]
  have l47 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [l38 ((X1 ◇ X0) ◇ X0) (X1 ◇ (X0 ◇ X1)) X2]
  have l48 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l47 X1 X0 (X1 ◇ ((X2 ◇ X0) ◇ X2))]
    conv => enter [1]; rw [← l32 X1 X2 X0]
  have l49 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l46 X1 X0]
    conv => enter [1, 1]; rw [l33 X1 (X1 ◇ X0)]
  have l50 : ∀ X2 X1 X0 : G, ((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = (((X2 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l45 X2 X1 X0]
    conv => enter [1, 1]; rw [l33 X2 (X2 ◇ X1)]
  have l51 : ∀ X0 X1 : G, ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) = ((((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l44 X0 X1]
    conv => enter [1, 2]; rw [← h271 ((X0 ◇ X1) ◇ X1) X0]
  have l52 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l49 X1 X0]
    conv => enter [1, 2]; rw [← l48 X1 X0 X0]
  have l53 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l35 ((X0 ◇ X1) ◇ X1) ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← l51 X0 X1]
  have l54 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l52 X1 X0]
    conv => enter [1]; rw [← l43 X1 X0 (X1 ◇ ((X1 ◇ X0) ◇ X1))]
  have l55 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l29 ((X0 ◇ X1) ◇ X1) X0 X1]
    conv => enter [1]; rw [l53 X0 X1]
  have l56 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X0]
    conv => enter [1]; rw [← l54 X1 X0]
  have l57 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l37 X0 X1]
    conv => enter [1, 2]; rw [← l55 X0 X1]
  have l58 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (((X2 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l56 X2 X1]
    conv => enter [1]; rw [l50 X2 X1 X0]
  have l59 : ∀ X2 X1 X0 : G, (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = ((X2 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) ◇ X0) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l56 X2 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l41 X2 X1 X0]
    conv => enter [1, 1, 2]; rw [← l56 X2 ((X1 ◇ X0) ◇ X1)]
  have l60 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l57 X1 X0]
    conv => enter [1]; rw [l14 X0 X1]
  have l61 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l57 X0 X1]
    conv => enter [1, 2, 2]; rw [← l57 X0 X1]
    conv => enter [1]; rw [l36 X0 X1]
  have l62 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l55 X0 X1]
    conv => enter [1, 1, 1]; rw [l57 X0 X1]
  have l63 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l60 X2 X0]
    conv => enter [1]; rw [l25 X2 (X0 ◇ (X0 ◇ (X2 ◇ X0))) X1]
  have l64 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X2)) ◇ X1) = (X0 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1, 1, 2, 1]; rw [← l60 X2 X0]
    conv => enter [1]; rw [l31 X1 X2 (X0 ◇ (X0 ◇ (X2 ◇ X0)))]
  have l65 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l21 X1 X0]
    conv => enter [1]; rw [← l26 (X1 ◇ X0) (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))]
  have l66 : ∀ X0 X1 : G, (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l26 (X0 ◇ ((X1 ◇ X0) ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← l23 X0 X1]
  have l67 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← l66 X0 X1]
  have l68 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l65 X1 X0]
    conv => enter [1]; rw [l64 (X1 ◇ X0) X1 X0]
  have l69 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l67 X0 X1]
    conv => enter [1]; rw [l64 (X0 ◇ ((X1 ◇ X0) ◇ X0)) X0 ((X1 ◇ X0) ◇ X0)]
  have l70 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l42 X0 X1]
    conv => enter [1]; rw [l68 X1 X0]
  have l71 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l69 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l72 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l42 X1 X0]
    conv => enter [1]; rw [l70 X0 X1]
  have l73 : ∀ X2 X0 X1 : G, ((X2 ◇ X2) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1, 2, 1]; rw [← l60 X1 X0]
    conv => enter [1]; rw [l40 X2 X1 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l74 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l58 X2 X1 X0]
    conv => enter [1]; rw [l73 (X2 ◇ ((X2 ◇ X1) ◇ X2)) X2 ((X0 ◇ X1) ◇ X0)]
  have l75 : ∀ X2 X1 X0 : G, (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ X0) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l59 X2 X1 X0]
    conv => enter [1, 1]; rw [← l74 X2 X0 X1]
  have l76 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l27 ((X0 ◇ X1) ◇ X1) X1]
    conv => enter [1, 2, 1]; rw [l27 X1 X0]
  have l77 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l76 X1 X0]
    conv => enter [1]; rw [l75 ((X0 ◇ X1) ◇ X1) X0 X0]
  have l78 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l77 X1 X0]
    conv => enter [1, 1]; rw [l72 X0 X1]
  have l79 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l78 X0 X1]
    conv => enter [1]; rw [l61 X0 X1]
  have l80 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l62 X0 X1]
    conv => enter [1, 1]; rw [← l78 X0 X1]
  have l81 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l80 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l79 X0 X1]
  have l82 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l63 X0 X1 X0]
    conv => enter [1]; rw [l81 X0 X1]
  have l83 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l82 X0 (((X1 ◇ X0) ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l71 X0 X1]
  intro x y
  conv => enter [1]; rw [← l83 x y]

theorem Equation50_218_implies_Equation2 (G : Type*) [Magma G] (h50 : Equation50 G) (h218 : Equation218 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h50 (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
    conv => enter [1, 2]; rw [← h218 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h218 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← l0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h50 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h218 X1 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation100_280_implies_Equation2 (G : Type*) [Magma G] (h100 : Equation100 G) (h280 : Equation280 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h280 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) X0]
    conv => enter [1, 1]; rw [← h100 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h100 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← l0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h280 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h100 X1 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation23_49_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h49 : Equation49 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h23 X0]
    conv => enter [1]; rw [← h49 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h49 X0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation8_260_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h260 : Equation260 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h260 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h260 X0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation31_307_implies_Equation231 (G : Type*) [Magma G] (h31 : Equation31 G) (h307 : Equation307 G) : Equation231 G := by
  intro x y
  conv => enter [1]; rw [h31 x y]
  conv => enter [1, 1]; rw [h307 y]

theorem Equation11_359_implies_Equation108 (G : Type*) [Magma G] (h11 : Equation11 G) (h359 : Equation359 G) : Equation108 G := by
  intro x y
  conv => enter [1]; rw [h11 x y]
  conv => enter [1, 2]; rw [h359 y]

theorem Equation31_221_implies_Equation211 (G : Type*) [Magma G] (h31 : Equation31 G) (h221 : Equation221 G) : Equation211 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h31 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h221 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation11_105_implies_Equation107 (G : Type*) [Magma G] (h11 : Equation11 G) (h105 : Equation105 G) : Equation107 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h11 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [← h105 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation31_312_implies_Equation246 (G : Type*) [Magma G] (h31 : Equation31 G) (h312 : Equation312 G) : Equation246 G := by
  intro x y z
  conv => enter [1]; rw [h31 x z]
  conv => enter [1, 1]; rw [h312 z y]

theorem Equation11_360_implies_Equation109 (G : Type*) [Magma G] (h11 : Equation11 G) (h360 : Equation360 G) : Equation109 G := by
  intro x y z
  conv => enter [1]; rw [h11 x y]
  conv => enter [1, 2]; rw [h360 y z]

theorem Equation31_310_implies_Equation246 (G : Type*) [Magma G] (h31 : Equation31 G) (h310 : Equation310 G) : Equation246 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [← h31 X2 X0]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

theorem Equation11_367_implies_Equation109 (G : Type*) [Magma G] (h11 : Equation11 G) (h367 : Equation367 G) : Equation109 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [← h367 X0 X1]
    conv => enter [1]; rw [← h11 X2 X0]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

theorem Equation31_309_implies_Equation242 (G : Type*) [Magma G] (h31 : Equation31 G) (h309 : Equation309 G) : Equation242 G := by
  intro x y z
  conv => enter [1]; rw [h31 x y]
  conv => enter [1, 1]; rw [h309 y z]

theorem Equation11_361_implies_Equation111 (G : Type*) [Magma G] (h11 : Equation11 G) (h361 : Equation361 G) : Equation111 G := by
  intro x y z
  conv => enter [1]; rw [h11 x y]
  conv => enter [1, 2]; rw [h361 y z]

theorem Equation31_205_implies_Equation246 (G : Type*) [Magma G] (h31 : Equation31 G) (h205 : Equation205 G) : Equation246 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h31 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h31 X1 X0]
  intro x y z
  conv => enter [1]; rw [h31 x z]
  conv => enter [1, 1]; rw [l1 z y]

theorem Equation31_205_implies_Equation312 (G : Type*) [Magma G] (h31 : Equation31 G) (h205 : Equation205 G) : Equation312 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h31 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h31 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation11_104_implies_Equation109 (G : Type*) [Magma G] (h11 : Equation11 G) (h104 : Equation104 G) : Equation109 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h104 (X0 ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h11 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h11 X1 X0]
  intro x y z
  conv => enter [1]; rw [h11 x y]
  conv => enter [1, 2]; rw [l1 y z]

theorem Equation11_104_implies_Equation360 (G : Type*) [Magma G] (h11 : Equation11 G) (h104 : Equation104 G) : Equation360 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h104 (X0 ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h11 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h11 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation31_56_implies_Equation2 (G : Type*) [Magma G] (h31 : Equation31 G) (h56 : Equation56 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h31 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h56 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h31 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h31 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation11_283_implies_Equation2 (G : Type*) [Magma G] (h11 : Equation11 G) (h283 : Equation283 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h11 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h11 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h283 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h11 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation31_53_implies_Equation50 (G : Type*) [Magma G] (h31 : Equation31 G) (h53 : Equation53 G) : Equation50 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h31 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h31 (X1 ◇ ((X0 ◇ X0) ◇ X1)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h31 X1 X0]
  intro x y
  conv => enter [1]; rw [← l0 x x]
  conv => enter [1, 2, 2]; rw [l2 x y]

theorem Equation31_53_implies_Equation40 (G : Type*) [Magma G] (h31 : Equation31 G) (h53 : Equation53 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h31 (X1 ◇ ((X0 ◇ X0) ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h31 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation11_273_implies_Equation280 (G : Type*) [Magma G] (h11 : Equation11 G) (h273 : Equation273 G) : Equation280 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h11 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [← h273 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h273 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h11 ((X1 ◇ (X0 ◇ X0)) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h11 X1 X0]
  intro x y
  conv => enter [1]; rw [← l0 x x]
  conv => enter [1, 1, 1]; rw [l2 x y]

theorem Equation11_273_implies_Equation40 (G : Type*) [Magma G] (h11 : Equation11 G) (h273 : Equation273 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h273 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h11 ((X1 ◇ (X0 ◇ X0)) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h11 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation31_50_implies_Equation40 (G : Type*) [Magma G] (h31 : Equation31 G) (h50 : Equation50 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h50 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h31 (X1 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h31 (X1 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation11_280_implies_Equation40 (G : Type*) [Magma G] (h11 : Equation11 G) (h280 : Equation280 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h11 (X1 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h11 (X1 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation40_218_implies_Equation246 (G : Type*) [Magma G] (h40 : Equation40 G) (h218 : Equation218 G) : Equation246 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X2) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 1, 2]; rw [h40 X0 X2]
    conv => enter [1]; rw [← h218 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

theorem Equation40_100_implies_Equation109 (G : Type*) [Magma G] (h40 : Equation40 G) (h100 : Equation100 G) : Equation109 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 1]; rw [h40 X0 X2]
    conv => enter [1]; rw [← h100 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

theorem Equation40_242_implies_Equation319 (G : Type*) [Magma G] (h40 : Equation40 G) (h242 : Equation242 G) : Equation319 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h242 (X0 ◇ (X1 ◇ X0)) X0 X1]
    conv => enter [1]; rw [h40 (X0 ◇ (X1 ◇ X0)) X2]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

theorem Equation40_111_implies_Equation371 (G : Type*) [Magma G] (h40 : Equation40 G) (h111 : Equation111 G) : Equation371 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h111 ((X0 ◇ X1) ◇ X0) X0 X1]
    conv => enter [1]; rw [h40 ((X0 ◇ X1) ◇ X0) X2]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

theorem Equation26_203_implies_Equation151 (G : Type*) [Magma G] (h26 : Equation26 G) (h203 : Equation203 G) : Equation151 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h203 X0]
    conv => enter [1]; rw [← h26 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h26 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation16_99_implies_Equation151 (G : Type*) [Magma G] (h16 : Equation16 G) (h99 : Equation99 G) : Equation151 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2]; rw [h99 X0]
    conv => enter [1]; rw [← h16 ((X0 ◇ X0) ◇ X0) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h16 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation26_326_implies_Equation212 (G : Type*) [Magma G] (h26 : Equation26 G) (h326 : Equation326 G) : Equation212 G := by
  intro x y
  conv => enter [1]; rw [h26 x y]
  conv => enter [1, 1]; rw [h326 x y]

theorem Equation16_375_implies_Equation127 (G : Type*) [Magma G] (h16 : Equation16 G) (h375 : Equation375 G) : Equation127 G := by
  intro x y
  conv => enter [1]; rw [h16 x y]
  conv => enter [1, 2]; rw [h375 y x]

theorem Equation26_325_implies_Equation209 (G : Type*) [Magma G] (h26 : Equation26 G) (h325 : Equation325 G) : Equation209 G := by
  intro x y
  conv => enter [1]; rw [h26 x y]
  conv => enter [1, 1]; rw [h325 x y]

theorem Equation16_385_implies_Equation117 (G : Type*) [Magma G] (h16 : Equation16 G) (h385 : Equation385 G) : Equation117 G := by
  intro x y
  conv => enter [1]; rw [h16 x y]
  conv => enter [1, 2]; rw [h385 y x]

theorem Equation26_323_implies_Equation24 (G : Type*) [Magma G] (h26 : Equation26 G) (h323 : Equation323 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h26 X0 X1]
    conv => enter [1]; rw [← h323 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h26 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h26 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h26 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation16_378_implies_Equation13 (G : Type*) [Magma G] (h16 : Equation16 G) (h378 : Equation378 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h16 X0 X1]
    conv => enter [1]; rw [← h378 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h16 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h16 (X1 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation26_212_implies_Equation326 (G : Type*) [Magma G] (h26 : Equation26 G) (h212 : Equation212 G) : Equation326 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h212 X0 X1]
    conv => enter [1]; rw [← h26 (X0 ◇ (X1 ◇ X1)) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation16_127_implies_Equation375 (G : Type*) [Magma G] (h16 : Equation16 G) (h127 : Equation127 G) : Equation375 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h127 X0 X1]
    conv => enter [1]; rw [← h16 ((X1 ◇ X1) ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation26_209_implies_Equation325 (G : Type*) [Magma G] (h26 : Equation26 G) (h209 : Equation209 G) : Equation325 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h26 (X0 ◇ (X1 ◇ X0)) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation16_117_implies_Equation385 (G : Type*) [Magma G] (h16 : Equation16 G) (h117 : Equation117 G) : Equation385 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h16 ((X0 ◇ X1) ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation26_208_implies_Equation24 (G : Type*) [Magma G] (h26 : Equation26 G) (h208 : Equation208 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h26 X0 X1]
    conv => enter [1]; rw [← h208 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h26 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h26 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation16_101_implies_Equation13 (G : Type*) [Magma G] (h16 : Equation16 G) (h101 : Equation101 G) : Equation13 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h16 X0 X1]
    conv => enter [1]; rw [← h101 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h16 (X1 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation26_206_implies_Equation24 (G : Type*) [Magma G] (h26 : Equation26 G) (h206 : Equation206 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h26 (X0 ◇ (X0 ◇ X1)) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h26 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h26 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h26 (X0 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation16_124_implies_Equation13 (G : Type*) [Magma G] (h16 : Equation16 G) (h124 : Equation124 G) : Equation13 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h16 ((X1 ◇ X0) ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h16 X0 X1]
    conv => enter [1]; rw [← l0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h16 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h16 (X1 ◇ X0) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation26_205_implies_Equation152 (G : Type*) [Magma G] (h26 : Equation26 G) (h205 : Equation205 G) : Equation152 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h26 (X0 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h26 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation26_205_implies_Equation308 (G : Type*) [Magma G] (h26 : Equation26 G) (h205 : Equation205 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h26 (X0 ◇ (X0 ◇ X1)) X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation16_104_implies_Equation166 (G : Type*) [Magma G] (h16 : Equation16 G) (h104 : Equation104 G) : Equation166 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h16 ((X1 ◇ X0) ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h16 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation16_104_implies_Equation364 (G : Type*) [Magma G] (h16 : Equation16 G) (h104 : Equation104 G) : Equation364 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h16 ((X1 ◇ X0) ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation26_159_implies_Equation209 (G : Type*) [Magma G] (h26 : Equation26 G) (h159 : Equation159 G) : Equation209 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h26 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [h26 x y]
  conv => enter [1, 1]; rw [l0 x y]

theorem Equation16_159_implies_Equation117 (G : Type*) [Magma G] (h16 : Equation16 G) (h159 : Equation159 G) : Equation117 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h16 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [h16 x y]
  conv => enter [1, 2]; rw [l0 y x]

theorem Equation26_156_307_implies_Equation24 (G : Type*) [Magma G] (h26 : Equation26 G) (h156 : Equation156 G) (h307 : Equation307 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h26 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h156 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h26 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h307 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation16_153_359_implies_Equation13 (G : Type*) [Magma G] (h16 : Equation16 G) (h153 : Equation153 G) (h359 : Equation359 G) : Equation13 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h16 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h153 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h16 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h359 X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation26_153_implies_Equation24 (G : Type*) [Magma G] (h26 : Equation26 G) (h153 : Equation153 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h26 X0 X1]
    conv => enter [1]; rw [← h153 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation16_156_implies_Equation13 (G : Type*) [Magma G] (h16 : Equation16 G) (h156 : Equation156 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h16 X0 X1]
    conv => enter [1]; rw [← h156 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation26_152_implies_Equation308 (G : Type*) [Magma G] (h26 : Equation26 G) (h152 : Equation152 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h26 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h152 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation16_166_implies_Equation364 (G : Type*) [Magma G] (h16 : Equation16 G) (h166 : Equation166 G) : Equation364 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h16 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h166 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation26_327_implies_Equation215 (G : Type*) [Magma G] (h26 : Equation26 G) (h327 : Equation327 G) : Equation215 G := by
  intro x y z
  conv => enter [1]; rw [h26 x y]
  conv => enter [1, 1]; rw [h327 x y z]

theorem Equation16_395_implies_Equation138 (G : Type*) [Magma G] (h16 : Equation16 G) (h395 : Equation395 G) : Equation138 G := by
  intro x y z
  conv => enter [1]; rw [h16 x y]
  conv => enter [1, 2]; rw [h395 y x z]

theorem Equation26_215_implies_Equation327 (G : Type*) [Magma G] (h26 : Equation26 G) (h215 : Equation215 G) : Equation327 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h215 X0 X1 X2]
    conv => enter [1]; rw [← h26 (X0 ◇ (X1 ◇ X2)) X1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation16_138_implies_Equation395 (G : Type*) [Magma G] (h16 : Equation16 G) (h138 : Equation138 G) : Equation395 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = ((X2 ◇ X1) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h138 X0 X1 X2]
    conv => enter [1]; rw [← h16 ((X2 ◇ X1) ◇ X0) X1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation26_75_implies_Equation63 (G : Type*) [Magma G] (h26 : Equation26 G) (h75 : Equation75 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h26 X1 (X1 ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation16_264_implies_Equation271 (G : Type*) [Magma G] (h16 : Equation16 G) (h264 : Equation264 G) : Equation271 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h16 X1 ((X0 ◇ X1) ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation26_63_implies_Equation75 (G : Type*) [Magma G] (h26 : Equation26 G) (h63 : Equation63 G) : Equation75 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h26 X1 (X0 ◇ (X0 ◇ X1))]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation16_271_implies_Equation264 (G : Type*) [Magma G] (h16 : Equation16 G) (h271 : Equation271 G) : Equation264 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h16 X1 ((X1 ◇ X0) ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation25_326_implies_Equation156 (G : Type*) [Magma G] (h25 : Equation25 G) (h326 : Equation326 G) : Equation156 G := by
  intro x y
  conv => enter [1]; rw [h25 x y]
  conv => enter [1]; rw [h326 (x ◇ y) x]

theorem Equation10_375_implies_Equation153 (G : Type*) [Magma G] (h10 : Equation10 G) (h375 : Equation375 G) : Equation153 G := by
  intro x y
  conv => enter [1]; rw [h10 x y]
  conv => enter [1]; rw [h375 x (y ◇ x)]

theorem Equation151_310_implies_Equation24 (G : Type*) [Magma G] (h151 : Equation151 G) (h310 : Equation310 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h310 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h151 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation151_367_implies_Equation13 (G : Type*) [Magma G] (h151 : Equation151 G) (h367 : Equation367 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h367 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h151 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation25_329_implies_Equation162 (G : Type*) [Magma G] (h25 : Equation25 G) (h329 : Equation329 G) : Equation162 G := by
  intro x y z
  conv => enter [1]; rw [h25 x y]
  conv => enter [1]; rw [h329 (x ◇ y) x z]

theorem Equation10_381_implies_Equation162 (G : Type*) [Magma G] (h10 : Equation10 G) (h381 : Equation381 G) : Equation162 G := by
  intro x y z
  conv => enter [1]; rw [h10 x z]
  conv => enter [1]; rw [h381 x (z ◇ x) y]

theorem Equation162_309_implies_Equation326 (G : Type*) [Magma G] (h162 : Equation162 G) (h309 : Equation309 G) : Equation326 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h162 (X0 ◇ X1) (X0 ◇ X0) X3]
    conv => enter [1, 1]; rw [← h162 X0 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation162_361_implies_Equation375 (G : Type*) [Magma G] (h162 : Equation162 G) (h361 : Equation361 G) : Equation375 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X3) ◇ X0) := by
    intro X1 X0 X3
    conv => enter [1]; rw [h162 (X1 ◇ X0) X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h162 X0 X1 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation25_31_224_implies_Equation242 (G : Type*) [Magma G] (h25 : Equation25 G) (h31 : Equation31 G) (h224 : Equation224 G) : Equation242 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h224 (sK1 ◇ (sK2 ◇ sK1)) X0 sK1]
    conv => enter [1, 1, 2]; rw [← h25 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h25 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 1]; rw [← l0 sK1 sK2 sK2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h224 (sK1 ◇ (sK2 ◇ sK1)) X0 (sK2 ◇ sK1)]
    conv => enter [1, 1, 2]; rw [← l1 sK2 sK1]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [← h31 X0 (sK1 ◇ (sK2 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

theorem Equation10_11_106_implies_Equation111 (G : Type*) [Magma G] (h10 : Equation10 G) (h11 : Equation11 G) (h106 : Equation106 G) : Equation111 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = (((sK1 ◇ sK2) ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h106 ((sK1 ◇ sK2) ◇ sK1) sK1 X0]
    conv => enter [1, 2, 1]; rw [← h10 sK1 (sK1 ◇ sK2)]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h10 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK1 sK2 sK2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = (((sK1 ◇ sK2) ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h106 ((sK1 ◇ sK2) ◇ sK1) (sK1 ◇ sK2) X0]
    conv => enter [1, 2, 1]; rw [← l1 sK1 sK2]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ sK1)) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [← h11 X0 ((sK1 ◇ sK2) ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l3 x y z]

theorem Equation3_378_385_implies_Equation333 (G : Type*) [Magma G] (h3 : Equation3 G) (h378 : Equation378 G) (h385 : Equation385 G) : Equation333 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h378 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation3_323_325_implies_Equation377 (G : Type*) [Magma G] (h3 : Equation3 G) (h323 : Equation323 G) (h325 : Equation325 G) : Equation377 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h323 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [← l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation273_385_implies_Equation5 (G : Type*) [Magma G] (h273 : Equation273 G) (h385 : Equation385 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h273 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation53_325_implies_Equation4 (G : Type*) [Magma G] (h53 : Equation53 G) (h325 : Equation325 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation3_273_384_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h273 : Equation273 G) (h384 : Equation384 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h384 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation3_273_384_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h273 : Equation273 G) (h384 : Equation384 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h384 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_273_384_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h273 : Equation273 G) (h384 : Equation384 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h384 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l7 y (x ◇ x)]

theorem Equation3_273_384_implies_Equation124 (G : Type*) [Magma G] (h3 : Equation3 G) (h273 : Equation273 G) (h384 : Equation384 G) : Equation124 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h384 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x]
  conv => enter [1, 2]; rw [h384 x y]

theorem Equation3_273_384_implies_Equation206 (G : Type*) [Magma G] (h3 : Equation3 G) (h273 : Equation273 G) (h384 : Equation384 G) : Equation206 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h384 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h384 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1, 1]; rw [l9 y x]

theorem Equation3_273_384_implies_Equation75 (G : Type*) [Magma G] (h3 : Equation3 G) (h273 : Equation273 G) (h384 : Equation384 G) : Equation75 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h384 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h384 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1]; rw [l9 (y ◇ x) y]

theorem Equation3_53_335_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h335 : Equation335 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation3_53_335_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h335 : Equation335 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_53_335_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h335 : Equation335 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l8 y (x ◇ x)]

theorem Equation3_273_378_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h273 : Equation273 G) (h378 : Equation378 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h378 X0 X1]
    conv => enter [1]; rw [← h273 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation3_53_323_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h323 : Equation323 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h323 X1 X0]
    conv => enter [1]; rw [← h53 X1 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation273_377_implies_Equation2 (G : Type*) [Magma G] (h273 : Equation273 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h377 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation53_333_implies_Equation2 (G : Type*) [Magma G] (h53 : Equation53 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h333 X0 X1]
    conv => enter [1]; rw [← h53 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h333 X1 X0]
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_273_335_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h273 : Equation273 G) (h335 : Equation335 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h335 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h335 X0 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l3 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation3_273_335_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h273 : Equation273 G) (h335 : Equation335 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h335 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h335 X0 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l3 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_53_384_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h384 : Equation384 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h384 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h384 (X1 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h53 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l3 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation3_53_384_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h384 : Equation384 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h384 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h384 (X1 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h53 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l3 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation273_333_implies_Equation28 (G : Type*) [Magma G] (h273 : Equation273 G) (h333 : Equation333 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h273 (X0 ◇ X1) X1]
    conv => enter [1, 1, 1]; rw [← h333 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h273 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l1 y x]

end Order3
