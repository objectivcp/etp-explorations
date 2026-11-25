import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation325_365_implies_Equation317 (G : Type*) [Magma G] (h325 : Equation325 G) (h365 : Equation365 G) : Equation317 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ X0) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h325 X1 (X1 ◇ X0)]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h365 X2 (X2 ◇ X1)]
    conv => enter [1, 1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 X1]
    conv => enter [1, 1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [l3 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [h325 X1 X1]
    conv => enter [1, 2]; rw [l3 X1 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 1]; rw [← l2 X1 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l2 (X1 ◇ X0) (X0 ◇ X0)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1 X0]
    conv => enter [1]; rw [← l9 X1 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h365 (X0 ◇ X0) (X1 ◇ X0)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← l12 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h365 X1 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X0]
    conv => enter [1]; rw [l14 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← l16 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y z
  conv => enter [1]; rw [l15 x z]
  conv => enter [1]; rw [l18 z y]

theorem Equation313_385_implies_Equation372 (G : Type*) [Magma G] (h313 : Equation313 G) (h385 : Equation385 G) : Equation372 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h385 X1 X0]
    conv => enter [1]; rw [← h313 (X0 ◇ X1) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h385 (X0 ◇ X1) X1]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h313 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [l1 X2 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 X1]
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [l3 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [h385 X1 X1]
    conv => enter [1, 1]; rw [l3 X1 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 2]; rw [← l2 X1 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X0 ◇ X0)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X0 X1]
    conv => enter [1]; rw [← l9 X1 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h313 (X0 ◇ X0) (X0 ◇ X1)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← l12 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h313 X1 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X0]
    conv => enter [1]; rw [l14 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 1]; rw [← l16 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y z
  conv => enter [1]; rw [l15 x y]
  conv => enter [1]; rw [l18 y z]

theorem Equation325_364_implies_Equation41 (G : Type*) [Magma G] (h325 : Equation325 G) (h364 : Equation364 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h364 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h364 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X1 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h325 X0 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l4 X0 X2]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h364 X1 X0]
    conv => enter [1]; rw [l5 (X0 ◇ X1) X1 X2]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [l4 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l6 X1 X0 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l5 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation308_385_implies_Equation41 (G : Type*) [Magma G] (h308 : Equation308 G) (h385 : Equation385 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h308 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h308 X0 X1]
    conv => enter [1]; rw [← h385 (X0 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h385 X1 X0]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l4 X0 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X1 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h308 X1 X0]
    conv => enter [1]; rw [l5 X1 (X1 ◇ X0) X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1, 1]; rw [l4 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [← l6 X1 (X1 ◇ X0) X0]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l5 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation325_362_implies_Equation326 (G : Type*) [Magma G] (h325 : Equation325 G) (h362 : Equation362 G) : Equation326 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h362 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation315_385_implies_Equation375 (G : Type*) [Magma G] (h315 : Equation315 G) (h385 : Equation385 G) : Equation375 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h385 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h315 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation325_361_implies_Equation308 (G : Type*) [Magma G] (h325 : Equation325 G) (h361 : Equation361 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h361 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation309_385_implies_Equation364 (G : Type*) [Magma G] (h309 : Equation309 G) (h385 : Equation385 G) : Equation364 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h309 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation323_378_385_implies_Equation333 (G : Type*) [Magma G] (h323 : Equation323 G) (h378 : Equation378 G) (h385 : Equation385 G) : Equation333 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X1]
    conv => enter [1]; rw [h323 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h378 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h378 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation323_325_378_implies_Equation377 (G : Type*) [Magma G] (h323 : Equation323 G) (h325 : Equation325 G) (h378 : Equation378 G) : Equation377 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [h378 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h323 X1 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h323 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation323_367_378_implies_Equation336 (G : Type*) [Magma G] (h323 : Equation323 G) (h367 : Equation367 G) (h378 : Equation378 G) : Equation336 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X1]
    conv => enter [1]; rw [h323 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h378 X0 X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h367 X2 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X1]
    conv => enter [1]; rw [← l1 X1 X0 X1]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2]
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X2)]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [l3 y y y]

theorem Equation310_323_378_implies_Equation374 (G : Type*) [Magma G] (h310 : Equation310 G) (h323 : Equation323 G) (h378 : Equation378 G) : Equation374 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [h378 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h323 X1 X0]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h310 X2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [← l1 X1 X1 X0]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = ((X2 ◇ X1) ◇ X0) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1]
    conv => enter [1]; rw [← l2 (X2 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [l3 x x x]

theorem Equation323_365_implies_Equation371 (G : Type*) [Magma G] (h323 : Equation323 G) (h365 : Equation365 G) : Equation371 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X1]
    conv => enter [1]; rw [h323 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h323 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [h365 X1 X2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation323_365_implies_Equation316 (G : Type*) [Magma G] (h323 : Equation323 G) (h365 : Equation365 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X1]
    conv => enter [1]; rw [h323 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h323 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]
  conv => enter [1]; rw [h323 y y]

theorem Equation313_378_implies_Equation319 (G : Type*) [Magma G] (h313 : Equation313 G) (h378 : Equation378 G) : Equation319 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X1]
    conv => enter [1]; rw [h378 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h313 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h378 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [h313 X1 X2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation313_378_implies_Equation368 (G : Type*) [Magma G] (h313 : Equation313 G) (h378 : Equation378 G) : Equation368 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X1]
    conv => enter [1]; rw [h378 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h313 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h378 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]
  conv => enter [1]; rw [h378 y y]

theorem Equation323_362_implies_Equation360 (G : Type*) [Magma G] (h323 : Equation323 G) (h362 : Equation362 G) : Equation360 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h323 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation315_378_implies_Equation312 (G : Type*) [Magma G] (h315 : Equation315 G) (h378 : Equation378 G) : Equation312 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h378 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation323_361_364_375_implies_Equation333 (G : Type*) [Magma G] (h323 : Equation323 G) (h361 : Equation361 G) (h364 : Equation364 G) (h375 : Equation375 G) : Equation333 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h323 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h361 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h364 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation308_309_326_378_implies_Equation377 (G : Type*) [Magma G] (h308 : Equation308 G) (h309 : Equation309 G) (h326 : Equation326 G) (h378 : Equation378 G) : Equation377 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h378 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h309 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h308 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h326 (X0 ◇ X1) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation323_360_378_implies_Equation379 (G : Type*) [Magma G] (h323 : Equation323 G) (h360 : Equation360 G) (h378 : Equation378 G) : Equation379 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X1]
    conv => enter [1]; rw [h323 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h378 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h360 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation312_323_378_implies_Equation343 (G : Type*) [Magma G] (h312 : Equation312 G) (h323 : Equation323 G) (h378 : Equation378 G) : Equation343 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [h378 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h323 X1 X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [h312 (X1 ◇ X0) X2]
    conv => enter [1, 2]; rw [← l0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation315_362_375_implies_Equation332 (G : Type*) [Magma G] (h315 : Equation315 G) (h362 : Equation362 G) (h375 : Equation375 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h362 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h315 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h315 (X0 ◇ X1) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation315_362_375_implies_Equation313 (G : Type*) [Magma G] (h315 : Equation315 G) (h362 : Equation362 G) (h375 : Equation375 G) : Equation313 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h362 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h315 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation315_326_362_implies_Equation332 (G : Type*) [Magma G] (h315 : Equation315 G) (h326 : Equation326 G) (h362 : Equation362 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h315 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h362 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 (X0 ◇ X1) X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h362 (X1 ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← h326 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l8 X1 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation315_361_implies_Equation367 (G : Type*) [Magma G] (h315 : Equation315 G) (h361 : Equation361 G) : Equation367 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h361 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h315 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation309_362_implies_Equation310 (G : Type*) [Magma G] (h309 : Equation309 G) (h362 : Equation362 G) : Equation310 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h362 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation315_360_implies_Equation317 (G : Type*) [Magma G] (h315 : Equation315 G) (h360 : Equation360 G) : Equation317 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h360 X1 ((X1 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h315 X1 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation315_360_implies_Equation368 (G : Type*) [Magma G] (h315 : Equation315 G) (h360 : Equation360 G) : Equation368 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h360 X1 ((X1 ◇ X1) ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h360 y y]

theorem Equation312_362_implies_Equation372 (G : Type*) [Magma G] (h312 : Equation312 G) (h362 : Equation362 G) : Equation372 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h312 X1 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h362 X1 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation312_362_implies_Equation316 (G : Type*) [Magma G] (h312 : Equation312 G) (h362 : Equation362 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h312 X1 (X0 ◇ (X1 ◇ X1))]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h312 y y]

theorem Equation315_326_367_implies_Equation370 (G : Type*) [Magma G] (h315 : Equation315 G) (h326 : Equation326 G) (h367 : Equation367 G) : Equation370 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h315 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h315 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h367 X2 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation310_362_375_implies_Equation311 (G : Type*) [Magma G] (h310 : Equation310 G) (h362 : Equation362 G) (h375 : Equation375 G) : Equation311 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h362 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← h362 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h310 X2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation315_326_365_implies_Equation332 (G : Type*) [Magma G] (h315 : Equation315 G) (h326 : Equation326 G) (h365 : Equation365 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h315 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h365 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X0) X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h326 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation315_326_365_implies_Equation362 (G : Type*) [Magma G] (h315 : Equation315 G) (h326 : Equation326 G) (h365 : Equation365 G) : Equation362 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h315 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h365 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation313_362_375_implies_Equation332 (G : Type*) [Magma G] (h313 : Equation313 G) (h362 : Equation362 G) (h375 : Equation375 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h313 (X0 ◇ X1) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation313_362_375_implies_Equation315 (G : Type*) [Magma G] (h313 : Equation313 G) (h362 : Equation362 G) (h375 : Equation375 G) : Equation315 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h362 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h313 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation315_326_364_375_implies_Equation333 (G : Type*) [Magma G] (h315 : Equation315 G) (h326 : Equation326 G) (h364 : Equation364 G) (h375 : Equation375 G) : Equation333 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h315 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h315 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h364 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h315 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation308_326_362_375_implies_Equation377 (G : Type*) [Magma G] (h308 : Equation308 G) (h326 : Equation326 G) (h362 : Equation362 G) (h375 : Equation375 G) : Equation377 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h362 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← h362 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h308 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h362 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h326 (X0 ◇ X1) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation313_367_implies_Equation319 (G : Type*) [Magma G] (h313 : Equation313 G) (h367 : Equation367 G) : Equation319 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h313 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h313 X1 X2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation313_367_implies_Equation368 (G : Type*) [Magma G] (h313 : Equation313 G) (h367 : Equation367 G) : Equation368 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h313 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]
  conv => enter [1]; rw [h367 y y]

theorem Equation310_365_implies_Equation371 (G : Type*) [Magma G] (h310 : Equation310 G) (h365 : Equation365 G) : Equation371 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h365 X1 X2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation310_365_implies_Equation316 (G : Type*) [Magma G] (h310 : Equation310 G) (h365 : Equation365 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]
  conv => enter [1]; rw [h310 y y]

theorem Equation313_364_implies_Equation372 (G : Type*) [Magma G] (h313 : Equation313 G) (h364 : Equation364 G) : Equation372 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h364 X0 X1]
    conv => enter [1]; rw [← h313 (X1 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← l2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  intro x y z
  conv => enter [1]; rw [l6 x z]
  conv => enter [1]; rw [h364 z y]

theorem Equation308_365_implies_Equation317 (G : Type*) [Magma G] (h308 : Equation308 G) (h365 : Equation365 G) : Equation317 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h308 X0 X1]
    conv => enter [1]; rw [← h365 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [← l2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  intro x y z
  conv => enter [1]; rw [l6 x y]
  conv => enter [1]; rw [h308 y z]

theorem Equation313_361_implies_Equation319 (G : Type*) [Magma G] (h313 : Equation313 G) (h361 : Equation361 G) : Equation319 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h361 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h313 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h313 (X1 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [h313 X1 X2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation313_361_implies_Equation371 (G : Type*) [Magma G] (h313 : Equation313 G) (h361 : Equation361 G) : Equation371 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h361 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h313 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h313 (X1 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y z
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h361 y z]

theorem Equation309_365_implies_Equation319 (G : Type*) [Magma G] (h309 : Equation309 G) (h365 : Equation365 G) : Equation319 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h365 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y z
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h309 y z]

theorem Equation313_360_implies_Equation319 (G : Type*) [Magma G] (h313 : Equation313 G) (h360 : Equation360 G) : Equation319 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h360 X1 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h313 X1 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation313_360_implies_Equation368 (G : Type*) [Magma G] (h313 : Equation313 G) (h360 : Equation360 G) : Equation368 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h360 X1 (X0 ◇ (X1 ◇ X1))]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h360 y y]

theorem Equation312_365_implies_Equation371 (G : Type*) [Magma G] (h312 : Equation312 G) (h365 : Equation365 G) : Equation371 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h312 X1 ((X1 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h365 X1 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation312_365_implies_Equation316 (G : Type*) [Magma G] (h312 : Equation312 G) (h365 : Equation365 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h312 X1 ((X1 ◇ X1) ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h312 y y]

theorem Equation312_361_implies_Equation367 (G : Type*) [Magma G] (h312 : Equation312 G) (h361 : Equation361 G) : Equation367 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h361 X1 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h312 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation309_360_implies_Equation310 (G : Type*) [Magma G] (h309 : Equation309 G) (h360 : Equation360 G) : Equation310 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h360 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation312_360_implies_Equation316 (G : Type*) [Magma G] (h312 : Equation312 G) (h360 : Equation360 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h360 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h312 y y]

theorem Equation312_360_implies_Equation368 (G : Type*) [Magma G] (h312 : Equation312 G) (h360 : Equation360 G) : Equation368 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h360 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h360 y y]

theorem Equation310_367_378_implies_Equation316 (G : Type*) [Magma G] (h310 : Equation310 G) (h367 : Equation367 G) (h378 : Equation378 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h310 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h367 (X1 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h310 X0 X1]
    conv => enter [1]; rw [h378 X0 (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← h310 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h310 X1 X2]
  intro x y
  conv => enter [1]; rw [l4 x y y]

theorem Equation310_367_378_implies_Equation368 (G : Type*) [Magma G] (h310 : Equation310 G) (h367 : Equation367 G) (h378 : Equation378 G) : Equation368 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h310 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h367 (X1 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h310 X0 X1]
    conv => enter [1]; rw [h378 X0 (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← h310 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]
  conv => enter [1]; rw [h378 y y]

theorem Equation310_323_367_implies_Equation316 (G : Type*) [Magma G] (h310 : Equation310 G) (h323 : Equation323 G) (h367 : Equation367 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h367 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h310 (X1 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h367 X0 X1]
    conv => enter [1]; rw [h323 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h367 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]
  conv => enter [1]; rw [h323 y y]

theorem Equation310_323_367_implies_Equation368 (G : Type*) [Magma G] (h310 : Equation310 G) (h323 : Equation323 G) (h367 : Equation367 G) : Equation368 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h367 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h310 (X1 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h367 X0 X1]
    conv => enter [1]; rw [h323 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h367 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X2 ◇ X2) ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h367 X1 X2]
  intro x y
  conv => enter [1]; rw [l4 x y y]

theorem Equation310_364_375_implies_Equation41 (G : Type*) [Magma G] (h310 : Equation310 G) (h364 : Equation364 G) (h375 : Equation375 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [h364 X0 X0]
    conv => enter [1, 1]; rw [h310 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h364 (X1 ◇ X1) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h375 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h310 X1 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← l4 X1 X0]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h375 X0 X2]
    conv => enter [1, 1]; rw [h310 X0 X1]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X1 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 1]; rw [← l4 X1 X0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [← l5 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

theorem Equation308_326_367_implies_Equation41 (G : Type*) [Magma G] (h308 : Equation308 G) (h326 : Equation326 G) (h367 : Equation367 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← h367 X0 X1]
    conv => enter [1]; rw [h308 X0 X0]
    conv => enter [1, 2]; rw [h367 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h308 (X1 ◇ X1) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h367 X1 X1]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← l4 X1 X0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 X0]
    conv => enter [1, 2]; rw [h367 X0 X1]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X1 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1, 2]; rw [← l4 X1 X0]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 X0 X2]
    conv => enter [1]; rw [← l5 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

theorem Equation310_361_375_implies_Equation381 (G : Type*) [Magma G] (h310 : Equation310 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation381 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h375 X0 X2]
    conv => enter [1, 1]; rw [h310 X0 X1]
  have l1 : ∀ X0 X2 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h361 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l0 ((X0 ◇ X0) ◇ X1) X2 X0]
  have l2 : ∀ X0 X2 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 1]; rw [← h375 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l2 X0 X2 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h375 X0 X2]
    conv => enter [1]; rw [l3 X0 X2 X1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation310_361_375_implies_Equation308 (G : Type*) [Magma G] (h310 : Equation310 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation308 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h375 X0 X2]
    conv => enter [1, 1]; rw [h310 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h310 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h361 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l0 ((X0 ◇ X0) ◇ X1) X2 X0]
  have l5 : ∀ X0 X2 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 1]; rw [← h375 X0 X1]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l5 X0 X2 X1]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h375 X0 X2]
    conv => enter [1]; rw [l6 X0 X2 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h310 (X0 ◇ X1) X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l7 X0 (X0 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation309_326_367_implies_Equation329 (G : Type*) [Magma G] (h309 : Equation309 G) (h326 : Equation326 G) (h367 : Equation367 G) : Equation329 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 X0]
    conv => enter [1, 2]; rw [h367 X0 X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h309 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l0 X2 (X1 ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1, 2]; rw [← h326 X1 X0]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 (X0 ◇ X0)]
    conv => enter [1]; rw [l2 X2 X0 X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 X0]
    conv => enter [1]; rw [l3 X2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation309_326_367_implies_Equation364 (G : Type*) [Magma G] (h309 : Equation309 G) (h326 : Equation326 G) (h367 : Equation367 G) : Equation364 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 X0]
    conv => enter [1, 2]; rw [h367 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h309 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h326 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h326 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h367 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h309 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l0 X2 (X1 ◇ (X0 ◇ X0)) X0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l4 X2 X0 X1]
    conv => enter [1, 2]; rw [← h326 X1 X0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 (X0 ◇ X0)]
    conv => enter [1]; rw [l5 X2 X0 X1]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 X0]
    conv => enter [1]; rw [l6 X2 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h367 (X1 ◇ X0) X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l7 (X1 ◇ X0) X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation310_323_359_361_implies_Equation360 (G : Type*) [Magma G] (h310 : Equation310 G) (h323 : Equation323 G) (h359 : Equation359 G) (h361 : Equation361 G) : Equation360 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h359 sK0]
    conv => enter [1]; rw [h323 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h359 sK0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h361 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← h310 ((sK0 ◇ sK0) ◇ sK1) sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h361 ((sK0 ◇ sK0) ◇ sK1) ((sK0 ◇ sK0) ◇ sK1)]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h323 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation307_309_367_378_implies_Equation312 (G : Type*) [Magma G] (h307 : Equation307 G) (h309 : Equation309 G) (h367 : Equation367 G) (h378 : Equation378 G) : Equation312 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1]; rw [h378 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h307 sK0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h309 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← h367 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h309 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h378 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation309_364_375_implies_Equation395 (G : Type*) [Magma G] (h309 : Equation309 G) (h364 : Equation364 G) (h375 : Equation375 G) : Equation395 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h364 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h309 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h309 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h375 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l4 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X2) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2]
    conv => enter [1]; rw [← h375 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l4 z x y]

theorem Equation308_326_361_implies_Equation327 (G : Type*) [Magma G] (h308 : Equation308 G) (h326 : Equation326 G) (h361 : Equation361 G) : Equation327 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h308 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h361 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h326 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1]; rw [← h326 X2 X0]
  intro x y z
  conv => enter [1]; rw [← l4 x y z]

theorem Equation309_326_364_implies_Equation329 (G : Type*) [Magma G] (h309 : Equation309 G) (h326 : Equation326 G) (h364 : Equation364 G) : Equation329 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h364 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l2 X0 X2]
    conv => enter [1]; rw [← h326 X1 (X2 ◇ X0)]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l3 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation308_361_375_implies_Equation381 (G : Type*) [Magma G] (h308 : Equation308 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation381 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h308 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l2 X0 X2]
    conv => enter [1]; rw [← h375 (X0 ◇ X2) X1]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l3 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation309_326_361_375_378_implies_Equation323 (G : Type*) [Magma G] (h309 : Equation309 G) (h326 : Equation326 G) (h361 : Equation361 G) (h375 : Equation375 G) (h378 : Equation378 G) : Equation323 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h378 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation309_323_326_361_375_implies_Equation378 (G : Type*) [Magma G] (h309 : Equation309 G) (h323 : Equation323 G) (h326 : Equation326 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation378 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h323 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation309_323_381_implies_Equation326 (G : Type*) [Magma G] (h309 : Equation309 G) (h323 : Equation323 G) (h381 : Equation381 G) : Equation326 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h381 X1 (X0 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h381 X1 (X1 ◇ X0) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation329_361_378_implies_Equation375 (G : Type*) [Magma G] (h329 : Equation329 G) (h361 : Equation361 G) (h378 : Equation378 G) : Equation375 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h329 (X0 ◇ X0) X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h329 (X0 ◇ X1) X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation309_323_359_361_364_implies_Equation367 (G : Type*) [Magma G] (h309 : Equation309 G) (h323 : Equation323 G) (h359 : Equation359 G) (h361 : Equation361 G) (h364 : Equation364 G) : Equation367 G := by
  have l0 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) = (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h309 ((sK1 ◇ sK1) ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h309 sK0 (sK1 ◇ sK1)]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h359 sK0]
    conv => enter [1]; rw [h323 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h359 sK0]
  have l2 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h359 sK1]
    conv => enter [1]; rw [h323 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h359 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (((sK1 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1]; rw [h361 (sK1 ◇ sK1) sK0]
  have l4 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h361 ((sK1 ◇ sK1) ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 1]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = (((sK1 ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h323 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h364 (sK0 ◇ sK0) ((sK1 ◇ sK1) ◇ sK0)]
    conv => enter [1, 1]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation307_308_309_361_378_implies_Equation310 (G : Type*) [Magma G] (h307 : Equation307 G) (h308 : Equation308 G) (h309 : Equation309 G) (h361 : Equation361 G) (h378 : Equation378 G) : Equation310 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h361 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 1]; rw [← h361 sK0 (sK1 ◇ sK1)]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1]; rw [h378 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h307 sK0]
  have l2 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h307 sK1]
    conv => enter [1]; rw [h378 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 1]; rw [← h307 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1]; rw [h309 (sK1 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h309 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h378 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h308 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation308_364_375_implies_Equation41 (G : Type*) [Magma G] (h308 : Equation308 G) (h364 : Equation364 G) (h375 : Equation375 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h364 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h308 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h308 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h375 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h375 X0 X2]
    conv => enter [1]; rw [← l3 X0 X1 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h364 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l5 X1 X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h308 X1 X0]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h308 X1 X2]
    conv => enter [1]; rw [l6 X1 (X1 ◇ X2) X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l8 X1 X0 X1]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l6 X1 X1 X2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation308_326_364_implies_Equation41 (G : Type*) [Magma G] (h308 : Equation308 G) (h326 : Equation326 G) (h364 : Equation364 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h308 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h364 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h364 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h326 X2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 X0]
    conv => enter [1]; rw [← l3 X2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h308 X0 X1]
    conv => enter [1]; rw [← l4 X0 X1 X0]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l5 X1 X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h364 X1 X0]
    conv => enter [1, 1]; rw [← l5 X0 X1]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = ((X2 ◇ X1) ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h364 X1 X2]
    conv => enter [1]; rw [l6 (X2 ◇ X1) X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l8 X1 X1 X0]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l6 X1 X1 X2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation255_333_implies_Equation3 (G : Type*) [Magma G] (h255 : Equation255 G) (h333 : Equation333 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h333 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h255 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation47_377_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h377 : Equation377 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h377 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h47 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation255_315_implies_Equation72 (G : Type*) [Magma G] (h255 : Equation255 G) (h315 : Equation315 G) : Equation72 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h315 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← h255 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h255 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x]
  conv => enter [1]; rw [← l2 y (x ◇ x)]

theorem Equation255_315_implies_Equation16 (G : Type*) [Magma G] (h255 : Equation255 G) (h315 : Equation315 G) : Equation16 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h315 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← h255 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h255 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation255_315_implies_Equation127 (G : Type*) [Magma G] (h255 : Equation255 G) (h315 : Equation315 G) : Equation127 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h315 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← h255 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h255 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2, 1]; rw [← l1 y]

theorem Equation255_315_implies_Equation228 (G : Type*) [Magma G] (h255 : Equation255 G) (h315 : Equation315 G) : Equation228 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h315 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← h255 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h255 X0]
  intro x y
  conv => enter [1]; rw [← l1 x]
  conv => enter [1, 1]; rw [← l1 x]
  conv => enter [1, 1]; rw [h315 x y]

theorem Equation47_362_implies_Equation258 (G : Type*) [Magma G] (h47 : Equation47 G) (h362 : Equation362 G) : Equation258 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h362 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← h47 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h47 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← h362 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x]
  conv => enter [1]; rw [← l2 (x ◇ x) y]

theorem Equation47_362_implies_Equation26 (G : Type*) [Magma G] (h47 : Equation47 G) (h362 : Equation362 G) : Equation26 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h362 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← h47 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h47 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← h362 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation47_362_implies_Equation212 (G : Type*) [Magma G] (h47 : Equation47 G) (h362 : Equation362 G) : Equation212 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h362 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← h47 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h47 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← h362 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1, 2]; rw [← l1 y]

theorem Equation47_362_implies_Equation102 (G : Type*) [Magma G] (h47 : Equation47 G) (h362 : Equation362 G) : Equation102 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h362 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← h47 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x y
  conv => enter [1]; rw [← l1 x]
  conv => enter [1, 2]; rw [← l1 x]
  conv => enter [1, 2]; rw [h362 x y]

theorem Equation255_310_325_implies_Equation256 (G : Type*) [Magma G] (h255 : Equation255 G) (h310 : Equation310 G) (h325 : Equation325 G) : Equation256 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h310 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l4 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [← l2 X0 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h255 X0]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation47_367_385_implies_Equation62 (G : Type*) [Magma G] (h47 : Equation47 G) (h367 : Equation367 G) (h385 : Equation385 G) : Equation62 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ X2) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h367 X2 X0]
    conv => enter [1, 1]; rw [h367 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← h367 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l4 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← l2 X0 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h47 X0]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation255_309_312_323_implies_Equation5 (G : Type*) [Magma G] (h255 : Equation255 G) (h309 : Equation309 G) (h312 : Equation312 G) (h323 : Equation323 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h309 X0 X1]
    conv => enter [1]; rw [← h309 (X1 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h255 (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l2 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h323 (X0 ◇ X0) X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l1 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l3 X0]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l4 X0]
    conv => enter [1]; rw [← h255 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0]
    conv => enter [1]; rw [← h312 X0 X1]
    conv => enter [1]; rw [l6 X0]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation47_360_361_378_implies_Equation4 (G : Type*) [Magma G] (h47 : Equation47 G) (h360 : Equation360 G) (h361 : Equation361 G) (h378 : Equation378 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h361 X0 X1]
    conv => enter [1]; rw [← h361 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h47 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l2 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h378 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l4 X0]
    conv => enter [1]; rw [← h47 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0]
    conv => enter [1]; rw [← h360 X0 X1]
    conv => enter [1]; rw [l6 X0]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation255_308_310_implies_Equation256 (G : Type*) [Magma G] (h255 : Equation255 G) (h308 : Equation308 G) (h310 : Equation310 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [← h255 X0]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h308 ((X0 ◇ X0) ◇ X0) X0]
  have l2 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l1 X0]
    conv => enter [1]; rw [← h255 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h310 X1 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [l2 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X0) ◇ X0)]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l3 X0 X2]
  have l6 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l5 (X0 ◇ X1) X2 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 X2 X3 : G, (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 ((X0 ◇ X1) ◇ X2) X3 X0]
    conv => enter [1]; rw [l6 X0 X1 X2]
  intro x y
  conv => enter [1]; rw [← l7 x x x y]

theorem Equation47_364_367_implies_Equation62 (G : Type*) [Magma G] (h47 : Equation47 G) (h364 : Equation364 G) (h367 : Equation367 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← h367 X0 X1]
    conv => enter [1]; rw [← h47 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h364 (X0 ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [← l1 X0]
    conv => enter [1]; rw [← h47 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h367 X1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [l2 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 1]; rw [← l2 X0]
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l3 X0 X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [l5 X2 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X3 X2 X1 X0 : G, (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := by
    intro X3 X2 X1 X0
    conv => enter [1]; rw [l5 X3 (X2 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l6 X0 X2 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x x x]

theorem Equation283_326_implies_Equation5 (G : Type*) [Magma G] (h283 : Equation283 G) (h326 : Equation326 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h326 ((X0 ◇ X0) ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h326 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h283 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation56_375_implies_Equation4 (G : Type*) [Magma G] (h56 : Equation56 G) (h375 : Equation375 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h375 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h56 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h375 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h56 X0 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation283_325_implies_Equation2 (G : Type*) [Magma G] (h283 : Equation283 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [← h283 (X1 ◇ ((X0 ◇ X0) ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h283 X1 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h325 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h325 X0 X0]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h283 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X1 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation56_385_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h56 ((X0 ◇ (X0 ◇ X0)) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h385 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h385 X0 X0]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation283_313_implies_Equation2 (G : Type*) [Magma G] (h283 : Equation283 G) (h313 : Equation313 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h283 ((X1 ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [h313 ((X1 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h283 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X1 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h283 ((X1 ◇ X1) ◇ X1) X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 X2 : G, ((X0 ◇ X0) ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h283 X2 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X0 X0]
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l4 X0 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l4 X1 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation56_365_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h365 : Equation365 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h56 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [h365 (X1 ◇ (X1 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h56 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ (X1 ◇ X1)) X0]
    conv => enter [1]; rw [← h56 (X1 ◇ (X1 ◇ X1)) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l4 : ∀ X2 X0 : G, (X2 ◇ (X0 ◇ X0)) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h56 X2 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l4 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l4 X1 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation283_312_implies_Equation5 (G : Type*) [Magma G] (h283 : Equation283 G) (h312 : Equation312 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h283 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [h312 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2]; rw [← h283 ((X0 ◇ X0) ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h312 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation56_360_implies_Equation4 (G : Type*) [Magma G] (h56 : Equation56 G) (h360 : Equation360 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [h360 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h56 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h360 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h56 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation283_310_implies_Equation2 (G : Type*) [Magma G] (h283 : Equation283 G) (h310 : Equation310 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h283 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← h310 ((X0 ◇ X0) ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h283 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ X0) ◇ X0) ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l1 X1 X2]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X2 : G, ((X0 ◇ X0) ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h283 X2 X0]
  have l4 : ∀ X0 X1 X2 : G, ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h283 X2 X1]
  have l5 : ∀ X1 X2 : G, (X1 ◇ X2) = X2 := by
    intro X1 X2
    conv => enter [1, 1]; rw [h283 X1 X1]
    conv => enter [1]; rw [l4 X1 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [← l2 X2 X0 X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l5 X2 X2]
  have l8 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l7 ((X0 ◇ X0) ◇ X0) X2 X0]
    conv => enter [1]; rw [← h283 X2 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation56_367_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h367 : Equation367 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h56 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← h367 (X0 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l1 X1 X2]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l3 : ∀ X2 X0 : G, (X2 ◇ (X0 ◇ X0)) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [← h56 X2 X2]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h56 X2 X1]
  have l5 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [h56 X1 X2]
    conv => enter [1]; rw [l4 X2 X1 X2]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l3 X0 X0]
    conv => enter [1]; rw [← l2 X2 X1 X0]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [l5 X2 X2]
  have l8 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l7 X2 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h56 X2 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation283_309_implies_Equation5 (G : Type*) [Magma G] (h283 : Equation283 G) (h309 : Equation309 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h309 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [← h283 (X1 ◇ ((X0 ◇ X0) ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h283 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h309 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l1 X0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h283 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [← h283 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation56_361_implies_Equation4 (G : Type*) [Magma G] (h56 : Equation56 G) (h361 : Equation361 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [← h56 ((X0 ◇ (X0 ◇ X0)) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h361 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l1 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation283_308_implies_Equation2 (G : Type*) [Magma G] (h283 : Equation283 G) (h308 : Equation308 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h283 X1 X0]
    conv => enter [1]; rw [← h308 ((X0 ◇ X0) ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h283 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← l0 X0 X1]
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

theorem Equation56_364_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h364 : Equation364 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h56 X1 X0]
    conv => enter [1]; rw [← h364 (X0 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← l0 X1 X0]
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

theorem Equation280_326_implies_Equation28 (G : Type*) [Magma G] (h280 : Equation280 G) (h326 : Equation326 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h280 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← h326 ((X0 ◇ X0) ◇ (X1 ◇ X1)) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h326 (X0 ◇ X0) X1]
  have l2 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1]; rw [← h280 X1 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h280 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation50_375_implies_Equation9 (G : Type*) [Magma G] (h50 : Equation50 G) (h375 : Equation375 G) : Equation9 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h50 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← h375 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h375 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1]; rw [← h50 X1 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation280_325_implies_Equation2 (G : Type*) [Magma G] (h280 : Equation280 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h280 X0 X1]
    conv => enter [1]; rw [← h325 X0 ((X1 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h280 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1]; rw [← h325 (X0 ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l1 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X1 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h280 X1 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0 X0]
    conv => enter [1]; rw [l5 X0 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l6 X1]
    conv => enter [1]; rw [← h280 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation50_385_implies_Equation2 (G : Type*) [Magma G] (h50 : Equation50 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h50 X0 X1]
    conv => enter [1]; rw [← h385 (X0 ◇ (X1 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h50 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2]; rw [← h385 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X1) X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h50 X1 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0 X0]
    conv => enter [1]; rw [l5 X0 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l6 X1]
    conv => enter [1]; rw [← h50 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation280_323_implies_Equation28 (G : Type*) [Magma G] (h280 : Equation280 G) (h323 : Equation323 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [← h323 (X0 ◇ X0) X1]
  have l1 : ∀ X0 X1 X2 : G, ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0) X0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h280 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation280_323_implies_Equation228 (G : Type*) [Magma G] (h280 : Equation280 G) (h323 : Equation323 G) : Equation228 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [← h323 (X0 ◇ X0) X1]
  have l1 : ∀ X0 X1 X2 : G, ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0) X0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h280 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 1]; rw [h323 y x]

theorem Equation50_378_implies_Equation9 (G : Type*) [Magma G] (h50 : Equation50 G) (h378 : Equation378 G) : Equation9 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h50 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← h378 X1 (X0 ◇ X0)]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h50 X2 (X1 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X0 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation50_378_implies_Equation102 (G : Type*) [Magma G] (h50 : Equation50 G) (h378 : Equation378 G) : Equation102 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h50 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← h378 X1 (X0 ◇ X0)]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h50 X2 (X1 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X0 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]
  conv => enter [1, 2]; rw [h378 x y]

theorem Equation280_313_implies_Equation319 (G : Type*) [Magma G] (h280 : Equation280 G) (h313 : Equation313 G) : Equation319 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h280 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h280 X0 X1]
    conv => enter [1]; rw [← h313 ((X1 ◇ X1) ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 ((X0 ◇ X0) ◇ X1) X1]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X0 (X1 ◇ X1)]
    conv => enter [1, 1]; rw [l3 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 ((X0 ◇ X0) ◇ (X1 ◇ X1)) X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l1 (X1 ◇ X1) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l5 X1 X1]
  intro x y z
  conv => enter [1]; rw [l9 x z]
  conv => enter [1]; rw [h313 z y]

theorem Equation50_365_implies_Equation371 (G : Type*) [Magma G] (h50 : Equation50 G) (h365 : Equation365 G) : Equation371 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h50 X0 X1]
    conv => enter [1]; rw [← h365 (X0 ◇ (X1 ◇ X1)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l3 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 ((X1 ◇ X1) ◇ (X0 ◇ X0)) X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l1 (X1 ◇ X1) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l5 X1 X1]
  intro x y z
  conv => enter [1]; rw [l9 x z]
  conv => enter [1]; rw [h365 z y]

theorem Equation280_310_implies_Equation316 (G : Type*) [Magma G] (h280 : Equation280 G) (h310 : Equation310 G) : Equation316 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h280 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [h310 X0 X2]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [← h280 X2 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h280 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h310 (X0 ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← l0 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h280 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [l2 (X0 ◇ X0) X1 X2]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h280 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1, 1]; rw [← l2 (X0 ◇ X0) X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l7 X1 X2 X0]
    conv => enter [1, 1]; rw [← l5 X0 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 1]; rw [← l8 X1 X2 X0]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l3 X1 X2 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) X0 X3]
  have l11 : ∀ X0 X3 : G, (X0 ◇ X0) = (X3 ◇ X3) := by
    intro X0 X3
    conv => enter [1]; rw [l10 X0 X0 X0 X3]
    conv => enter [1]; rw [← l9 X3 (X0 ◇ (X0 ◇ X0)) X0]
  intro x y
  conv => enter [1]; rw [l11 x y]
  conv => enter [1]; rw [h310 y y]

theorem Equation50_367_implies_Equation368 (G : Type*) [Magma G] (h50 : Equation50 G) (h367 : Equation367 G) : Equation368 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← h367 X0 X1]
    conv => enter [1]; rw [h367 X0 X2]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ X2) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h367 X2 X0]
    conv => enter [1, 1]; rw [h367 X0 X1]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← h367 X0 X1]
    conv => enter [1]; rw [← h50 X2 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h50 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h367 (X0 ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [← l0 X0]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h50 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [l2 (X0 ◇ X0) X2 X1]
  have l7 : ∀ X2 X1 X0 : G, ((X2 ◇ X2) ◇ X1) = (((X2 ◇ X2) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h50 ((X2 ◇ X2) ◇ X1) X0]
    conv => enter [1, 2]; rw [← l2 (X0 ◇ X0) X2 X1]
  have l8 : ∀ X2 X1 X0 : G, ((X2 ◇ X2) ◇ X1) = (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l7 X2 X1 X0]
    conv => enter [1, 2]; rw [← l5 X0 X0]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← l8 X2 X1 X0]
  have l10 : ∀ X0 X3 X2 X1 : G, (X0 ◇ X0) = ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X1))) := by
    intro X0 X3 X2 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X0) X2 X1]
    conv => enter [1]; rw [l1 X0 ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X1)) X3]
  have l11 : ∀ X0 X3 : G, (X0 ◇ X0) = (X3 ◇ X3) := by
    intro X0 X3
    conv => enter [1]; rw [l10 X0 X3 X0 X0]
    conv => enter [1]; rw [← l9 X3 X0 ((X0 ◇ X0) ◇ X0)]
  intro x y
  conv => enter [1]; rw [l11 x y]
  conv => enter [1]; rw [h367 y y]

theorem Equation280_309_implies_Equation312 (G : Type*) [Magma G] (h280 : Equation280 G) (h309 : Equation309 G) : Equation312 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h280 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h280 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1]; rw [← h309 (X0 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← l0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h309 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation50_361_implies_Equation360 (G : Type*) [Magma G] (h50 : Equation50 G) (h361 : Equation361 G) : Equation360 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h50 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2]; rw [← h361 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← l0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h361 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation280_308_implies_Equation2 (G : Type*) [Magma G] (h280 : Equation280 G) (h308 : Equation308 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h280 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [← h308 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← l0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h308 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h280 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l6 X0 X2]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation50_364_implies_Equation2 (G : Type*) [Magma G] (h50 : Equation50 G) (h364 : Equation364 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h50 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← h364 (X0 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← l0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h364 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h50 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l6 X0 X2]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation280_283_implies_Equation5 (G : Type*) [Magma G] (h280 : Equation280 G) (h283 : Equation283 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h280 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l0 X1 X1]
    conv => enter [1]; rw [← h283 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation50_56_implies_Equation4 (G : Type*) [Magma G] (h50 : Equation50 G) (h56 : Equation56 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h50 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h56 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X1]
    conv => enter [1]; rw [← h56 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation273_307_implies_Equation3 (G : Type*) [Magma G] (h273 : Equation273 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h273 (X0 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h307 X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h273 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h273 X0 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation53_359_implies_Equation3 (G : Type*) [Magma G] (h53 : Equation53 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h53 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h359 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h53 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h53 X0 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation273_283_implies_Equation5 (G : Type*) [Magma G] (h273 : Equation273 G) (h283 : Equation283 G) : Equation5 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h283 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h273 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h283 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation53_56_implies_Equation4 (G : Type*) [Magma G] (h53 : Equation53 G) (h56 : Equation56 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h56 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h53 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation273_274_implies_Equation2 (G : Type*) [Magma G] (h273 : Equation273 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h273 X1 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h274 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation53_73_implies_Equation2 (G : Type*) [Magma G] (h53 : Equation53 G) (h73 : Equation73 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h53 X1 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h73 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation264_323_implies_Equation256 (G : Type*) [Magma G] (h264 : Equation264 G) (h323 : Equation323 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h323 ((X0 ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [← h264 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h264 ((X0 ◇ X1) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h264 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation75_378_implies_Equation62 (G : Type*) [Magma G] (h75 : Equation75 G) (h378 : Equation378 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h378 X1 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h75 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h75 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation264_313_implies_Equation14 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l3 X0 (X1 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [← l9 y x]

theorem Equation264_313_implies_Equation66 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l4 X0 (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l6 X1 X1]
    conv => enter [1]; rw [l10 X1 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l12 y x]
  conv => enter [1, 2, 2]; rw [← l11 y]

theorem Equation264_313_implies_Equation115 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l4 X0 (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l6 X1 X1]
    conv => enter [1]; rw [l10 X1 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1]; rw [← l12 y (x ◇ x)]

theorem Equation264_313_implies_Equation219 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation219 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X0 (X1 ◇ X0)]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l8 X1 X1]
    conv => enter [1]; rw [l13 X1 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l14 X0]
    conv => enter [1, 1, 1]; rw [← l14 X0]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l14 x]
  conv => enter [1]; rw [← l17 y (x ◇ x)]

theorem Equation264_313_implies_Equation335 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation335 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X2) ◇ X2) X2]
    conv => enter [1, 2]; rw [← h264 X0 X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l5 X0 (X1 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [← l11 X0 ((X0 ◇ X2) ◇ X2)]
    conv => enter [1]; rw [l3 X0 X0 X2]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l11 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l12 X1 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation264_313_implies_Equation124 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation124 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X2) ◇ X2) X2]
    conv => enter [1, 2]; rw [← h264 X0 X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l5 X0 (X1 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [← l11 X0 ((X0 ◇ X2) ◇ X2)]
    conv => enter [1]; rw [l3 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [← l11 y x]
  conv => enter [1, 2]; rw [← l12 y x]

theorem Equation264_313_implies_Equation206 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation206 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X2) ◇ X2) X2]
    conv => enter [1, 2]; rw [← h264 X0 X2]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l7 X0 (X1 ◇ X0)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l10 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [← l6 X0 X1]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l9 X1 X1]
    conv => enter [1]; rw [l14 X1 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  have l17 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 X1 X0]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [← l16 X0 ((X0 ◇ X2) ◇ X2)]
    conv => enter [1]; rw [l3 X0 X0 X2]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l15 X0]
    conv => enter [1, 1, 1]; rw [← l15 X0]
    conv => enter [1]; rw [l17 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l16 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l18 X1 X0]
  intro x y
  conv => enter [1]; rw [← l19 y x]
  conv => enter [1, 1]; rw [l20 y x]

theorem Equation264_313_implies_Equation53 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation53 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l4 X0 (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l6 X1 X1]
    conv => enter [1]; rw [l10 X1 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1, 2]; rw [← l12 y x]

theorem Equation264_313_implies_Equation273 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation273 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X0 (X1 ◇ X0)]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l8 X1 X1]
    conv => enter [1]; rw [l13 X1 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l14 X0]
    conv => enter [1, 1, 1]; rw [← l14 X0]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l14 x]
  conv => enter [1, 1]; rw [← l17 y x]

theorem Equation264_313_implies_Equation105 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation105 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X0 (X1 ◇ X0)]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l8 X1 X1]
    conv => enter [1]; rw [l13 X1 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l14 X0]
    conv => enter [1, 1, 1]; rw [← l14 X0]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l14 x]
  conv => enter [1, 2]; rw [← l17 y x]

end Order3
