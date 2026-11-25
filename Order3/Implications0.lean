import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation377_385_implies_Equation335 (G : Type*) [Magma G] (h377 : Equation377 G) (h385 : Equation385 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h377 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation377_385_implies_Equation384 (G : Type*) [Magma G] (h377 : Equation377 G) (h385 : Equation385 G) : Equation384 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h377 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1, 2]; rw [l0 x y]
  conv => enter [1]; rw [l0 x (y ◇ x)]

theorem Equation377_385_implies_Equation43 (G : Type*) [Magma G] (h377 : Equation377 G) (h385 : Equation385 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h377 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation377_385_implies_Equation325 (G : Type*) [Magma G] (h377 : Equation377 G) (h385 : Equation385 G) : Equation325 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h377 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [l2 y x]

theorem Equation377_385_implies_Equation333 (G : Type*) [Magma G] (h377 : Equation377 G) (h385 : Equation385 G) : Equation333 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h377 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation377_385_implies_Equation323 (G : Type*) [Magma G] (h377 : Equation377 G) (h385 : Equation385 G) : Equation323 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h377 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation377_385_implies_Equation378 (G : Type*) [Magma G] (h377 : Equation377 G) (h385 : Equation385 G) : Equation378 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h377 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [l0 y (x ◇ y)]

theorem Equation325_333_implies_Equation335 (G : Type*) [Magma G] (h325 : Equation325 G) (h333 : Equation333 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h333 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1, 1]; rw [l0 x y]
  conv => enter [1]; rw [l0 (y ◇ x) y]

theorem Equation325_333_implies_Equation384 (G : Type*) [Magma G] (h325 : Equation325 G) (h333 : Equation333 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h333 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation325_333_implies_Equation43 (G : Type*) [Magma G] (h325 : Equation325 G) (h333 : Equation333 G) : Equation43 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h333 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation325_333_implies_Equation385 (G : Type*) [Magma G] (h325 : Equation325 G) (h333 : Equation333 G) : Equation385 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h333 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [l2 y x]

theorem Equation325_333_implies_Equation377 (G : Type*) [Magma G] (h325 : Equation325 G) (h333 : Equation333 G) : Equation377 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h333 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation375_377_implies_Equation307 (G : Type*) [Magma G] (h375 : Equation375 G) (h377 : Equation377 G) : Equation307 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h377 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [l2 x]

theorem Equation326_333_implies_Equation359 (G : Type*) [Magma G] (h326 : Equation326 G) (h333 : Equation333 G) : Equation359 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h333 (X0 ◇ X0) X0]
  intro x
  conv => enter [1]; rw [l2 x]

theorem Equation367_378_385_implies_Equation39 (G : Type*) [Magma G] (h367 : Equation367 G) (h378 : Equation378 G) (h385 : Equation385 G) : Equation39 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h378 X0 X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h367 X2 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X0) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h378 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation310_323_325_implies_Equation38 (G : Type*) [Magma G] (h310 : Equation310 G) (h323 : Equation323 G) (h325 : Equation325 G) : Equation38 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h323 X1 X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h323 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation367_377_implies_Equation41 (G : Type*) [Magma G] (h367 : Equation367 G) (h377 : Equation377 G) : Equation41 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h367 X2 X1]
    conv => enter [1, 1]; rw [h367 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h367 X0 X1]
    conv => enter [1]; rw [h377 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h367 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [h377 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h377 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [h367 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l4 X1 (X0 ◇ X0)]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X2]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l7 X2 X3 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l8 x x y z]

theorem Equation310_333_implies_Equation41 (G : Type*) [Magma G] (h310 : Equation310 G) (h333 : Equation333 G) : Equation41 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h310 X2 X1]
    conv => enter [1, 2]; rw [h310 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h310 X0 X1]
    conv => enter [1]; rw [h333 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h310 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [h333 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h333 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [h310 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l4 X1 (X0 ◇ X0)]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l6 (X1 ◇ X0) X2]
  have l8 : ∀ X1 X0 X3 X2 : G, (X1 ◇ X0) = (X3 ◇ X2) := by
    intro X1 X0 X3 X2
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l7 X3 X2 (X1 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [l8 x x y z]

theorem Equation367_375_implies_Equation39 (G : Type*) [Magma G] (h367 : Equation367 G) (h375 : Equation375 G) : Equation39 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h375 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation310_326_implies_Equation38 (G : Type*) [Magma G] (h310 : Equation310 G) (h326 : Equation326 G) : Equation38 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h326 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation365_385_implies_Equation41 (G : Type*) [Magma G] (h365 : Equation365 G) (h385 : Equation385 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h385 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l0 X0 X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h365 X2 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X1) X0 X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X0]
    conv => enter [1]; rw [l2 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

theorem Equation313_325_implies_Equation41 (G : Type*) [Magma G] (h313 : Equation313 G) (h325 : Equation325 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h325 X1 X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l0 X0 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [← h313 X2 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h325 X0 X1]
    conv => enter [1]; rw [l1 X0 (X1 ◇ X0) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1]; rw [l2 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

theorem Equation365_378_implies_Equation371 (G : Type*) [Magma G] (h365 : Equation365 G) (h378 : Equation378 G) : Equation371 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X1]
    conv => enter [1]; rw [h378 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h378 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1]
  intro x y z
  conv => enter [1]; rw [l3 x z]
  conv => enter [1]; rw [h365 z y]

theorem Equation313_323_implies_Equation319 (G : Type*) [Magma G] (h313 : Equation313 G) (h323 : Equation323 G) : Equation319 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X1]
    conv => enter [1]; rw [h323 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h323 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1]
  intro x y z
  conv => enter [1]; rw [l3 x z]
  conv => enter [1]; rw [h313 z y]

theorem Equation365_377_implies_Equation41 (G : Type*) [Magma G] (h365 : Equation365 G) (h377 : Equation377 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [← h365 X1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h365 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 (X2 ◇ X1) X2]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

theorem Equation313_333_implies_Equation41 (G : Type*) [Magma G] (h313 : Equation313 G) (h333 : Equation333 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [← h313 X1 X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [l0 X2 (X1 ◇ X2)]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

theorem Equation365_375_implies_Equation313 (G : Type*) [Magma G] (h365 : Equation365 G) (h375 : Equation375 G) : Equation313 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation365_375_implies_Equation326 (G : Type*) [Magma G] (h365 : Equation365 G) (h375 : Equation375 G) : Equation326 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h375 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h365 (X0 ◇ X1) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h375 X1 (X0 ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l6 X1 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation313_326_implies_Equation365 (G : Type*) [Magma G] (h313 : Equation313 G) (h326 : Equation326 G) : Equation365 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation313_326_implies_Equation375 (G : Type*) [Magma G] (h313 : Equation313 G) (h326 : Equation326 G) : Equation375 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h326 (X0 ◇ X1) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h313 (X1 ◇ X0) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h326 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation365_367_implies_Equation371 (G : Type*) [Magma G] (h365 : Equation365 G) (h367 : Equation367 G) : Equation371 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h367 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h365 X1 X2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation310_313_implies_Equation319 (G : Type*) [Magma G] (h310 : Equation310 G) (h313 : Equation313 G) : Equation319 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h310 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h313 X1 X2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation364_378_implies_Equation39 (G : Type*) [Magma G] (h364 : Equation364 G) (h378 : Equation378 G) : Equation39 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X1]
    conv => enter [1]; rw [← h364 X1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  intro x y
  conv => enter [1]; rw [l1 x x y]

theorem Equation308_323_implies_Equation38 (G : Type*) [Magma G] (h308 : Equation308 G) (h323 : Equation323 G) : Equation38 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [← h308 X1 X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l0 X1 X2]
  intro x y
  conv => enter [1]; rw [l1 x x y]

theorem Equation364_377_implies_Equation41 (G : Type*) [Magma G] (h364 : Equation364 G) (h377 : Equation377 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h364 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h377 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h377 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l1 X0 X2]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h364 X1 X0]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X0 X2]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X0 X1]
    conv => enter [1]; rw [← l5 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation308_333_implies_Equation41 (G : Type*) [Magma G] (h308 : Equation308 G) (h333 : Equation333 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h308 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h333 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h333 X1 X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l1 X0 X2]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h308 X1 X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0) X2]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l2 X2 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X0 X1]
    conv => enter [1]; rw [← l5 X2 X1 X0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation362_385_implies_Equation319 (G : Type*) [Magma G] (h362 : Equation362 G) (h385 : Equation385 G) : Equation319 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h362 (X1 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h362 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h362 X0 X1]
    conv => enter [1, 2]; rw [← h362 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← l0 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [h385 X1 X1]
    conv => enter [1, 1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l2 X1 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l8 X1 X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l6 X1 X2]
  intro x y z
  conv => enter [1]; rw [← l10 x z x]
  conv => enter [1]; rw [l9 x z y]

theorem Equation315_325_implies_Equation371 (G : Type*) [Magma G] (h315 : Equation315 G) (h325 : Equation325 G) : Equation371 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h325 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h315 (X0 ◇ X1) X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h315 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h315 X0 X1]
    conv => enter [1, 1]; rw [← h315 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← l0 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [h325 X1 X1]
    conv => enter [1, 2]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l2 X1 X0]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l8 X1 X2]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l6 X1 X2]
  intro x y z
  conv => enter [1]; rw [← l10 x z x]
  conv => enter [1]; rw [l9 x z y]

theorem Equation362_378_implies_Equation374 (G : Type*) [Magma G] (h362 : Equation362 G) (h378 : Equation378 G) : Equation374 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h378 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [h362 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y x]

theorem Equation315_323_implies_Equation336 (G : Type*) [Magma G] (h315 : Equation315 G) (h323 : Equation323 G) : Equation336 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h323 X1 X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [h315 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y y]

theorem Equation362_377_implies_Equation308 (G : Type*) [Magma G] (h362 : Equation362 G) (h377 : Equation377 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [h377 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h377 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 X1]
    conv => enter [1]; rw [h377 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← h362 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l3 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation362_377_implies_Equation375 (G : Type*) [Magma G] (h362 : Equation362 G) (h377 : Equation377 G) : Equation375 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [h377 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h377 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation315_333_implies_Equation364 (G : Type*) [Magma G] (h315 : Equation315 G) (h333 : Equation333 G) : Equation364 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [h333 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h333 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 X1]
    conv => enter [1]; rw [h333 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h315 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l3 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation315_333_implies_Equation326 (G : Type*) [Magma G] (h315 : Equation315 G) (h333 : Equation333 G) : Equation326 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [h333 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h333 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation362_375_implies_Equation307 (G : Type*) [Magma G] (h362 : Equation362 G) (h375 : Equation375 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1]; rw [h362 sK0 sK0]
    conv => enter [1]; rw [← h362 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h362 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← h375 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l2 x]

theorem Equation315_326_implies_Equation359 (G : Type*) [Magma G] (h315 : Equation315 G) (h326 : Equation326 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← h326 (sK0 ◇ sK0) sK0]
  intro x
  conv => enter [1]; rw [l2 x]

theorem Equation362_364_implies_Equation372 (G : Type*) [Magma G] (h362 : Equation362 G) (h364 : Equation364 G) : Equation372 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h364 X1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x z]
  conv => enter [1]; rw [h364 z y]

theorem Equation308_315_implies_Equation317 (G : Type*) [Magma G] (h308 : Equation308 G) (h315 : Equation315 G) : Equation317 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h308 X1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h308 y z]

theorem Equation361_385_implies_Equation39 (G : Type*) [Magma G] (h361 : Equation361 G) (h385 : Equation385 G) : Equation39 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h361 X1 X0]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation309_325_implies_Equation38 (G : Type*) [Magma G] (h309 : Equation309 G) (h325 : Equation325 G) : Equation38 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h309 X1 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation361_377_implies_Equation374 (G : Type*) [Magma G] (h361 : Equation361 G) (h377 : Equation377 G) : Equation374 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X1]
    conv => enter [1]; rw [← h377 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [h377 x x]

theorem Equation309_333_implies_Equation336 (G : Type*) [Magma G] (h309 : Equation309 G) (h333 : Equation333 G) : Equation336 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h309 X0 X1]
    conv => enter [1]; rw [← h333 X1 X0]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [h333 y y]

theorem Equation361_365_implies_Equation371 (G : Type*) [Magma G] (h361 : Equation361 G) (h365 : Equation365 G) : Equation371 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X1]
    conv => enter [1]; rw [← h365 X1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x z]
  conv => enter [1]; rw [h365 z y]

theorem Equation309_313_implies_Equation319 (G : Type*) [Magma G] (h309 : Equation309 G) (h313 : Equation313 G) : Equation319 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h309 X0 X1]
    conv => enter [1]; rw [← h313 X1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x z]
  conv => enter [1]; rw [h313 z y]

theorem Equation361_362_implies_Equation360 (G : Type*) [Magma G] (h361 : Equation361 G) (h362 : Equation362 G) : Equation360 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h361 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation309_315_implies_Equation312 (G : Type*) [Magma G] (h309 : Equation309 G) (h315 : Equation315 G) : Equation312 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h309 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h309 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation360_385_implies_Equation316 (G : Type*) [Magma G] (h360 : Equation360 G) (h385 : Equation385 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h360 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [l1 y y]

theorem Equation312_325_implies_Equation368 (G : Type*) [Magma G] (h312 : Equation312 G) (h325 : Equation325 G) : Equation368 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h312 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [l1 y y]

theorem Equation360_377_implies_Equation379 (G : Type*) [Magma G] (h360 : Equation360 G) (h377 : Equation377 G) : Equation379 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [h377 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h377 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h360 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation312_333_implies_Equation343 (G : Type*) [Magma G] (h312 : Equation312 G) (h333 : Equation333 G) : Equation343 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [h333 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h333 X1 X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [h312 (X1 ◇ X0) X2]
    conv => enter [1, 2]; rw [← l0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation360_375_implies_Equation374 (G : Type*) [Magma G] (h360 : Equation360 G) (h375 : Equation375 G) : Equation374 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 X1]
    conv => enter [1]; rw [← h375 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [h360 x x]

theorem Equation312_326_implies_Equation336 (G : Type*) [Magma G] (h312 : Equation312 G) (h326 : Equation326 G) : Equation336 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 X1]
    conv => enter [1]; rw [← h326 X1 X0]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [h312 y y]

theorem Equation360_367_implies_Equation368 (G : Type*) [Magma G] (h360 : Equation360 G) (h367 : Equation367 G) : Equation368 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 X1]
    conv => enter [1]; rw [← h367 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h367 y y]

theorem Equation310_312_implies_Equation316 (G : Type*) [Magma G] (h310 : Equation310 G) (h312 : Equation312 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 X1]
    conv => enter [1]; rw [← h310 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h310 y y]

theorem Equation360_364_implies_Equation372 (G : Type*) [Magma G] (h360 : Equation360 G) (h364 : Equation364 G) : Equation372 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h360 X0 X1]
    conv => enter [1]; rw [← h364 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x z]
  conv => enter [1]; rw [h364 z y]

theorem Equation308_312_implies_Equation317 (G : Type*) [Magma G] (h308 : Equation308 G) (h312 : Equation312 G) : Equation317 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h312 X0 X1]
    conv => enter [1]; rw [← h308 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [h308 y z]

theorem Equation384_385_implies_Equation335 (G : Type*) [Magma G] (h384 : Equation384 G) (h385 : Equation385 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l1 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [← l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation384_385_implies_Equation43 (G : Type*) [Magma G] (h384 : Equation384 G) (h385 : Equation385 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l1 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← l6 X1 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation384_385_implies_Equation325 (G : Type*) [Magma G] (h384 : Equation384 G) (h385 : Equation385 G) : Equation325 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l1 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l7 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation384_385_implies_Equation333 (G : Type*) [Magma G] (h384 : Equation384 G) (h385 : Equation385 G) : Equation333 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation325_335_implies_Equation384 (G : Type*) [Magma G] (h325 : Equation325 G) (h335 : Equation335 G) : Equation384 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h325 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l1 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X1]
    conv => enter [1]; rw [← l7 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation325_335_implies_Equation43 (G : Type*) [Magma G] (h325 : Equation325 G) (h335 : Equation335 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h325 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l1 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation325_335_implies_Equation385 (G : Type*) [Magma G] (h325 : Equation325 G) (h335 : Equation335 G) : Equation385 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h325 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l1 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l7 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation378_384_implies_Equation335 (G : Type*) [Magma G] (h378 : Equation378 G) (h384 : Equation384 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1, 1]; rw [h378 X1 X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h378 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [l2 y x]

theorem Equation378_384_implies_Equation43 (G : Type*) [Magma G] (h378 : Equation378 G) (h384 : Equation384 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h378 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation378_384_implies_Equation325 (G : Type*) [Magma G] (h378 : Equation378 G) (h384 : Equation384 G) : Equation325 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h378 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation323_335_implies_Equation384 (G : Type*) [Magma G] (h323 : Equation323 G) (h335 : Equation335 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1, 2]; rw [h323 X0 X1]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h323 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l1 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [l2 y x]

theorem Equation323_335_implies_Equation43 (G : Type*) [Magma G] (h323 : Equation323 G) (h335 : Equation335 G) : Equation43 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h323 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation323_335_implies_Equation325 (G : Type*) [Magma G] (h323 : Equation323 G) (h335 : Equation335 G) : Equation325 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h323 X1 X0]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [l0 x y]

theorem Equation377_384_implies_Equation335 (G : Type*) [Magma G] (h377 : Equation377 G) (h384 : Equation384 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h377 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [h377 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← l6 X1 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]
  conv => enter [1]; rw [l4 y x]

theorem Equation377_384_implies_Equation43 (G : Type*) [Magma G] (h377 : Equation377 G) (h384 : Equation384 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [h377 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation377_384_implies_Equation325 (G : Type*) [Magma G] (h377 : Equation377 G) (h384 : Equation384 G) : Equation325 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation333_335_implies_Equation384 (G : Type*) [Magma G] (h333 : Equation333 G) (h335 : Equation335 G) : Equation384 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h333 X1 X0]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [h333 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l3 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [← l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]
  conv => enter [1]; rw [l4 y x]

theorem Equation333_335_implies_Equation43 (G : Type*) [Magma G] (h333 : Equation333 G) (h335 : Equation335 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [h333 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation333_335_implies_Equation325 (G : Type*) [Magma G] (h333 : Equation333 G) (h335 : Equation335 G) : Equation325 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [h333 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]
  conv => enter [1]; rw [h333 y x]

theorem Equation375_384_implies_Equation326 (G : Type*) [Magma G] (h375 : Equation375 G) (h384 : Equation384 G) : Equation326 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h375 X0 X1]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation326_335_implies_Equation375 (G : Type*) [Magma G] (h326 : Equation326 G) (h335 : Equation335 G) : Equation375 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h326 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation307_367_385_implies_Equation312 (G : Type*) [Magma G] (h307 : Equation307 G) (h367 : Equation367 G) (h385 : Equation385 G) : Equation312 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h367 X1 X0]
    conv => enter [1]; rw [h367 X1 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h385 X0 (X1 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h307 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X1 ((X1 ◇ X1) ◇ (X1 ◇ X1)) X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 (X1 ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [l1 X1 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h307 X1]
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [← h307 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation310_325_359_implies_Equation360 (G : Type*) [Magma G] (h310 : Equation310 G) (h325 : Equation325 G) (h359 : Equation359 G) : Equation360 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← h310 X1 X0]
    conv => enter [1]; rw [h310 X1 X2]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h325 (X1 ◇ X1) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h359 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 ((X1 ◇ X1) ◇ (X1 ◇ X1)) X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X1) X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [l1 X1 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h359 X1]
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← h359 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation365_384_implies_Equation335 (G : Type*) [Magma G] (h365 : Equation365 G) (h384 : Equation384 G) : Equation335 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l5 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X2 X0 X1]
    conv => enter [1]; rw [l3 X2 (X0 ◇ X1)]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h365 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h365 (X0 ◇ X1) X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← l9 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ X1) (X1 ◇ X0)]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l14 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1]; rw [← l17 X1 X0]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 1]; rw [← l16 X1 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [← l16 X0 (X1 ◇ X1)]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1]; rw [← l21 X0 X1]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← l22 (X0 ◇ (X1 ◇ X1)) X1]
  have l24 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l22 X0 X1]
    conv => enter [1]; rw [← l23 X1 X0]
  have l25 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [l24 X0 X1]
  have l26 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l26 x y]

theorem Equation365_384_implies_Equation313 (G : Type*) [Magma G] (h365 : Equation365 G) (h384 : Equation384 G) : Equation313 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation365_384_implies_Equation326 (G : Type*) [Magma G] (h365 : Equation365 G) (h384 : Equation384 G) : Equation326 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l5 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X2 X0 X1]
    conv => enter [1]; rw [l3 X2 (X0 ◇ X1)]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h365 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h365 (X0 ◇ X1) X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← l9 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ X1) (X1 ◇ X0)]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l14 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1]; rw [← l17 X1 X0]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 1]; rw [← l16 X1 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [← l16 X0 (X1 ◇ X1)]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1]; rw [← l21 X0 X1]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation313_335_implies_Equation384 (G : Type*) [Magma G] (h313 : Equation313 G) (h335 : Equation335 G) : Equation384 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X2 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l5 X2 X1 X0]
    conv => enter [1]; rw [l3 X2 (X1 ◇ X0)]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h313 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l7 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h313 (X1 ◇ X0) X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l9 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l14 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 (X1 ◇ X0) (X0 ◇ X1)]
  have l15 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l9 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l4 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [l15 X1 X0]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← l14 X1 X0]
  have l18 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l13 X1 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← l17 X0 X1]
  have l20 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1, 2]; rw [← l16 X0 X1]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1]; rw [← l16 (X1 ◇ X1) X0]
  have l22 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1]; rw [← l21 X1 X0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l22 X1 ((X1 ◇ X1) ◇ X0)]
  have l24 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l22 X1 X0]
    conv => enter [1]; rw [← l23 X0 X1]
  have l25 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [l24 X1 X0]
  have l26 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l26 x y]

theorem Equation313_335_implies_Equation365 (G : Type*) [Magma G] (h313 : Equation313 G) (h335 : Equation335 G) : Equation365 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation364_384_implies_Equation41 (G : Type*) [Magma G] (h364 : Equation364 G) (h384 : Equation384 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h364 X0 X1]
    conv => enter [1]; rw [← h384 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l0 X0 X2]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h364 X1 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X1) X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X1 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l1 (X1 ◇ X1) X0 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0]
    conv => enter [1]; rw [← l3 X1 X1 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l1 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation308_335_implies_Equation41 (G : Type*) [Magma G] (h308 : Equation308 G) (h335 : Equation335 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h308 X0 X1]
    conv => enter [1]; rw [← h335 X1 X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l0 X0 X2]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X1 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h308 X1 X0]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X0) X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ (X1 ◇ X1)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 (X1 ◇ X1) X2]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0 X1]
    conv => enter [1]; rw [← l3 X1 X1 X1]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation362_384_implies_Equation41 (G : Type*) [Magma G] (h362 : Equation362 G) (h384 : Equation384 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h362 X1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X1 ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h362 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 (X1 ◇ X2) X2]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

theorem Equation315_335_implies_Equation41 (G : Type*) [Magma G] (h315 : Equation315 G) (h335 : Equation335 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h315 X1 X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ (X2 ◇ X1)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [h315 X1 X2]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [l0 X2 (X2 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

theorem Equation361_384_implies_Equation41 (G : Type*) [Magma G] (h361 : Equation361 G) (h384 : Equation384 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h361 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h361 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l4 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l5 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l12 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l10 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l7 X0 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← l4 (X0 ◇ X0) X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X0]
    conv => enter [1]; rw [← l14 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l7 X0 X1]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← l12 X0 X1 X2]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [← l17 X1 X0 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l18 x y]
  conv => enter [1]; rw [l16 y z]

theorem Equation309_335_implies_Equation41 (G : Type*) [Magma G] (h309 : Equation309 G) (h335 : Equation335 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h309 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h309 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h309 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h309 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l12 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l7 X2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l10 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l7 X0 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [← l4 (X0 ◇ X0) X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X0]
    conv => enter [1]; rw [← l14 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l7 X1 X0]
  have l17 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 X0 ((X1 ◇ X0) ◇ X2)]
    conv => enter [1]; rw [← l12 X2 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [← l17 X1 (X1 ◇ X0) X0]
  intro x y z
  conv => enter [1]; rw [l18 x z]
  conv => enter [1]; rw [l16 z y]

theorem Equation307_360_384_implies_Equation316 (G : Type*) [Magma G] (h307 : Equation307 G) (h360 : Equation360 G) (h384 : Equation384 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h360 X0 X1]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h307 y]

theorem Equation360_384_implies_Equation368 (G : Type*) [Magma G] (h360 : Equation360 G) (h384 : Equation384 G) : Equation368 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h360 X0 X1]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h384 y y]

theorem Equation312_335_implies_Equation316 (G : Type*) [Magma G] (h312 : Equation312 G) (h335 : Equation335 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h312 X0 X1]
    conv => enter [1]; rw [← h335 (X0 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h335 y y]

theorem Equation335_385_implies_Equation384 (G : Type*) [Magma G] (h335 : Equation335 G) (h385 : Equation385 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h385 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h335 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h385 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]
  conv => enter [1]; rw [l5 y x]

theorem Equation325_384_implies_Equation335 (G : Type*) [Magma G] (h325 : Equation325 G) (h384 : Equation384 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h384 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h325 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← h325 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]
  conv => enter [1]; rw [l5 y x]

theorem Equation335_378_implies_Equation384 (G : Type*) [Magma G] (h335 : Equation335 G) (h378 : Equation378 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [h378 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h335 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h378 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) (X0 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l9 X1 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]
  conv => enter [1]; rw [h378 y x]

theorem Equation323_384_implies_Equation335 (G : Type*) [Magma G] (h323 : Equation323 G) (h384 : Equation384 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [h323 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h384 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h323 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h384 (X1 ◇ X0) (X0 ◇ X1)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l3 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [← l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]
  conv => enter [1]; rw [h323 y x]

theorem Equation335_377_implies_Equation384 (G : Type*) [Magma G] (h335 : Equation335 G) (h377 : Equation377 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h377 X1 X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [h377 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h335 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [h377 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h377 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l5 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [l6 x (y ◇ x)]

theorem Equation333_384_implies_Equation335 (G : Type*) [Magma G] (h333 : Equation333 G) (h384 : Equation384 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h333 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [h333 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h384 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [h333 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h333 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [l6 (y ◇ x) y]

theorem Equation335_375_implies_Equation326 (G : Type*) [Magma G] (h335 : Equation335 G) (h375 : Equation375 G) : Equation326 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h375 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation326_384_implies_Equation375 (G : Type*) [Magma G] (h326 : Equation326 G) (h384 : Equation384 G) : Equation375 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h326 (X1 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h326 X1 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation335_365_implies_Equation384 (G : Type*) [Magma G] (h335 : Equation335 G) (h365 : Equation365 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h335 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h365 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h335 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h365 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← l9 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l12 x y]
  conv => enter [1]; rw [← l6 y x]

theorem Equation313_384_implies_Equation335 (G : Type*) [Magma G] (h313 : Equation313 G) (h384 : Equation384 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h384 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h313 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h384 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← h313 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l5 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← l9 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  intro x y
  conv => enter [1]; rw [l12 x y]
  conv => enter [1]; rw [← l6 y x]

theorem Equation335_364_implies_Equation41 (G : Type*) [Magma G] (h335 : Equation335 G) (h364 : Equation364 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h364 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h335 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h364 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l2 X0 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h364 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← h335 X0 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← l2 X0 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h364 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l11 X0 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X0 X0]
    conv => enter [1]; rw [← l12 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [l14 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l15 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X0]
    conv => enter [1]; rw [l16 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l5 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l2 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l5 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1, 2]; rw [← h364 (X0 ◇ X1) X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [← l17 X0 X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1, 1]; rw [← l6 X1 X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ X0) (X1 ◇ X0)]
  have l25 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
  have l26 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l24 X0 X1]
  have l27 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [h335 (X1 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l28 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l2 (X1 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l29 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = ((X2 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 (X1 ◇ X0) X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l30 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X2 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l26 (X1 ◇ X0) X2]
    conv => enter [1]; rw [l29 X1 X0 X2]
  have l31 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 X0]
    conv => enter [1]; rw [← l28 X0 X1]
  have l32 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 X0]
    conv => enter [1]; rw [← l27 X0 X1]
  have l33 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l31 X1 X0]
    conv => enter [1]; rw [← l30 X1 X0 (X0 ◇ X1)]
  have l34 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l26 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l26 X0 X1]
  have l35 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l34 X1 X0]
  have l36 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l33 X1 X0]
    conv => enter [1]; rw [← l35 X0 X1]
  have l37 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l36 X0 X1]
    conv => enter [1]; rw [← l26 X1 X0]
  have l38 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l37 X0 X1]
    conv => enter [1]; rw [← l37 X2 X1]
  have l39 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1, 2]; rw [l37 X1 X0]
  have l40 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l37 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l1 X1 X2]
  have l41 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l32 X1 X2]
    conv => enter [1]; rw [← l40 X0 X1 X2]
  have l42 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l39 X0 X1]
    conv => enter [1]; rw [l38 X1 (X0 ◇ X0) X2]
  have l43 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l41 X0 X0 X0]
    conv => enter [1]; rw [← l42 X0 X1 X0]
  have l44 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l43 X0 X2]
    conv => enter [1]; rw [l38 X0 X2 X1]
  intro x y z
  conv => enter [1]; rw [l44 x y z]

theorem Equation308_384_implies_Equation41 (G : Type*) [Magma G] (h308 : Equation308 G) (h384 : Equation384 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h308 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h384 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h308 X0 X1]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l2 X0 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h308 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 1]; rw [← h384 X0 X0]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 1]; rw [← l2 X0 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h308 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l11 X0 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X0]
    conv => enter [1]; rw [← l12 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [l14 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l15 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X0]
    conv => enter [1]; rw [l16 X0 X1]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l2 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l5 ((X1 ◇ X0) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l5 X1 X0]
  have l21 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1, 1]; rw [← h308 (X1 ◇ X0) X1]
  have l22 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 1]; rw [← l17 X0 X1]
  have l23 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1, 2]; rw [← l6 X1 X0]
  have l24 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ X0) (X0 ◇ X1)]
  have l25 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l23 X1 X0]
    conv => enter [1]; rw [← l2 (X1 ◇ X0) (X0 ◇ X1)]
  have l26 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l24 X0 X1]
  have l27 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [h384 (X0 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l28 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l29 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l30 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l26 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l29 X0 X1 X2]
  have l31 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1]; rw [← l28 X0 X1]
  have l32 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1]; rw [← l27 X0 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l31 X0 X1]
    conv => enter [1]; rw [← l30 X0 X1 (X1 ◇ X0)]
  have l34 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l26 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l26 X0 X1]
  have l35 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l34 X0 X1]
  have l36 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l33 X0 X1]
    conv => enter [1]; rw [← l35 X0 X1]
  have l37 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l36 X1 X0]
    conv => enter [1]; rw [← l26 X1 X0]
  have l38 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1]; rw [← l37 X1 X2]
  have l39 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1, 1]; rw [l37 X0 X1]
  have l40 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ (X1 ◇ X2)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l37 (X2 ◇ X1) X0]
    conv => enter [1]; rw [l1 X2 X1]
  have l41 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = ((X2 ◇ X1) ◇ X0) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l32 X2 X1]
    conv => enter [1]; rw [← l40 X2 X1 X0]
  have l42 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l39 X1 X0]
    conv => enter [1]; rw [l38 (X0 ◇ X0) X1 X2]
  have l43 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l41 X0 X0 X0]
    conv => enter [1]; rw [← l42 X1 X0 X0]
  have l44 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l43 X0 X2]
    conv => enter [1]; rw [l38 X2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l44 x y z]

theorem Equation335_362_implies_Equation326 (G : Type*) [Magma G] (h335 : Equation335 G) (h362 : Equation362 G) : Equation326 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h335 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h362 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h335 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [h362 (X0 ◇ X0) X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 1]; rw [← h335 X1 X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X0 ◇ X0) ◇ X1) X1]
    conv => enter [1, 1]; rw [← l9 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← h335 X1 (X0 ◇ X0)]
  have l14 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l5 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [← h362 X1 (X0 ◇ X1)]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 1]; rw [← l7 X0 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1]; rw [l14 X1 X0]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation315_384_implies_Equation326 (G : Type*) [Magma G] (h315 : Equation315 G) (h384 : Equation384 G) : Equation326 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h384 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h315 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h384 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l5 ((X1 ◇ X0) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l5 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1, 1]; rw [← h315 X1 (X1 ◇ X0)]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 2]; rw [← l7 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← l10 X0 X1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation335_361_implies_Equation41 (G : Type*) [Magma G] (h335 : Equation335 G) (h361 : Equation361 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h361 X1 X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h361 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h335 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h361 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l5 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l4 X0 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← h361 (X0 ◇ X0) X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2]; rw [← l8 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X0]
    conv => enter [1]; rw [← l11 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l4 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1]; rw [← l13 X1 (X0 ◇ X0)]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [l16 X1 X0]
  intro x y z
  conv => enter [1]; rw [l17 x y]
  conv => enter [1]; rw [← l16 y z]

theorem Equation309_384_implies_Equation41 (G : Type*) [Magma G] (h309 : Equation309 G) (h384 : Equation384 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h309 X1 X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h384 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h309 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l4 X0 X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h309 (X0 ◇ X0) X1]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 1]; rw [← l8 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X0]
    conv => enter [1]; rw [← l11 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l12 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l4 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1]; rw [← l13 X1 (X0 ◇ X0)]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y z
  conv => enter [1]; rw [l17 x z]
  conv => enter [1]; rw [← l16 y z]

theorem Equation335_360_implies_Equation316 (G : Type*) [Magma G] (h335 : Equation335 G) (h360 : Equation360 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← h335 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l0 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [h335 y y]

theorem Equation312_384_implies_Equation316 (G : Type*) [Magma G] (h312 : Equation312 G) (h384 : Equation384 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h384 (X0 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l0 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [h312 y y]

theorem Equation333_377_implies_Equation323 (G : Type*) [Magma G] (h333 : Equation333 G) (h377 : Equation377 G) : Equation323 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [h333 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h377 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation333_377_implies_Equation378 (G : Type*) [Magma G] (h333 : Equation333 G) (h377 : Equation377 G) : Equation378 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h333 X0 X1]
    conv => enter [1]; rw [h377 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h333 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation333_367_implies_Equation370 (G : Type*) [Magma G] (h333 : Equation333 G) (h367 : Equation367 G) : Equation370 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h333 X0 X1]
    conv => enter [1]; rw [h333 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h333 X0 X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h367 X2 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation310_377_implies_Equation311 (G : Type*) [Magma G] (h310 : Equation310 G) (h377 : Equation377 G) : Equation311 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h377 X1 X0]
    conv => enter [1]; rw [h377 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h377 X1 X0]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h310 X2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation333_365_implies_Equation41 (G : Type*) [Magma G] (h333 : Equation333 G) (h365 : Equation365 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h333 X0 X1]
    conv => enter [1]; rw [h333 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h333 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X1]
    conv => enter [1]; rw [h333 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h365 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 ((X1 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l3 X2 X3 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l4 x x y z]

theorem Equation313_377_implies_Equation41 (G : Type*) [Magma G] (h313 : Equation313 G) (h377 : Equation377 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h377 X1 X0]
    conv => enter [1]; rw [h377 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h377 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X1]
    conv => enter [1]; rw [h377 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h313 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 (X0 ◇ (X1 ◇ X1))]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X2]
  have l4 : ∀ X1 X0 X3 X2 : G, (X1 ◇ X0) = (X3 ◇ X2) := by
    intro X1 X0 X3 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l3 X3 X2 (X1 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [l4 x x y z]

theorem Equation333_362_implies_Equation41 (G : Type*) [Magma G] (h333 : Equation333 G) (h362 : Equation362 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h333 X0 X1]
    conv => enter [1]; rw [h333 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h333 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 X1]
    conv => enter [1]; rw [h333 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h362 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 (X0 ◇ (X1 ◇ X1))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l3 X2 X3 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l4 x x y z]

theorem Equation315_377_implies_Equation41 (G : Type*) [Magma G] (h315 : Equation315 G) (h377 : Equation377 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h377 X1 X0]
    conv => enter [1]; rw [h377 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h377 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 X1]
    conv => enter [1]; rw [h377 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h315 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 ((X1 ◇ X1) ◇ X0)]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X2]
  have l4 : ∀ X1 X0 X3 X2 : G, (X1 ◇ X0) = (X3 ◇ X2) := by
    intro X1 X0 X3 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l3 X3 X2 (X1 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [l4 x x y z]

theorem Equation333_361_implies_Equation364 (G : Type*) [Magma G] (h333 : Equation333 G) (h361 : Equation361 G) : Equation364 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h361 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h333 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation309_377_implies_Equation308 (G : Type*) [Magma G] (h309 : Equation309 G) (h377 : Equation377 G) : Equation308 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h377 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation333_361_375_implies_Equation323 (G : Type*) [Magma G] (h333 : Equation333 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation323 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h333 X0 X1]
    conv => enter [1]; rw [h333 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h333 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation309_326_377_implies_Equation378 (G : Type*) [Magma G] (h309 : Equation309 G) (h326 : Equation326 G) (h377 : Equation377 G) : Equation378 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h377 X1 X0]
    conv => enter [1]; rw [h377 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h377 X1 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation333_360_implies_Equation41 (G : Type*) [Magma G] (h333 : Equation333 G) (h360 : Equation360 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h333 X0 X1]
    conv => enter [1]; rw [h333 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h333 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 X1]
    conv => enter [1]; rw [h333 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h360 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l3 X2 X3 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l4 x x y z]

theorem Equation312_377_implies_Equation41 (G : Type*) [Magma G] (h312 : Equation312 G) (h377 : Equation377 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h377 X1 X0]
    conv => enter [1]; rw [h377 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h377 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 X1]
    conv => enter [1]; rw [h377 X1 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h312 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X2]
  have l4 : ∀ X1 X0 X3 X2 : G, (X1 ◇ X0) = (X3 ◇ X2) := by
    intro X1 X0 X3 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l3 X3 X2 (X1 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [l4 x x y z]

theorem Equation326_385_implies_Equation375 (G : Type*) [Magma G] (h326 : Equation326 G) (h385 : Equation385 G) : Equation375 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h326 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation325_375_implies_Equation326 (G : Type*) [Magma G] (h325 : Equation325 G) (h375 : Equation375 G) : Equation326 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h375 X1 X0]
    conv => enter [1]; rw [← h325 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation326_360_362_implies_Equation327 (G : Type*) [Magma G] (h326 : Equation326 G) (h360 : Equation360 G) (h362 : Equation362 G) : Equation327 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h326 X1 (X0 ◇ X2)]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l2 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation326_360_362_implies_Equation361 (G : Type*) [Magma G] (h326 : Equation326 G) (h360 : Equation360 G) (h362 : Equation362 G) : Equation361 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h326 X1 (X0 ◇ X2)]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l2 X1 X0 X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l3 (X0 ◇ X1) X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation312_315_375_implies_Equation395 (G : Type*) [Magma G] (h312 : Equation312 G) (h315 : Equation315 G) (h375 : Equation375 G) : Equation395 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h375 (X2 ◇ X0) X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l2 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation312_315_375_implies_Equation309 (G : Type*) [Magma G] (h312 : Equation312 G) (h315 : Equation315 G) (h375 : Equation375 G) : Equation309 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h375 (X2 ◇ X0) X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l3 X0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation326_360_361_implies_Equation327 (G : Type*) [Magma G] (h326 : Equation326 G) (h360 : Equation360 G) (h361 : Equation361 G) : Equation327 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h326 X1 (X0 ◇ X2)]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l2 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation309_312_375_implies_Equation395 (G : Type*) [Magma G] (h309 : Equation309 G) (h312 : Equation312 G) (h375 : Equation375 G) : Equation395 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h375 (X2 ◇ X0) X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l2 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation325_385_implies_Equation335 (G : Type*) [Magma G] (h325 : Equation325 G) (h385 : Equation385 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h325 X1 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X0) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l8 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation325_367_implies_Equation316 (G : Type*) [Magma G] (h325 : Equation325 G) (h367 : Equation367 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h367 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l2 (X1 ◇ X1) X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l3 X1 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h367 X1 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h367 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l2 X1 X2]
  intro x y
  conv => enter [1]; rw [l9 x y y]

theorem Equation310_385_implies_Equation316 (G : Type*) [Magma G] (h310 : Equation310 G) (h385 : Equation385 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h310 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l2 (X1 ◇ X1) X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l3 X1 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h310 X1 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h310 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [h310 X1 X2]
  intro x y
  conv => enter [1]; rw [l9 x y y]

theorem Equation310_385_implies_Equation368 (G : Type*) [Magma G] (h310 : Equation310 G) (h385 : Equation385 G) : Equation368 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h310 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l2 (X1 ◇ X1) X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l3 X1 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h310 X1 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h310 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X2 ◇ X2) ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l2 X1 X2]
  intro x y
  conv => enter [1]; rw [l9 x y y]

end Order3
