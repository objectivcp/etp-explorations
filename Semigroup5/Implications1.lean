import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation38_implies_Equation4286 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4286 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation38_implies_Equation4318 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4318 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation3260 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3260 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation38_implies_Equation3265 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3265 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation38_implies_Equation3264 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3264 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation38_implies_Equation310 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation310 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation3259 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3259 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation38_implies_Equation4288 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4288 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation38_implies_Equation3261 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3261 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation38_implies_Equation4269 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (y ◇ x)]

@[equational_result]
theorem Equation38_implies_Equation308 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h38 x (x ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation3256 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3256 G := by
  intro x y
  conv => enter [1]; rw [h38 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation38_implies_Equation3255 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3255 G := by
  intro x y
  conv => enter [1]; rw [h38 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation38_implies_Equation3258 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3258 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation38_implies_Equation4358 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4358 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation4314 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4314 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation4270 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (y ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation4283 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4283 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation38_implies_Equation4284 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4284 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation38_implies_Equation4268 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (x ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation307 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h38 x (x ◇ x)]

@[equational_result]
theorem Equation38_implies_Equation3253 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h38 x (x ◇ (x ◇ x))]

theorem Equation39_4512_implies_Equation3388 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3388 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK2]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l1 sK2 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 X0 sK2]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation39_4512_implies_Equation318 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation318 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 (sK2 ◇ sK0) sK1]
    conv => enter [1, 1]; rw [← h39 sK0 sK2]
    conv => enter [1, 2]; rw [← h39 sK0 sK2]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation39_4512_implies_Equation329 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation329 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK2]
    conv => enter [1]; rw [h39 sK1 X0]
  have l1 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l0 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0 sK2]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation39_4512_implies_Equation343 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation39_4512_implies_Equation3334 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3334 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK2]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [l1 sK2 sK1 sK0]
    conv => enter [1]; rw [l0 sK2 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 X0 sK2]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l7 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation39_4512_implies_Equation3414 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3414 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h39 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]
  conv => enter [1]; rw [l4 z x y z]

@[equational_result]
theorem Equation39_implies_Equation4278 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4278 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 (sK2 ◇ sK0) sK1]
    conv => enter [1, 1]; rw [← h39 sK0 sK2]
    conv => enter [1, 2]; rw [← h39 sK0 sK2]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) X0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x x]

theorem Equation39_4512_implies_Equation3322 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3322 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation39_4512_implies_Equation3326 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3326 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l4 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X0 sK2]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]
  conv => enter [1]; rw [l4 z x y x]

theorem Equation39_4512_implies_Equation3346 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3346 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation39_4512_implies_Equation333 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation333 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation39_implies_Equation4300 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4300 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation39_implies_Equation4360 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4360 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 sK0]
  intro x y z w
  conv => enter [1, 2]; rw [l0 y z w]

theorem Equation39_4512_implies_Equation3309 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3309 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h39 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1, 2]; rw [h39 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation39_4512_implies_Equation3353 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3353 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 X0]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation39_4512_implies_Equation323 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation323 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation39_4512_implies_Equation326 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation326 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation39_4512_implies_Equation3300 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3300 G := by
  have l0 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ sK1) sK3]
    conv => enter [1, 1]; rw [← h39 sK1 sK0]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l1 : ∀ sK3 sK0 sK1 X0 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l0 sK3 sK0 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h39 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0 sK1]
  have l4 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK3 sK0 sK1]
  have l5 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h39 (sK3 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 1]; rw [← l4 sK1 sK3 sK0]
    conv => enter [1, 2]; rw [← l4 sK1 sK3 sK0]
  have l6 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK3 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK2 sK3 sK0 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK3 sK0]
    conv => enter [1]; rw [l6 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

theorem Equation39_4512_implies_Equation3316 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3316 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]
  conv => enter [1]; rw [l4 y x x]

theorem Equation39_4512_implies_Equation309 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation309 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation39_4512_implies_Equation3306 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3306 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0 sK0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]
  conv => enter [1]; rw [l5 x y]

theorem Equation39_4512_implies_Equation3319 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3319 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation39_implies_Equation4296 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4296 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation39_implies_Equation4327 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4327 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ sK0) sK2]
    conv => enter [1, 1]; rw [h39 sK0 sK1]
    conv => enter [1, 2]; rw [h39 sK0 sK1]
  have l1 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l0 sK2 sK0 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK0) X0]
  intro x y z
  conv => enter [1]; rw [← l1 z x x y]

theorem Equation39_4512_implies_Equation3274 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3274 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [← h39 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [h39 sK0 sK2]
  have l5 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← l4 sK0 sK2]
    conv => enter [1, 2]; rw [← l4 sK0 sK2]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [l6 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation39_4512_implies_Equation3292 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3292 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ sK0) sK2]
    conv => enter [1, 1]; rw [← h39 sK0 sK1]
    conv => enter [1, 2]; rw [← h39 sK0 sK1]
  have l1 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK2 sK1 sK0]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK2 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK2 sK1]
    conv => enter [1]; rw [l5 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation39_4512_implies_Equation3264 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3264 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 (sK2 ◇ sK0) sK1]
    conv => enter [1, 1]; rw [← h39 sK0 sK2]
    conv => enter [1, 2]; rw [← h39 sK0 sK2]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK1 sK2 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation39_4512_implies_Equation315 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [h39 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation39_4512_implies_Equation3271 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3271 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [h39 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation39_implies_Equation4304 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4304 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ sK1) sK2]
    conv => enter [1, 1]; rw [h39 sK1 sK0]
    conv => enter [1, 2]; rw [h39 sK1 sK0]
  have l1 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) X0]
  intro x y z
  conv => enter [1]; rw [← l1 z y x x]

theorem Equation39_4512_implies_Equation3261 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3261 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h39 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation39_implies_Equation4269 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4269 G := by
  intro x y
  conv => enter [1, 2]; rw [h39 x y]

theorem Equation39_4512_implies_Equation312 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation39_4512_implies_Equation3278 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3278 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l0 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0 sK1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]
  conv => enter [1]; rw [l3 y x y]

theorem Equation39_4512_implies_Equation3255 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3255 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation39_4512_implies_Equation3258 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3258 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l0 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0 sK1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]
  conv => enter [1]; rw [l3 y x x]

@[equational_result]
theorem Equation39_implies_Equation4362 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4362 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation39_implies_Equation4291 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4291 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation39_implies_Equation4275 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4275 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [h39 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation39_implies_Equation4284 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4284 G := by
  intro x y
  conv => enter [1, 2]; rw [← h39 y x]

@[equational_result]
theorem Equation39_implies_Equation4320 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4320 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h39 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation39_implies_Equation4272 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4272 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation307 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation307 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

theorem Equation39_4512_implies_Equation3253 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3253 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1, 2]; rw [l3 sK0]
  intro x
  conv => enter [1]; rw [l4 x]

@[equational_result]
theorem Equation40_implies_Equation4270 (G : Type*) [Magma G] (h40 : Equation40 G) : Equation4270 G := by
  intro x y
  conv => enter [1, 2]; rw [h40 x y]

theorem Equation40_4512_implies_Equation4275 (G : Type*) [Magma G] (h40 : Equation40 G) (h4512 : Equation4512 G) : Equation4275 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h40 X0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation41_implies_Equation3345 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3345 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation41_implies_Equation3370 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3370 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK2 ◇ sK0))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l0 z x y]

@[equational_result]
theorem Equation41_implies_Equation38 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation38 G := by
  intro x y
  conv => enter [1]; rw [h41 x x y]

@[equational_result]
theorem Equation41_implies_Equation39 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation39 G := by
  intro x y
  conv => enter [1]; rw [h41 x y x]

@[equational_result]
theorem Equation41_implies_Equation314 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation314 G := by
  intro x y z
  conv => enter [1]; rw [h41 x y (x ◇ z)]

@[equational_result]
theorem Equation41_implies_Equation3342 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3342 G := by
  intro x y
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x y (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation41_implies_Equation4274 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x (x ◇ x)]
  conv => enter [1]; rw [h41 x y (x ◇ z)]

@[equational_result]
theorem Equation41_implies_Equation313 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (x ◇ y)]

@[equational_result]
theorem Equation41_implies_Equation3304 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3304 G := by
  have l0 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41 sK2 sK1 sK0]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [h41 sK2 sK4 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK2 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [l0 z w u y]

@[equational_result]
theorem Equation41_implies_Equation43 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation41_implies_Equation4301 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4301 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation41_implies_Equation4331 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4331 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK0]
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [← h41 y y x]
  conv => enter [1]; rw [h41 y z (y ◇ y)]

@[equational_result]
theorem Equation41_implies_Equation4305 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4305 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation41_implies_Equation4325 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4325 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK2)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK0]
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [← h41 z y x]
  conv => enter [1]; rw [l0 z y]

@[equational_result]
theorem Equation41_implies_Equation3273 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3273 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation41_implies_Equation3290 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3290 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK0 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [h41 x z (x ◇ z)]
  conv => enter [1]; rw [l0 z x y]

@[equational_result]
theorem Equation41_implies_Equation3301 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3301 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ sK2))]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h41 sK1 sK0 sK2]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [h41 sK1 sK3 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [l0 z w y]

@[equational_result]
theorem Equation41_implies_Equation4364 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4364 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK0]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK0)]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK2)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]
  conv => enter [1]; rw [l2 y z x]
  conv => enter [1]; rw [l0 z x y]

@[equational_result]
theorem Equation41_implies_Equation4369 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4369 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]
  conv => enter [1]; rw [l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation316 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (y ◇ y)]

@[equational_result]
theorem Equation41_implies_Equation40 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation40 G := by
  intro x y
  conv => enter [1]; rw [h41 x y y]

@[equational_result]
theorem Equation41_implies_Equation4279 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4279 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x (x ◇ x)]
  conv => enter [1]; rw [h41 x y (z ◇ y)]

@[equational_result]
theorem Equation41_implies_Equation4273 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [← h41 x x (x ◇ x)]
  conv => enter [1]; rw [h41 x y (x ◇ y)]

@[equational_result]
theorem Equation41_implies_Equation4299 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4299 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x (x ◇ y)]
  conv => enter [1]; rw [h41 x z (x ◇ x)]

@[equational_result]
theorem Equation41_implies_Equation4297 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4297 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← h41 z x (x ◇ y)]
  conv => enter [1]; rw [l0 z y]

@[equational_result]
theorem Equation41_implies_Equation4277 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4277 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x (x ◇ x)]
  conv => enter [1]; rw [h41 x y (y ◇ z)]

@[equational_result]
theorem Equation41_implies_Equation4280 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4280 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x (x ◇ x)]
  conv => enter [1]; rw [h41 x y (z ◇ z)]

@[equational_result]
theorem Equation41_implies_Equation4290 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [← h41 x x (x ◇ y)]
  conv => enter [1]; rw [h41 x y (x ◇ x)]

@[equational_result]
theorem Equation41_implies_Equation4321 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4321 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation41_implies_Equation4293 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4293 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation41_implies_Equation4343 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4343 G := by
  intro x y
  conv => enter [1]; rw [← h41 y x (y ◇ y)]
  conv => enter [1]; rw [h41 y y (x ◇ x)]

@[equational_result]
theorem Equation41_implies_Equation4276 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4276 G := by
  intro x y
  conv => enter [1]; rw [← h41 x x (x ◇ x)]
  conv => enter [1]; rw [h41 x y (y ◇ y)]

@[equational_result]
theorem Equation43_implies_Equation4358 (G : Type*) [Magma G] (h43 : Equation43 G) : Equation4358 G := by
  intro x y z
  conv => enter [1, 2]; rw [h43 y z]

@[equational_result]
theorem Equation43_implies_Equation4283 (G : Type*) [Magma G] (h43 : Equation43 G) : Equation4283 G := by
  intro x y
  conv => enter [1, 2]; rw [h43 x y]

theorem Equation43_4512_implies_Equation4362 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) : Equation4362 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (sK0 ◇ (X0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK2) sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation43_4512_implies_Equation4320 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) : Equation4320 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation10_4512_implies_Equation47 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation47 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  intro x
  conv => enter [1]; rw [← l2 x]
  conv => enter [1, 2]; rw [h10 x x]

@[equational_result]
theorem Equation56_implies_Equation47 (G : Type*) [Magma G] (h56 : Equation56 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h56 x x]

@[equational_result]
theorem Equation75_implies_Equation47 (G : Type*) [Magma G] (h75 : Equation75 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h75 x x]

@[equational_result]
theorem Equation66_implies_Equation47 (G : Type*) [Magma G] (h66 : Equation66 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h66 x x]

@[equational_result]
theorem Equation307_implies_Equation3253 (G : Type*) [Magma G] (h307 : Equation307 G) : Equation3253 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation308_implies_Equation3256 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation3256 G := by
  intro x y
  conv => enter [1]; rw [h308 x (y ◇ y)]

@[equational_result]
theorem Equation308_implies_Equation3255 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation3255 G := by
  intro x y
  conv => enter [1]; rw [h308 x (y ◇ x)]

@[equational_result]
theorem Equation308_implies_Equation4268 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [← h308 x x]
  conv => enter [1]; rw [h308 x y]

@[equational_result]
theorem Equation308_implies_Equation307 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h308 x x]

@[equational_result]
theorem Equation312_implies_Equation3278 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation3278 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [h312 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation312_implies_Equation3258 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation3258 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h312 sK0 sK0]
    conv => enter [1, 2]; rw [h312 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation312_implies_Equation4272 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [← h312 x x]
  conv => enter [1]; rw [h312 x y]

@[equational_result]
theorem Equation312_implies_Equation307 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h312 x x]

@[equational_result]
theorem Equation309_implies_Equation4269 (G : Type*) [Magma G] (h309 : Equation309 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [← h309 x x]
  conv => enter [1]; rw [h309 x y]

@[equational_result]
theorem Equation309_implies_Equation3255 (G : Type*) [Magma G] (h309 : Equation309 G) : Equation3255 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h309 sK0 sK0]
    conv => enter [1, 2]; rw [h309 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation309_implies_Equation307 (G : Type*) [Magma G] (h309 : Equation309 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h309 x x]

theorem Equation309_4512_implies_Equation3258 (G : Type*) [Magma G] (h309 : Equation309 G) (h4512 : Equation4512 G) : Equation3258 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h309 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h309 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation310_implies_Equation3256 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation3256 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h310 sK0 sK0]
    conv => enter [1, 2]; rw [h310 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation310_implies_Equation3258 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation3258 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y x]

@[equational_result]
theorem Equation310_implies_Equation4270 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation4270 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h310 X0 sK0]
    conv => enter [1, 2]; rw [h310 sK0 sK1]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← h310 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h310 sK0 sK1]
    conv => enter [1]; rw [l1 sK0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation310_implies_Equation307 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h310 x x]

@[equational_result]
theorem Equation315_implies_Equation3278 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation3278 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation315_4512_implies_Equation3255 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation3255 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h315 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h315 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h315 (sK1 ◇ sK0) sK0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h315 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h315 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h315 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation315_implies_Equation4275 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [← h315 x x]
  conv => enter [1]; rw [h315 x y]

@[equational_result]
theorem Equation315_implies_Equation307 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h315 x x]

@[equational_result]
theorem Equation311_implies_Equation4271 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4271 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h311 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h311 sK0 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 x y z]

@[equational_result]
theorem Equation311_implies_Equation4339 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4339 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK2]
    conv => enter [1]; rw [h311 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation4360 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4360 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h311 sK1 sK2 sK3]
    conv => enter [1]; rw [h311 sK1 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation311_implies_Equation3267 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1]; rw [h311 x y (z ◇ w)]

@[equational_result]
theorem Equation311_implies_Equation309 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h311 x y x]

@[equational_result]
theorem Equation311_implies_Equation4286 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4286 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK0 sK1]
    conv => enter [1]; rw [h311 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation4318 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4318 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK0]
    conv => enter [1]; rw [h311 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation3260 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3260 G := by
  intro x y z
  conv => enter [1]; rw [h311 x y (x ◇ z)]

@[equational_result]
theorem Equation311_implies_Equation3265 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3265 G := by
  intro x y z
  conv => enter [1]; rw [h311 x y (z ◇ y)]

@[equational_result]
theorem Equation311_implies_Equation3264 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3264 G := by
  intro x y z
  conv => enter [1]; rw [h311 x y (z ◇ x)]

@[equational_result]
theorem Equation311_implies_Equation310 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation310 G := by
  intro x y
  conv => enter [1]; rw [h311 x y y]

@[equational_result]
theorem Equation311_implies_Equation3259 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3259 G := by
  intro x y
  conv => enter [1]; rw [h311 x y (x ◇ y)]

@[equational_result]
theorem Equation311_implies_Equation4288 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4288 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK0 sK1]
    conv => enter [1]; rw [h311 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation3261 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3261 G := by
  intro x y
  conv => enter [1]; rw [h311 x y (y ◇ x)]

@[equational_result]
theorem Equation311_implies_Equation308 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h311 x x y]

@[equational_result]
theorem Equation311_implies_Equation4358 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4358 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK2]
    conv => enter [1]; rw [h311 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation4314 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4314 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h311 sK0 sK1 sK0]
    conv => enter [1]; rw [h311 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation311_implies_Equation4283 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4283 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h311 sK0 sK0 sK1]
    conv => enter [1]; rw [h311 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation311_implies_Equation4284 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4284 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h311 sK0 sK0 sK1]
    conv => enter [1]; rw [h311 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation318_implies_Equation4278 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4278 G := by
  intro x y z
  conv => enter [1]; rw [← h318 x x x]
  conv => enter [1]; rw [h318 x y z]

@[equational_result]
theorem Equation318_implies_Equation4300 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4300 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h318 sK1 sK2 sK0]
    conv => enter [1]; rw [h318 sK1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation318_implies_Equation4360 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4360 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h318 sK3 X0 sK0]
    conv => enter [1]; rw [h318 sK3 X1 sK0]
  have l1 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK3 ◇ sK3) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← h318 sK3 sK1 sK0]
  have l2 : ∀ sK1 sK0 sK3 X0 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 X0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 sK3]
    conv => enter [1]; rw [h318 sK3 X0 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z x w]

@[equational_result]
theorem Equation318_implies_Equation3300 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3300 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h318 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [h318 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation318_implies_Equation309 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h318 x x y]

@[equational_result]
theorem Equation318_implies_Equation4296 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4296 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h318 sK1 sK0 sK0]
    conv => enter [1]; rw [h318 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation318_implies_Equation4327 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4327 G := by
  intro x y z
  conv => enter [1]; rw [← h318 x x y]
  conv => enter [1]; rw [h318 x z x]

@[equational_result]
theorem Equation318_implies_Equation3274 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3274 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h318 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation318_implies_Equation3292 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3292 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h318 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation318_implies_Equation3264 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3264 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h318 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation318_implies_Equation315 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation315 G := by
  intro x y
  conv => enter [1]; rw [h318 x y y]

@[equational_result]
theorem Equation318_implies_Equation3271 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3271 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h318 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation318_implies_Equation4304 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4304 G := by
  intro x y z
  conv => enter [1]; rw [← h318 y x x]
  conv => enter [1]; rw [h318 y z y]

@[equational_result]
theorem Equation318_implies_Equation3261 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3261 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h318 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation318_implies_Equation312 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h318 x y x]

@[equational_result]
theorem Equation318_implies_Equation4362 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4362 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h318 sK2 X0 sK1]
    conv => enter [1]; rw [h318 sK2 X1 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h318 sK2 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [h318 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z y]

@[equational_result]
theorem Equation318_implies_Equation4291 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4291 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h318 sK1 X0 sK0]
    conv => enter [1]; rw [h318 sK1 X1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x x y y]

@[equational_result]
theorem Equation318_implies_Equation4284 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [← h318 y x x]
  conv => enter [1]; rw [h318 y x y]

@[equational_result]
theorem Equation318_implies_Equation4320 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4320 G := by
  intro x y
  conv => enter [1]; rw [← h318 x x y]
  conv => enter [1]; rw [h318 x y x]

@[equational_result]
theorem Equation313_implies_Equation4273 (G : Type*) [Magma G] (h313 : Equation313 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [← h313 x x]
  conv => enter [1]; rw [h313 x y]

@[equational_result]
theorem Equation313_implies_Equation3259 (G : Type*) [Magma G] (h313 : Equation313 G) : Equation3259 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 sK0 sK0]
    conv => enter [1, 2]; rw [h313 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation313_implies_Equation307 (G : Type*) [Magma G] (h313 : Equation313 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h313 x x]

theorem Equation313_4512_implies_Equation3271 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation3271 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h313 sK0 sK0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [h313 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h313 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation314_implies_Equation4274 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [← h314 x x x]
  conv => enter [1]; rw [h314 x y z]

@[equational_result]
theorem Equation314_implies_Equation311 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation311 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x x y z]

@[equational_result]
theorem Equation314_implies_Equation318 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation318 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h314 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation314_implies_Equation313 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h314 x y y]

@[equational_result]
theorem Equation314_implies_Equation3304 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3304 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h314 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h314 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h314 sK2 X0 sK2]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1]
    conv => enter [1]; rw [h314 sK1 sK4 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h314 sK2 sK3 sK2]
    conv => enter [1, 2]; rw [l2 sK2 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation314_implies_Equation4301 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4301 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK0 sK1]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation314_implies_Equation4331 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4331 G := by
  intro x y z
  conv => enter [1]; rw [← h314 y x x]
  conv => enter [1]; rw [h314 y z y]

@[equational_result]
theorem Equation314_implies_Equation4305 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4305 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK0 sK1]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation314_implies_Equation4325 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4325 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h314 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h314 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h314 sK2 X0 sK2]
  have l2 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1]
    conv => enter [1]; rw [h314 sK1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 z x y x]
  conv => enter [1]; rw [h314 z y z]

@[equational_result]
theorem Equation314_implies_Equation3273 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3273 G := by
  intro x y z
  conv => enter [1]; rw [h314 x y (y ◇ z)]

@[equational_result]
theorem Equation314_implies_Equation3290 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3290 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h314 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation314_implies_Equation3301 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3301 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h314 sK0 sK3 sK2]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h314 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation314_implies_Equation4364 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4364 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h314 X1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h314 X0 X1 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0 X1]
    conv => enter [1]; rw [← h314 X1 X0 X1]
  have l2 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h314 sK1 X0 sK2]
    conv => enter [1]; rw [h314 sK1 X1 sK2]
  have l3 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l2 (sK1 ◇ sK2) sK1 sK2 sK0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l3 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [h314 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z y]

@[equational_result]
theorem Equation314_implies_Equation4369 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4369 G := by
  have l0 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h314 sK1 sK2 sK0]
    conv => enter [1]; rw [h314 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z z]

@[equational_result]
theorem Equation314_implies_Equation316 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation316 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h314 y y y]

@[equational_result]
theorem Equation314_implies_Equation40 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation40 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation314_implies_Equation4279 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4279 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h314 sK2 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← h314 x x x]
  conv => enter [1]; rw [l2 x y z y]

@[equational_result]
theorem Equation314_implies_Equation4299 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4299 G := by
  intro x y z
  conv => enter [1]; rw [← h314 x x y]
  conv => enter [1]; rw [h314 x z x]

@[equational_result]
theorem Equation314_implies_Equation4297 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4297 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h314 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h314 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h314 sK2 X0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1]; rw [h314 z y z]

@[equational_result]
theorem Equation314_implies_Equation4277 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4277 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← h314 x x x]
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation314_implies_Equation4280 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4280 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h314 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h314 sK2 X0 sK2]
  have l3 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l2 X0 X0 sK2]
    conv => enter [1]; rw [← h314 sK2 X0 sK2]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← h314 x x x]
  conv => enter [1]; rw [l4 x z]
  conv => enter [1]; rw [h314 z y z]

@[equational_result]
theorem Equation314_implies_Equation4290 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [← h314 x x y]
  conv => enter [1]; rw [h314 x y x]

@[equational_result]
theorem Equation314_implies_Equation4321 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4321 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h314 sK0 sK1 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK1]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h314 sK0 sK1 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK1 sK1]
  have l2 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l2 X0 X0 sK1 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 X0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l3 sK1 sK1 sK0]
    conv => enter [1]; rw [h314 sK1 X0 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y y]

@[equational_result]
theorem Equation314_implies_Equation4293 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4293 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK0 sK1]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation314_implies_Equation4343 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4343 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← h314 y x y]
  conv => enter [1]; rw [l4 y x]
  conv => enter [1]; rw [h314 x y x]

@[equational_result]
theorem Equation314_implies_Equation4276 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4276 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← h314 x x x]
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h314 y y y]

@[equational_result]
theorem Equation315_implies_Equation3261 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation3261 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1, 2]; rw [h315 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation310_4512_implies_Equation3261 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation3261 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1 sK0]
  have l3 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l2 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l4 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X2 X1 sK0
    conv => enter [1, 1]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l5 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [h310 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l5 X0 X1 sK0]
  have l7 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [l4 X0 X2 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l8 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l3 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l9 : ∀ X0 X2 X1 sK0 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l7 X0 X2 X1 sK0]
  have l10 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← l8 X0 sK0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h310 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h310 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [l6 X0 X1 sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l11 sK0]
    conv => enter [1]; rw [← l6 X0 sK0 sK0]
  have l15 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l0 X1 X0 X0]
    conv => enter [1, 2]; rw [l6 X0 X0 sK0]
  have l16 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l15 X1 X0 sK0]
    conv => enter [1]; rw [l10 X1 X0 sK0 X0]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l13 X0 sK0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l17 X0 X1 X0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK1 sK0]
    conv => enter [1]; rw [← h310 sK1 sK0]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ sK1) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0 X0]
    conv => enter [1]; rw [← l18 sK1 X0]
  have l22 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l21 sK1 sK0 X0]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l22 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l24 x y]

@[equational_result]
theorem Equation316_implies_Equation40 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation40 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation316_implies_Equation310 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation310 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h316 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation316_implies_Equation312 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation312 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h316 X0 sK0]
    conv => enter [1]; rw [← h316 sK0 sK0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation316_implies_Equation4280 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation4280 G := by
  have l0 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l0 X1 sK0]
    conv => enter [1]; rw [← h316 sK0 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [h316 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1]
    conv => enter [1, 2]; rw [← h316 sK0 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h316 sK2 sK0]
    conv => enter [1, 2]; rw [← h316 sK0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← h316 x x]
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation316_implies_Equation4343 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation4343 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h316 sK1 sK1]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h316 X0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l4 y x]
  conv => enter [1]; rw [l3 y x]

@[equational_result]
theorem Equation316_implies_Equation4276 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation4276 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h316 sK1 sK1]
    conv => enter [1]; rw [h316 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation316_4512_implies_Equation315 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation315 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l10 x y x]

theorem Equation316_4512_implies_Equation308 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l10 x x y]

theorem Equation316_4512_implies_Equation4277 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4277 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l1 sK0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h316 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X1]
    conv => enter [1, 2]; rw [← h316 sK0 sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l4 X0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h316 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 X0 X0]
    conv => enter [1]; rw [← l8 sK0 X0 X0]
  have l10 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l9 X0 sK0]
    conv => enter [1]; rw [l5 X0 X0 sK0]
  have l12 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1]; rw [l5 X1 (X1 ◇ X2) sK0]
  have l13 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l12 X0 X2 sK0 sK0]
  have l14 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l13 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [← h316 x x]
  conv => enter [1]; rw [l14 x y z]

theorem Equation316_4512_implies_Equation4293 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4293 G := by
  have l0 : ∀ X0 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X2
    conv => enter [1]; rw [← h316 X0 X0]
    conv => enter [1]; rw [h316 X0 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l1 X2 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l1 sK1 X0]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l5 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X2)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← l2 X1 X1 X2]
    conv => enter [1]; rw [l4 X1 sK0 sK1]
  have l6 : ∀ sK0 sK1 X1 X0 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ X1) = (sK0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ X0) X1]
  have l7 : ∀ sK0 sK1 X1 X0 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ X1) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X1]
    conv => enter [1]; rw [l7 sK0 sK1 X1 X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 sK0 sK1 X0 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 (sK0 ◇ sK1) sK1 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l13 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l4 X0 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← l14 sK0 sK1 X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 X0]
  have l18 : ∀ X0 X1 sK0 sK1 : G, ((X0 ◇ X0) ◇ X1) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 1]; rw [l13 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X1]
  have l19 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l17 sK0 sK1 X1]
    conv => enter [1]; rw [← l18 X0 X1 sK0 sK1]
  have l20 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l19 sK0 sK1 X0 X1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation316_4512_implies_Equation4299 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4299 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l4 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l1 X2 sK0]
    conv => enter [1]; rw [l3 X2 X2 sK0]
  have l7 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [l3 X1 (X1 ◇ X2) sK0]
  have l8 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l7 X0 X2 sK0 sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l8 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l9 x x y]
  conv => enter [1]; rw [l2 x z]

theorem Equation316_4512_implies_Equation4297 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4297 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK2 : G, (X1 ◇ X1) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK2]
  have l3 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X2
    conv => enter [1]; rw [l2 sK2 X2 sK2]
  have l4 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK2 X2
    conv => enter [1]; rw [l7 sK2 sK2 sK2]
    conv => enter [1]; rw [← l6 X2 sK2 sK2]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X2
    conv => enter [1]; rw [l8 sK2 X2]
    conv => enter [1]; rw [l4 X2 X2 sK2]
  have l11 : ∀ X0 X2 sK2 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK2 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK2 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK2]
  have l12 : ∀ sK2 X0 X2 : G, (sK2 ◇ sK2) = ((X0 ◇ X0) ◇ X2) := by
    intro sK2 X0 X2
    conv => enter [1]; rw [l10 sK2 (sK2 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK2 sK2]
  have l13 : ∀ sK2 X0 X2 : G, (sK2 ◇ sK2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK2 X0 X2
    conv => enter [1]; rw [l12 sK2 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l13 z x y]
  conv => enter [1]; rw [l3 z y]

theorem Equation316_4512_implies_Equation4288 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4288 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 sK2 : G, (X1 ◇ (X1 ◇ X1)) = (sK2 ◇ sK2) := by
    intro X1 sK2
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK2]
  have l2 : ∀ sK2 X1 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X1
    conv => enter [1]; rw [← l1 X1 sK2]
    conv => enter [1, 2]; rw [l0 X1 sK2]
  have l3 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK2]
  have l4 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X2
    conv => enter [1]; rw [← l1 X2 sK2]
    conv => enter [1]; rw [l3 X2 X2 sK2]
  have l7 : ∀ X0 X2 sK2 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK2 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [l3 X1 (X1 ◇ X2) sK2]
  have l8 : ∀ sK2 X0 X2 : G, (sK2 ◇ sK2) = ((X0 ◇ X0) ◇ X2) := by
    intro sK2 X0 X2
    conv => enter [1]; rw [l6 sK2 (sK2 ◇ X2)]
    conv => enter [1]; rw [← l7 X0 X2 sK2 sK2]
  have l9 : ∀ sK2 X0 X2 : G, (sK2 ◇ sK2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK2 X0 X2
    conv => enter [1]; rw [l8 sK2 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l9 z x y]
  conv => enter [1]; rw [l2 z x]

theorem Equation316_4512_implies_Equation4304 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4304 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l2 sK1 X2 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK1 X2
    conv => enter [1]; rw [l7 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 X2 sK1 sK1]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l8 sK1 X2]
    conv => enter [1]; rw [l4 X2 X2 sK1]
  have l11 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK1]
  have l12 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK1 sK1]
  have l13 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l12 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l13 y x y]
  conv => enter [1]; rw [l3 y z]

theorem Equation316_4512_implies_Equation4284 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4284 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (sK1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK1]
  have l2 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [← l1 X1 sK1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l4 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [← l1 X2 sK1]
    conv => enter [1]; rw [l3 X2 X2 sK1]
  have l7 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [l3 X1 (X1 ◇ X2) sK1]
  have l8 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l7 X0 X2 sK1 sK1]
  have l9 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l8 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [← l9 y x y]
  conv => enter [1]; rw [l2 y x]

theorem Equation316_4512_implies_Equation4290 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4290 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l4 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l1 X2 sK0]
    conv => enter [1]; rw [l3 X2 X2 sK0]
  have l7 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [l3 X1 (X1 ◇ X2) sK0]
  have l8 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l7 X0 X2 sK0 sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l8 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [← l9 x x y]
  conv => enter [1]; rw [l2 x y]

theorem Equation313_4512_implies_Equation309 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation309 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h313 sK0 sK0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [h313 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h313 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation313_4512_implies_Equation4331 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation4331 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h313 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h313 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1, 1]; rw [h313 sK1 sK0]
    conv => enter [1, 2]; rw [h313 sK1 sK0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h313 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h313 sK2 sK2]
    conv => enter [1, 2]; rw [h313 sK2 (sK1 ◇ sK1)]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2, 1]; rw [h313 sK1 sK0]
  have l5 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h313 sK2 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 sK2]
  have l6 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK1))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l5 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK1)))]
  have l7 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK2 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l7 sK2 sK1 sK0]
    conv => enter [1]; rw [← h313 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l8 sK2 sK0 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [h313 sK2 sK2]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h313 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation313_4512_implies_Equation4325 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation4325 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h313 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h313 sK2 sK2]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [h313 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h313 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← h313 sK1 (sK2 ◇ sK2)]
  have l6 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK1]
    conv => enter [1, 2]; rw [h313 sK1 sK0]
  have l7 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l1 sK2]
    conv => enter [1]; rw [l6 sK2 sK1 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ (sK2 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l7 sK2 sK1 sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK1 sK2 sK0]
    conv => enter [1]; rw [h313 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l8 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ (sK2 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK2) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2))]
  have l12 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 (sK2 ◇ sK2) (sK0 ◇ (sK1 ◇ sK0))]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l12 sK1 sK2 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [h313 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK2 sK1 sK0]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [l16 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

theorem Equation313_4512_implies_Equation3290 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation3290 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h313 sK0 sK0]
  have l2 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h313 sK1 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [h313 sK1 (sK2 ◇ (sK0 ◇ sK2))]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 1]; rw [h313 sK0 sK2]
    conv => enter [1]; rw [l2 sK2 sK0 sK1]
    conv => enter [1, 2, 1]; rw [← h313 sK0 sK2]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h313 sK1 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2]
  have l5 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK2]
    conv => enter [1]; rw [← l0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK0 ◇ sK0)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK1 sK0]
    conv => enter [1]; rw [← h313 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [h313 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation313_4512_implies_Equation4318 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation4318 G := by
  have l0 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h313 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h313 sK2 sK2]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [h313 sK1 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l5 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h313 (sK2 ◇ sK2) (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK2 ◇ sK2)]
  have l6 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l0 sK2]
    conv => enter [1]; rw [l5 sK2 sK0]
  have l7 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h313 (sK0 ◇ (sK2 ◇ sK2)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK2 sK0]
  have l8 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ sK2)]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l8 sK0 sK2]
    conv => enter [1]; rw [h313 (sK0 ◇ (sK2 ◇ sK2)) (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l8 sK0 sK2]
  have l10 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l9 sK0 sK2]
  have l11 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l10 sK0 sK2]
  have l12 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l6 sK2 sK0]
    conv => enter [1]; rw [← l11 sK0 sK2]
  have l13 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l12 sK2 sK0]
    conv => enter [1]; rw [h313 sK0 sK0]
    conv => enter [1, 2]; rw [l12 sK0 sK2]
  have l14 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1, 2]; rw [l12 sK0 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l14 sK1 sK0 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
  have l17 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h313 (sK2 ◇ sK2) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l16 sK0 sK1 sK2]
  have l18 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l17 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l19 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l18 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l20 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l19 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l12 sK0 sK2]
  have l21 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l0 sK2]
    conv => enter [1]; rw [l20 sK2 sK1 sK0]
  have l22 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l21 sK2 sK1 sK0]
    conv => enter [1]; rw [← h313 (sK1 ◇ sK0) (sK2 ◇ sK2)]
  have l23 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l0 sK2]
    conv => enter [1]; rw [l22 sK2 sK1 sK0]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l23 sK2 sK1 sK0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK2]
  intro x y z
  conv => enter [1]; rw [l25 x y z]
  conv => enter [1]; rw [l13 z x]

theorem Equation313_4512_implies_Equation4327 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation4327 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h313 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [h313 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l6 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h313 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h313 sK2 sK2]
    conv => enter [1, 2]; rw [h313 sK2 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h313 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0]
  have l17 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h313 sK2 ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
  have l18 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l17 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK2 ◇ (sK0 ◇ sK0)) ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))]
  have l19 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l18 sK2 sK0]
    conv => enter [1]; rw [← l0 (sK2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l20 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l19 sK2 sK0]
    conv => enter [1]; rw [← h313 (sK0 ◇ sK0) (sK2 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l20 sK2 sK0]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [h313 sK2 sK2]
    conv => enter [1, 2]; rw [← l22 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l16 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

theorem Equation313_4512_implies_Equation3265 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation3265 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h313 sK0 sK0]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h313 sK2 sK1]
    conv => enter [1]; rw [h313 sK2 sK2]
    conv => enter [1, 2]; rw [h313 sK2 sK1]
  have l3 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ (sK2 ◇ sK1))]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h313 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l2 sK1 sK2]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h313 sK2 sK1]
    conv => enter [1]; rw [l4 sK2 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ sK1)) ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h313 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h313 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← h313 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ sK0)]
  have l18 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l18 sK1 sK2 sK0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h313 sK0 sK0]
    conv => enter [1, 2]; rw [l19 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

theorem Equation313_4512_implies_Equation3274 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation3274 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h313 sK0 sK0]
  have l2 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h313 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK2 ◇ sK0)]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h313 sK2 sK0]
    conv => enter [1]; rw [h313 sK2 sK2]
    conv => enter [1, 2]; rw [h313 sK2 sK0]
  have l4 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h313 sK2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l3 sK0 sK2]
  have l5 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h313 sK2 sK0]
    conv => enter [1]; rw [l4 sK2 sK0]
  have l6 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h313 sK1 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [h313 sK1 (sK0 ◇ (sK2 ◇ sK0))]
  have l7 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h313 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK2 sK0]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [l7 sK0 sK2]
  have l9 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h313 (sK0 ◇ sK0) ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK0 sK2]
  have l10 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l9 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0))]
  have l11 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK2]
    conv => enter [1, 2]; rw [← h313 sK0 (sK2 ◇ sK0)]
  have l12 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l11 sK0 sK2]
  have l13 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l12 sK0 sK2]
    conv => enter [1]; rw [← h313 (sK2 ◇ sK0) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l13 sK0 sK2]
  have l15 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l8 sK0 sK2]
    conv => enter [1, 2]; rw [← l14 sK0 sK2]
  have l16 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK2]
  have l17 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = (((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h313 sK1 ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l6 sK0 sK2 sK1]
  have l18 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l17 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))]
  have l19 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l18 sK1 sK0 sK2]
    conv => enter [1]; rw [← l0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK0 ◇ (sK2 ◇ sK0))]
  have l20 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l19 sK1 sK0 sK2]
    conv => enter [1]; rw [← h313 (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l21 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [← l20 sK1 sK0 sK2]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [l22 sK1 sK0]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2]; rw [l16 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

theorem Equation313_4512_implies_Equation316 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h313 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h313 sK1 sK1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h313 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h313 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h313 sK0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 X0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l0 X0 X0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h313 X0 X0]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]
  conv => enter [1]; rw [h313 y y]

theorem Equation313_4512_implies_Equation4279 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation4279 G := by
  have l0 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h313 sK2 sK1]
    conv => enter [1]; rw [h313 sK2 sK2]
    conv => enter [1, 2]; rw [h313 sK2 sK1]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h313 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l0 sK1 sK2]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h313 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h313 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h313 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 X0 (sK0 ◇ sK0)]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [l4 (sK1 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h313 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← h313 x x]
  conv => enter [1]; rw [l7 x y z]

theorem Equation313_4512_implies_Equation4314 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation4314 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h313 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h313 sK1 sK1]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h313 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1]
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h313 sK0 sK0]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [← h313 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation313_4512_implies_Equation4320 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation4320 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h313 sK0 sK0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [h313 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h313 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation313_4512_implies_Equation4321 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation4321 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [h313 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h313 sK0 sK1]
    conv => enter [1]; rw [h313 sK0 sK0]
    conv => enter [1, 2]; rw [h313 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h313 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 2]; rw [h313 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ (sK0 ◇ sK1)) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [h313 sK0 sK1]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← h313 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ sK1))]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← l17 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l18 x y]

end Semigroup5
