import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup4

@[equational_result]
theorem Equation14_implies_Equation489 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation489 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 sK0 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 1]; rw [← h14 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation14_implies_Equation477 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation477 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 1]; rw [← h14 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation14_implies_Equation417 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation417 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1]; rw [← h14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation14_implies_Equation466 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation466 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 1]; rw [← h14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation14_implies_Equation3331 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation3331 G := by
  intro x y z
  conv => enter [1, 2]; rw [h14 y z]

@[equational_result]
theorem Equation14_implies_Equation3308 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation3308 G := by
  intro x y
  conv => enter [1, 2]; rw [h14 y x]

@[equational_result]
theorem Equation14_implies_Equation8 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h14 x x]

@[equational_result]
theorem Equation14_implies_Equation3259 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation3259 G := by
  intro x y
  conv => enter [1, 2]; rw [h14 x y]

@[equational_result]
theorem Equation14_implies_Equation4273 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [← h14 x x]
  conv => enter [1]; rw [h14 x y]

theorem Equation14_4512_implies_Equation556 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation556 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK0 ◇ sK2)]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h14 (sK1 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h14 sK2 (sK1 ◇ (sK0 ◇ sK2))]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ sK2) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) sK1 X0]
  have l3 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK0 ◇ sK2)]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h14 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [l3 sK1 sK0 sK2]
  have l5 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK0 sK2]
    conv => enter [1]; rw [← l2 sK0 sK2 sK1 sK1]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← l5 sK1 sK0 sK2]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK2]
  have l8 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l6 sK0 sK2 sK1]
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h14 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) sK2]
    conv => enter [1, 2]; rw [← l8 sK0 sK2 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 sK0 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation14_4512_implies_Equation511 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation511 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h14 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h14 sK0 sK1]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h14 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [h14 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation14_4512_implies_Equation427 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation427 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation14_4512_implies_Equation473 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation473 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h14 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h14 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation14_4512_implies_Equation3388 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation3388 G := by
  have l0 : ∀ sK1 sK2 : G, sK1 = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h14 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h14 sK2 sK1]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK2 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) sK2 X0]
  have l2 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK2 ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h14 sK2 sK1]
  have l3 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h14 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK2 sK1]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1]
    conv => enter [1]; rw [← l1 sK1 sK2 sK2]
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← l5 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation14_4512_implies_Equation3346 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation3346 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation14_4512_implies_Equation3271 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation3271 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h14 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h14 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation16_implies_Equation466 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation466 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK1]
    conv => enter [1, 2]; rw [h16 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation16_implies_Equation575 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation575 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h16 sK0 sK1]
    conv => enter [1, 2]; rw [h16 (sK1 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation16_implies_Equation436 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation436 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK0]
    conv => enter [1, 2]; rw [h16 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation16_implies_Equation3334 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation3334 G := by
  intro x y z
  conv => enter [1, 2]; rw [h16 y z]

@[equational_result]
theorem Equation16_implies_Equation3261 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation3261 G := by
  intro x y
  conv => enter [1, 2]; rw [h16 x y]

theorem Equation11_4512_implies_Equation427 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation427 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h11 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h11 sK1 sK0]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation11_4512_implies_Equation455 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation455 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h11 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l1 : ∀ sK1 sK2 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h11 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1))]
  have l2 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l3 : ∀ sK2 sK1 : G, sK2 = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [h11 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 sK1]
  have l4 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK2 ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l3 sK2 sK1]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l4 sK2 sK1]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [h11 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2]
    conv => enter [1]; rw [← l5 sK1 sK2]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← h11 X0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1, 1]; rw [l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation11_4512_implies_Equation419 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation419 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h11 X0 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 1]; rw [l7 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation11_4512_implies_Equation3334 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation3334 G := by
  have l0 : ∀ sK2 sK1 : G, sK2 = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [h11 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 sK1]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK2 ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← l0 sK2 sK1]
  have l2 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK2 ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l0 sK2 sK1]
  have l3 : ∀ sK2 sK1 : G, sK2 = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h11 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l4 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1, 1]; rw [l3 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
  have l5 : ∀ sK0 sK2 sK1 : G, sK0 = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h11 sK0 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1))]
  have l6 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1, 1]; rw [l5 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l7 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 (sK1 ◇ X0) sK1]
    conv => enter [1, 2]; rw [l1 sK2 sK1 X0]
  have l8 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l4 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l0 sK2 sK1]
  have l9 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [l7 sK2 sK1 X0]
  have l10 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK2) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [← l8 sK2 sK1]
  have l11 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2 X0]
    conv => enter [1, 1]; rw [l10 sK0 sK2 sK1]
  have l12 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) X0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [l2 sK2 sK1]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK2 sK1 sK2]
  have l15 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [h11 (sK2 ◇ (sK2 ◇ sK1)) sK2]
    conv => enter [1]; rw [← l9 sK2 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l15 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation11_4512_implies_Equation3261 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation3261 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [h11 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h11 X2 (X0 ◇ X1)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0]
    conv => enter [1]; rw [← l2 sK0 X0]
  have l4 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l9 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l1 X0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l8 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [l9 X0 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation38_implies_Equation322 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation322 G := by
  intro x y
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (x ◇ x)]

@[equational_result]
theorem Equation38_implies_Equation3329 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3329 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK1 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation3331 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3331 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation311 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation311 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ z)]

@[equational_result]
theorem Equation38_implies_Equation327 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation327 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation329 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation329 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation3312 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3312 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK2 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation3317 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3317 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation3320 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3320 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l0 x y z y]

@[equational_result]
theorem Equation38_implies_Equation3321 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3321 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation3330 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3330 G := by
  have l0 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK0 ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h38 sK0 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l0 x z y y]

@[equational_result]
theorem Equation38_implies_Equation3308 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3308 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation3323 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3323 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ (sK2 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation3334 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3334 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK2 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation325 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation325 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation3318 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3318 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation3322 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3322 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l0 x y z y]

@[equational_result]
theorem Equation38_implies_Equation3326 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation4271 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4271 G := by
  intro x y z
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (y ◇ z)]

@[equational_result]
theorem Equation38_implies_Equation3309 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3309 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation3315 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3315 G := by
  intro x y
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation38_implies_Equation4287 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4287 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation38_implies_Equation4315 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4315 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation4339 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4339 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation4340 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4340 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation323 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation323 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation326 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation326 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y y]

@[equational_result]
theorem Equation38_implies_Equation3267 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1]; rw [h38 x (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation38_implies_Equation3316 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation3306 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3306 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation3319 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3319 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y y]

@[equational_result]
theorem Equation38_implies_Equation309 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ x)]

@[equational_result]
theorem Equation38_implies_Equation3260 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3260 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation38_implies_Equation3265 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3265 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation38_implies_Equation310 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation310 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation3262 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3262 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation38_implies_Equation3263 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3263 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation38_implies_Equation3266 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3266 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation38_implies_Equation3259 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3259 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation38_implies_Equation3264 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3264 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation38_implies_Equation308 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h38 x (x ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation3254 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3254 G := by
  intro x y
  conv => enter [1]; rw [h38 x (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation38_implies_Equation3257 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3257 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (x ◇ (y ◇ z))]

@[equational_result]
theorem Equation38_implies_Equation3256 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3256 G := by
  intro x y
  conv => enter [1]; rw [h38 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation38_implies_Equation3261 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3261 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ (y ◇ x))]

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
theorem Equation38_implies_Equation4269 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (y ◇ x)]

@[equational_result]
theorem Equation38_implies_Equation4270 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (y ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation4268 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (x ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation4314 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4314 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation307 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h38 x (x ◇ x)]

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
theorem Equation38_implies_Equation3253 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h38 x (x ◇ (x ◇ x))]

theorem Equation39_4512_implies_Equation336 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation336 G := by
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
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation39_4512_implies_Equation3349 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3349 G := by
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
  have l3 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

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

theorem Equation39_4512_implies_Equation3312 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3312 G := by
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
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation39_4512_implies_Equation3330 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3330 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ sK1) sK2]
    conv => enter [1, 1]; rw [h39 sK1 sK0]
    conv => enter [1, 2]; rw [h39 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK2 sK1 sK0]
  have l6 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation39_4512_implies_Equation3363 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3363 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
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
  conv => enter [1]; rw [l4 z x y y]

theorem Equation39_4512_implies_Equation3380 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3380 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK0 ◇ sK1)) sK2]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y]
  conv => enter [1]; rw [l6 x y z]

theorem Equation39_4512_implies_Equation3397 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3397 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
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
  have l6 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK0 ◇ sK1)) sK2]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y]
  conv => enter [1]; rw [l6 y x z]

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

theorem Equation39_4512_implies_Equation3414 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3414 G := by
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
  conv => enter [1]; rw [l4 z x y z]

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

theorem Equation39_4512_implies_Equation3343 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3343 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]
  conv => enter [1]; rw [l4 x y y]

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
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation39_implies_Equation4287 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4287 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK2]
    conv => enter [1]; rw [h39 sK1 X0]
  intro x y z
  conv => enter [1, 2]; rw [l0 x y z]

@[equational_result]
theorem Equation39_implies_Equation4300 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4300 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation39_implies_Equation4330 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4330 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h39 (sK1 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation39_implies_Equation4340 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4340 G := by
  intro x y z
  conv => enter [1, 2]; rw [h39 y z]

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

theorem Equation39_4512_implies_Equation3281 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3281 G := by
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
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation39_4512_implies_Equation3284 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3284 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [← h39 sK0 sK2]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h39 sK0 sK2]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation39_4512_implies_Equation3296 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3296 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1, 2]; rw [← h39 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1, 2]; rw [h39 sK0 sK2]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← l4 sK0 sK2]
    conv => enter [1, 2]; rw [← l4 sK0 sK2]
  have l6 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [l6 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

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

theorem Equation39_4512_implies_Equation3268 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3268 G := by
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
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← l2 sK0 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation39_4512_implies_Equation3288 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3288 G := by
  have l0 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l0 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l2 sK2 sK0 X0 sK2]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l5 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h39 (sK2 ◇ (sK0 ◇ sK0)) sK1]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [l6 x z]
  conv => enter [1]; rw [l5 z x y]

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

@[equational_result]
theorem Equation39_implies_Equation4269 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4269 G := by
  intro x y
  conv => enter [1, 2]; rw [h39 x y]

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
theorem Equation39_implies_Equation4272 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4272 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation39_implies_Equation4291 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4291 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

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
theorem Equation39_implies_Equation4284 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation4284 G := by
  intro x y
  conv => enter [1, 2]; rw [← h39 y x]

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
theorem Equation41_implies_Equation332 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation332 G := by
  intro x y
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x y (x ◇ x)]

@[equational_result]
theorem Equation41_implies_Equation335 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation335 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

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
theorem Equation41_implies_Equation3350 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3350 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK2 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l0 z y x]

@[equational_result]
theorem Equation41_implies_Equation3352 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3352 G := by
  intro x y
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x y (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation41_implies_Equation3364 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3364 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK0 ◇ sK2))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l0 z x y]

@[equational_result]
theorem Equation41_implies_Equation3385 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3385 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation41_implies_Equation3398 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3398 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation41_implies_Equation3404 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3404 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation41_implies_Equation3417 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3417 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

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
theorem Equation41_implies_Equation3355 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3355 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation41_implies_Equation4274 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x (x ◇ x)]
  conv => enter [1]; rw [h41 x y (x ◇ z)]

@[equational_result]
theorem Equation41_implies_Equation4295 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4295 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK0]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK0)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 z x y]

@[equational_result]
theorem Equation41_implies_Equation4303 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4303 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation41_implies_Equation4344 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4344 G := by
  intro x y z
  conv => enter [1]; rw [← h41 y x (y ◇ y)]
  conv => enter [1]; rw [h41 y y (x ◇ z)]

@[equational_result]
theorem Equation41_implies_Equation4345 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4345 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK0]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [h41 y z x]
  conv => enter [1]; rw [l0 z x y]

@[equational_result]
theorem Equation41_implies_Equation3277 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3277 G := by
  have l0 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK1 (sK3 ◇ sK0)]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h41 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

@[equational_result]
theorem Equation41_implies_Equation3291 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3291 G := by
  have l0 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK1 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [h41 x z (x ◇ w)]
  conv => enter [1]; rw [l0 z x w y]

@[equational_result]
theorem Equation41_implies_Equation43 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation41_implies_Equation313 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (x ◇ y)]

@[equational_result]
theorem Equation41_implies_Equation319 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation319 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [h41 x z y]
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
theorem Equation41_implies_Equation3275 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3275 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK0 (sK2 ◇ sK1)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation41_implies_Equation3289 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3289 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [h41 x z (x ◇ y)]
  conv => enter [1]; rw [l0 z x y]

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
theorem Equation41_implies_Equation316 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (y ◇ y)]

@[equational_result]
theorem Equation41_implies_Equation317 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation317 G := by
  intro x y z
  conv => enter [1]; rw [h41 x y (y ◇ z)]

@[equational_result]
theorem Equation41_implies_Equation320 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation320 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [h41 x z z]
  conv => enter [1]; rw [l0 z y]

@[equational_result]
theorem Equation41_implies_Equation3270 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3270 G := by
  intro x y z
  conv => enter [1]; rw [h41 x y (x ◇ (x ◇ z))]

@[equational_result]
theorem Equation41_implies_Equation3272 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3272 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation41_implies_Equation3276 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3276 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK2 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [h41 x z z]
  conv => enter [1]; rw [l0 z y x]

@[equational_result]
theorem Equation41_implies_Equation3279 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3279 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation41_implies_Equation3280 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3280 G := by
  intro x y z
  conv => enter [1]; rw [h41 x y (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation41_implies_Equation3283 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3283 G := by
  intro x y z
  conv => enter [1]; rw [h41 x y (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation41_implies_Equation3285 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3285 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK1)]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1]
    conv => enter [1, 2]; rw [← l1 sK2 sK1]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x z y]
  conv => enter [1]; rw [l0 z y]

@[equational_result]
theorem Equation41_implies_Equation3293 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3293 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [h41 x z (y ◇ y)]
  conv => enter [1]; rw [l0 z y]

@[equational_result]
theorem Equation41_implies_Equation3298 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3298 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK2 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [h41 x z (z ◇ z)]
  conv => enter [1]; rw [l0 z y]

@[equational_result]
theorem Equation41_implies_Equation40 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation40 G := by
  intro x y
  conv => enter [1]; rw [h41 x y y]

@[equational_result]
theorem Equation41_implies_Equation3269 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3269 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation41_implies_Equation3282 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3282 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation41_implies_Equation3294 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3294 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [h41 x z (y ◇ z)]
  conv => enter [1]; rw [l0 z y]

@[equational_result]
theorem Equation41_implies_Equation3297 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3297 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [h41 x z (z ◇ y)]
  conv => enter [1]; rw [l0 z y]

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
theorem Equation41_implies_Equation4343 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4343 G := by
  intro x y
  conv => enter [1]; rw [← h41 y x (y ◇ y)]
  conv => enter [1]; rw [h41 y y (x ◇ x)]

@[equational_result]
theorem Equation41_implies_Equation4290 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [← h41 x x (x ◇ y)]
  conv => enter [1]; rw [h41 x y (x ◇ x)]

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

@[equational_result]
theorem Equation48_implies_Equation412 (G : Type*) [Magma G] (h48 : Equation48 G) : Equation412 G := by
  intro x y
  conv => enter [1]; rw [h48 x (x ◇ y)]

@[equational_result]
theorem Equation48_implies_Equation414 (G : Type*) [Magma G] (h48 : Equation48 G) : Equation414 G := by
  intro x y
  conv => enter [1]; rw [h48 x (y ◇ y)]

@[equational_result]
theorem Equation48_implies_Equation413 (G : Type*) [Magma G] (h48 : Equation48 G) : Equation413 G := by
  intro x y
  conv => enter [1]; rw [h48 x (y ◇ x)]

@[equational_result]
theorem Equation48_implies_Equation3 (G : Type*) [Magma G] (h48 : Equation48 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation48_implies_Equation3254 (G : Type*) [Magma G] (h48 : Equation48 G) : Equation3254 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [h48 x y]

theorem Equation62_4512_implies_Equation463 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation463 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← h62 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h62 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l6 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h62 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 sK0 X0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [h62 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation62_4512_implies_Equation500 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation500 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← h62 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h62 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l6 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h62 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 sK0 X0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [h62 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation62_4512_implies_Equation426 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation426 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← h62 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h62 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l6 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h62 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 sK0 X0]
    conv => enter [1, 2]; rw [← l6 sK0]
  intro x y
  conv => enter [1]; rw [l7 x x]
  conv => enter [1, 2]; rw [h62 x y]

theorem Equation62_4512_implies_Equation3 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 X0]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h62 X1 X2]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l7 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0]
  intro x
  conv => enter [1]; rw [l7 x]

theorem Equation62_4512_implies_Equation3268 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation3268 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← h62 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h62 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l6 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h62 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 sK0 X0]
    conv => enter [1, 2]; rw [← l6 sK0]
  intro x y
  conv => enter [1]; rw [← l7 x x]
  conv => enter [1]; rw [h62 x y]

@[equational_result]
theorem Equation49_implies_Equation47 (G : Type*) [Magma G] (h49 : Equation49 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h49 x x]

@[equational_result]
theorem Equation52_implies_Equation47 (G : Type*) [Magma G] (h52 : Equation52 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h52 x x]

theorem Equation50_4512_implies_Equation47 (G : Type*) [Magma G] (h50 : Equation50 G) (h4512 : Equation4512 G) : Equation47 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h50 X0 X0]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l4 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1, 2]; rw [l3 sK0]
  intro x
  conv => enter [1]; rw [l4 x]

@[equational_result]
theorem Equation72_implies_Equation47 (G : Type*) [Magma G] (h72 : Equation72 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h72 x x]

@[equational_result]
theorem Equation53_implies_Equation47 (G : Type*) [Magma G] (h53 : Equation53 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h53 x x]

@[equational_result]
theorem Equation65_implies_Equation47 (G : Type*) [Magma G] (h65 : Equation65 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h65 x x]

@[equational_result]
theorem Equation55_implies_Equation47 (G : Type*) [Magma G] (h55 : Equation55 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h55 x x]

@[equational_result]
theorem Equation56_implies_Equation47 (G : Type*) [Magma G] (h56 : Equation56 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h56 x x]

@[equational_result]
theorem Equation75_implies_Equation47 (G : Type*) [Magma G] (h75 : Equation75 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h75 x x]

@[equational_result]
theorem Equation58_implies_Equation49 (G : Type*) [Magma G] (h58 : Equation58 G) : Equation49 G := by
  intro x y
  conv => enter [1]; rw [h58 x x y]

@[equational_result]
theorem Equation58_implies_Equation52 (G : Type*) [Magma G] (h58 : Equation58 G) : Equation52 G := by
  intro x y
  conv => enter [1]; rw [h58 x y x]

@[equational_result]
theorem Equation58_implies_Equation55 (G : Type*) [Magma G] (h58 : Equation58 G) : Equation55 G := by
  intro x y
  conv => enter [1]; rw [h58 x y y]

theorem Equation62_4512_implies_Equation65 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation65 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h62 X1 X2]
  have l6 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l3 X1 X2]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X1) X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X1 := by
    intro X2 X1
    conv => enter [1]; rw [l6 X2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK1 sK0]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation62_4512_implies_Equation72 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 X0]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h62 X1 X2]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l7 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [l7 sK0]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation62_4512_implies_Equation39 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation39 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation62_4512_implies_Equation49 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation49 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h62 X1 X2]
  have l6 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l3 X1 X2]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X1) X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X1 := by
    intro X2 X1
    conv => enter [1]; rw [l6 X2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK0]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation62_4512_implies_Equation52 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 X0]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h62 X1 X2]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l7 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [l7 sK0]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation62_4512_implies_Equation55 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation55 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h62 X1 X2]
  have l6 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l3 X1 X2]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X1) X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X1 := by
    intro X2 X1
    conv => enter [1]; rw [l6 X2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK1 sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK0]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation62_4512_implies_Equation58 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation58 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h62 X1 X2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK2 ◇ sK0)) sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l3 (sK2 ◇ sK0) sK1]
  have l9 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l5 (sK2 ◇ sK0) (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l3 sK0 sK2]
  have l11 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [← l10 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x z]
  conv => enter [1]; rw [l9 z x y]
  conv => enter [1]; rw [l7 y z x]

theorem Equation62_4512_implies_Equation75 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation75 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h62 X1 X2]
  have l6 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l3 X1 X2]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X1) X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X1 := by
    intro X2 X1
    conv => enter [1]; rw [l6 X2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK1 sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK1 sK0]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation48_4512_implies_Equation50 (G : Type*) [Magma G] (h48 : Equation48 G) (h4512 : Equation4512 G) : Equation50 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h48 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)]
  have l9 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  intro x y
  conv => enter [1]; rw [l9 x (x ◇ (y ◇ y))]

theorem Equation48_4512_implies_Equation53 (G : Type*) [Magma G] (h48 : Equation48 G) (h4512 : Equation4512 G) : Equation53 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h48 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l9 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) X0]
  intro x y
  conv => enter [1]; rw [l9 x (y ◇ (x ◇ y))]

theorem Equation48_4512_implies_Equation38 (G : Type*) [Magma G] (h48 : Equation48 G) (h4512 : Equation4512 G) : Equation38 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h48 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l9 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) X0]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [l9 x y]

theorem Equation48_4512_implies_Equation49 (G : Type*) [Magma G] (h48 : Equation48 G) (h4512 : Equation4512 G) : Equation49 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h48 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l9 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  intro x y
  conv => enter [1]; rw [l9 x (x ◇ (y ◇ x))]

theorem Equation48_4512_implies_Equation52 (G : Type*) [Magma G] (h48 : Equation48 G) (h4512 : Equation4512 G) : Equation52 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h48 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)]
  have l9 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  intro x y
  conv => enter [1]; rw [l9 x (y ◇ (x ◇ x))]

theorem Equation48_4512_implies_Equation55 (G : Type*) [Magma G] (h48 : Equation48 G) (h4512 : Equation4512 G) : Equation55 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h48 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)]
  have l9 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  intro x y
  conv => enter [1]; rw [l9 x (y ◇ (y ◇ x))]

theorem Equation48_4512_implies_Equation56 (G : Type*) [Magma G] (h48 : Equation48 G) (h4512 : Equation4512 G) : Equation56 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X0 X0 X1]
    conv => enter [1]; rw [← h48 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 x (y ◇ (y ◇ y))]

theorem Equation48_4512_implies_Equation58 (G : Type*) [Magma G] (h48 : Equation48 G) (h4512 : Equation4512 G) : Equation58 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h48 sK0 ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) X0]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0)]
  have l9 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  intro x y z
  conv => enter [1]; rw [l9 x (y ◇ (z ◇ x))]

theorem Equation63_4512_implies_Equation47 (G : Type*) [Magma G] (h63 : Equation63 G) (h4512 : Equation4512 G) : Equation47 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h63 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← h63 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l3 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ((sK0 ◇ sK0) ◇ sK0)]
  have l6 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l5 sK0]
  have l7 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h63 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← l6 sK0]
  have l8 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1, 2, 2, 2]; rw [l3 sK0 sK0]
  intro x
  conv => enter [1]; rw [l8 x]

@[equational_result]
theorem Equation66_implies_Equation47 (G : Type*) [Magma G] (h66 : Equation66 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h66 x x]

@[equational_result]
theorem Equation73_implies_Equation47 (G : Type*) [Magma G] (h73 : Equation73 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h73 x x]

theorem Equation72_4512_implies_Equation55 (G : Type*) [Magma G] (h72 : Equation72 G) (h4512 : Equation4512 G) : Equation55 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h72 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h72 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h72 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h72 X0 X1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation72_4512_implies_Equation4275 (G : Type*) [Magma G] (h72 : Equation72 G) (h4512 : Equation4512 G) : Equation4275 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h72 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h72 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h72 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h72 sK0 sK0]
    conv => enter [1, 2]; rw [← l1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h72 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l5 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l1 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l3 x]
  conv => enter [1]; rw [l6 x y]

theorem Equation50_4512_implies_Equation55 (G : Type*) [Magma G] (h50 : Equation50 G) (h4512 : Equation4512 G) : Equation55 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h50 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation50_4512_implies_Equation4270 (G : Type*) [Magma G] (h50 : Equation50 G) (h4512 : Equation4512 G) : Equation4270 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h50 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  have l4 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x]
  conv => enter [1]; rw [← l6 x (y ◇ y)]

@[equational_result]
theorem Equation307_implies_Equation3253 (G : Type*) [Magma G] (h307 : Equation307 G) : Equation3253 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation308_implies_Equation3254 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation3254 G := by
  intro x y
  conv => enter [1]; rw [h308 x (x ◇ y)]

@[equational_result]
theorem Equation308_implies_Equation3257 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation3257 G := by
  intro x y z
  conv => enter [1]; rw [h308 x (y ◇ z)]

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
theorem Equation312_implies_Equation3268 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation3268 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [h312 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation312_implies_Equation3288 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation3288 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [h312 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

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
theorem Equation309_implies_Equation3255 (G : Type*) [Magma G] (h309 : Equation309 G) : Equation3255 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h309 sK0 sK0]
    conv => enter [1, 2]; rw [h309 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation309_implies_Equation4269 (G : Type*) [Magma G] (h309 : Equation309 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [← h309 x x]
  conv => enter [1]; rw [h309 x y]

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
theorem Equation310_implies_Equation3262 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation3262 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h310 sK0 sK1]
    conv => enter [1, 2]; rw [h310 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation310_implies_Equation3266 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation3266 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [h310 X0 sK2]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 X0]
    conv => enter [1, 2]; rw [l1 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation310_implies_Equation3256 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation3256 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h310 sK0 sK0]
    conv => enter [1, 2]; rw [h310 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

end Semigroup4
