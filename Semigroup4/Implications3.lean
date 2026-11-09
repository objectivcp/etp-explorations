import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup4

theorem Equation434_4512_implies_Equation437 (G : Type*) [Magma G] (h434 : Equation434 G) (h4512 : Equation4512 G) : Equation437 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h434 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h434 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h434 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h434 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l5 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK1 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation434_4512_implies_Equation443 (G : Type*) [Magma G] (h434 : Equation434 G) (h4512 : Equation4512 G) : Equation443 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h434 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h434 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h434 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h434 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l5 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l4 sK1 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation434_4512_implies_Equation11 (G : Type*) [Magma G] (h434 : Equation434 G) (h4512 : Equation4512 G) : Equation11 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h434 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h434 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h434 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h434 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x (y ◇ y)]

@[equational_result]
theorem Equation434_implies_Equation10 (G : Type*) [Magma G] (h434 : Equation434 G) : Equation10 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h434 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h434 X0 X1 (X0 ◇ (X0 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation434_4512_implies_Equation4318 (G : Type*) [Magma G] (h434 : Equation434 G) (h4512 : Equation4512 G) : Equation4318 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h434 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h434 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h434 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h434 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [← l4 x (z ◇ z)]

theorem Equation434_4512_implies_Equation4314 (G : Type*) [Magma G] (h434 : Equation434 G) (h4512 : Equation4512 G) : Equation4314 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h434 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h434 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h434 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h434 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [← l4 x (y ◇ y)]

theorem Equation506_4512_implies_Equation476 (G : Type*) [Magma G] (h506 : Equation506 G) (h4512 : Equation4512 G) : Equation476 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h506 (X1 ◇ X0) (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h506 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h506 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h506 sK0 (sK1 ◇ sK0) sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h506 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h506 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h506 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h506 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h506 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h506 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h506 X0 (X0 ◇ (X1 ◇ X0)) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h506 X0 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l8 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l11 X0 X0]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l8 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l8 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK1 ◇ sK0))]
  have l20 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l12 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l20 x y]
  conv => enter [1]; rw [l19 y x]
  conv => enter [1]; rw [l18 y x]
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation506_implies_Equation503 (G : Type*) [Magma G] (h506 : Equation506 G) : Equation503 G := by
  intro x y
  conv => enter [1]; rw [h506 x y y]

theorem Equation506_4512_implies_Equation558 (G : Type*) [Magma G] (h506 : Equation506 G) (h4512 : Equation4512 G) : Equation558 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h506 (X1 ◇ X0) (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h506 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h506 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h506 sK0 (sK1 ◇ sK0) sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h506 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h506 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h506 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h506 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h506 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h506 (sK1 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK2]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h506 X0 (X0 ◇ (X1 ◇ X0)) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h506 X0 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l8 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l11 X0 X0]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l8 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l15 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l8 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK2 sK1 sK0]
  have l16 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l8 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK0]
  have l17 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l16 sK2 sK1 sK0]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l18 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l15 sK1 sK0 sK2]
    conv => enter [1]; rw [l12 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK1 ◇ sK0))]
  have l20 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l12 (sK1 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l20 x y]
  conv => enter [1]; rw [l19 y x]
  conv => enter [1]; rw [l18 y x z]
  conv => enter [1]; rw [l17 z y x]

theorem Equation506_4512_implies_Equation16 (G : Type*) [Magma G] (h506 : Equation506 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h506 (X1 ◇ X0) (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h506 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h506 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h506 sK0 (sK1 ◇ sK0) sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h506 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h506 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h506 X0 (X0 ◇ (X1 ◇ X0)) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h506 X0 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l9 X0 X0]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [l10 (sK1 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l10 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l14 x y]
  conv => enter [1]; rw [l13 y x]

theorem Equation506_4512_implies_Equation10 (G : Type*) [Magma G] (h506 : Equation506 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h506 (X1 ◇ X0) (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h506 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h506 X0 X1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h506 X0 (X0 ◇ (X1 ◇ X0)) X1]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h506 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l8 X0 X0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l9 (sK0 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation506_implies_Equation4296 (G : Type*) [Magma G] (h506 : Equation506 G) : Equation4296 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h506 (sK1 ◇ (sK2 ◇ sK1)) X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h506 sK1 (sK1 ◇ (sK2 ◇ sK1)) sK2]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

@[equational_result]
theorem Equation506_implies_Equation4291 (G : Type*) [Magma G] (h506 : Equation506 G) : Equation4291 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h506 (sK1 ◇ (sK0 ◇ sK1)) X0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h506 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  intro x y
  conv => enter [1]; rw [← l0 y x x]

@[equational_result]
theorem Equation437_implies_Equation411 (G : Type*) [Magma G] (h437 : Equation437 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h437 x x]

@[equational_result]
theorem Equation476_implies_Equation411 (G : Type*) [Magma G] (h476 : Equation476 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h476 x x]

@[equational_result]
theorem Equation439_implies_Equation411 (G : Type*) [Magma G] (h439 : Equation439 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h439 x x]

@[equational_result]
theorem Equation440_implies_Equation411 (G : Type*) [Magma G] (h440 : Equation440 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h440 x x]

@[equational_result]
theorem Equation513_implies_Equation411 (G : Type*) [Magma G] (h513 : Equation513 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h513 x x]

@[equational_result]
theorem Equation442_implies_Equation413 (G : Type*) [Magma G] (h442 : Equation442 G) : Equation413 G := by
  intro x y
  conv => enter [1]; rw [h442 x x y]

theorem Equation442_4512_implies_Equation426 (G : Type*) [Magma G] (h442 : Equation442 G) (h4512 : Equation4512 G) : Equation426 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h442 (X1 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h442 X0 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h442 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h442 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h442 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l4 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h442 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l6 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1, 2]; rw [l5 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h442 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [← l1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 1]; rw [← l6 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation442_4512_implies_Equation432 (G : Type*) [Magma G] (h442 : Equation442 G) (h4512 : Equation4512 G) : Equation432 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h442 (X1 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h442 X0 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h442 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← h442 (sK2 ◇ sK0) sK1 sK0]
  have l3 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l2 sK1 sK0 sK2]
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0)]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h442 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK2]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation442_implies_Equation439 (G : Type*) [Magma G] (h442 : Equation442 G) : Equation439 G := by
  intro x y
  conv => enter [1]; rw [h442 x y y]

@[equational_result]
theorem Equation442_implies_Equation436 (G : Type*) [Magma G] (h442 : Equation442 G) : Equation436 G := by
  intro x y
  conv => enter [1]; rw [h442 x y x]

@[equational_result]
theorem Equation454_implies_Equation413 (G : Type*) [Magma G] (h454 : Equation454 G) : Equation413 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h454 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h454 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h454 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation454_implies_Equation426 (G : Type*) [Magma G] (h454 : Equation454 G) : Equation426 G := by
  intro x y
  conv => enter [1]; rw [h454 x y x]

theorem Equation454_4512_implies_Equation432 (G : Type*) [Magma G] (h454 : Equation454 G) (h4512 : Equation4512 G) : Equation432 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h454 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h454 X0 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h454 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h454 (sK2 ◇ sK0) sK0 sK0]
  have l3 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h454 (sK2 ◇ sK0) X0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 sK2]
  have l4 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l3 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← l1 X0 (sK0 ◇ (sK2 ◇ sK0))]
  have l5 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h454 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK2 sK0 sK1]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l1 X0 (sK2 ◇ sK0)]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h454 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK2]
    conv => enter [1, 2]; rw [← l6 sK1 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation454_implies_Equation439 (G : Type*) [Magma G] (h454 : Equation454 G) : Equation439 G := by
  intro x y
  conv => enter [1]; rw [h454 x y y]

@[equational_result]
theorem Equation454_implies_Equation419 (G : Type*) [Magma G] (h454 : Equation454 G) : Equation419 G := by
  intro x y
  conv => enter [1]; rw [h454 x x y]

@[equational_result]
theorem Equation443_implies_Equation437 (G : Type*) [Magma G] (h443 : Equation443 G) : Equation437 G := by
  intro x y
  conv => enter [1]; rw [h443 x y x]

@[equational_result]
theorem Equation443_implies_Equation413 (G : Type*) [Magma G] (h443 : Equation443 G) : Equation413 G := by
  intro x y
  conv => enter [1]; rw [h443 x x y]

@[equational_result]
theorem Equation443_implies_Equation440 (G : Type*) [Magma G] (h443 : Equation443 G) : Equation440 G := by
  intro x y
  conv => enter [1]; rw [h443 x y y]

@[equational_result]
theorem Equation558_implies_Equation476 (G : Type*) [Magma G] (h558 : Equation558 G) : Equation476 G := by
  intro x y
  conv => enter [1]; rw [h558 x y x]

@[equational_result]
theorem Equation558_implies_Equation426 (G : Type*) [Magma G] (h558 : Equation558 G) : Equation426 G := by
  intro x y
  conv => enter [1]; rw [h558 x x y]

@[equational_result]
theorem Equation558_implies_Equation513 (G : Type*) [Magma G] (h558 : Equation558 G) : Equation513 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h558 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h558 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h558 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation446_4512_implies_Equation413 (G : Type*) [Magma G] (h446 : Equation446 G) (h4512 : Equation4512 G) : Equation413 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h446 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h446 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h446 X0 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h446 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation446_4512_implies_Equation422 (G : Type*) [Magma G] (h446 : Equation446 G) (h4512 : Equation4512 G) : Equation422 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h446 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h446 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h446 X0 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h446 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h446 X0 X1 X2]
  have l6 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK2 ◇ sK0)) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l4 (sK2 ◇ sK0) sK1]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation446_4512_implies_Equation432 (G : Type*) [Magma G] (h446 : Equation446 G) (h4512 : Equation4512 G) : Equation432 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h446 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h446 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h446 X0 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h446 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK2]
    conv => enter [1]; rw [← l4 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [l4 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation446_4512_implies_Equation439 (G : Type*) [Magma G] (h446 : Equation446 G) (h4512 : Equation4512 G) : Equation439 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h446 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h446 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h446 X0 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h446 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h446 X0 X1 X2]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l4 (sK1 ◇ sK0) sK1]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l4 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation446_4512_implies_Equation442 (G : Type*) [Magma G] (h446 : Equation446 G) (h4512 : Equation4512 G) : Equation442 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h446 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h446 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h446 X0 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h446 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h446 X0 X1 X2]
  have l6 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK2 ◇ sK0)) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l4 (sK2 ◇ sK0) sK1]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l4 (sK1 ◇ (sK2 ◇ sK0)) sK1]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation446_4512_implies_Equation450 (G : Type*) [Magma G] (h446 : Equation446 G) (h4512 : Equation4512 G) : Equation450 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h446 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h446 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h446 X0 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h446 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h446 X0 X1 X2]
  have l6 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← l5 (sK2 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l4 (sK1 ◇ sK0) sK2]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l4 (sK2 ◇ (sK1 ◇ sK0)) sK1]
  have l8 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l9 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l4 sK0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK2 sK1 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK2 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation446_4512_implies_Equation454 (G : Type*) [Magma G] (h446 : Equation446 G) (h4512 : Equation4512 G) : Equation454 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h446 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h446 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h446 X0 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h446 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h446 X0 X1 X2]
  have l6 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l5 (sK2 ◇ (sK2 ◇ sK0)) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l4 (sK2 ◇ sK0) sK2]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l4 (sK2 ◇ (sK2 ◇ sK0)) sK1]
  have l8 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l6 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK2]
  have l9 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l4 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation422_4512_implies_Equation426 (G : Type*) [Magma G] (h422 : Equation422 G) (h4512 : Equation4512 G) : Equation426 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h422 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 X1 : G, sK0 = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h422 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ sK0))]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h422 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0]
  have l4 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h422 (sK0 ◇ sK0) sK1 sK0]
    conv => enter [1, 1]; rw [← l4 sK0]
    conv => enter [1, 2, 1]; rw [← l4 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 1]; rw [← l4 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation422_4512_implies_Equation432 (G : Type*) [Magma G] (h422 : Equation422 G) (h4512 : Equation4512 G) : Equation432 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [h422 (sK2 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))]
  have l1 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h422 sK0 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h422 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
  have l3 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h422 (sK2 ◇ sK0) sK0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK2]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l5 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h422 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK2 sK0]
  have l6 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [← l4 sK0 (sK2 ◇ sK0)]
  have l7 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1, 1]; rw [← l6 sK0 sK2]
  have l8 : ∀ sK0 sK2 sK1 : G, sK0 = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l9 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK2 sK1]
    conv => enter [1, 1]; rw [← l6 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation422_4512_implies_Equation439 (G : Type*) [Magma G] (h422 : Equation422 G) (h4512 : Equation4512 G) : Equation439 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h422 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h422 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l5 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h422 sK0 X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1]; rw [← l2 sK0 (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l6 x y y]

theorem Equation422_4512_implies_Equation442 (G : Type*) [Magma G] (h422 : Equation422 G) (h4512 : Equation4512 G) : Equation442 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h422 (sK1 ◇ (sK2 ◇ sK0)) sK0 sK0]
    conv => enter [1, 2, 2]; rw [← h422 sK0 sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h422 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK2]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0)]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h422 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK0)) ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h422 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK2 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation422_4512_implies_Equation446 (G : Type*) [Magma G] (h422 : Equation422 G) (h4512 : Equation4512 G) : Equation446 G := by
  have l0 : ∀ sK0 X0 : G, sK0 = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h422 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK2 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h422 sK0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h422 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h422 (sK0 ◇ sK0) sK1 sK2]
    conv => enter [1, 1]; rw [← l4 sK0]
    conv => enter [1, 2, 1]; rw [← l4 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1, 1]; rw [← l4 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation450_4512_implies_Equation413 (G : Type*) [Magma G] (h450 : Equation450 G) (h4512 : Equation4512 G) : Equation413 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h450 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h450 X0 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h450 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [← h450 sK0 sK1 sK0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h450 X1 X1 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l3 X0 X0]
    conv => enter [1]; rw [← h450 X0 X0 X0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation450_implies_Equation416 (G : Type*) [Magma G] (h450 : Equation450 G) : Equation416 G := by
  intro x y
  conv => enter [1]; rw [h450 x x y]

theorem Equation450_4512_implies_Equation426 (G : Type*) [Magma G] (h450 : Equation450 G) (h4512 : Equation4512 G) : Equation426 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h450 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h450 X0 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h450 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h450 (sK0 ◇ sK0) sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h450 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [← h450 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h450 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h450 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l6 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h450 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l7 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) X0]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1]; rw [← l10 sK1 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h450 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l15 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h450 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0))]
  have l16 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l8 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h450 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 2, 2, 2]; rw [← l17 sK1 sK0]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [← l11 sK0 sK1 (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l20 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation450_4512_implies_Equation432 (G : Type*) [Magma G] (h450 : Equation450 G) (h4512 : Equation4512 G) : Equation432 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h450 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h450 X0 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h450 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h450 (sK2 ◇ sK0) sK0 sK1]
  have l3 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h450 (sK2 ◇ sK0) sK0 sK2]
    conv => enter [1, 2]; rw [← h450 sK0 sK2 sK0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h450 X1 X1 X0]
  have l5 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l4 sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK2 sK0]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l4 (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0 sK2]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l4 X0 X0]
    conv => enter [1]; rw [← h450 X0 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l2 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l10 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l4 ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK2 sK1]
  have l11 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l10 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) (((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l12 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l11 sK0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK0 ◇ (sK2 ◇ sK0))]
  have l13 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h450 (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK0 sK2 sK1]
  have l14 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h450 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 2, 2, 2]; rw [← l13 sK0 sK2 sK1]
  have l15 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l14 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l9 sK1 sK0 sK2 (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l16 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l15 sK1 sK0 sK2 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l16 sK1 sK0 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

@[equational_result]
theorem Equation450_implies_Equation439 (G : Type*) [Magma G] (h450 : Equation450 G) : Equation439 G := by
  intro x y
  conv => enter [1]; rw [h450 x y y]

@[equational_result]
theorem Equation452_implies_Equation417 (G : Type*) [Magma G] (h452 : Equation452 G) : Equation417 G := by
  intro x y
  conv => enter [1]; rw [h452 x x y]

@[equational_result]
theorem Equation452_implies_Equation429 (G : Type*) [Magma G] (h452 : Equation452 G) : Equation429 G := by
  intro x y
  conv => enter [1]; rw [h452 x y x]

@[equational_result]
theorem Equation452_implies_Equation440 (G : Type*) [Magma G] (h452 : Equation452 G) : Equation440 G := by
  intro x y
  conv => enter [1]; rw [h452 x y y]

@[equational_result]
theorem Equation562_implies_Equation473 (G : Type*) [Magma G] (h562 : Equation562 G) : Equation473 G := by
  intro x y
  conv => enter [1]; rw [h562 x y x]

@[equational_result]
theorem Equation562_implies_Equation429 (G : Type*) [Magma G] (h562 : Equation562 G) : Equation429 G := by
  intro x y
  conv => enter [1]; rw [h562 x x y]

@[equational_result]
theorem Equation562_implies_Equation513 (G : Type*) [Magma G] (h562 : Equation562 G) : Equation513 G := by
  intro x y
  conv => enter [1]; rw [h562 x y y]

theorem Equation454_4512_implies_Equation416 (G : Type*) [Magma G] (h454 : Equation454 G) (h4512 : Equation4512 G) : Equation416 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h454 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h454 X0 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h454 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h454 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h454 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0]
  have l4 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [l1 X0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h454 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l5 x]
  conv => enter [1, 2]; rw [l4 x y]

theorem Equation454_4512_implies_Equation422 (G : Type*) [Magma G] (h454 : Equation454 G) (h4512 : Equation4512 G) : Equation422 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h454 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h454 X0 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h454 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) X0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h454 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0)) sK0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h454 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 sK1 sK2 sK0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l1 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h454 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h454 (sK1 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h454 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h454 (sK1 ◇ (sK2 ◇ sK0)) X0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← l1 X0 (sK1 ◇ (sK2 ◇ sK0))]
  have l11 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h454 (sK2 ◇ sK0) (sK1 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK0 sK1]
  have l12 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h454 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2 sK1]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h454 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l12 sK2 sK0 sK1]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l1 X0 (sK2 ◇ sK0)]
  have l15 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h454 (sK1 ◇ (sK2 ◇ sK0)) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK2 sK0 sK1]
  have l16 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← l1 X0 (sK2 ◇ sK0)]
  have l17 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h454 sK0 (sK1 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [← l16 sK1 sK2 sK0 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h454 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK2]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 sK2 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 sK1 sK2]
  have l20 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 sK0 sK0]
    conv => enter [1, 1]; rw [← l17 sK0 sK0 sK0]
  have l21 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1, 2]; rw [l17 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l21 x y z]

theorem Equation442_4512_implies_Equation416 (G : Type*) [Magma G] (h442 : Equation442 G) (h4512 : Equation4512 G) : Equation416 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h442 (X1 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h442 X0 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h442 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← h442 (sK1 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (sK1 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h442 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h442 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h442 (sK0 ◇ sK0) (sK0 ◇ sK0) sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h442 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h442 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l11 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1, 1]; rw [← l8 sK0 sK0]
  have l12 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h442 sK0 sK0 sK0]
    conv => enter [1, 2, 2]; rw [← l11 sK0]
  have l13 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l13 x]
  conv => enter [1, 2]; rw [l8 x y]

theorem Equation442_4512_implies_Equation422 (G : Type*) [Magma G] (h442 : Equation442 G) (h4512 : Equation4512 G) : Equation422 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h442 (X1 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h442 X0 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h442 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) (sK1 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← h442 (sK1 ◇ (sK2 ◇ sK0)) sK0 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) (sK1 ◇ (sK2 ◇ sK0))]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h442 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 sK2]
  have l5 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h442 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l5 sK2 sK0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0)]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h442 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK2]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation455_implies_Equation11 (G : Type*) [Magma G] (h455 : Equation455 G) : Equation11 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h455 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h455 X1 (X0 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation575_4512_implies_Equation16 (G : Type*) [Magma G] (h575 : Equation575 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X3 ◇ (X1 ◇ X0))) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [h575 (X3 ◇ (X3 ◇ (X1 ◇ X0))) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h575 X0 X1 X3]
  have l1 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))) = (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 sK0 X1
    conv => enter [1, 2, 2, 2]; rw [h575 (sK1 ◇ sK0) sK1 X1]
    conv => enter [1]; rw [← h575 (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1 X0]
  have l2 : ∀ sK0 X1 sK1 : G, sK0 = (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [h575 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK0 X1]
  have l3 : ∀ sK0 X0 X1 sK1 : G, sK0 = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 (X0 ◇ X1) sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ sK0))]
  have l4 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l3 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l0 X0 X0 X2 X1]
    conv => enter [1]; rw [← h575 X2 X0 X0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation463_4512_implies_Equation469 (G : Type*) [Magma G] (h463 : Equation463 G) (h4512 : Equation4512 G) : Equation469 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h463 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 X2 : G, (X0 ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h463 X2 X0]
    conv => enter [1]; rw [l0 X0 X0 X2]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l1 sK2 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK2 ◇ sK0)]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 (sK2 ◇ sK0)]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation412_4512_implies_Equation418 (G : Type*) [Magma G] (h412 : Equation412 G) (h4512 : Equation4512 G) : Equation418 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h412 X0 X0]
    conv => enter [1]; rw [← h412 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h412 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X2]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ (X0 ◇ X1)) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l7 X0 X2 X1]
  have l9 : ∀ sK0 sK2 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h412 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK2 X0]
  have l10 : ∀ sK0 sK2 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l2 sK0 ((sK0 ◇ sK2) ◇ X0)]
  have l11 : ∀ sK0 sK2 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l10 sK0 sK2 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ sK2) ◇ X0)]
  have l12 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 sK0 X0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0) X0]
  intro x y z
  conv => enter [1]; rw [l12 x (x ◇ (y ◇ (x ◇ z)))]

theorem Equation412_4512_implies_Equation420 (G : Type*) [Magma G] (h412 : Equation412 G) (h4512 : Equation4512 G) : Equation420 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h412 X0 X0]
    conv => enter [1]; rw [← h412 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X2]
    conv => enter [1, 1]; rw [← h412 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ (X0 ◇ X1)) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l7 X0 X2 X1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h412 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)))]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) ◇ X1)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) X1]
    conv => enter [1, 1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l11 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h412 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l12 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l2 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)]
  have l13 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l10 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [l8 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l15 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)]
  have l16 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l8 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l8 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l18 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 sK0 X0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
  have l19 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1) = (sK0 ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l16 sK0 sK1 sK0 X1]
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) X1]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [l8 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l21 : ∀ sK0 sK1 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l18 sK0 X1]
    conv => enter [1]; rw [← l19 sK0 sK1 X1]
  have l22 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1 sK0]
    conv => enter [1]; rw [← l20 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation412_4512_implies_Equation428 (G : Type*) [Magma G] (h412 : Equation412 G) (h4512 : Equation4512 G) : Equation428 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h412 X0 X0]
    conv => enter [1]; rw [← h412 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h412 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X2]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ (X0 ◇ X1)) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l7 X0 X2 X1]
  have l9 : ∀ sK0 sK2 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h412 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK2 X0]
  have l10 : ∀ sK0 sK2 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l2 sK0 ((sK0 ◇ sK2) ◇ X0)]
  have l11 : ∀ sK0 sK2 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l10 sK0 sK2 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ sK2) ◇ X0)]
  have l12 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 sK0 X0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0) X0]
  intro x y z
  conv => enter [1]; rw [l12 x (y ◇ (x ◇ (x ◇ z)))]

@[equational_result]
theorem Equation464_implies_Equation411 (G : Type*) [Magma G] (h464 : Equation464 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h464 x x]

@[equational_result]
theorem Equation467_implies_Equation411 (G : Type*) [Magma G] (h467 : Equation467 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h467 x x]

@[equational_result]
theorem Equation501_implies_Equation411 (G : Type*) [Magma G] (h501 : Equation501 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h501 x x]

theorem Equation474_4512_implies_Equation8 (G : Type*) [Magma G] (h474 : Equation474 G) (h4512 : Equation4512 G) : Equation8 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h474 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l3 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h474 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h474 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h474 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK0]
  have l8 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l7 sK0]
  have l9 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1, 2]; rw [l8 sK0]
  intro x
  conv => enter [1]; rw [l9 x]

@[equational_result]
theorem Equation477_implies_Equation411 (G : Type*) [Magma G] (h477 : Equation477 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h477 x x]

@[equational_result]
theorem Equation511_implies_Equation411 (G : Type*) [Magma G] (h511 : Equation511 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h511 x x]

@[equational_result]
theorem Equation481_implies_Equation477 (G : Type*) [Magma G] (h481 : Equation481 G) : Equation477 G := by
  intro x y
  conv => enter [1]; rw [h481 x y y]

@[equational_result]
theorem Equation481_implies_Equation414 (G : Type*) [Magma G] (h481 : Equation481 G) : Equation414 G := by
  intro x y
  conv => enter [1]; rw [h481 x x y]

@[equational_result]
theorem Equation481_implies_Equation473 (G : Type*) [Magma G] (h481 : Equation481 G) : Equation473 G := by
  intro x y
  conv => enter [1]; rw [h481 x y x]

@[equational_result]
theorem Equation481_implies_Equation40 (G : Type*) [Magma G] (h481 : Equation481 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h481 X0 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h481 (X1 ◇ X1) X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation522_implies_Equation511 (G : Type*) [Magma G] (h522 : Equation522 G) : Equation511 G := by
  intro x y
  conv => enter [1]; rw [h522 x y y]

theorem Equation522_4512_implies_Equation417 (G : Type*) [Magma G] (h522 : Equation522 G) (h4512 : Equation4512 G) : Equation417 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h522 X0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h522 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation522_implies_Equation500 (G : Type*) [Magma G] (h522 : Equation522 G) : Equation500 G := by
  intro x y
  conv => enter [1]; rw [h522 x y x]

theorem Equation522_4512_implies_Equation40 (G : Type*) [Magma G] (h522 : Equation522 G) (h4512 : Equation4512 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h522 X0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h522 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h522 X0 X1 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h522 X1 (X1 ◇ X0) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l4 X0 sK0]
    conv => enter [1]; rw [l2 X0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← l4 X0 sK1]
    conv => enter [1]; rw [l2 X0 (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation489_implies_Equation14 (G : Type*) [Magma G] (h489 : Equation489 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h489 (X0 ◇ X1) X0 X1]
    conv => enter [1]; rw [← h489 X0 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation556_4512_implies_Equation14 (G : Type*) [Magma G] (h556 : Equation556 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h556 X1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h556 (X1 ◇ X0) X0 (X1 ◇ X0)]
  have l1 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h556 sK1 X0 (X0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h556 sK0 X0 sK1]
  have l2 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l1 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) sK0]
  have l3 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l2 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 (sK0 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h556 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK1 (sK0 ◇ sK1) sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation492_4512_implies_Equation14 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation492_4512_implies_Equation464 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation464 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h492 (X1 ◇ X0) X0 X1]
  have l3 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation492_4512_implies_Equation522 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation522 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h492 (X1 ◇ X0) X0 X1]
  have l3 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ (sK0 ◇ sK2)) sK1]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 sK0 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK2 sK0]
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation492_4512_implies_Equation572 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation572 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h492 (X1 ◇ X0) X0 X1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK1) sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 (sK2 ◇ (sK0 ◇ sK1)) sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation492_4512_implies_Equation3364 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation3364 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h492 (X1 ◇ X0) X0 X1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation492_4512_implies_Equation3417 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation3417 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h492 X0 X0 X1]
    conv => enter [1]; rw [← h492 X2 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X0) (X2 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l5 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = X2 := by
    intro X1 X2
    conv => enter [1, 2, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l4 X1 X1 X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h492 (X1 ◇ X0) X0 X1]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l2 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK0) sK2]
  have l8 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
    conv => enter [1]; rw [l6 (sK2 ◇ (sK1 ◇ sK0)) sK2]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l9 x y]
  conv => enter [1]; rw [l8 y x z]

theorem Equation492_4512_implies_Equation16 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h492 (X1 ◇ X0) X0 X1]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation492_4512_implies_Equation3342 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation3342 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h492 (X1 ◇ X0) X0 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation492_4512_implies_Equation3355 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation3355 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h492 X0 X0 X1]
    conv => enter [1]; rw [← h492 X2 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X0) (X2 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l5 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = X2 := by
    intro X1 X2
    conv => enter [1, 2, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l4 X1 X1 X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h492 (X1 ◇ X0) X0 X1]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
    conv => enter [1]; rw [l5 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l9 x y]
  conv => enter [1, 2]; rw [l8 x y]

theorem Equation492_4512_implies_Equation43 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation43 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h492 X0 X0 X1]
    conv => enter [1]; rw [← h492 X2 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X0) (X2 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l5 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = X2 := by
    intro X1 X2
    conv => enter [1, 2, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l4 X1 X1 X2]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation492_4512_implies_Equation4305 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation4305 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h492 (X1 ◇ X0) X0 X1]
  have l3 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [← l4 y x]
  conv => enter [1]; rw [← l1 z y]

theorem Equation572_4512_implies_Equation14 (G : Type*) [Magma G] (h572 : Equation572 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h572 X0 X1 X1]
    conv => enter [1]; rw [← h572 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation572_4512_implies_Equation464 (G : Type*) [Magma G] (h572 : Equation572 G) (h4512 : Equation4512 G) : Equation464 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h572 X0 X1 X1]
    conv => enter [1]; rw [← h572 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h572 X0 X1 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation572_4512_implies_Equation481 (G : Type*) [Magma G] (h572 : Equation572 G) (h4512 : Equation4512 G) : Equation481 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h572 X0 X1 X1]
    conv => enter [1]; rw [← h572 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h572 X0 X1 X1]
  have l3 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK2) sK1]
  have l4 : ∀ sK1 sK2 : G, sK1 = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 (sK1 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1, 2]; rw [← l3 sK2 sK1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1, 1]; rw [l6 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1, 1]; rw [← l7 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation572_4512_implies_Equation492 (G : Type*) [Magma G] (h572 : Equation572 G) (h4512 : Equation4512 G) : Equation492 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h572 X0 X1 X1]
    conv => enter [1]; rw [← h572 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h572 X0 X1 X1]
  have l3 : ∀ sK1 sK2 : G, sK1 = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l1 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l2 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK1) sK2]
  have l5 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [← l4 sK2 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 (sK2 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1, 1]; rw [← l5 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation572_4512_implies_Equation3350 (G : Type*) [Magma G] (h572 : Equation572 G) (h4512 : Equation4512 G) : Equation3350 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h572 X0 X1 X1]
    conv => enter [1]; rw [← h572 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h572 X0 X1 X1]
  have l3 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK2) sK0]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ (sK2 ◇ sK2)) sK1]
  have l5 : ∀ sK0 sK2 : G, sK0 = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [← l3 sK2 sK0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1, 1]; rw [l7 sK0 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 1]; rw [l8 sK0 sK2]
    conv => enter [1]; rw [← l4 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation572_4512_implies_Equation3404 (G : Type*) [Magma G] (h572 : Equation572 G) (h4512 : Equation4512 G) : Equation3404 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h572 X0 X1 X1]
    conv => enter [1]; rw [← h572 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h572 X0 X1 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
  have l4 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [← l2 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK2 ◇ sK0))]
  have l5 : ∀ sK2 sK0 sK1 : G, sK2 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK2]
    conv => enter [1]; rw [l4 sK0 sK2 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK2 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 sK2 sK0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 (sK1 ◇ (sK2 ◇ sK0)) sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation572_4512_implies_Equation11 (G : Type*) [Magma G] (h572 : Equation572 G) (h4512 : Equation4512 G) : Equation11 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h572 X0 X1 X1]
    conv => enter [1]; rw [← h572 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h572 X0 X1 X1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 1]; rw [l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation572_4512_implies_Equation4325 (G : Type*) [Magma G] (h572 : Equation572 G) (h4512 : Equation4512 G) : Equation4325 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h572 X0 X1 X1]
    conv => enter [1]; rw [← h572 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h572 X0 X1 X1]
  have l3 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK2) sK1]
  have l4 : ∀ sK1 sK2 : G, sK1 = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 (sK1 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1, 2]; rw [← l3 sK2 sK1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1, 1]; rw [l6 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [l7 y z]

theorem Equation500_4512_implies_Equation466 (G : Type*) [Magma G] (h500 : Equation500 G) (h4512 : Equation4512 G) : Equation466 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h500 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h500 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← h500 X2 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h500 X0 X1]
    conv => enter [1]; rw [l2 X1 X1 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation500_implies_Equation575 (G : Type*) [Magma G] (h500 : Equation500 G) : Equation575 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h500 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h500 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 X1 X2]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h500 sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l1 sK1 (sK1 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation414_4512_implies_Equation427 (G : Type*) [Magma G] (h414 : Equation414 G) (h4512 : Equation4512 G) : Equation427 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h414 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h414 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h414 X2 (X0 ◇ X1)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h414 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l4 sK0 sK1]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h414 X0 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l8 X0]
    conv => enter [1]; rw [l2 X1 X0 (X0 ◇ X0)]
  have l12 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0))))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l2 X0 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)]
  have l13 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1))))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [l2 X0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l10 X0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1))]
    conv => enter [1]; rw [l13 X0 sK0 sK1]
  have l15 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l10 X0 (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0))]
    conv => enter [1]; rw [l12 X0 sK0 sK1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 (X0 ◇ ((X0 ◇ X0) ◇ X0))]
    conv => enter [1]; rw [l11 X1 X0]
  have l17 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 sK0]
    conv => enter [1]; rw [l15 X0 sK0 sK1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l16 X1 X0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = X0 := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l7 sK0 sK0 X0]
    conv => enter [1]; rw [l17 X0 sK0 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [l18 X1 X0]
  have l21 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l20 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l20 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l21 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l23 sK0 sK1]
  have l26 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l19 sK1 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l14 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1))]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2]; rw [← l26 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l30 x y]

theorem Equation414_4512_implies_Equation455 (G : Type*) [Magma G] (h414 : Equation414 G) (h4512 : Equation4512 G) : Equation455 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h414 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h414 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h414 X2 (X0 ◇ X1)]
  have l3 : ∀ sK2 sK1 : G, sK2 = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h414 sK2 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK1 sK1]
  have l4 : ∀ sK2 sK1 : G, sK2 = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ sK1) sK1]
  have l5 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) ◇ X0)) = (sK2 ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l4 sK2 sK1]
  have l6 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← l5 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK1)) sK1 X0]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h414 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [← l7 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ sK1)]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l11 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) (sK1 ◇ sK1)]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l7 X0]
    conv => enter [1]; rw [l2 X1 X0 (X0 ◇ X0)]
  have l14 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) ◇ sK2))))) = X0 := by
    intro X0 sK2 sK1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [l2 X0 sK2 ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1)]
  have l15 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))))))) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l2 X0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l16 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))))) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l10 X0 ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))))]
    conv => enter [1]; rw [l15 X0 sK1 sK2]
  have l17 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) ◇ sK2))) = X0 := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l10 X0 (sK2 ◇ (((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) ◇ sK2))]
    conv => enter [1]; rw [l14 X0 sK2 sK1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 (X0 ◇ ((X0 ◇ X0) ◇ X0))]
    conv => enter [1]; rw [l13 X1 X0]
  have l19 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)))) = X0 := by
    intro X0 sK2 sK1
    conv => enter [1, 2, 2]; rw [h4512 (sK2 ◇ (sK2 ◇ sK1)) sK1 sK2]
    conv => enter [1]; rw [l17 X0 sK2 sK1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l18 X1 X0]
  have l21 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = X0 := by
    intro X0 sK2
    conv => enter [1, 2]; rw [l6 sK2 sK2 X0]
    conv => enter [1]; rw [l19 X0 sK2 X0]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [l20 X1 X0]
  have l23 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l24 : ∀ sK2 sK1 : G, sK2 = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l22 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 sK1]
  have l25 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK2 ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l24 sK2 sK1]
  have l26 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l25 sK2 sK1]
  have l27 : ∀ sK1 sK2 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l21 sK1 sK2]
    conv => enter [1]; rw [← l26 sK1 sK2]
  have l28 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK1))))) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l27 sK1 sK2]
    conv => enter [1]; rw [l2 X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK1]
  have l29 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l10 X0 ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l28 X0 sK1 sK2]
  have l30 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [l29 X0 sK1 sK2]
  have l31 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1, 1]; rw [l30 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l31 x y z]

@[equational_result]
theorem Equation504_implies_Equation411 (G : Type*) [Magma G] (h504 : Equation504 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h504 x x]

theorem Equation506_4512_implies_Equation463 (G : Type*) [Magma G] (h506 : Equation506 G) (h4512 : Equation4512 G) : Equation463 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ X0))) = (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X0))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h506 (X2 ◇ (X0 ◇ (X3 ◇ X0))) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h506 X0 X2 X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h506 (X1 ◇ X0) (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h506 X0 (X1 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l3 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X0)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l0 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ X0)) X0]
  have l4 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X0))))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l3 X2 X0 X3 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X3 ◇ X0) X0]
  have l5 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l4 X2 X0 X3 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X3 X0 X0]
  have l6 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0))))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l5 X2 X0 X3 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X3 X0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h506 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h506 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h506 X0 (X0 ◇ (X1 ◇ X0)) X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l2 X0 X0]
    conv => enter [1]; rw [← h506 X0 X1 X0]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h506 (X1 ◇ X1) X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X1]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l10 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 (X0 ◇ X1)]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l8 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X1 X0]
    conv => enter [1]; rw [← l6 X1 X1 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← l14 X1 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l12 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l15 X0 X1]
  have l18 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l12 X0 X0]
    conv => enter [1]; rw [l17 X0 X0]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK0]
  have l20 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l18 sK0]
    conv => enter [1]; rw [l19 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2]; rw [← l20 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0]
    conv => enter [1]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l18 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l23 x y]

theorem Equation434_4512_implies_Equation412 (G : Type*) [Magma G] (h434 : Equation434 G) (h4512 : Equation4512 G) : Equation412 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h434 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h434 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h434 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h434 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x (x ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation508_implies_Equation11 (G : Type*) [Magma G] (h508 : Equation508 G) : Equation11 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h508 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h508 X1 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation508_implies_Equation16 (G : Type*) [Magma G] (h508 : Equation508 G) : Equation16 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h508 (X0 ◇ (X2 ◇ X2)) X1 (X0 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h508 X0 (X0 ◇ (X2 ◇ X2)) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h508 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h508 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

@[equational_result]
theorem Equation508_implies_Equation504 (G : Type*) [Magma G] (h508 : Equation508 G) : Equation504 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h508 (X0 ◇ (X2 ◇ X2)) X1 (X0 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h508 X0 (X0 ◇ (X2 ◇ X2)) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h508 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h508 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation508_implies_Equation40 (G : Type*) [Magma G] (h508 : Equation508 G) : Equation40 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h508 (X0 ◇ (X2 ◇ X2)) X1 (X0 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h508 X0 (X0 ◇ (X2 ◇ X2)) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h508 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h508 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l1 X0 sK0]
    conv => enter [1]; rw [l2 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation508_implies_Equation3269 (G : Type*) [Magma G] (h508 : Equation508 G) : Equation3269 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h508 (X0 ◇ (X2 ◇ X2)) X1 (X0 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h508 X0 (X0 ◇ (X2 ◇ X2)) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h508 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h508 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l1 X0 sK0]
    conv => enter [1]; rw [l2 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation508_implies_Equation3282 (G : Type*) [Magma G] (h508 : Equation508 G) : Equation3282 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h508 (X0 ◇ (X2 ◇ X2)) X1 (X0 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h508 X0 (X0 ◇ (X2 ◇ X2)) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h508 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h508 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l1 X0 sK0]
    conv => enter [1]; rw [l2 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1, 2]; rw [← l1 y y]

@[equational_result]
theorem Equation508_implies_Equation3297 (G : Type*) [Magma G] (h508 : Equation508 G) : Equation3297 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h508 (X0 ◇ (X2 ◇ X2)) X1 (X0 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h508 X0 (X0 ◇ (X2 ◇ X2)) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h508 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h508 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l1 X0 sK0]
    conv => enter [1]; rw [l2 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation508_implies_Equation4297 (G : Type*) [Magma G] (h508 : Equation508 G) : Equation4297 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h508 (X0 ◇ (X2 ◇ X2)) X1 (X0 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h508 X0 (X0 ◇ (X2 ◇ X2)) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h508 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h508 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [← l1 y z]

@[equational_result]
theorem Equation508_implies_Equation4290 (G : Type*) [Magma G] (h508 : Equation508 G) : Equation4290 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h508 (X0 ◇ (X2 ◇ X2)) X1 (X0 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h508 X0 (X0 ◇ (X2 ◇ X2)) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h508 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h508 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [← l1 y x]

theorem Equation510_4512_implies_Equation439 (G : Type*) [Magma G] (h510 : Equation510 G) (h4512 : Equation4512 G) : Equation439 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h510 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h510 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h510 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h510 X0 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l5 X0]
    conv => enter [1]; rw [← h510 X0 X1]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0]
    conv => enter [1, 2]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation420_4512_implies_Equation439 (G : Type*) [Magma G] (h420 : Equation420 G) (h4512 : Equation4512 G) : Equation439 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X2]
    conv => enter [1, 1]; rw [← h420 X0 X1]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l4 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h420 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l6 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h420 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [h420 sK0 X0]
    conv => enter [1]; rw [← l7 sK1 (sK0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h420 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK0 sK0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (X0 ◇ X0))]
  have l12 : ∀ sK1 sK0 X0 : G, sK1 = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 X0]
  have l13 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [l8 sK1 sK0 X1]
    conv => enter [1]; rw [← l3 X0 ((sK1 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X1))) (sK1 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l8 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l14 sK1 sK0]
  have l16 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = (X0 ◇ sK1) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l13 X0 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l12 sK1 sK0 X0]
  have l17 : ∀ X0 sK1 : G, (X0 ◇ sK1) = X0 := by
    intro X0 sK1
    conv => enter [1]; rw [← l16 X0 sK1 X0]
    conv => enter [1]; rw [← h420 X0 (sK1 ◇ (sK1 ◇ X0))]
  have l18 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l3 X0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2, 2]; rw [← l15 sK1 sK0]
  have l19 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l18 X0 sK1 sK0]
    conv => enter [1]; rw [← h420 X0 (sK1 ◇ (sK1 ◇ sK0))]
  have l20 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l17 sK0 sK1]
    conv => enter [1, 2]; rw [← l19 sK1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation522_4512_implies_Equation14 (G : Type*) [Magma G] (h522 : Equation522 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h522 X0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h522 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation522_4512_implies_Equation464 (G : Type*) [Magma G] (h522 : Equation522 G) (h4512 : Equation4512 G) : Equation464 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h522 X0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h522 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h522 X0 X1 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation522_4512_implies_Equation492 (G : Type*) [Magma G] (h522 : Equation522 G) (h4512 : Equation4512 G) : Equation492 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h522 X0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h522 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h522 X0 X1 X1]
  have l3 : ∀ sK1 sK2 : G, sK1 = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l1 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l2 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK1) sK2]
  have l5 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [← l4 sK2 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 (sK2 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1, 1]; rw [← l5 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation481_4512_implies_Equation14 (G : Type*) [Magma G] (h481 : Equation481 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h481 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h481 X2 (X0 ◇ X1) X3]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3)))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X3 ◇ X3)]
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
  have l3 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [l0 X2 X0 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation481_4512_implies_Equation464 (G : Type*) [Magma G] (h481 : Equation481 G) (h4512 : Equation4512 G) : Equation464 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h481 X0 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h481 (X1 ◇ X1) X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h481 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h481 X2 (X0 ◇ X1) X3]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3)))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X3 ◇ X3)]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [l1 X2 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X2 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [l4 X1 X1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l4 (sK0 ◇ sK1) sK0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l4 (X1 ◇ X1) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l4 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK1 sK0]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation481_4512_implies_Equation492 (G : Type*) [Magma G] (h481 : Equation481 G) (h4512 : Equation4512 G) : Equation492 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h481 X0 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h481 (X1 ◇ X1) X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h481 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h481 X2 (X0 ◇ X1) X3]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3)))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X3 ◇ X3)]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [l1 X2 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X2 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [l4 X1 X1]
  have l6 : ∀ sK1 sK2 : G, sK1 = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l4 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK2]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l4 (X1 ◇ X1) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l8 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [l4 (sK2 ◇ sK1) sK2]
  have l10 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← l9 sK2 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 (sK2 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1, 1]; rw [← l10 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation541_implies_Equation463 (G : Type*) [Magma G] (h541 : Equation541 G) : Equation463 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h541 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h541 X0 X1 (X1 ◇ X0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h541 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation433_4512_implies_Equation412 (G : Type*) [Magma G] (h433 : Equation433 G) (h4512 : Equation4512 G) : Equation412 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h433 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h433 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X0 X2]
    conv => enter [1]; rw [← h433 X1 (X2 ◇ X0) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l2 X1 X2 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h433 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x (x ◇ (x ◇ (x ◇ y)))]

theorem Equation543_4512_implies_Equation508 (G : Type*) [Magma G] (h543 : Equation543 G) (h4512 : Equation4512 G) : Equation508 G := by
  have l0 : ∀ sK0 sK2 X0 : G, sK0 = ((sK2 ◇ sK2) ◇ ((X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h543 sK0 (sK2 ◇ sK2) (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← h543 X0 sK0 (sK2 ◇ sK2)]
  have l1 : ∀ sK0 sK2 X0 : G, sK0 = ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK2 ◇ sK2)) X0]
  have l2 : ∀ sK2 X0 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ sK0)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h543 (sK2 ◇ sK2) X0 ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK2 X0]
  have l3 : ∀ sK2 X0 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l2 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) X0 sK0]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((X0 ◇ sK0) ◇ (sK2 ◇ sK2))) = X0 := by
    intro sK0 sK2 X0
    conv => enter [1, 2, 2]; rw [l3 sK2 X0 sK0]
    conv => enter [1]; rw [← h543 X0 (sK0 ◇ (sK2 ◇ sK2)) (X0 ◇ sK0)]
  have l5 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = X0 := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [h4512 X0 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l4 sK0 sK2 X0]
  have l6 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ X1) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [← l5 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK2 ◇ sK2))]
  have l7 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h543 (sK0 ◇ (sK2 ◇ sK2)) X0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [l5 sK0 sK2 X0]
  have l8 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))))) = X1 := by
    intro X0 sK0 sK2 X1
    conv => enter [1, 2, 2, 2]; rw [l7 sK0 sK2 X0]
    conv => enter [1]; rw [← h543 X1 X0 ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)]
  have l9 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))))) = X1 := by
    intro X0 sK0 sK2 X1
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ (sK2 ◇ sK2)) X0 (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l8 X0 sK0 sK2 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X0 X1 X0 X0]
    conv => enter [1]; rw [l9 X0 X0 X0 X1]
  have l11 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h543 sK0 sK2 sK2]
    conv => enter [1]; rw [l10 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l11 x z]
  conv => enter [1]; rw [← l10 y (x ◇ (z ◇ z))]

theorem Equation543_4512_implies_Equation3398 (G : Type*) [Magma G] (h543 : Equation543 G) (h4512 : Equation4512 G) : Equation3398 G := by
  have l0 : ∀ sK0 sK1 X0 : G, sK0 = (sK1 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h543 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h543 X0 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ sK1))) = X0 := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2, 2, 2]; rw [h543 sK1 sK0 sK2]
    conv => enter [1]; rw [← h543 X0 sK0 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l3 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h543 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← h543 sK1 sK0 sK2]
  have l4 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h543 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK1]
  have l5 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ X0) = (sK2 ◇ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1, 1]; rw [l3 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) X0]
  have l6 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ X0))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) sK1 X0]
  have l7 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l6 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ X0)]
  have l8 : ∀ sK0 sK2 sK1 : G, sK0 = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h543 sK0 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l2 sK0 sK2 sK1 sK0]
  have l9 : ∀ sK0 sK2 sK1 : G, sK0 = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l8 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l10 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (X0 ◇ sK0))) = X0 := by
    intro sK2 sK1 sK0 X0
    conv => enter [1, 2, 2, 2]; rw [l9 sK0 sK2 sK1]
    conv => enter [1]; rw [← h543 X0 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK1]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 (X0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0 sK0 X0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l11 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l13 : ∀ sK0 X0 : G, sK0 = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h543 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [l11 sK0 X0]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ sK0))) = X1 := by
    intro X0 sK0 X1
    conv => enter [1, 2, 2, 2]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← h543 X1 X0 (sK0 ◇ X0)]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ sK0)))) = X1 := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 sK0 X0 (X1 ◇ sK0)]
    conv => enter [1]; rw [l14 X0 sK0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l12 X0 X1 X0]
    conv => enter [1]; rw [l15 X0 X0 X1]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l16 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK1]
    conv => enter [1]; rw [l2 sK0 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

theorem Equation543_4512_implies_Equation4369 (G : Type*) [Magma G] (h543 : Equation543 G) (h4512 : Equation4512 G) : Equation4369 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK1 ◇ sK2) ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h543 sK0 (sK1 ◇ sK2) (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← h543 X0 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l2 : ∀ sK1 sK2 X0 : G, sK1 = (sK2 ◇ ((X0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h543 sK1 sK2 (X0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← h543 X0 sK1 sK2]
  have l3 : ∀ sK1 sK2 X0 : G, sK1 = (sK2 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h543 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h543 sK2 sK1 sK0]
  have l5 : ∀ sK0 sK2 sK1 : G, sK0 = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h543 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK0 sK2]
  have l6 : ∀ sK2 sK1 sK0 X0 : G, sK2 = ((sK1 ◇ sK0) ◇ ((X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h543 sK2 (sK1 ◇ sK0) (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← h543 X0 sK2 (sK1 ◇ sK0)]
  have l7 : ∀ sK2 sK1 sK0 X0 : G, sK2 = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l6 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l8 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h543 (sK1 ◇ sK2) X0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 sK2 X0]
  have l9 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l8 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
  have l10 : ∀ sK2 sK1 : G, sK2 = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [h543 sK2 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK2]
  have l11 : ∀ sK2 sK1 sK0 : G, sK2 = ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l7 sK2 sK1 sK0 (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK2 sK1]
  have l12 : ∀ sK2 sK1 sK0 : G, sK2 = ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l11 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 sK0]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((X0 ◇ sK0) ◇ (sK1 ◇ sK2))) = X0 := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2, 2]; rw [l9 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h543 X0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = X0 := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h4512 X0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0]
  have l15 : ∀ sK1 sK0 sK2 : G, sK1 = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h543 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l9 sK1 sK2 sK1 sK0]
  have l16 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK2))]
  have l17 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h543 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [l14 sK0 sK1 sK2 X0]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h543 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l15 sK1 sK0 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK0) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l10 sK2 sK1]
  have l20 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = X1 := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1, 2, 2, 2]; rw [l17 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h543 X1 X0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l21 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) = X1 := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) X0 (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l20 X0 sK0 sK1 sK2 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l16 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l21 X0 X0 X0 X0 X1]
  have l23 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK2) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l22 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l12 sK2 sK1 sK0]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

theorem Equation546_4512_implies_Equation464 (G : Type*) [Magma G] (h546 : Equation546 G) (h4512 : Equation4512 G) : Equation464 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h546 X0 X0 X1]
    conv => enter [1]; rw [← h546 X1 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X0 X1 X1]
  have l3 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X2 (X1 ◇ X1) X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X1 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l5 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l2 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X0 X2]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation546_4512_implies_Equation473 (G : Type*) [Magma G] (h546 : Equation546 G) (h4512 : Equation4512 G) : Equation473 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h546 X0 X0 X1]
    conv => enter [1]; rw [← h546 X1 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X0 X1 X1]
  have l3 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X2 (X1 ◇ X1) X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X1 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l5 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l2 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X0 X2]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation546_4512_implies_Equation504 (G : Type*) [Magma G] (h546 : Equation546 G) (h4512 : Equation4512 G) : Equation504 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h546 X0 X0 X1]
    conv => enter [1]; rw [← h546 X1 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X0 X1 X1]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation546_4512_implies_Equation562 (G : Type*) [Magma G] (h546 : Equation546 G) (h4512 : Equation4512 G) : Equation562 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h546 X0 X0 X1]
    conv => enter [1]; rw [← h546 X1 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X0 X1 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h546 (X1 ◇ X0) X0 X1]
  have l4 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X2 (X1 ◇ X1) X0]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X1 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l4 X1 X0 X2]
  have l6 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l2 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X0 X2]
  have l7 : ∀ sK0 sK2 sK1 : G, sK0 = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l6 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [← h546 sK1 sK0 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
    conv => enter [1]; rw [l3 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation546_4512_implies_Equation4369 (G : Type*) [Magma G] (h546 : Equation546 G) (h4512 : Equation4512 G) : Equation4369 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h546 X0 X0 X1]
    conv => enter [1]; rw [← h546 X1 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X0 X1 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h546 (X1 ◇ X0) X0 X1]
  have l4 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X2 (X1 ◇ X1) X0]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X1 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l4 X1 X0 X2]
  have l6 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l2 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X0 X2]
  have l7 : ∀ sK2 sK0 sK1 : G, sK2 = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h546 sK2 (sK0 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1, 2, 2]; rw [← h546 sK0 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK0) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l7 sK2 sK0 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 (sK1 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation546_4512_implies_Equation4290 (G : Type*) [Magma G] (h546 : Equation546 G) (h4512 : Equation4512 G) : Equation4290 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h546 X0 X0 X1]
    conv => enter [1]; rw [← h546 X1 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X0 X1 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [← l1 y x]

theorem Equation546_4512_implies_Equation417 (G : Type*) [Magma G] (h546 : Equation546 G) (h4512 : Equation4512 G) : Equation417 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h546 X0 X0 X1]
    conv => enter [1]; rw [← h546 X1 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X0 X1 X1]
  have l3 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X2 (X1 ◇ X1) X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X1 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l5 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l2 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1]; rw [← l2 x (y ◇ (x ◇ y))]

theorem Equation546_4512_implies_Equation452 (G : Type*) [Magma G] (h546 : Equation546 G) (h4512 : Equation4512 G) : Equation452 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h546 X0 X0 X1]
    conv => enter [1]; rw [← h546 X1 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X0 X1 X1]
  have l3 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X2 (X1 ◇ X1) X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X1 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l5 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l2 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X0 X2]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK1))) = X0 := by
    intro sK1 sK2 X0
    conv => enter [1, 2, 2, 2]; rw [← l5 (sK2 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1]; rw [← h546 X0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) (sK2 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (X0 ◇ sK1))) = X0 := by
    intro sK1 sK2 X0
    conv => enter [1, 2, 1]; rw [← l5 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0) = X0 := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← l5 sK1 X0]
    conv => enter [1]; rw [l7 sK1 sK2 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1]; rw [l8 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))))]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation556_implies_Equation562 (G : Type*) [Magma G] (h556 : Equation556 G) : Equation562 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h556 X1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h556 (X1 ◇ X0) X0 (X1 ◇ X0)]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h556 sK0 sK1 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h556 sK2 sK1 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK2 ◇ sK0)) sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation556_implies_Equation43 (G : Type*) [Magma G] (h556 : Equation556 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h556 X1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h556 (X1 ◇ X0) X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation489_4512_implies_Equation452 (G : Type*) [Magma G] (h489 : Equation489 G) (h4512 : Equation4512 G) : Equation452 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h489 (X0 ◇ X1) X0 X1]
    conv => enter [1]; rw [← h489 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK1))) = X0 := by
    intro sK2 sK1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 (sK2 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1]; rw [← h489 X0 (sK2 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
  have l2 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK1))) = X0 := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [← l0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 X0]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation558_implies_Equation463 (G : Type*) [Magma G] (h558 : Equation558 G) : Equation463 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h558 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← h558 (sK0 ◇ sK0) sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h558 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation443_4512_implies_Equation412 (G : Type*) [Magma G] (h443 : Equation443 G) (h4512 : Equation4512 G) : Equation412 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h443 (X0 ◇ (X1 ◇ X0)) X0 X1]
    conv => enter [1]; rw [← h443 X2 (X0 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X2 X0 X1]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l1 X2 X0 X1]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h443 X1 X0 X1]
    conv => enter [1]; rw [l2 X2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h443 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x (x ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation3254_implies_Equation307 (G : Type*) [Magma G] (h3254 : Equation3254 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3254 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h3254 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation3268_4512_implies_Equation307 (G : Type*) [Magma G] (h3268 : Equation3268 G) (h4512 : Equation4512 G) : Equation307 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3268 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h3268 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← h3268 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h3268 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [h3268 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← h3268 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x
  conv => enter [1]; rw [l7 x x]

@[equational_result]
theorem Equation3255_implies_Equation3253 (G : Type*) [Magma G] (h3255 : Equation3255 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3255 x x]

@[equational_result]
theorem Equation3258_implies_Equation3253 (G : Type*) [Magma G] (h3258 : Equation3258 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3258 x x]

@[equational_result]
theorem Equation3256_implies_Equation3253 (G : Type*) [Magma G] (h3256 : Equation3256 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3256 x x]

@[equational_result]
theorem Equation3278_implies_Equation3253 (G : Type*) [Magma G] (h3278 : Equation3278 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3278 x x]

@[equational_result]
theorem Equation3257_implies_Equation3254 (G : Type*) [Magma G] (h3257 : Equation3257 G) : Equation3254 G := by
  intro x y
  conv => enter [1]; rw [h3257 x x y]

@[equational_result]
theorem Equation3257_implies_Equation3256 (G : Type*) [Magma G] (h3257 : Equation3257 G) : Equation3256 G := by
  intro x y
  conv => enter [1]; rw [h3257 x y y]

@[equational_result]
theorem Equation3257_implies_Equation3255 (G : Type*) [Magma G] (h3257 : Equation3257 G) : Equation3255 G := by
  intro x y
  conv => enter [1]; rw [h3257 x y x]

@[equational_result]
theorem Equation3288_implies_Equation3268 (G : Type*) [Magma G] (h3288 : Equation3288 G) : Equation3268 G := by
  intro x y
  conv => enter [1]; rw [h3288 x y x]

@[equational_result]
theorem Equation3288_implies_Equation3278 (G : Type*) [Magma G] (h3288 : Equation3288 G) : Equation3278 G := by
  intro x y
  conv => enter [1]; rw [h3288 x y y]

end Semigroup4
