import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53871_implies_Equation53882 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53871 : Equation53871 G) : Equation53882 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h53871 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
    conv => enter [1]; rw [← h53871 (X0 ◇ X1) X2 X3]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53871 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ X0)]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53871 X0 X1 (X1 ◇ X2)]
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1]; rw [← l0 X0 X1 X2 (X1 ◇ X0)]
  have l8 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ X0) X1]
  have l9 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l8 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l10 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l9 sK1 sK2 X1 sK1]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK0)]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l11 sK1 sK2 sK1]
  have l13 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53871 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h53871 sK1 X0 sK0]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l13 sK1 X0 sK1]
  have l15 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l14 sK1 X0]
    conv => enter [1]; rw [h53871 sK1 sK1 sK2]
  have l16 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [← l15 sK1 X0 sK2]
  have l17 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l16 sK1 sK2 sK3]
    conv => enter [1]; rw [h53871 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l17 x y z w]

theorem Equation4512_53882_implies_Equation53871 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53882 : Equation53882 G) : Equation53871 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53882 sK0 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53882 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h53882 sK0 X0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_53874_implies_Equation53887 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53874 : Equation53874 G) : Equation53887 G := by
  have l0 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ sK0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h53874 X1 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53874 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h53874 sK0 (sK2 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK0)) ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0)]
  have l3 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h53874 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ X0)]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h53874 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← h53874 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0]
  have l6 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l0 X1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53874 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
  have l8 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l6 X1 sK0 sK1 X0]
    conv => enter [1]; rw [h53874 X1 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1 sK0]
  have l10 : ∀ sK2 sK0 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ X1) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK2 sK0 X1 X0
    conv => enter [1, 1]; rw [l3 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ X0) X1]
  have l11 : ∀ sK2 sK0 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ X1) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l10 sK2 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l12 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l3 sK2 sK0 (sK2 ◇ X1)]
    conv => enter [1]; rw [← l11 sK2 sK0 X1 sK2]
  have l13 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [l12 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK0)) X0]
  have l14 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l13 sK0 sK2 ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)]
    conv => enter [1]; rw [← h53874 X0 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0]
  have l15 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ X0) X1]
  have l16 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l17 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l16 sK0 sK1 X1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l19 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK2)) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK0)) ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK2)]
    conv => enter [1, 2]; rw [h53874 (sK2 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l20 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK0)) (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l19 sK0 sK2]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2 sK2]
    conv => enter [1]; rw [← l20 sK0 sK2]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l13 sK0 sK2 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l21 sK0 sK2]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0 sK0 sK2]
    conv => enter [1]; rw [← h53874 sK0 sK0 (sK2 ◇ (sK2 ◇ sK0))]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53874 sK0 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK2]
  have l25 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [← l24 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l26 x y z]

theorem Equation4512_53887_implies_Equation53874 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53887 : Equation53887 G) : Equation53874 G := by
  have l0 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h53887 sK1 ((sK1 ◇ sK2) ◇ X0) sK0]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53887 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [h53887 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← h53887 sK1 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l3 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK1 sK2 X0 sK0]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53887 sK1 sK2 sK1]
    conv => enter [1]; rw [← l3 sK1 sK2 X0 sK1]
  have l5 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53887 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)]
  intro x y z
  conv => enter [1]; rw [l5 x y y z]

theorem Equation4512_53874_implies_Equation53889 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53874 : Equation53874 G) : Equation53889 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ X0)]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l0 sK2 X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l2 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l4 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK2
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) sK2]
  have l5 : ∀ sK2 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l6 : ∀ sK2 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l5 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l7 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1, 2]; rw [← l4 sK2]
  have l8 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l4 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) sK2 X0]
  have l9 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [l8 sK2 X0]
  have l10 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ sK0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h53874 X1 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53874 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l12 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h53874 sK0 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK2)) ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)]
  have l13 : ∀ sK2 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ X0))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [h53874 sK2 X0 X1]
    conv => enter [1]; rw [← l9 sK2 (X0 ◇ (X0 ◇ X1))]
  have l14 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ X0))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [h53874 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK2 (X0 ◇ (X0 ◇ X1))]
  have l15 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [h53874 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (X0 ◇ X1))]
  have l16 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h53874 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (X0 ◇ X1))]
  have l17 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [h53874 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l3 sK2 (X0 ◇ (X0 ◇ X1))]
  have l18 : ∀ sK2 X0 X1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [h53874 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) (X0 ◇ (X0 ◇ X1))]
  have l19 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l18 sK2 X0 sK2]
    conv => enter [1]; rw [← h53874 (sK2 ◇ (sK2 ◇ sK2)) X0 sK2]
  have l20 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [l17 sK2 X0 sK2]
    conv => enter [1, 2]; rw [← h53874 (sK2 ◇ (sK2 ◇ sK2)) X0 sK2]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← h53874 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0]
  have l22 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l15 sK2 X0 sK2]
    conv => enter [1]; rw [← h53874 (sK2 ◇ sK2) X0 sK2]
  have l23 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ X0))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l14 sK2 X0 sK2]
    conv => enter [1]; rw [← h53874 (sK2 ◇ (sK2 ◇ sK2)) X0 sK2]
  have l24 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ X0))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [l13 sK2 X0 sK2]
    conv => enter [1, 2]; rw [← h53874 (sK2 ◇ (sK2 ◇ sK2)) X0 sK2]
  have l25 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l10 X1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l26 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h53874 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l19 sK2 X0]
  have l27 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [h53874 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [← l20 sK2 X0]
  have l28 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53874 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l21 sK0 sK1 X0]
  have l29 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ X0))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l22 sK2 X0]
    conv => enter [1]; rw [l3 sK2 X0]
  have l30 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h53874 (sK2 ◇ sK2) sK2 X0]
    conv => enter [1]; rw [l23 sK2 X0]
  have l31 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [h53874 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [← l24 sK2 X0]
  have l32 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l25 X1 sK0 sK1 X0]
    conv => enter [1]; rw [h53874 X1 sK0 sK1]
  have l33 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l26 sK2 X0]
  have l34 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l27 sK2 sK2]
    conv => enter [1]; rw [← h53874 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2]
  have l35 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h53874 sK2 sK2 X0]
    conv => enter [1]; rw [l29 sK2 X0]
  have l36 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h53874 (sK2 ◇ sK2) sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l30 sK2 X0]
  have l37 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l31 sK2 sK2]
    conv => enter [1]; rw [← h53874 (sK2 ◇ (sK2 ◇ sK2)) sK2 sK2]
  have l38 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l33 sK2 X0]
  have l39 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l34 sK2]
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ sK2)]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1 sK0]
    conv => enter [1]; rw [l32 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1 sK0]
  have l41 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l35 sK2 X0]
  have l42 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l36 sK2 X0]
    conv => enter [1]; rw [← l1 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l43 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [l37 sK2]
    conv => enter [1]; rw [h53874 (sK2 ◇ (sK2 ◇ sK2)) sK2 (sK2 ◇ sK2)]
  have l44 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [l39 sK2]
    conv => enter [1, 2]; rw [l6 sK2]
  have l45 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l41 sK2 X0]
  have l46 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l38 sK2 sK2]
    conv => enter [1]; rw [l42 sK2 sK2]
  have l47 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [l43 sK2]
    conv => enter [1]; rw [← l9 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l48 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l44 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) (sK2 ◇ (sK2 ◇ sK2))]
  have l49 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [l45 sK2 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l47 sK2]
  have l50 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [l46 sK2]
    conv => enter [1]; rw [← l48 sK2]
  have l51 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l49 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l52 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l50 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l53 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l51 sK2]
    conv => enter [1]; rw [← l52 sK2]
  have l54 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l53 sK2]
    conv => enter [1]; rw [← l7 sK0 sK2]
  have l55 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l53 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l56 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l45 sK2 X0]
    conv => enter [1]; rw [← l55 sK2 X0]
  have l57 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [l56 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l58 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h53874 X0 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) sK2]
    conv => enter [1, 2, 2]; rw [← l54 sK0 sK2]
  have l59 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l57 sK0 sK2 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l58 X0 sK0 sK2]
  have l60 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ X0) X1]
  have l61 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l60 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l62 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l11 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l61 sK0 sK1 X1 sK0]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l40 sK0 sK1]
  have l64 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ sK2)) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK2)) ((sK2 ◇ (sK2 ◇ sK2)) ◇ sK2)]
    conv => enter [1, 2]; rw [h53874 (sK2 ◇ (sK2 ◇ sK2)) sK2 sK2]
  have l65 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK2)) (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l64 sK0 sK2]
  have l66 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l12 sK0 sK2 sK2]
    conv => enter [1]; rw [← l65 sK0 sK2]
  have l67 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l57 sK0 sK2 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l66 sK0 sK2]
  have l68 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l59 sK0 sK0 sK2]
    conv => enter [1]; rw [← h53874 sK0 sK0 (sK2 ◇ (sK2 ◇ sK2))]
  have l69 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53874 sK0 sK0 sK1]
    conv => enter [1]; rw [← l68 sK0 sK2]
  have l70 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l67 sK0 sK2]
    conv => enter [1]; rw [← l69 sK0 sK1 sK2]
  have l71 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [← l70 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l71 x y z]

theorem Equation4512_53889_implies_Equation53874 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53889 : Equation53889 G) : Equation53874 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53889 X0 X1 X0]
    conv => enter [1]; rw [← h53889 X0 X2 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK2]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53889 X0 X1 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← l4 sK1 sK2 X0]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l5 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l7 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53889 X0 X1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l8 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l3 X0 X0 sK1 sK2]
    conv => enter [1]; rw [l7 X0 X0 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_53874_implies_Equation53890 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53874 : Equation53874 G) : Equation53890 G := by
  have l0 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ sK1)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h53874 X1 sK1 (sK2 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53874 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ X0)]
  have l2 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h53874 sK1 (sK3 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK3 ◇ sK0)) ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)]
  have l3 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h53874 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK3 sK0 (sK0 ◇ X0)]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [h53874 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← h53874 (sK1 ◇ (sK1 ◇ sK2)) X0 sK1]
  have l6 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [l0 X1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53874 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l5 sK1 sK2 X0]
  have l8 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [← l6 X1 sK1 sK2 X0]
    conv => enter [1]; rw [h53874 X1 sK1 sK2]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2 sK1]
    conv => enter [1]; rw [l8 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2 sK1]
  have l10 : ∀ sK3 sK0 X1 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X1) = ((sK3 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK3 sK0 X1 X0
    conv => enter [1, 1]; rw [l3 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK0) (sK0 ◇ X0) X1]
  have l11 : ∀ sK3 sK0 X1 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X1) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 X1 X0
    conv => enter [1]; rw [l10 sK3 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l12 : ∀ sK3 sK0 X1 : G, (sK3 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ X1) := by
    intro sK3 sK0 X1
    conv => enter [1]; rw [l3 sK3 sK0 (sK3 ◇ X1)]
    conv => enter [1]; rw [← l11 sK3 sK0 X1 sK3]
  have l13 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1, 2]; rw [l12 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l14 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1, 2]; rw [l13 sK1 sK3 sK0 ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0)]
    conv => enter [1]; rw [← h53874 X0 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) X0]
  have l15 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK2 ◇ X0) X1]
  have l16 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l15 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l17 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l16 sK1 sK2 X1 sK1]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l9 sK1 sK2]
  have l19 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3)) = (sK1 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK3 ◇ sK0)) ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3)]
    conv => enter [1, 2]; rw [h53874 (sK3 ◇ (sK3 ◇ sK0)) sK3 sK0]
  have l20 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK3 ◇ sK0)) (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l19 sK1 sK3 sK0]
  have l21 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK3 sK0 sK3]
    conv => enter [1]; rw [← l20 sK1 sK3 sK0]
  have l22 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l13 sK1 sK3 sK0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l21 sK1 sK3 sK0]
  have l23 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l14 sK1 sK1 sK3 sK0]
    conv => enter [1]; rw [← h53874 sK1 sK1 (sK3 ◇ (sK3 ◇ sK0))]
  have l24 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h53874 sK1 sK1 sK2]
    conv => enter [1]; rw [← l23 sK1 sK3 sK0]
  have l25 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l22 sK1 sK3 sK0]
    conv => enter [1]; rw [← l24 sK1 sK2 sK3 sK0]
  have l26 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [← l25 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l26 x y z w]

@[equational_result]
theorem Equation53890_implies_Equation53874 (G : Type*) [Magma G] (h53890 : Equation53890 G) : Equation53874 G := by
  intro x y z
  conv => enter [1]; rw [h53890 x y y z]

theorem Equation4512_53875_implies_Equation53883 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53875 : Equation53875 G) : Equation53883 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l3 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l7 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ X0) ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ X0) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h53875 (sK0 ◇ X0) X1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l8 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h53875 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l9 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK2)) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h53875 X0 sK2 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ sK0) X0]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53875 X0 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1 X0]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h53875 X0 X1 X2]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53875 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (X0 ◇ sK0)]
    conv => enter [1]; rw [← h53875 sK0 (sK0 ◇ sK1) X0]
  have l14 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ sK0)]
    conv => enter [1]; rw [← h53875 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l15 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l1 sK0 sK1 (X0 ◇ (X1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h53875 sK0 X0 X1]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h53875 sK1 sK0 X0]
  have l17 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l15 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ X0)]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53875 X0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l10 X0 sK0 sK1]
  have l20 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ X0) ◇ ((sK0 ◇ X0) ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l7 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [l17 sK0 sK1 X0 sK0]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l23 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ ((sK0 ◇ X0) ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l20 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h53875 X0 X1 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [l21 sK0 sK1 X0]
  have l25 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l22 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l26 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ X0) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l23 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK0 ◇ X0) ◇ X1)]
  have l27 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l25 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l28 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l26 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 X0 X1]
  have l29 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ sK0)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h53875 sK0 (sK1 ◇ sK0) sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h53875 sK0 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK0)]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h53875 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l33 sK0 sK1]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l36 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l44 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
  have l45 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK1 sK0]
    conv => enter [1]; rw [l44 sK2 sK1 sK0]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h53875 sK1 sK0 sK0]
  have l47 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l46 sK1 sK0]
  have l48 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l45 sK2 sK1 sK0]
  have l49 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l48 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
  have l50 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [l16 sK1 sK0 X0]
  have l51 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1, 2]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← l50 sK2 sK1 sK0 X0]
  have l52 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK0]
    conv => enter [1]; rw [l51 sK2 sK1 sK0 X0]
  have l53 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l14 sK0 sK2 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l54 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [l14 sK0 sK2 sK1 sK0]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l54 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l56 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l55 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
  have l57 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l55 sK0 sK1 sK2]
    conv => enter [1]; rw [← h53875 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 (sK1 ◇ sK0)]
  have l58 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l14 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l57 sK0 sK2 sK1]
  have l59 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l58 sK0 sK2 sK1]
    conv => enter [1]; rw [l49 sK0 sK2 sK1]
  have l60 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53875 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2, 2]; rw [l19 sK0 sK0 sK1]
  have l61 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l60 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l62 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l61 sK0 X0 sK1]
    conv => enter [1]; rw [← l27 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l63 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l62 sK0 X0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l64 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← l63 sK0 X0 sK1]
  have l65 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l64 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l66 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l65 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
  have l67 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l66 sK0 sK1 X0]
    conv => enter [1]; rw [← l37 sK0 sK1 (sK0 ◇ X0)]
  have l68 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l67 sK0 sK1 X0]
    conv => enter [1]; rw [← h53875 X0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l69 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l67 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ X0) X1]
  have l70 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l69 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l71 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l67 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l70 sK0 sK1 X1 sK0]
  have l72 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53875 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l71 sK0 sK1 X0]
  have l73 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l71 sK0 sK1 sK0]
  have l74 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53875 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h53875 (sK0 ◇ sK1) X0 sK0]
  have l75 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l73 sK0 sK1 X0]
    conv => enter [1]; rw [← l74 X0 sK0 sK1]
  have l76 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l75 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))]
  have l77 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l76 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l78 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l77 sK2 sK1 sK0]
  have l79 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l45 sK2 sK1 sK0]
    conv => enter [1]; rw [l78 sK2 sK1 sK0]
  have l80 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l52 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ sK1)]
  have l81 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l80 sK0 sK2 sK1 X0]
  have l82 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l59 sK0 sK2 sK1]
    conv => enter [1]; rw [l81 sK0 sK2 sK1 X0]
  have l83 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h53875 (sK1 ◇ sK0) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [← l53 sK0 sK2 sK1]
  have l84 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l56 sK1 sK0 sK2]
    conv => enter [1]; rw [l83 sK1 sK0 sK2]
  have l85 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l79 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l86 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l85 sK0 sK2 sK1]
  have l87 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l59 sK0 sK2 sK1]
    conv => enter [1]; rw [l86 sK0 sK2 sK1]
  have l88 : ∀ sK0 sK2 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X1) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK2 sK1 X1 X0
    conv => enter [1, 1]; rw [l82 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (X0 ◇ sK1) X1]
  have l89 : ∀ sK0 sK2 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X1) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK0 sK2 sK1 X1 X0
    conv => enter [1]; rw [l88 sK0 sK2 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l90 : ∀ sK0 sK2 sK1 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X1)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK0 sK2 sK1 X1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X1]
    conv => enter [1]; rw [l89 sK0 sK2 sK1 X1 X0]
  have l91 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h53875 (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l84 sK1 sK0 sK2]
  have l92 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l91 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l93 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l92 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← l90 sK0 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l94 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l93 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← l72 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 sK1]
  have l95 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l37 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l94 sK0 sK2 sK1 X0]
  have l96 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l95 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)]
  have l97 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l96 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l98 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l97 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l28 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l99 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l67 sK0 sK1 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l98 sK0 sK1 sK2 X0]
  have l100 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l87 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l101 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l100 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l102 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l101 sK0 sK2 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l71 sK0 sK1 X0]
  have l103 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l87 sK0 sK2 sK1]
    conv => enter [1]; rw [← l102 sK0 sK2 sK1 X0]
  have l104 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l103 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l105 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l99 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l68 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 sK1]
  have l106 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l105 sK0 sK1 sK2]
    conv => enter [1]; rw [← l104 sK0 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l107 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l9 sK0 sK2 sK1 sK0]
  have l108 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h53875 sK0 sK2 sK1]
    conv => enter [1]; rw [← l107 sK0 sK2 sK1]
  have l109 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l108 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l110 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l14 sK0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l109 sK0 sK2 sK1 sK0]
  have l111 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l108 sK0 sK2 sK1]
    conv => enter [1]; rw [← l110 sK0 sK2 sK1]
  have l112 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l106 sK0 sK1 sK2]
    conv => enter [1]; rw [← l111 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l112 x y z]

theorem Equation4512_53883_implies_Equation53875 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53883 : Equation53883 G) : Equation53875 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK0) X0]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l2 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53883 X0 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← l1 sK2 sK0 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h53883 sK0 X0 sK1]
  have l4 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53883 X0 sK1 (X0 ◇ sK0)]
    conv => enter [1]; rw [← l2 X0 sK0 sK1 X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h53883 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1 X0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53883 (sK0 ◇ (sK0 ◇ sK1)) X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l8 sK0 sK1 X0]
    conv => enter [1]; rw [l12 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← l14 sK0 sK1 X0]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← l16 sK0 sK1 X0]
  have l18 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53883 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l17 sK0 sK1 (X1 ◇ X0)]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← h53883 sK0 sK2 sK1]
  have l20 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK0 sK2 sK0 sK1]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l22 x y z]

theorem Equation4512_53875_implies_Equation53891 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53875 : Equation53875 G) : Equation53891 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK1 ◇ sK2)]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK2) X0]
  have l2 : ∀ sK0 sK1 sK3 X0 : G, (sK0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK3 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK3 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 sK3 X0 : G, (sK0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK3 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK3 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK3 ◇ (sK0 ◇ sK1)) X0]
  have l4 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ X1)) = ((sK1 ◇ X0) ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h53875 (sK1 ◇ X0) X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h53875 X0 X1 X2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53875 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ sK1)]
  have l7 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK1)) (X0 ◇ sK1)]
    conv => enter [1]; rw [← h53875 sK1 (sK3 ◇ (sK0 ◇ sK1)) X0]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l9 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l4 sK1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK1 X0 (X1 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l11 : ∀ sK1 X0 X1 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ X1)) = (sK1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l9 sK1 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h53875 X0 X1 (sK1 ◇ sK1)]
  have l12 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l10 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l13 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X1))) = (sK1 ◇ (X0 ◇ ((sK1 ◇ X0) ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l11 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 X0 ((sK1 ◇ X0) ◇ X1)]
  have l14 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l12 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l15 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l13 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 X0 X1]
  have l16 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l17 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l18 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h53875 (sK0 ◇ sK1) X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK2 sK0]
  have l19 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ sK1) X0]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2 (sK1 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 sK1]
  have l21 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l16 sK1 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2]; rw [l7 sK1 sK3 sK0 sK1]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l20 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l23 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l16 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK3 ◇ (sK0 ◇ sK1))]
  have l24 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l21 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))]
  have l25 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [h53875 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) (sK1 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← l21 sK1 sK2 sK3 sK0]
  have l26 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l22 sK1 sK2]
  have l27 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l26 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l28 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h53875 sK1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [l28 sK0 sK1 X0]
  have l30 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK3)) := by
    intro sK0 sK1 sK3
    conv => enter [1, 2]; rw [← h53875 sK1 sK3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK3)]
  have l31 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK3) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1, 1]; rw [← h53875 sK1 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK3) X0]
  have l32 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK3 ◇ X0))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l31 sK1 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK3 X0]
  have l33 : ∀ sK0 sK1 sK3 : G, ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK3)) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l30 sK0 sK1 sK3]
  have l34 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK3)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK2 (sK1 ◇ sK3) sK0]
    conv => enter [1, 2]; rw [← l33 sK0 sK1 sK3]
  have l35 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK1 sK2 sK1 sK1]
  have l36 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l16 sK1 sK2 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l19 sK1 sK2 (sK0 ◇ sK1) sK0]
  have l37 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK2 (sK3 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l34 sK1 sK2 sK3 sK0]
  have l38 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l23 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l37 sK1 sK2 sK3 sK1]
  have l39 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK2 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l35 sK1 sK2]
  have l40 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l7 sK1 sK3 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l35 sK1 sK2]
  have l41 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53875 sK1 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l35 sK1 sK2]
  have l42 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l35 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) sK1 X0]
  have l43 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l36 sK1 sK2 sK1]
    conv => enter [1]; rw [← l17 sK1 sK2 sK1]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l36 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
  have l45 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l36 sK1 sK2 sK1]
    conv => enter [1]; rw [← h53875 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l46 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l45 sK1 sK2]
    conv => enter [1]; rw [← l41 sK1 sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [← l29 sK0 sK1 (sK1 ◇ sK2)]
  have l48 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [l46 sK1 sK2]
  have l49 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
  have l50 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l51 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l39 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l52 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [l51 sK1 sK2 X0]
  have l53 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1, 2]; rw [l40 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 sK1 sK3 (sK1 ◇ (sK1 ◇ sK2))]
  have l54 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l53 sK0 sK1 sK3 sK0]
    conv => enter [1]; rw [← l18 sK0 sK1 (sK3 ◇ (sK0 ◇ sK1)) sK0]
  have l55 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l54 sK0 sK1 sK3]
    conv => enter [1]; rw [← h53875 (sK0 ◇ sK1) (sK0 ◇ sK1) sK3]
  have l56 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1]; rw [l55 sK0 sK1 sK3]
    conv => enter [1]; rw [l18 sK0 sK1 (sK0 ◇ sK1) sK2]
  have l57 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1]; rw [l56 sK0 sK1 sK3 sK2]
    conv => enter [1]; rw [h53875 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK2)) sK3]
  have l58 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK3 sK2]
    conv => enter [1, 2]; rw [← l23 sK1 sK2 sK3 sK0]
  have l59 : ∀ sK0 sK1 sK2 sK3 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1, 2]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [← l58 sK0 sK1 sK3 sK2]
  have l60 : ∀ sK0 sK1 sK2 sK3 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l59 sK0 sK1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l61 : ∀ sK0 sK1 sK2 sK3 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l49 sK0 sK1 sK2]
    conv => enter [1]; rw [l60 sK0 sK1 sK2 sK3]
  have l62 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l48 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l63 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l62 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
  have l64 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l49 sK0 sK1 sK2]
  have l65 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l64 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK1) (sK1 ◇ sK2)]
  have l66 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l52 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
  have l67 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l52 sK1 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l40 sK1 sK3 sK0 sK2]
  have l68 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l67 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l42 sK1 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l69 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l66 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← h53875 (sK1 ◇ (sK1 ◇ sK2)) X0 sK1]
  have l70 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l61 sK0 sK1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK1) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l71 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l70 sK3 sK0 sK1 sK2]
  have l72 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l65 sK3 sK0 sK1 sK2]
  have l73 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l72 sK1 sK3 sK0 sK2]
  have l74 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l40 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l73 sK1 sK3 sK0 sK2]
  have l75 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h53875 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l69 sK1 sK2 X0]
  have l76 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l69 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) X1]
  have l77 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l76 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
  have l78 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l75 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) X0 (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l79 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l77 sK1 sK2 X1 X0]
    conv => enter [1]; rw [l27 sK1 sK2 (X0 ◇ X1)]
  have l80 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l78 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53875 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
  have l81 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l50 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← l79 sK1 sK2 X1 X0]
  have l82 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l80 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l27 sK1 sK2 X0]
  have l83 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l50 sK1 sK2 X0]
    conv => enter [1]; rw [← l82 sK1 sK2 X0 X1]
  have l84 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l83 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) X0 (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)]
  have l85 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l84 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l81 sK1 sK2 X0 (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)]
  have l86 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l85 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l81 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) X1]
  have l87 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l71 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l88 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l87 sK1 sK3 sK0 sK2]
  have l89 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l74 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l88 sK1 sK3 sK0 sK1]
  have l90 : ∀ sK1 sK3 sK0 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1, 1]; rw [l74 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) (sK1 ◇ sK2) X0]
  have l91 : ∀ sK1 sK3 sK0 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l90 sK1 sK3 sK0 X0 sK2]
  have l92 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l68 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l86 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l93 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l89 sK1 sK3 sK0]
  have l94 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l93 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) X0]
  have l95 : ∀ sK1 sK3 sK0 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [h53875 (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l24 sK1 sK2 sK3 sK0]
  have l96 : ∀ sK1 sK3 sK0 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [l95 sK1 sK3 sK0 X0 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l97 : ∀ sK1 sK3 sK0 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [l96 sK1 sK3 sK0 X0 sK2]
    conv => enter [1]; rw [← l14 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l98 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l97 sK1 sK3 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l41 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK1]
  have l99 : ∀ sK1 sK3 sK0 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [l98 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← l63 sK1 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l100 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l68 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l99 sK1 sK3 sK0 X0 sK2]
  have l101 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l100 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0)]
  have l102 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l101 sK1 sK2 sK3 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) X0]
  have l103 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l102 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← l15 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) X0]
  have l104 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l103 sK1 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [l94 sK1 sK3 sK0 X0]
  have l105 : ∀ sK1 sK3 sK0 sK2 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1, 1]; rw [← l25 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) X0]
  have l106 : ∀ sK1 sK3 sK0 sK2 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l105 sK1 sK3 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) (sK1 ◇ sK2) X0]
  have l107 : ∀ sK1 sK3 sK0 sK2 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l106 sK1 sK3 sK0 sK2 X0]
    conv => enter [1]; rw [l94 sK1 sK3 sK0 ((sK1 ◇ sK2) ◇ X0)]
  have l108 : ∀ sK1 sK3 sK0 sK2 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l107 sK1 sK3 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l91 sK1 sK3 sK0 X0 sK2]
  have l109 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l104 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← l108 sK1 sK3 sK0 sK2 X0]
  have l110 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l109 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l111 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l110 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l92 sK1 sK2 sK1]
  have l112 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l111 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l40 sK1 sK3 sK0 sK2]
  have l113 : ∀ sK1 sK3 X0 sK2 : G, ((sK1 ◇ sK3) ◇ ((sK1 ◇ sK3) ◇ X0)) = ((sK1 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK3 X0 sK2
    conv => enter [1]; rw [h53875 (sK1 ◇ sK3) X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l38 sK1 sK2 sK3]
  have l114 : ∀ sK1 sK3 X0 sK2 : G, ((sK1 ◇ sK3) ◇ ((sK1 ◇ sK3) ◇ X0)) = (sK1 ◇ (sK3 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK3 X0 sK2
    conv => enter [1]; rw [l113 sK1 sK3 X0 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK3 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l115 : ∀ sK1 sK3 X0 sK2 : G, ((sK1 ◇ sK3) ◇ ((sK1 ◇ sK3) ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK3 X0 sK2
    conv => enter [1]; rw [l114 sK1 sK3 X0 sK2]
    conv => enter [1]; rw [← l14 sK1 sK3 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l116 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK3) ◇ ((sK1 ◇ sK3) ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l32 sK1 sK3 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l115 sK1 sK3 X0 sK2]
  have l117 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK3 ◇ ((sK1 ◇ sK3) ◇ X0))) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l116 sK1 sK3 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 sK3 ((sK1 ◇ sK3) ◇ X0)]
  have l118 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ X0)))) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l117 sK1 sK3 sK0 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK3 X0]
  have l119 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK3 ◇ (sK3 ◇ X0))) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l118 sK1 sK3 sK0 sK2 X0]
    conv => enter [1]; rw [← l15 sK1 sK3 X0]
  have l120 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK3 ◇ (sK3 ◇ X0))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l40 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l119 sK1 sK3 sK0 sK1 X0]
  have l121 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ X0))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l112 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l120 sK1 sK3 sK1 X0]
  have l122 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l121 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← h53875 sK1 sK3 sK3]
  have l123 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l122 sK1 sK2 sK3]
    conv => enter [1]; rw [h53875 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l123 x y z w]

theorem Equation4512_53891_implies_Equation53875 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53891 : Equation53891 G) : Equation53875 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← h53891 sK0 X0 sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
  have l2 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [h53891 sK0 sK0 X1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53891 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l2 sK0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_53877_implies_Equation53894 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53877 : Equation53877 G) : Equation53894 G := by
  have l0 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53877 X0 X1 X2]
    conv => enter [1]; rw [h53877 X0 X1 X3]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53877 X0 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l3 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [h53877 X0 sK1 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK0)) (sK3 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53877 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53877 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ X0)]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53877 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X0 ◇ X0)]
  have l7 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h53877 sK1 (sK3 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK0)) (X0 ◇ X0)]
  have l8 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK0) (X0 ◇ X0)]
    conv => enter [1]; rw [← h53877 sK3 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53877 X0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 X0]
  have l12 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l5 sK1 sK2 X0]
  have l13 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l12 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l15 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ sK0) X0]
  have l16 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l14 sK1 sK2 sK0]
  have l17 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l16 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l18 : ∀ sK1 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) ◇ X1) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l7 sK1 sK3 sK0 X0]
  have l19 : ∀ sK1 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ ((X0 ◇ X0) ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l18 sK1 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) X1]
  have l20 : ∀ sK1 sK3 sK0 X1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ X1)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK3 sK0 X1 X0
    conv => enter [1]; rw [← l19 sK1 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l21 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1, 2]; rw [l10 sK0 X0]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK0) (X0 ◇ X0)]
  have l22 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l21 sK3 sK0 sK3]
    conv => enter [1]; rw [l8 sK3 sK0 sK3]
  have l23 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l22 sK3 sK0]
    conv => enter [1]; rw [← l8 sK3 sK0 sK0]
  have l24 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l0 sK3 sK0]
    conv => enter [1]; rw [l23 sK3 sK0]
  have l25 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 sK0 sK0]
  have l26 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l24 sK3 sK0]
  have l27 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l26 sK1 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK0)) sK0]
  have l28 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l7 sK1 sK3 sK0 sK0]
    conv => enter [1]; rw [l27 sK1 sK3 sK0]
  have l29 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l11 (sK1 ◇ sK2) sK1 sK2]
  have l30 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l29 sK1 sK2]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l30 sK1 sK2]
  have l32 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← h53877 X0 X1 X2]
    conv => enter [1]; rw [h53877 X0 X1 sK0]
  have l33 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l15 sK1 sK2 sK0 sK0]
  have l34 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [l11 (sK0 ◇ sK0) sK1 sK2]
  have l35 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l15 sK1 sK2 (X0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← h53877 (sK0 ◇ sK0) X0 sK0]
  have l36 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h53877 (sK1 ◇ sK2) (sK0 ◇ sK0) sK0]
  have l37 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53877 (sK1 ◇ sK2) (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l36 sK1 sK2 sK0]
  have l38 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l13 sK1 sK2 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l35 sK1 sK2 X0 sK0]
  have l39 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [← l34 sK1 sK2 sK0]
  have l40 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l25 sK1 sK2 sK0]
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
  have l41 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2 sK1]
    conv => enter [1]; rw [← l37 sK1 sK2 sK1]
  have l42 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l39 sK1 sK2 sK1]
    conv => enter [1]; rw [l17 sK1 sK2 sK1 (sK1 ◇ sK2)]
  have l43 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l41 sK1 sK2]
  have l44 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l42 sK1 sK2]
    conv => enter [1]; rw [← l2 sK1 sK1 sK2]
  have l45 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [l44 sK1 sK2]
  have l46 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [l45 sK1 sK2]
  have l47 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l40 sK1 sK2 sK0]
    conv => enter [1]; rw [h53877 (sK1 ◇ (sK1 ◇ sK2)) sK0 sK0]
  have l48 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l47 sK1 sK2 sK0]
    conv => enter [1]; rw [← l38 sK1 sK2 sK0 sK0]
  have l49 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l40 sK1 sK2 sK1]
    conv => enter [1]; rw [← l48 sK1 sK2 sK1]
  have l50 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53877 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l49 sK1 sK2]
  have l51 : ∀ X0 sK1 sK3 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (X1 ◇ X1))) := by
    intro X0 sK1 sK3 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK0)) (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l1 X0 sK1 (sK3 ◇ (sK0 ◇ sK0)) X1]
  have l52 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (X1 ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l46 sK1 sK2]
    conv => enter [1]; rw [l1 X0 sK1 sK1 X1]
  have l53 : ∀ X0 sK3 sK0 X1 : G, (X0 ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK3 ◇ (X1 ◇ X1))) := by
    intro X0 sK3 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK3 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 X0 sK3 (sK0 ◇ sK0) X1]
  have l54 : ∀ X0 sK3 sK0 : G, (X0 ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l53 X0 sK3 sK0 X0]
    conv => enter [1]; rw [l32 X0 sK3 X0 sK0]
  have l55 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l52 X0 sK1 sK2 X0]
    conv => enter [1]; rw [l32 X0 sK1 X0 sK0]
  have l56 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [l51 X0 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [l32 X0 sK1 X0 sK0]
  have l57 : ∀ X0 sK1 sK3 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l56 X0 sK1 sK3 sK0]
    conv => enter [1]; rw [← l55 X0 sK1 sK2 sK0]
  have l58 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [← l54 X0 sK3 sK0]
    conv => enter [1, 2]; rw [← l24 sK3 sK0]
  have l59 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l7 sK1 sK3 sK0 ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [l57 ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0))) sK1 sK3 sK0 sK2]
  have l60 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l59 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [← l50 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0))) sK1 sK1]
  have l61 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l60 sK1 sK3 sK0]
    conv => enter [1]; rw [← l20 sK1 sK3 sK0 (sK3 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))]
  have l62 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l61 sK1 sK3 sK0]
    conv => enter [1]; rw [← l3 sK1 sK1 sK3 sK0]
  have l63 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l46 sK1 sK2]
    conv => enter [1]; rw [← l62 sK1 sK3 sK0]
  have l64 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l58 sK1 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK0)) sK0]
  have l65 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l64 sK1 sK3 sK0]
    conv => enter [1]; rw [← l28 sK1 sK3 sK0]
  have l66 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l63 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l65 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l66 x y z w]

theorem Equation4512_53894_implies_Equation53877 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53894 : Equation53894 G) : Equation53877 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) = (sK0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [h53894 sK0 ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) X1 sK2]
  have l1 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53894 X0 X1 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h53894 sK0 X0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h53894 sK0 (sK1 ◇ (sK2 ◇ sK2)) sK0 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 X0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 X0]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53894 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_53878_implies_Equation53886 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53878 : Equation53878 G) : Equation53886 G := by
  have l0 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) sK0 X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 sK0]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) X0]
  have l2 : ∀ sK1 sK2 sK0 X0 X1 : G, (sK1 ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ X1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [← l1 sK1 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53878 (sK1 ◇ sK2) sK0 X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h53878 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ X1)]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53878 sK1 (sK1 ◇ sK2) X0 X1]
  have l5 : ∀ sK1 sK2 sK0 X0 X1 : G, (sK1 ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ X1))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53878 sK1 (sK2 ◇ sK0) sK1 sK1]
    conv => enter [1]; rw [l5 sK1 sK2 sK0 sK1 sK1]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK1 sK2 sK0]
  have l8 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2 sK1]
    conv => enter [1]; rw [← h53878 sK1 sK1 sK2 sK1]
  have l9 : ∀ X0 X1 X2 X3 sK1 sK2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 X3 sK1 sK2
    conv => enter [1]; rw [← h53878 X0 X1 X2 X3]
    conv => enter [1]; rw [h53878 X0 X1 sK1 sK2]
  have l10 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X2) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h53878 X0 X0 X1 X2]
    conv => enter [1]; rw [h53878 X0 (X1 ◇ X2) sK1 sK2]
  have l11 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (X1 ◇ X2))) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [h53878 X0 X0 sK1 sK2]
    conv => enter [1]; rw [h53878 X0 (sK1 ◇ sK2) X1 X2]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53878 sK1 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l13 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53878 sK1 sK1 sK1 sK2]
    conv => enter [1]; rw [l12 sK1 sK2]
  have l14 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l11 X0 sK1 sK2 X0 X0]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 X0 X0]
  have l15 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l10 X0 X1 X2 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (sK1 ◇ sK2)]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 sK2]
  have l17 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l15 X0 X1 X0 sK1 sK2]
    conv => enter [1]; rw [l9 X0 X1 X0 (sK1 ◇ sK2) sK1 sK2]
  have l18 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [← l17 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l14 X0 sK1 sK2]
  have l19 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
  have l20 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l19 sK1 sK2 X0]
    conv => enter [1]; rw [l4 sK1 sK2 (sK1 ◇ sK2) X0]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [l20 sK1 sK2 (sK1 ◇ sK2)]
  have l22 : ∀ X0 X1 X2 sK1 sK2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h53878 (X0 ◇ X1) X2 sK1 (sK1 ◇ sK2)]
  have l23 : ∀ X0 X1 X2 sK1 sK2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l22 X0 X1 X2 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l24 : ∀ X0 X1 X2 sK1 sK2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l23 X0 X1 X2 sK1 sK2]
    conv => enter [1]; rw [l9 X0 X1 X2 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l25 : ∀ X0 X1 X2 sK1 sK2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l24 X0 X1 X2 sK1 sK2]
    conv => enter [1]; rw [l18 X0 X1 sK1 sK2]
  have l26 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [← l25 X0 X1 X2 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X2))]
  have l27 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53878 X0 X1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l26 X0 sK1 sK2 X1 X0]
  have l28 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l27 X0 sK3 sK1 sK2]
    conv => enter [1]; rw [h53878 X0 sK3 sK2 sK0]
  have l29 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK1 sK2]
    conv => enter [1]; rw [l28 sK1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l29 x y z w]

theorem Equation4512_53886_implies_Equation53878 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53886 : Equation53886 G) : Equation53878 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK3 ◇ sK0) X0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
  have l2 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ (((sK3 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK3 ◇ sK0) ◇ X0) X1]
  have l3 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ ((sK3 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK3 ◇ sK0) X0 X1]
  have l4 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l3 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h53886 sK2 X0 (sK3 ◇ sK0) X1]
  have l5 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l4 sK2 sK3 sK0 X0 X1]
  have l6 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ X0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l5 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0)) (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [l5 sK2 sK3 sK0 X0 sK2]
  have l7 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l5 sK2 sK3 sK0 X0 X1]
  have l8 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ X0)]
  have l9 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l5 sK2 sK3 sK0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l6 sK2 sK3 sK0 sK2]
  have l10 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK2 sK3 sK0 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l9 sK2 sK3 sK0]
  have l11 : ∀ X1 sK1 sK2 sK3 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) = (X1 ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro X1 sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h53886 X1 (sK3 ◇ sK0) (sK1 ◇ sK2) X0]
  have l12 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53886 sK1 X0 sK2 X1]
  have l13 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h53886 (sK2 ◇ (sK3 ◇ sK0)) X0 X1 sK2]
    conv => enter [1]; rw [l5 sK2 sK3 sK0 X1 (X0 ◇ sK2)]
  have l14 : ∀ sK2 sK3 sK0 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 sK0 X1
    conv => enter [1]; rw [← l5 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0)) sK2]
    conv => enter [1]; rw [l13 sK2 sK3 sK0 sK2 X1]
  have l15 : ∀ sK2 sK3 sK0 X1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 sK0 X1
    conv => enter [1]; rw [l10 sK2 sK3 sK0]
    conv => enter [1]; rw [l14 sK2 sK3 sK0 X1]
  have l16 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [← l15 sK2 sK3 sK0 X0]
  have l17 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l16 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK3 ◇ sK0))]
  have l18 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l12 sK1 sK2 sK2 sK1]
    conv => enter [1]; rw [l17 sK1 sK2 sK1 sK3 sK0]
  have l19 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1, 1]; rw [l18 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l20 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l21 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l12 sK1 sK2 sK2 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l20 sK1 sK2 X0 sK1 sK1]
  have l22 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
  have l23 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53886 X0 X1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [← l21 sK1 sK2 (X1 ◇ X0)]
  have l24 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1, 1]; rw [l22 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l25 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l24 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l11 sK1 sK1 sK2 sK3 sK0 X0]
  have l26 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l25 sK1 sK2 X0 sK1 sK1]
    conv => enter [1]; rw [l23 sK1 (sK1 ◇ sK1) sK1 sK2]
  have l27 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l21 sK1 sK2 sK1]
    conv => enter [1]; rw [l26 sK1 sK2 sK1]
  have l28 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h53886 sK1 sK3 sK2 sK0]
  have l29 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l23 sK1 sK3 sK1 sK2]
  have l30 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l27 sK1 sK2]
    conv => enter [1]; rw [← l29 sK1 sK2 sK3 sK0]
  have l31 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l30 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l31 x y z w]

theorem Equation4512_53878_implies_Equation53895 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53878 : Equation53878 G) : Equation53895 G := by
  have l0 : ∀ sK4 sK1 sK0 X0 X1 : G, (((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (sK4 ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK4 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← h4512 sK4 ((sK1 ◇ sK0) ◇ X0) X1]
  have l1 : ∀ sK4 sK1 sK0 X0 X1 : G, (((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (sK4 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l0 sK4 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) X0 X1]
  have l2 : ∀ sK4 sK1 sK0 X0 X1 : G, (((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK4 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h53878 sK4 (sK1 ◇ sK0) X0 X1]
  have l3 : ∀ sK4 sK1 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK4 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l2 sK4 sK1 sK0 X0 X1]
  have l4 : ∀ sK2 sK4 sK1 sK0 X0 X1 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK4 ◇ (sK1 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l3 sK4 sK1 sK0 X0 X1]
  have l5 : ∀ sK4 sK1 sK0 sK2 sK3 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l3 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [← l3 sK4 sK1 sK0 sK2 (sK2 ◇ sK3)]
  have l6 : ∀ sK4 sK1 sK0 sK2 sK3 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l3 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [← l3 sK4 sK1 sK0 sK4 (sK1 ◇ sK0)]
  have l7 : ∀ sK2 sK4 sK1 sK0 sK3 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK2 ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK4 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← l5 sK4 sK1 sK0 sK2 sK3]
  have l8 : ∀ sK2 sK4 sK1 sK0 sK3 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [l7 sK2 sK4 sK1 sK0 sK3]
    conv => enter [1]; rw [h4512 sK2 (sK4 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK3)]
  have l9 : ∀ sK2 sK4 sK1 sK0 sK3 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK4 ◇ (sK1 ◇ sK0)) (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l6 sK4 sK1 sK0 sK2 sK3]
  have l10 : ∀ sK2 sK4 sK1 sK0 sK3 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK4 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [l9 sK2 sK4 sK1 sK0 sK3]
    conv => enter [1]; rw [h4512 sK2 (sK4 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK3)]
  have l11 : ∀ sK2 sK4 sK1 sK0 X0 X1 X2 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X2) := by
    intro sK2 sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l4 sK2 sK4 sK1 sK0 X0 X1]
  have l12 : ∀ sK2 sK4 sK1 sK0 X0 X1 X2 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = (sK2 ◇ ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X2)) := by
    intro sK2 sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l11 sK2 sK4 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 sK2 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) X2]
  have l13 : ∀ sK2 sK4 sK1 sK0 X0 X1 X2 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = (sK2 ◇ (sK4 ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ X2))) := by
    intro sK2 sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l12 sK2 sK4 sK1 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 sK4 (sK4 ◇ (sK1 ◇ sK0)) X2]
  have l14 : ∀ sK2 sK4 sK1 sK0 X0 X1 X2 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = (sK2 ◇ (sK2 ◇ sK4)) := by
    intro sK2 sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l13 sK2 sK4 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h53878 sK2 sK4 (sK4 ◇ (sK1 ◇ sK0)) X2]
  have l15 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ sK4)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [← l4 sK2 sK4 sK1 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [l14 sK2 sK4 sK1 sK0 sK2 sK2 sK2]
  have l16 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ sK4)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1, 2]; rw [l3 sK4 sK1 sK0 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l15 sK2 sK4 sK1 sK0]
  have l17 : ∀ sK2 sK4 sK1 sK0 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK2 ◇ sK4)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK4 ◇ (sK1 ◇ sK0)) (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l16 sK2 sK4 sK1 sK0]
  have l18 : ∀ sK2 sK4 sK1 sK0 sK3 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK4)) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← l10 sK2 sK4 sK1 sK0 sK3]
    conv => enter [1]; rw [l17 sK2 sK4 sK1 sK0]
  have l19 : ∀ sK2 sK4 sK1 sK0 sK3 X0 : G, (((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK4) ◇ X0)) := by
    intro sK2 sK4 sK1 sK0 sK3 X0
    conv => enter [1, 1]; rw [l18 sK2 sK4 sK1 sK0 sK3]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK4) X0]
  have l20 : ∀ sK2 sK4 sK1 sK0 sK3 X0 : G, (((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK4 ◇ X0))) := by
    intro sK2 sK4 sK1 sK0 sK3 X0
    conv => enter [1]; rw [l19 sK2 sK4 sK1 sK0 sK3 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK4 X0]
  have l21 : ∀ sK2 sK4 sK1 sK0 sK3 X0 : G, (((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK4 sK1 sK0 sK3 X0
    conv => enter [1]; rw [l20 sK2 sK4 sK1 sK0 sK3 X0]
    conv => enter [1]; rw [← h53878 sK2 sK2 sK4 X0]
  have l22 : ∀ sK2 sK4 sK1 sK0 sK3 X0 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ sK3) ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK4 sK1 sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [l21 sK2 sK4 sK1 sK0 sK3 X0]
  have l23 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [← l4 sK2 sK4 sK1 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [l22 sK2 sK4 sK1 sK0 sK2 sK2]
  have l24 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1, 2]; rw [l3 sK4 sK1 sK0 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l23 sK2 sK4 sK1 sK0]
  have l25 : ∀ sK2 sK4 sK1 sK0 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK4 ◇ (sK1 ◇ sK0)) (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l24 sK2 sK4 sK1 sK0]
  have l26 : ∀ sK2 sK4 sK1 sK0 sK3 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← l10 sK2 sK4 sK1 sK0 sK3]
    conv => enter [1]; rw [l25 sK2 sK4 sK1 sK0]
  have l27 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h53878 sK2 sK3 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK3 (X0 ◇ X1)]
  have l28 : ∀ sK2 sK3 X0 X1 X2 : G, ((sK2 ◇ sK3) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ X2) := by
    intro sK2 sK3 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l27 sK2 sK3 X0 X1]
  have l29 : ∀ sK2 sK3 X2 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ X2) := by
    intro sK2 sK3 X2
    conv => enter [1]; rw [l27 sK2 sK3 (sK2 ◇ sK2) X2]
    conv => enter [1]; rw [l28 sK2 sK3 sK2 sK2 X2]
  have l30 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [h53878 sK2 (sK2 ◇ sK3) sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK3) (sK1 ◇ sK0)]
  have l31 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l29 sK2 sK3 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l30 sK2 sK3 sK2 sK2]
  have l32 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l31 sK2 sK3]
    conv => enter [1]; rw [← h53878 sK2 sK2 sK2 sK3]
  have l33 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l32 sK2 sK3]
    conv => enter [1]; rw [← l26 sK2 sK4 sK1 sK0 sK3]
  have l34 : ∀ sK2 sK4 sK1 sK0 sK3 : G, (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← l4 sK2 sK4 sK1 sK0 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l32 sK2 sK3]
  have l35 : ∀ sK2 sK4 sK1 sK0 sK3 : G, (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [l34 sK2 sK4 sK1 sK0 sK3]
    conv => enter [1]; rw [l8 sK2 sK4 sK1 sK0 sK3]
  have l36 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l33 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l35 sK2 sK4 sK1 sK0 sK3]
  have l37 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK4)) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [l36 sK2 sK3 sK4 sK2 sK2]
    conv => enter [1]; rw [← h53878 sK2 sK4 sK4 (sK2 ◇ sK2)]
  have l38 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l37 sK2 sK3 sK4]
    conv => enter [1]; rw [h53878 sK2 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l38 x y z w u]

theorem Equation4512_53895_implies_Equation53878 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53895 : Equation53895 G) : Equation53878 G := by
  have l0 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53895 sK1 X0 sK2 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53895 sK1 sK2 sK2 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h53895 sK1 X0 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK2]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 sK3 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_53885_implies_Equation53893 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53885 : Equation53885 G) : Equation53893 G := by
  have l0 : ∀ X0 sK0 sK3 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [h53885 X0 sK0 (sK3 ◇ (sK0 ◇ sK3))]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK3 (sK0 ◇ sK3)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53885 X2 X0 X0]
    conv => enter [1, 2]; rw [h53885 X0 X0 X1]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h53885 X2 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h53885 (X0 ◇ X1) X0 X1]
  have l3 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [h53885 sK1 X0 (sK3 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) (X0 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l4 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ (sK0 ◇ sK3))) = (sK3 ◇ (sK3 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK3) (X0 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [← h53885 sK3 X0 (sK0 ◇ sK3)]
  have l5 : ∀ sK1 sK3 sK0 X1 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (X1 ◇ (X0 ◇ X1))) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ X0))) := by
    intro sK1 sK3 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← h53885 (sK3 ◇ (sK0 ◇ sK3)) X0 X1]
  have l6 : ∀ sK1 sK3 sK0 X1 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (X1 ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK3 sK0 X1 X0
    conv => enter [1]; rw [l5 sK1 sK3 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) ((sK3 ◇ (sK0 ◇ sK3)) ◇ X0)]
  have l7 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l2 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X0)]
  have l8 : ∀ X0 sK0 sK3 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [l0 X0 sK0 sK3]
    conv => enter [1, 2]; rw [l4 sK3 sK0 (sK0 ◇ sK3)]
  have l9 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ X0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← l6 sK1 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [← h53885 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) X0 sK1]
  have l10 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l7 X2 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X0]
  have l11 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l10 X2 X1 X0]
    conv => enter [1, 2]; rw [← l1 X0 X1 X0]
  have l12 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [← h53885 X0 sK0 sK3]
    conv => enter [1]; rw [l8 X0 sK0 sK3]
  have l13 : ∀ X0 sK0 sK3 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [h53885 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h53885 sK0 sK0 sK3]
  have l14 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ ((sK0 ◇ sK3) ◇ sK0)) = (sK3 ◇ ((sK0 ◇ sK3) ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK3) ((sK0 ◇ sK3) ◇ sK0)]
    conv => enter [1, 2]; rw [h53885 (sK0 ◇ sK3) sK0 sK3]
  have l15 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ ((sK0 ◇ sK3) ◇ sK0)) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l14 sK3 sK0]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK3) (sK3 ◇ (sK0 ◇ sK3))]
  have l16 : ∀ X0 sK0 sK3 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [l13 X0 sK0 sK3]
    conv => enter [1, 2]; rw [h4512 sK0 sK3 (sK0 ◇ sK3)]
  have l17 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [← h53885 X0 sK0 sK3]
    conv => enter [1]; rw [l16 X0 sK0 sK3]
  have l18 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK0 ◇ sK3) ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1, 2]; rw [← l15 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) ((sK0 ◇ sK3) ◇ sK0)]
  have l19 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK0 ◇ sK3) ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) (sK3 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [l18 sK1 sK3 sK0]
  have l20 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l17 sK3 sK3 sK0]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK3) (sK0 ◇ sK3)]
  have l21 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) (sK0 ◇ sK3)]
    conv => enter [1, 2]; rw [← l20 sK3 sK0]
  have l22 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK3 sK0]
    conv => enter [1]; rw [← l21 sK1 sK3 sK0]
  have l23 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK0 ◇ sK3) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1, 1]; rw [l22 sK1 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) (sK0 ◇ sK3) X0]
  have l24 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l12 sK0 sK3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK3 (sK3 ◇ (sK0 ◇ sK3))]
  have l25 : ∀ sK0 sK3 : G, ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) = ((sK0 ◇ sK3) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← h4512 sK0 sK3 (sK0 ◇ sK3)]
    conv => enter [1]; rw [l24 sK0 sK3]
  have l26 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ (sK0 ◇ sK3))) = (sK3 ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK3) (sK3 ◇ (sK0 ◇ sK3))]
    conv => enter [1, 2]; rw [← l25 sK0 sK3]
  have l27 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK3) (sK0 ◇ sK3)]
    conv => enter [1]; rw [← l26 sK3 sK0]
  have l28 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l20 sK3 sK0]
    conv => enter [1]; rw [l27 sK3 sK0]
  have l29 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ sK3))) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) (sK3 ◇ (sK0 ◇ sK3))]
    conv => enter [1, 2]; rw [← l28 sK3 sK0]
  have l30 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK3 sK0]
    conv => enter [1]; rw [← l29 sK1 sK3 sK0]
  have l31 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1, 1]; rw [l30 sK1 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) (sK3 ◇ (sK0 ◇ sK3)) X0]
  have l32 : ∀ sK1 sK3 sK0 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (((sK0 ◇ sK3) ◇ sK0) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1, 1]; rw [l19 sK1 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ((sK0 ◇ sK3) ◇ sK0) X0]
  have l33 : ∀ sK1 sK3 sK0 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l32 sK1 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK3) sK0 X0]
  have l34 : ∀ sK1 sK3 sK0 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l33 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← l23 sK1 sK3 sK0 (sK0 ◇ X0)]
  have l35 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ X0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) (sK3 ◇ (sK0 ◇ sK3)) X0]
    conv => enter [1]; rw [l34 sK1 sK3 sK0 X0]
  have l36 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l31 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [l35 sK1 sK3 sK0 X0]
  have l37 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1, 2]; rw [← h53885 sK0 sK0 sK3]
    conv => enter [1]; rw [← l36 sK1 sK3 sK0 (sK0 ◇ sK0)]
  have l38 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l12 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK3 sK0]
    conv => enter [1]; rw [l36 sK1 sK3 sK0 (sK3 ◇ (sK0 ◇ sK3))]
  have l39 : ∀ X0 sK0 sK1 sK3 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro X0 sK0 sK1 sK3
    conv => enter [1]; rw [h53885 X0 sK0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
    conv => enter [1, 2]; rw [← l36 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l40 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h53885 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) X0 sK0]
    conv => enter [1]; rw [← l36 sK1 sK3 sK0 (X0 ◇ sK0)]
  have l41 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [← h53885 X0 sK0 sK3]
    conv => enter [1]; rw [l39 X0 sK0 sK1 sK3]
  have l42 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l38 sK1 sK3 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 sK3 sK0]
  have l43 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l37 sK1 sK3 sK0]
    conv => enter [1]; rw [← l40 sK1 sK3 sK0 sK0]
  have l44 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK3) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK3 sK0]
    conv => enter [1]; rw [← l36 sK1 sK3 sK0 sK3]
  have l45 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h53885 sK1 sK0 sK3]
    conv => enter [1]; rw [← l42 sK1 sK3 sK0]
  have l46 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l43 sK1 sK3 sK0]
    conv => enter [1]; rw [← l40 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l47 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l45 sK1 sK3 sK0]
    conv => enter [1]; rw [← l3 sK1 sK3 sK3 sK0]
  have l48 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l46 sK1 sK3 sK0]
    conv => enter [1]; rw [← l9 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l49 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l48 sK1 sK3 sK0]
    conv => enter [1]; rw [← l31 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l50 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l49 sK1 sK3 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 sK3 sK0]
  have l51 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h53885 sK1 sK0 sK3]
    conv => enter [1]; rw [← l50 sK1 sK3 sK0]
  have l52 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [h53885 X0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK3]
    conv => enter [1, 2, 2]; rw [← l44 sK1 sK3 sK0]
  have l53 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) = (X0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [h53885 X0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
    conv => enter [1, 2, 2]; rw [← l51 sK1 sK3 sK0]
  have l54 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [l41 X0 sK3 sK0 sK1]
    conv => enter [1]; rw [← l53 X0 sK1 sK3 sK0]
  have l55 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK1 ◇ X1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← h53885 X0 sK1 sK2]
    conv => enter [1]; rw [h53885 X0 sK1 X1]
  have l56 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h53885 sK1 sK1 sK2]
  have l57 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK3) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [h53885 X0 sK1 (sK1 ◇ sK3)]
    conv => enter [1, 2, 2]; rw [← l47 sK1 sK3 sK0]
  have l58 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [l57 X0 sK1 sK3 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK3 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l59 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [l58 X0 sK1 sK3 sK0]
    conv => enter [1, 2]; rw [← l52 sK1 sK1 sK3 sK0]
  have l60 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [l59 X0 sK1 sK3 sK0]
    conv => enter [1, 2]; rw [← l54 sK1 sK3 sK0 sK1]
  have l61 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l56 sK1 sK2]
  have l62 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l61 sK1 X0 sK2]
  have l63 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l62 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
  have l64 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l11 sK1 X0 sK1]
    conv => enter [1]; rw [← l63 sK1 sK2 X0]
  have l65 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [l41 X0 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l51 sK1 sK3 sK0]
  have l66 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h53885 X0 sK1 sK2]
    conv => enter [1]; rw [l60 X0 sK1 sK3 sK0]
  have l67 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l66 X0 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← l65 X0 sK3 sK0 sK1]
  have l68 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X0 ◇ sK1)))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [h53885 X1 X0 ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← h53885 X0 sK1 (sK1 ◇ sK2)]
  have l69 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ sK1))))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l68 X1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ (X0 ◇ sK1))]
  have l70 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l69 X1 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l11 (sK1 ◇ (sK1 ◇ sK2)) sK1 X0]
  have l71 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK1))) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1, 2]; rw [l11 (sK1 ◇ sK2) sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l70 X1 X0 sK1 sK2]
  have l72 : ∀ X1 X0 sK1 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [← l71 X1 sK1 X1 X0]
    conv => enter [1, 2]; rw [← l64 sK1 sK1 X1]
  have l73 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [l72 X1 X0 sK1]
    conv => enter [1]; rw [l55 X1 sK1 sK1 sK2]
  have l74 : ∀ X1 sK3 sK0 X0 : G, (X1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 sK3 sK0 X0
    conv => enter [1]; rw [l67 X1 sK3 sK0 X1 X1]
    conv => enter [1]; rw [← l73 X1 X0 X1 X1]
  intro x y z w
  conv => enter [1]; rw [← l74 x z w y]

@[equational_result]
theorem Equation53893_implies_Equation53885 (G : Type*) [Magma G] (h53893 : Equation53893 G) : Equation53885 G := by
  intro x y z
  conv => enter [1]; rw [h53893 x y z y]

theorem Equation4512_53901_implies_Equation53920 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53901 : Equation53901 G) : Equation53920 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53901 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53901 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ X0)]
  have l3 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l2 sK0 sK1 X0]
  have l4 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 sK1 X0 X1]
    conv => enter [1]; rw [l3 sK1 sK0 X0 X1]
  have l5 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l0 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 sK1 sK0 X0 X1]
  have l6 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [l5 sK1 sK0 sK0 X1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53901 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 (X0 ◇ sK0)]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l9 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53901 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1 X1]
  have l10 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l9 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 X0]
  have l11 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l10 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 X1]
  have l12 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h53901 X0 X1 X2]
    conv => enter [1]; rw [l11 X0 X1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l12 y z x x y]

theorem Equation4512_53920_implies_Equation53901 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53920 : Equation53920 G) : Equation53901 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53920 X0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ X0)]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53920 X0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ X0)]
  have l3 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h53920 X0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ X0)]
  have l4 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [← h53920 (sK0 ◇ (sK1 ◇ sK2)) sK1 X0]
    conv => enter [1]; rw [l2 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l5 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [← h53920 sK2 sK1 X0]
    conv => enter [1]; rw [l3 sK2 sK1 sK0 sK2]
  have l6 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h53920 (sK1 ◇ sK2) sK0 X0]
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) sK0 sK1]
  have l7 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h53920 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 sK1]
    conv => enter [1, 2]; rw [l4 sK1 X0 sK0 sK2]
  have l8 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l5 sK1 sK2 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l9 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l5 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l5 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK2 sK0]
    conv => enter [1, 2]; rw [← l5 sK1 sK0 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h53920 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0 sK2 sK0]
  have l11 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l4 sK1 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l9 sK1 sK0 sK2]
  have l12 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l9 sK1 sK0 sK2]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0]
  have l13 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h53920 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2) X0]
    conv => enter [1, 2, 2]; rw [← l12 sK1 sK0 sK2]
  have l14 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l7 sK1 sK0 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l13 sK1 sK0 sK2 X0]
  have l15 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [l12 sK1 sK0 sK2]
    conv => enter [1]; rw [l14 sK1 sK2 sK0 X0]
  have l16 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK0 sK2]
    conv => enter [1]; rw [l15 sK1 sK2 sK0 X0]
  have l17 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l5 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l8 sK1 sK0 sK2]
  have l18 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h53920 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2, 2]; rw [l8 sK1 sK0 sK2]
  have l19 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK0 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l18 sK1 sK2 sK0 X0]
  have l20 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l19 sK1 sK0 sK2 X0]
    conv => enter [1, 2, 2]; rw [← l17 sK1 sK0 sK2]
  have l21 : ∀ X0 sK1 sK0 sK2 X1 : G, ((X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1]; rw [h53920 (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1]
    conv => enter [1, 2, 2]; rw [← l20 sK1 sK0 sK2 X0]
  have l22 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l21 X0 sK1 sK0 sK2 sK1]
  have l23 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l22 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l24 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l23 sK1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK0 (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l25 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK0 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l24 sK1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← l16 sK1 sK0 sK2 (sK1 ◇ sK2)]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l25 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
  have l27 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l25 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l29 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l6 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h53920 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
  have l30 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l27 sK1 sK0 sK2]
    conv => enter [1]; rw [l29 X0 sK0 sK1 sK2]
  have l31 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l27 sK1 sK0 sK2]
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
  have l32 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l25 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l30 X0 sK1 sK0 sK2]
  have l33 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l31 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l34 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l32 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l33 sK1 sK0 sK2 X0]
  have l35 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [h53920 X0 X1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l34 sK1 sK0 sK2 (X1 ◇ X0)]
  have l36 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [l35 X0 X1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l25 sK1 sK0 sK2 X1]
  intro x y z
  conv => enter [1]; rw [l36 x y y x z]

theorem Equation4512_53901_implies_Equation53923 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53901 : Equation53901 G) : Equation53923 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53901 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK2 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK1 ◇ sK2) ◇ X0) X1]
  have l2 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l1 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 X1]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l2 sK1 sK2 X1 sK1]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l3 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1]; rw [← h53901 (sK1 ◇ (sK1 ◇ sK2)) X0 X0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1]; rw [← l4 X0 sK1 sK2]
  have l6 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53901 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK2 X1]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 X0]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l5 sK1 sK2 X1]
  have l9 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h53901 X0 X1 X2]
    conv => enter [1]; rw [l8 X0 X1 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l9 y z w x y]

theorem Equation4512_53923_implies_Equation53901 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53923 : Equation53923 G) : Equation53901 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53923 X0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53923 X0 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l2 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53923 X0 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l3 : ∀ sK0 X1 sK1 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← h53923 sK0 sK0 X1 sK1]
    conv => enter [1]; rw [h53923 sK0 sK0 sK0 sK1]
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X1 ◇ (sK0 ◇ X2))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [← h53923 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [h53923 sK0 sK0 X1 X2]
  have l5 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [h53923 X0 sK0 sK0 sK1]
  have l6 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ ((X0 ◇ sK0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l5 X0 sK0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l7 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l6 X0 sK0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l8 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ ((X0 ◇ sK0) ◇ X1)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l1 X0 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK1) sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l8 X0 sK0 X1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X1]
  have l12 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X0 sK0 X1 sK1
    conv => enter [1, 2]; rw [h4512 X0 sK0 X1]
    conv => enter [1]; rw [l11 X0 sK0 X1 sK1]
  have l13 : ∀ sK0 sK1 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l7 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [l12 sK0 sK0 X1 sK1]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53923 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ sK0) X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [← l13 sK0 sK1 (sK0 ◇ X0)]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l17 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l20 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53923 X0 sK0 (sK1 ◇ sK2) (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ sK1))]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l20 sK0 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l22 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l23 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l24 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l19 sK0 sK1 X0]
  have l26 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53923 X0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l25 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l27 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [← l26 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l28 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l27 sK0 sK1 X0 sK2]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1]; rw [l28 sK0 sK1 X0 sK2]
  have l30 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53923 X0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ X0))) X0]
    conv => enter [1]; rw [← l29 sK0 sK1 X0 (sK1 ◇ X0)]
  have l31 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h53923 sK1 sK1 sK0 sK2]
    conv => enter [1]; rw [l30 sK1 sK1 sK0]
  have l32 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l31 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l33 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l32 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l19 sK0 sK1 X0]
  have l34 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l31 sK1 sK0 sK2]
    conv => enter [1]; rw [← l33 sK1 sK0 sK2 X0]
  have l35 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l34 sK1 sK0 sK2 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0)]
    conv => enter [1]; rw [l0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK1]
  have l36 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [h53923 X0 X1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [← l34 sK1 sK0 sK2 (X1 ◇ X0)]
  have l37 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l35 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l38 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l37 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l36 (sK0 ◇ sK1) X0 sK1 sK0 sK2]
  have l39 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l34 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l38 sK1 sK0 sK2 X0]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l39 sK1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l40 x y z]

theorem Equation4512_53901_implies_Equation53944 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53901 : Equation53901 G) : Equation53944 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53901 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK2 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK1 ◇ sK2) ◇ X0) X1]
  have l2 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l1 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 X1]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l2 sK1 sK2 X1 sK1]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l3 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1]; rw [← h53901 (sK1 ◇ (sK1 ◇ sK2)) X0 X0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1]; rw [← l4 X0 sK1 sK2]
  have l6 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53901 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK2 X1]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 X0]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l5 sK1 sK2 X1]
  have l9 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h53901 X0 X1 X2]
    conv => enter [1]; rw [l8 X0 X1 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l9 z x w x y]

theorem Equation4512_53944_implies_Equation53901 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53944 : Equation53944 G) : Equation53901 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l1 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (X0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [← h53944 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK2]
  have l2 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53944 X0 X1 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK2]
  have l3 : ∀ X2 X0 X3 X4 X1 : G, (X2 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) = ((X0 ◇ (X0 ◇ X1)) ◇ X4) := by
    intro X2 X0 X3 X4 X1
    conv => enter [1]; rw [h4512 X2 (X0 ◇ (X2 ◇ X3)) X4]
    conv => enter [1, 1]; rw [← h53944 X0 X1 X2 X3]
  have l4 : ∀ X2 X0 X3 X4 X1 : G, (X2 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) = (X0 ◇ ((X0 ◇ X1) ◇ X4)) := by
    intro X2 X0 X3 X4 X1
    conv => enter [1]; rw [l3 X2 X0 X3 X4 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X4]
  have l5 : ∀ X2 X0 X3 X4 X1 : G, (X2 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) = (X0 ◇ (X0 ◇ (X1 ◇ X4))) := by
    intro X2 X0 X3 X4 X1
    conv => enter [1]; rw [l4 X2 X0 X3 X4 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X4]
  have l6 : ∀ sK0 sK1 X0 sK2 X2 X3 X4 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X2 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) := by
    intro sK0 sK1 X0 sK2 X2 X3 X4
    conv => enter [1]; rw [← l2 X0 (sK0 ◇ X4) sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 X2 X0 X3 X4 sK0]
  have l7 : ∀ sK0 sK1 X0 sK2 X2 X3 X4 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X2 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) := by
    intro sK0 sK1 X0 sK2 X2 X3 X4
    conv => enter [1]; rw [l6 sK0 sK1 X0 sK2 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l8 : ∀ sK0 sK1 X0 sK2 X2 X3 X4 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X2 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro sK0 sK1 X0 sK2 X2 X3 X4
    conv => enter [1]; rw [l7 sK0 sK1 X0 sK2 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X4]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h53944 X0 (X0 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [h53944 X0 sK0 sK0 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h53944 sK0 ((sK0 ◇ sK1) ◇ X0) sK0 sK1]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l1 X0 sK0 (sK0 ◇ sK1) sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 X0 sK1]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l11 sK0 sK1 sK0 X0]
    conv => enter [1]; rw [l10 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l13 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1, 2]; rw [← h53944 X1 X1 X0 X2]
    conv => enter [1]; rw [h53944 X1 (X1 ◇ X1) sK0 (sK0 ◇ sK1)]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h53944 X0 sK0 sK0 sK1]
    conv => enter [1]; rw [h53944 X0 sK0 sK0 (sK0 ◇ sK1)]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l14 sK0 X0 sK1]
    conv => enter [1]; rw [l12 sK0 X0 sK1]
  have l16 : ∀ sK0 sK1 X0 sK2 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 sK2 X1
    conv => enter [1]; rw [l8 sK0 sK1 X0 sK2 X1 X0 sK0]
    conv => enter [1]; rw [l13 X1 X0 sK0 sK0 sK1]
  have l17 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l16 sK0 sK1 X0 sK2 sK0]
    conv => enter [1]; rw [l15 sK0 sK0 sK1]
  have l18 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
    conv => enter [1]; rw [h53944 (X0 ◇ X1) X2 sK0 (sK1 ◇ sK2)]
  have l19 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l18 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK2))]
  have l20 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l19 X0 X1 X2 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 X1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 X1 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK1 X1 sK2 X0 X1 sK0]
    conv => enter [1]; rw [l20 X0 X1 sK0 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [← l17 sK0 sK1 X1 sK2]
    conv => enter [1]; rw [l21 sK0 sK1 X1 sK2 X0]
  have l23 : ∀ sK0 sK1 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [h53944 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1 X0 X1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK0 sK0 sK2]
    conv => enter [1]; rw [h53944 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

theorem Equation4512_53901_implies_Equation53958 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53901 : Equation53901 G) : Equation53958 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53901 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (sK1 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 ((sK0 ◇ sK1) ◇ X0) X1]
  have l2 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) X0 X1]
  have l3 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l2 sK0 sK1 X1 sK0]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l3 sK0 sK1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h53901 (sK0 ◇ (sK0 ◇ sK1)) X0 X0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1]; rw [← l4 X0 sK0 sK1]
  have l6 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53901 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1 X1]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l6 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 X0]
  have l8 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l7 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 X1]
  have l9 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h53901 X0 X1 X2]
    conv => enter [1]; rw [l8 X0 X1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l9 z y x x y]

end Semigroup5
