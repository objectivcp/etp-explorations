import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53946_implies_Equation53963 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53946 : Equation53946 G) : Equation53963 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK0 ◇ sK2)]
  have l1 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))) = (X1 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [h53946 X0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) X1 sK1]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [h53946 sK1 (sK2 ◇ (sK0 ◇ sK2)) X0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK2 sK0]
  have l3 : ∀ sK2 X0 sK1 X1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK2 X0 sK1 X1
    conv => enter [1]; rw [h53946 sK2 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X1 ◇ X0)]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h53946 (sK1 ◇ sK2) X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X1 ◇ X0)]
  have l5 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [l1 X0 sK1 sK2 sK0 X1]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK0 X0]
  have l6 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l5 X0 sK1 sK2 sK0 sK1]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h53946 X0 (sK2 ◇ (sK0 ◇ sK2)) X0 sK1]
  have l8 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h53946 X0 (sK0 ◇ sK2) X0 sK2]
  have l9 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h53946 X0 sK2 X0 sK0]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 sK1 X0]
    conv => enter [1, 2]; rw [l9 sK1 sK2 sK1 sK1]
  have l11 : ∀ X1 X0 sK1 sK2 sK0 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X1 X0 sK1 sK2 sK0
    conv => enter [1, 2, 2]; rw [← l9 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← h53946 X0 (sK0 ◇ sK2) X1 (sK1 ◇ (sK1 ◇ sK2))]
  have l12 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [← l9 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK2) X0]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK2 X0 (sK1 ◇ sK2)]
  have l14 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h53946 X0 sK2 X0 X0]
    conv => enter [1]; rw [← l11 X1 X0 sK1 sK2 X0]
  have l15 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l13 sK1 sK2 X0]
    conv => enter [1]; rw [← l3 sK2 X0 sK1 (sK1 ◇ sK2)]
  have l16 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l14 X0 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 X0]
  have l17 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2 sK1]
    conv => enter [1]; rw [← l16 X0 sK2 sK1 sK1]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2 sK2]
    conv => enter [1]; rw [← l15 sK1 sK2 sK2]
  have l19 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← h53946 sK2 sK2 X0 sK0]
    conv => enter [1]; rw [← l15 sK1 sK2 sK2]
  have l20 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [← l19 X0 sK2 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l20 x y z w]

theorem Equation4512_53946_implies_Equation53942 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53946 : Equation53946 G) : Equation53942 G := by
  have l0 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ X0) X1]
  have l1 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l0 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l2 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h53946 sK1 X1 sK2 X0]
  have l3 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l2 sK2 sK1 X0 X1]
  have l4 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK1 sK0 sK1]
    conv => enter [1]; rw [← l3 sK2 sK1 sK2 sK1]
  have l5 : ∀ X0 sK2 sK1 X1 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK1 X1 sK0
    conv => enter [1]; rw [h53946 X0 (sK2 ◇ sK1) X1 (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l4 sK2 sK1 sK0]
  have l6 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK0 sK1]
    conv => enter [1]; rw [h53946 sK1 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l3 sK2 sK1 sK0 sK1]
  have l7 : ∀ X1 sK2 sK1 sK0 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X1 sK2 sK1 sK0 X0
    conv => enter [1, 2]; rw [l6 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← l5 X0 sK2 sK1 X1 sK0]
  have l8 : ∀ X1 sK2 sK1 sK0 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X1 sK2 sK1 sK0 X0
    conv => enter [1]; rw [l7 X1 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h53946 X0 sK1 X0 sK2]
  have l9 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l6 sK2 sK1 sK0 sK2]
    conv => enter [1]; rw [l8 sK2 sK2 sK1 sK0 X0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK2 sK1 sK0 sK0]
    conv => enter [1]; rw [l9 sK2 sK1 sK0 sK2]
  have l11 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l9 sK2 sK1 sK2 sK2]
    conv => enter [1]; rw [l6 sK2 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l9 sK2 sK1 sK2 sK2]
  have l12 : ∀ X0 sK0 sK1 X1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 X1 sK2
    conv => enter [1]; rw [h53946 X0 (sK0 ◇ sK1) X1 (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l9 sK2 sK1 sK0 sK2]
  have l13 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [h53946 X0 sK1 X0 X0]
    conv => enter [1]; rw [l12 X0 X0 sK1 X1 sK2]
  have l14 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [l13 X0 sK1 X1 sK2]
    conv => enter [1, 2]; rw [← l11 sK2 sK1 X0]
  have l15 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l14 X0 sK1 X0 sK2]
    conv => enter [1]; rw [← l11 sK2 sK1 X0]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
  have l17 : ∀ sK0 sK1 X1 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X2 ◇ sK1))) := by
    intro sK0 sK1 X1 X0 X2
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [h53946 X0 sK1 X1 X2]
  intro x y z
  conv => enter [1]; rw [l17 x y z x z]

theorem Equation4512_53946_implies_Equation53903 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53946 : Equation53946 G) : Equation53903 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK2 ◇ sK1))]
  have l1 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))) = (X1 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [h53946 X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) X1 sK0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [h53946 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK2]
  have l3 : ∀ X0 sK1 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 X1 sK0 sK2
    conv => enter [1]; rw [h53946 X0 sK1 X0 sK2]
    conv => enter [1]; rw [h53946 X0 (sK2 ◇ sK1) X1 sK0]
  have l4 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [l1 X0 sK0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2 X0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 sK1 sK2 sK0]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h53946 X0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0 sK0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h53946 X0 (sK0 ◇ (sK2 ◇ sK1)) X0 sK1]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l3 X0 sK1 X0 sK0 sK2]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l8 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK0 sK0]
  have l10 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h53946 X0 (sK0 ◇ (sK2 ◇ sK1)) X1 (sK0 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l3 X0 sK1 X0 sK0 X0]
    conv => enter [1]; rw [← l10 X1 X0 sK0 sK1 X0]
  have l12 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← l11 X0 sK1 X1 sK0]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 X1 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X2 ◇ sK1))) := by
    intro sK0 sK1 X1 X0 X2
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [h53946 X0 sK1 X1 X2]
  intro x y z
  conv => enter [1]; rw [l14 x y y x z]

theorem Equation4512_53946_implies_Equation53917 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53946 : Equation53946 G) : Equation53917 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l2 : ∀ sK2 sK0 sK1 X0 X1 : G, (((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK2 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK0 ◇ sK1) ◇ X0) X1]
  have l3 : ∀ sK2 sK0 sK1 X0 X1 : G, (((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK2 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) X0 X1]
  have l4 : ∀ sK2 sK0 sK1 X0 X1 : G, (((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h53946 (sK0 ◇ sK1) X1 sK2 X0]
  have l5 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X0 X1]
  have l6 : ∀ sK1 sK2 sK0 X1 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK0 ◇ sK1)) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l5 sK2 sK0 sK1 X1 X0]
  have l7 : ∀ sK0 sK1 X0 sK2 X1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 sK2 X1
    conv => enter [1]; rw [h53946 (sK0 ◇ sK1) X0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l6 sK1 sK2 sK0 X1 X0]
  have l8 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l5 sK2 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [l5 sK2 sK0 sK1 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 sK2 sK0 sK1 sK0 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l8 sK2 sK0 sK1]
  have l10 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l5 sK2 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
  have l11 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l5 sK2 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 sK2 (sK0 ◇ sK1)]
  have l12 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l5 sK2 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1 sK1 sK2 sK0]
  have l13 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l12 sK2 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
  have l14 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l10 sK2 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK2 sK1]
  have l15 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l11 sK2 sK0 sK1]
    conv => enter [1]; rw [l14 sK2 sK0 sK1]
  have l16 : ∀ X1 X0 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro X1 X0 sK2 sK0 sK1
    conv => enter [1, 2, 2]; rw [l5 sK2 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← h53946 X0 ((sK0 ◇ sK1) ◇ sK1) X1 (sK0 ◇ sK1)]
  have l17 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l5 sK2 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [h53946 (sK0 ◇ sK1) sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 sK2 sK0 sK1 sK0 sK1]
  have l18 : ∀ X0 X1 sK0 sK1 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X2 ◇ X1))) := by
    intro X0 X1 sK0 sK1 X2
    conv => enter [1]; rw [h53946 X0 X1 (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) X2]
    conv => enter [1]; rw [← l7 sK0 sK1 (X2 ◇ X1) X0 X0]
  have l19 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l18 X0 X1 sK0 sK1 X0]
    conv => enter [1]; rw [← h53946 (sK0 ◇ sK1) X1 (sK0 ◇ sK1) X0]
  have l20 : ∀ X0 sK1 X1 sK2 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X1 ◇ (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 X1 sK2 sK0
    conv => enter [1]; rw [h53946 X0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l16 X1 X0 sK2 sK0 sK1]
  have l21 : ∀ X1 sK2 sK0 sK1 X0 : G, (X1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X1 sK2 sK0 sK1 X0
    conv => enter [1, 2]; rw [l17 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← l20 X0 sK1 X1 sK2 sK0]
  have l22 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l17 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK2 sK2 sK0 sK1 X0]
  have l23 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l17 sK2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l15 sK2 sK0 sK1]
  have l24 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l22 sK2 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l25 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l15 sK2 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK2 sK1]
  have l26 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l23 sK2 sK0 sK1]
    conv => enter [1]; rw [l25 sK2 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 sK0 sK0 sK1 sK0]
    conv => enter [1]; rw [l26 sK0 sK0 sK1]
  have l28 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l22 sK0 sK0 sK1 sK0]
    conv => enter [1]; rw [l17 sK0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l22 sK0 sK0 sK1 sK0]
  have l29 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [← l22 sK2 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK1 (sK0 ◇ sK1) X0]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53946 (sK0 ◇ sK1) sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l27 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1 sK0]
    conv => enter [1]; rw [← l31 sK0 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1 sK1]
  have l34 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l19 sK2 sK1 sK0 sK1]
    conv => enter [1]; rw [h53946 sK2 sK1 X0 sK0]
  have l35 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← l34 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l30 sK0 sK1 sK1]
  have l36 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l35 X0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l36 x y y z]

theorem Equation4512_53946_implies_Equation53854 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53946 : Equation53946 G) : Equation53854 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l3 sK1 X0]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ X0)]
  have l7 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53946 sK1 X0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 X0]
  have l8 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l7 sK1 X0 sK0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l5 sK1]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l13 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l12 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53946 sK1 X0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l13 sK1 X0 sK1]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l14 sK1 X0]
  have l16 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) = (X2 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [h53946 X1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) X2 sK1]
    conv => enter [1, 2, 2]; rw [← l15 sK1 X0]
  have l17 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = (X1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h53946 sK1 X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l18 : ∀ X2 sK1 X0 X1 : G, (X2 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro X2 sK1 X0 X1
    conv => enter [1, 2]; rw [l17 sK1 X0 X1]
    conv => enter [1]; rw [← l16 X1 sK1 X0 X2]
  have l19 : ∀ X2 sK1 X0 X1 : G, (X2 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X2 sK1 X0 X1
    conv => enter [1]; rw [l18 X2 sK1 X0 X1]
    conv => enter [1]; rw [← h53946 X1 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l17 sK1 X0 sK1]
    conv => enter [1]; rw [l19 sK1 sK1 X0 X1]
  have l21 : ∀ sK1 X0 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l20 sK1 sK1 sK3]
    conv => enter [1]; rw [h53946 sK3 sK1 X0 sK0]
  have l22 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l21 sK1 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l22 x y z w]

theorem Equation4512_53946_implies_Equation53938 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53946 : Equation53946 G) : Equation53938 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l2 sK2 sK0 sK1]
  have l4 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 X0]
  have l5 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l4 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
  have l6 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h53946 (sK0 ◇ sK1) X0 sK2 (sK1 ◇ sK1)]
  have l7 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ (X1 ◇ (sK1 ◇ X0))) = (X2 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [h53946 X1 (sK1 ◇ X0) X2 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l8 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← h53946 sK0 X0 X1 sK1]
  have l9 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = (X1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h53946 sK1 X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l10 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ X0))) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [h53946 sK1 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1]
    conv => enter [1]; rw [l6 sK1 sK0 sK1 (X1 ◇ X0)]
  have l11 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l10 sK1 X0 sK0 sK1]
    conv => enter [1]; rw [← h53946 (sK0 ◇ sK1) X0 (sK0 ◇ sK1) sK1]
  have l12 : ∀ X2 sK1 X0 X1 : G, (X2 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro X2 sK1 X0 X1
    conv => enter [1, 2]; rw [l9 sK1 X0 X1]
    conv => enter [1]; rw [← l7 X1 sK1 X0 X2]
  have l13 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l11 sK1 X0 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) sK0 sK1 X0]
  have l14 : ∀ X2 sK1 X0 X1 : G, (X2 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X2 sK1 X0 X1
    conv => enter [1]; rw [l12 X2 sK1 X0 X1]
    conv => enter [1]; rw [← h53946 X1 X0 X1 sK1]
  have l15 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l13 sK1 X0 sK0]
  have l16 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l9 sK1 X0 sK1]
    conv => enter [1]; rw [l14 sK1 sK1 X0 X1]
  have l17 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l15 sK1 sK1 sK0]
    conv => enter [1]; rw [h53946 sK0 sK1 X0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l16 sK1 sK1 sK0]
    conv => enter [1]; rw [l17 sK1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

theorem Equation4512_53946_implies_Equation53846 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53946 : Equation53946 G) : Equation53846 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l5 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l4 sK2 sK1 sK0]
  have l6 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l5 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l7 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK2 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← l6 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l8 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l7 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h53946 sK1 X0 sK2 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l3 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l10 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53946 (sK0 ◇ sK0) X0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK1 sK0 X0]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l1 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X0 sK1]
  have l12 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK2 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [← l11 sK0 X0 sK1]
  have l13 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h53946 sK0 X0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK2 sK1 sK0 X0]
  have l14 : ∀ sK0 X0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l13 sK0 X0 sK2 sK1]
  have l15 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l14 sK0 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53946 X0 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1]; rw [h53946 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [← l17 sK0 sK0]
  have l20 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l18 X0 sK0 X1]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 sK0]
    conv => enter [1]; rw [l20 sK0 sK0 X0]
  have l22 : ∀ sK0 X1 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (X2 ◇ sK0))) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [h53946 X0 sK0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l22 x y z y]

theorem Equation4512_54187_implies_Equation54178 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54187 : Equation54187 G) : Equation54178 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l2 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54187 X0 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK1 sK1]
  have l3 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54187 X0 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l4 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54187 sK0 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l5 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l2 X0 sK2 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK1]
  have l6 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l5 X0 sK2 sK1]
    conv => enter [1]; rw [← h54187 X0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l6 X0 sK2 sK1]
    conv => enter [1]; rw [h54187 X0 sK2 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h54187 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h54187 sK2 sK1 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ sK1)]
  have l10 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 sK1]
    conv => enter [1]; rw [l9 sK2 sK1]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ sK1)]
  have l12 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1))) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [← h54187 X0 (sK2 ◇ sK1) (sK1 ◇ sK1)]
  have l13 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← l12 X0 sK1 sK2]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK1]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l11 sK1 sK2]
  have l15 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54187 X0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l13 X0 sK2 sK1]
  have l16 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← l15 X0 sK1 sK2]
    conv => enter [1]; rw [l7 X0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l14 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l19 : ∀ X0 sK1 X1 sK2 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1)) := by
    intro X0 sK1 X1 sK2
    conv => enter [1, 1]; rw [h54187 X0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h4512 X0 ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) X1]
  have l20 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1))) = (X0 ◇ (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [← h54187 X0 ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) X1]
    conv => enter [1, 2]; rw [← h54187 ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) sK1 (sK2 ◇ sK1)]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54187 sK1 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [h54187 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK1 (sK2 ◇ sK1)]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 (sK2 ◇ sK1) sK1 sK2]
  have l24 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1))) = (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l20 X0 X1 sK2 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ sK1)]
  have l25 : ∀ X0 sK1 X1 sK2 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [l19 X0 sK1 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X1]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l16 sK0 sK2 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1 sK2]
  have l27 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1))) = (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l24 X0 X1 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← l14 sK1 sK2]
  have l28 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ sK1) X1]
    conv => enter [1]; rw [l25 X0 sK1 X1 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ sK1)]
  have l30 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1))) = (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l27 X0 X1 sK2 sK1]
    conv => enter [1, 2]; rw [← l3 (sK2 ◇ sK1) sK2 sK1]
  have l31 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ (X1 ◇ (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [h54187 X0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l30 X0 X1 sK2 sK1]
  have l32 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1)))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [l31 X0 sK2 sK1 X1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X1]
  have l33 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [l32 X0 sK2 sK1 X1]
    conv => enter [1, 2]; rw [← l28 X1 sK1 X1 sK2]
  have l34 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54187 X0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l33 X0 sK2 sK1 X0]
  have l35 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l34 X0 sK1 sK2]
    conv => enter [1]; rw [l16 X0 sK2 sK1]
  have l36 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l8 sK1]
    conv => enter [1]; rw [l35 X0 sK1 sK2]
  have l37 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54187 X0 sK1 sK1]
    conv => enter [1]; rw [l36 X0 sK1 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l21 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 sK1 sK2]
    conv => enter [1]; rw [← l37 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK1 sK2]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [← l41 sK0 sK1 sK2]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54187 sK0 sK1 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l43 x y z]

theorem Equation4512_54187_implies_Equation54183 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54187 : Equation54187 G) : Equation54183 G := by
  have l0 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54187 sK0 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (X0 ◇ (sK2 ◇ sK2))]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54187 sK0 sK2 sK2]
    conv => enter [1]; rw [← l0 sK0 sK2]
  have l3 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h54187 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [h54187 (sK0 ◇ (sK2 ◇ sK2)) sK2 sK2]
  have l5 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0 sK2 sK2]
    conv => enter [1]; rw [← l4 sK0 sK2]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l7 : ∀ X0 sK2 sK0 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK0
    conv => enter [1, 2, 2]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [← h54187 X0 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l8 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X0]
  have l9 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54187 X0 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l7 X0 sK2 sK0]
  have l10 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h54187 X0 sK0 sK1]
    conv => enter [1]; rw [l9 X0 sK0 sK2]
  have l11 : ∀ X0 sK2 sK0 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h54187 X0 (sK2 ◇ sK2) (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l8 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l12 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l11 X0 sK2 sK0]
    conv => enter [1]; rw [← l10 X0 sK1 sK0 sK2]
  have l13 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1, 2]; rw [l3 sK2]
    conv => enter [1]; rw [l12 X0 sK2 sK1 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l13 sK0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l15 x z y]

theorem Equation4512_54187_implies_Equation54167 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54187 : Equation54187 G) : Equation54167 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54187 X0 sK1 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK2 ◇ sK2)]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54187 sK0 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (X0 ◇ (sK2 ◇ sK2))]
  have l3 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l1 X0 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l2 sK0 (sK1 ◇ sK0) X0]
  have l4 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l3 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h54187 X0 sK1 sK0]
    conv => enter [1]; rw [l4 X0 sK1 sK0]
  have l6 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h54187 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [h54187 (sK0 ◇ (sK2 ◇ sK2)) sK2 sK2]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2 sK2]
    conv => enter [1]; rw [← l7 sK0 sK2]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l8 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l10 : ∀ X0 sK2 sK0 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK0
    conv => enter [1, 2, 2]; rw [l9 sK0 sK2]
    conv => enter [1]; rw [← h54187 X0 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l11 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l9 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X0]
  have l12 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54187 X0 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l10 X0 sK2 sK0]
  have l13 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54187 X0 sK1 sK1]
    conv => enter [1, 2]; rw [h54187 sK1 sK1 sK0]
  have l14 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l13 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l15 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l14 X0 sK1 sK0]
    conv => enter [1]; rw [h54187 X0 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l15 (sK1 ◇ sK0) sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54187 X0 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l18 sK1 sK0]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l19 X0 sK0 sK1]
    conv => enter [1]; rw [l15 X0 sK1 sK0]
  have l21 : ∀ X0 sK2 sK0 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h54187 X0 (sK2 ◇ sK2) (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l11 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l22 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l12 X0 sK0 sK2]
    conv => enter [1]; rw [← l21 X0 sK2 sK0]
  have l23 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l22 X0 sK0 sK2]
    conv => enter [1, 2]; rw [← l6 sK2]
  have l24 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l23 X0 sK0 sK2]
    conv => enter [1]; rw [← h54187 X0 sK2 sK2]
  have l25 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l24 X0 sK2 sK0]
    conv => enter [1]; rw [l20 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l25 x y x z]

theorem Equation4512_54187_implies_Equation53819 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54187 : Equation54187 G) : Equation53819 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54187 X0 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (X0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← h54187 sK1 X0 (sK2 ◇ sK1)]
  have l2 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l0 X0 sK2 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK2 (sK2 ◇ sK1)]
  have l3 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l2 X0 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h54187 X0 sK2 sK1]
    conv => enter [1]; rw [l3 X0 sK2 sK1]
  have l5 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54187 X0 sK2 sK2]
    conv => enter [1, 2]; rw [h54187 sK2 sK2 sK1]
  have l6 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l5 X0 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l7 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← l6 X0 sK2 sK1]
    conv => enter [1]; rw [h54187 X0 sK2 sK1]
  have l8 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h54187 X0 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h54187 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0 (sK1 ◇ (sK2 ◇ sK1))]
  have l9 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X1))) = (X0 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [← h54187 X0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) X1]
    conv => enter [1, 2]; rw [← h54187 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) sK0 (sK1 ◇ (sK2 ◇ sK1))]
  have l10 : ∀ X0 sK0 X1 sK1 sK2 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X1)) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1, 1]; rw [h54187 X0 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) X1]
  have l11 : ∀ X0 sK0 X1 sK1 sK2 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1))) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [l10 X0 sK0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X1]
  have l12 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l9 X0 X1 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK0 ◇ sK0)]
  have l13 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1))) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l11 X0 sK0 X1 sK1 sK2]
  have l14 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l12 X0 X1 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l8 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK2 sK0]
  have l15 : ∀ X0 sK1 sK2 X1 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X1 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X1))) := by
    intro X0 sK1 sK2 X1 sK0
    conv => enter [1]; rw [h54187 X0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l14 X0 X1 sK1 sK2 sK0]
  have l16 : ∀ X0 sK1 sK2 X1 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1)))) := by
    intro X0 sK1 sK2 X1 sK0
    conv => enter [1]; rw [l15 X0 sK1 sK2 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X1]
  have l17 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l13 X1 sK0 X1 sK1 sK2]
    conv => enter [1]; rw [← l16 X0 sK1 sK2 X1 sK0]
  have l18 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54187 X0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l17 X0 X0 sK0 sK1 sK2]
  have l19 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 X0 sK0 sK1 sK2]
  have l20 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [h54187 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 X0 sK0 sK1 sK2]
  have l21 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54187 X0 sK0 sK0]
    conv => enter [1]; rw [l20 X0 sK0 sK1 sK2]
  have l22 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1]; rw [l7 sK1 sK2 sK1]
  have l23 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l22 sK1 sK2]
  have l24 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l23 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l25 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ X1))) = (X0 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [← h54187 X0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) X1]
    conv => enter [1, 2]; rw [← l4 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) sK1 sK2]
  have l26 : ∀ X0 sK1 sK2 X1 : G, ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1) = (X0 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 1]; rw [l4 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) X1]
  have l27 : ∀ X0 sK1 sK2 X1 : G, ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l26 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X1]
  have l28 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (X1 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l25 X0 X1 sK1 sK2]
  have l29 : ∀ X0 sK1 sK2 X1 : G, ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l27 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [l24 sK1 sK2 X1]
  have l30 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l28 X0 sK1 sK2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X1]
  have l31 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) X1]
    conv => enter [1]; rw [l29 X0 sK1 sK2 X1]
  have l32 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l30 X0 sK1 sK2 X1]
    conv => enter [1, 2, 2]; rw [l24 sK1 sK2 X1]
  have l33 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l32 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← l31 X1 sK1 sK2 X1]
  have l34 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54187 X0 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [← l33 X0 sK1 sK2 X0]
  have l35 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l34 X0 sK1 sK2]
    conv => enter [1]; rw [← h54187 X0 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l36 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l35 X0 sK1 sK2]
    conv => enter [1]; rw [l7 X0 sK2 sK1]
  have l37 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l21 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l36 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l37 x x y z]

@[equational_result]
theorem Equation53942_implies_Equation53880 (G : Type*) [Magma G] (h53942 : Equation53942 G) : Equation53880 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h53942 X0 sK1 sK0]
    conv => enter [1]; rw [h53942 X0 sK1 X0]
    conv => enter [1, 2]; rw [h53942 X0 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53942 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← l0 sK0 X0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53942 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4512_53942_implies_Equation53959 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53942 : Equation53942 G) : Equation53959 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l0 sK2 sK1 X0]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l3 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK1 sK2]
  have l4 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l5 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ X0)) = (((sK2 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l4 sK2 sK1]
  have l6 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l5 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l7 : ∀ X3 X1 X2 X0 : G, (X3 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [← h53942 X1 (X1 ◇ X2) X3]
    conv => enter [1, 2]; rw [h53942 X1 X2 X0]
  have l8 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ X0))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [h53942 X1 ((sK2 ◇ sK1) ◇ X0) (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l6 sK2 sK1 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h53942 X1 X2 X0]
    conv => enter [1]; rw [h53942 X1 X2 X1]
    conv => enter [1, 2]; rw [h53942 X1 X2 X0]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53942 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53942 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [← h53942 sK2 X0 sK1]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [← h53942 sK2 X0 (sK1 ◇ (sK2 ◇ sK1))]
  have l14 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0]
    conv => enter [1]; rw [h53942 (sK2 ◇ sK1) X0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK2 sK1 X0]
  have l15 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h53942 X1 X2 X1]
    conv => enter [1]; rw [h53942 X1 (X1 ◇ X2) X0]
  have l16 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h53942 (sK2 ◇ sK1) X0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ X0)]
  have l17 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h53942 (sK2 ◇ sK1) X0 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l6 sK2 sK1 ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)]
  have l18 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0]
    conv => enter [1]; rw [l17 sK2 sK1 X0]
  have l19 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0]
    conv => enter [1]; rw [l16 sK2 sK1 X0]
  have l20 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l12 sK1 sK2 X0]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [← l15 X0 X2 X1]
  have l22 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ X0))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [l8 X1 sK2 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l14 sK2 sK1 X0]
  have l23 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l15 X1 X2 X1]
    conv => enter [1]; rw [l7 X1 X1 X2 X0]
  have l24 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l18 sK2 sK1 X0]
    conv => enter [1]; rw [← l14 sK2 sK1 ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)]
  have l25 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = (X1 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l21 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) X1 X0]
    conv => enter [1]; rw [← l22 X1 sK2 sK1 X0]
  have l26 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l23 X1 X2 X0]
    conv => enter [1]; rw [l21 X1 X0 (X0 ◇ X2)]
  have l27 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (X1 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l24 sK2 sK1 X0]
    conv => enter [1]; rw [l25 sK2 sK1 X0 X1]
  have l28 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l27 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← l26 X1 X0 (sK2 ◇ sK1)]
  have l29 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l19 sK2 sK1 X0]
    conv => enter [1]; rw [← h53942 (sK1 ◇ (sK2 ◇ sK1)) X0 sK1]
  have l30 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53942 sK1 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l19 sK2 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l31 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l28 sK2 sK1 X0 sK1]
    conv => enter [1]; rw [l30 sK1 X0 sK2]
  have l32 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l28 sK2 sK1 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l29 sK1 sK2 X0]
  have l33 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK2 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l34 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [l20 sK1 sK2 X0]
    conv => enter [1]; rw [← l20 sK1 sK2 (sK2 ◇ X0)]
  have l35 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 X0 X1 sK1
    conv => enter [1, 2]; rw [h53942 X0 X1 sK2]
    conv => enter [1]; rw [← l20 sK1 sK2 (X0 ◇ (sK2 ◇ X1))]
  have l36 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h53942 sK2 X0 sK2]
    conv => enter [1]; rw [← l20 sK1 sK2 (sK2 ◇ X0)]
  have l37 : ∀ sK2 X1 sK1 X0 : G, (sK2 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = (X1 ◇ (X1 ◇ (sK2 ◇ X0))) := by
    intro sK2 X1 sK1 X0
    conv => enter [1, 2, 2]; rw [l20 sK1 sK2 X0]
    conv => enter [1]; rw [← h53942 X1 (sK2 ◇ X0) sK2]
  have l38 : ∀ sK2 X1 sK1 X0 : G, (sK2 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK2 X1 sK1 X0
    conv => enter [1]; rw [l37 sK2 X1 sK1 X0]
    conv => enter [1]; rw [← l26 X1 X0 sK2]
  have l39 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK2 X0]
    conv => enter [1]; rw [l36 sK2 X0 sK1]
  have l40 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ X1))) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l35 sK2 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l28 sK2 sK1 X1 X0]
  have l41 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l34 sK2 sK1 X0]
  have l42 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l28 sK2 sK1 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l33 sK1 sK2 X0]
  have l43 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK2 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l28 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← l38 sK2 X1 sK1 X0]
  have l44 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l39 sK1 sK2 X0]
    conv => enter [1]; rw [← l41 sK2 sK1 X0]
  have l45 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53942 X0 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l20 sK1 sK2 sK1]
  have l46 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l45 X0 sK1 sK2]
    conv => enter [1]; rw [l40 sK1 sK2 X0 (sK2 ◇ sK1)]
  have l47 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l42 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l46 X0 sK1 sK2]
  have l48 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l47 sK2 sK1 sK2]
    conv => enter [1]; rw [← l28 sK2 sK1 sK1 sK2]
  have l49 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l48 sK2 sK1]
    conv => enter [1]; rw [← l44 sK1 sK2 sK1]
  have l50 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l49 sK2 sK1]
    conv => enter [1]; rw [l20 sK1 sK2 sK1]
  have l51 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l44 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l50 sK2 sK1]
  have l52 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 sK1 sK2]
    conv => enter [1]; rw [l51 sK1 sK2]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53942 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK0]
    conv => enter [1, 2]; rw [l20 sK1 sK2 sK1]
  have l54 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h53942 X0 sK1 sK0]
    conv => enter [1]; rw [h53942 X0 sK1 X0]
    conv => enter [1, 2]; rw [h53942 X0 sK1 sK0]
  have l55 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) = (sK2 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)]
    conv => enter [1, 2]; rw [h53942 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK0]
  have l56 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h53942 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK1 sK0]
    conv => enter [1]; rw [← l44 sK1 sK2 ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1)]
  have l57 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l13 sK1 sK2 sK1]
    conv => enter [1]; rw [← l56 sK0 sK2 sK1]
  have l58 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l43 sK2 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l55 sK2 sK1 sK0]
  have l59 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53942 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← l54 sK0 X0 sK1]
  have l60 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l39 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l53 sK0 sK1 sK2]
  have l61 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l57 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l44 sK1 sK2 (sK0 ◇ sK1)]
  have l62 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l31 sK2 sK1 sK1]
    conv => enter [1]; rw [← l58 sK2 sK1 sK0]
  have l63 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l59 sK0 sK1 X0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK1) sK1]
  have l64 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l2 sK1 sK2]
    conv => enter [1]; rw [l60 sK1 sK2 sK0]
  have l65 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK1]
    conv => enter [1]; rw [l61 sK2 sK1 sK0]
  have l66 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l62 sK2 sK1 sK0]
    conv => enter [1]; rw [← l44 sK1 sK2 (sK0 ◇ sK1)]
  have l67 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l64 sK1 sK2 sK0]
    conv => enter [1]; rw [l63 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l68 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l65 sK1 sK2 sK0]
    conv => enter [1]; rw [l63 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l69 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 sK1]
    conv => enter [1]; rw [l66 sK2 sK1 sK0]
  have l70 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l67 sK1 sK2 sK1]
    conv => enter [1]; rw [← l68 sK1 sK2 sK1]
  have l71 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l20 sK1 sK2 sK1]
    conv => enter [1]; rw [l69 sK1 sK2 sK0]
  have l72 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l52 sK1 sK2]
    conv => enter [1]; rw [l71 sK2 sK1 sK0]
  have l73 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ (X1 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))) = (sK1 ◇ (X1 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [h53942 X1 ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) sK1]
    conv => enter [1, 2, 2]; rw [← l32 sK2 sK1 X0]
  have l74 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1, 2, 2]; rw [l44 sK1 sK2 X0]
    conv => enter [1]; rw [← l73 X1 sK2 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l44 sK1 sK2 X0]
  have l75 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [l74 sK1 X1 sK2 X0]
    conv => enter [1]; rw [← l26 X1 X0 (sK1 ◇ (sK2 ◇ sK1))]
  have l76 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l28 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← l75 sK1 X1 sK2 X0]
  have l77 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l44 sK1 sK2 X0]
    conv => enter [1]; rw [l76 sK2 sK1 X0 X1]
  have l78 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53942 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l79 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l28 sK2 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l78 sK1 sK0]
  have l80 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l79 sK2 sK1 sK0]
  have l81 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l72 sK1 sK2 sK0]
    conv => enter [1]; rw [l80 sK1 sK2 sK0]
  have l82 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l81 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l83 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l82 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l11 sK0 X0 sK1]
  have l84 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l83 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l10 sK0 X0 sK1]
  have l85 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1]; rw [l84 sK1 sK2 X0 sK0]
  have l86 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l32 sK2 sK1 X0]
    conv => enter [1]; rw [l85 sK1 sK2 X0 sK0]
  have l87 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l44 sK1 sK2 X0]
    conv => enter [1]; rw [l86 sK2 sK1 X0 sK0]
  have l88 : ∀ X1 sK0 sK1 X0 sK2 : G, (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro X1 sK0 sK1 X0 sK2
    conv => enter [1]; rw [h53942 X1 ((sK0 ◇ sK1) ◇ X0) sK1]
    conv => enter [1, 2, 2]; rw [← l87 sK1 sK2 X0 sK0]
  have l89 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l77 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l88 X1 sK0 sK1 X0 sK2]
  have l90 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l89 sK1 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← l26 X1 X0 (sK1 ◇ sK1)]
  have l91 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l90 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l70 sK1 sK2]
  have l92 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h53942 sK1 sK1 sK2]
  have l93 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l92 sK2 sK1]
    conv => enter [1]; rw [← l28 sK2 sK1 sK1 sK1]
  have l94 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l93 sK2 sK1]
    conv => enter [1]; rw [← l44 sK1 sK2 sK1]
  have l95 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l94 sK2 sK1]
    conv => enter [1]; rw [l20 sK1 sK2 sK1]
  have l96 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l95 sK2 sK1]
    conv => enter [1]; rw [← l52 sK1 sK2]
  have l97 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l91 sK0 sK1 sK2]
    conv => enter [1]; rw [← l96 sK2 sK1]
  have l98 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l97 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l98 x y z]

theorem Equation4512_53942_implies_Equation53921 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53942 : Equation53942 G) : Equation53921 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X3 X1 X2 X0 : G, (X3 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [← h53942 X1 (X1 ◇ X2) X3]
    conv => enter [1, 2]; rw [h53942 X1 X2 X0]
  have l2 : ∀ X1 sK1 X0 : G, (X1 ◇ (X1 ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h53942 X1 (sK1 ◇ X0) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l0 sK1 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h53942 X1 X2 X0]
    conv => enter [1]; rw [h53942 X1 X2 X1]
    conv => enter [1, 2]; rw [h53942 X1 X2 X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h53942 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h53942 X1 X2 X1]
    conv => enter [1]; rw [h53942 X1 (X1 ◇ X2) X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53942 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l9 : ∀ X1 sK1 X0 : G, (X1 ◇ (X1 ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l2 X1 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l4 sK1 X0]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X1]
    conv => enter [1]; rw [l1 X1 X1 X2 X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1 X0]
    conv => enter [1]; rw [← l4 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l12 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l8 (sK1 ◇ sK1) X1 X0]
    conv => enter [1]; rw [← l9 X1 sK1 X0]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l10 X1 X2 X0]
    conv => enter [1]; rw [l8 X1 X0 (X0 ◇ X2)]
  have l14 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = (X1 ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l11 sK1 X0]
    conv => enter [1]; rw [l12 sK1 X0 X1]
  have l15 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l14 sK1 X0 X1]
    conv => enter [1]; rw [← l13 X1 X0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 sK1 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 sK1 X0]
    conv => enter [1]; rw [h53942 X0 sK1 sK1]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l17 sK1 X0]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l18 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

theorem Equation4512_53942_implies_Equation53846 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53942 : Equation53942 G) : Equation53846 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53942 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h53942 X0 sK0 sK0]
    conv => enter [1]; rw [h53942 X0 sK0 X0]
    conv => enter [1, 2]; rw [h53942 X0 sK0 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53942 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h53942 X0 sK0 sK0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [h53942 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_54186_implies_Equation54165 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54186 : Equation54186 G) : Equation54165 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54186 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54186 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h54186 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h54186 (sK0 ◇ (sK1 ◇ sK1)) sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_54186_implies_Equation54175 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54186 : Equation54186 G) : Equation54175 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h54186 X0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_54186_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54186 : Equation54186 G) : Equation53812 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54186 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54186 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54186 sK1 sK0 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_53866_implies_Equation53863 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53866 : Equation53866 G) : Equation53863 G := by
  have l0 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ X0) X1]
  have l1 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = (sK1 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l2 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l1 sK1 X0 X1]
    conv => enter [1]; rw [← h53866 sK1 X1 X0]
  have l3 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l2 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 X1]
  have l4 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l3 sK1 X0 X1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK1)]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l4 sK1 sK0 (sK1 ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← h53866 sK0 X0 (sK1 ◇ sK1)]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l18 sK0 sK1 X0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l19 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l19 sK0 sK1 sK1]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation4512_53866_implies_Equation53860 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53866 : Equation53866 G) : Equation53860 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← h53866 sK0 X0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK1 ◇ X0)]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53866 sK0 X1 X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 sK1 X1]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [l4 sK0 sK1 sK1 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_53866_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53866 : Equation53866 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53866 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ X0)]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54185_implies_Equation54177 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54185 : Equation54185 G) : Equation54177 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK2 ◇ sK0)]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK2 ◇ sK0)]
  have l4 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK0)) X0]
  have l5 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l6 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h54185 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0 X0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 sK2]
  have l7 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ X2)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h54185 (X1 ◇ X0) X2 X0]
    conv => enter [1, 2]; rw [← h54185 X0 X1 X2]
  have l8 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54185 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h54185 X0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l10 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54185 X0 (sK0 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [← l5 sK2 sK0 sK1 X0]
  have l11 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X0 sK1
    conv => enter [1]; rw [h54185 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 X0]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54185 X0 X2 (X2 ◇ X0)]
    conv => enter [1]; rw [h54185 X0 (X2 ◇ X0) X1]
  have l13 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [h4512 X0 (X2 ◇ (X1 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54185 X0 X1 X2]
  have l14 : ∀ sK1 X0 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [h54185 (sK1 ◇ sK1) X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l4 sK1 sK2 sK0 (X0 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK1 sK2 sK0 X1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [← l4 sK1 sK2 sK0 (X1 ◇ (X0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h54185 (sK2 ◇ sK0) X0 X1]
  have l16 : ∀ sK1 sK2 sK0 X1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK0))))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [l15 sK1 sK2 sK0 X1 X0]
    conv => enter [1]; rw [l4 sK1 sK2 sK0 (X0 ◇ X0)]
  have l17 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l13 X0 X2 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l18 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l12 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X0]
  have l19 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l11 X0 sK1]
    conv => enter [1]; rw [← h54185 X0 (sK1 ◇ sK1) sK1]
  have l20 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54185 X0 (sK1 ◇ sK1) (X0 ◇ sK0)]
    conv => enter [1]; rw [← l10 X0 sK0 sK1 X0]
  have l21 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ (X1 ◇ X1))]
  have l22 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK0)) (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0)))]
  have l23 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l17 X0 X2 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l24 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X2
    conv => enter [1]; rw [l18 X0 X2 X0]
    conv => enter [1]; rw [← l8 X0 X0 X0 X2]
  have l25 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l21 X1 X0 X2]
    conv => enter [1]; rw [← l8 X1 X1 X0 X0]
  have l26 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l22 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l16 sK1 sK2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l23 X0 X2 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ X0) X3]
  have l28 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l25 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ X2)]
  have l29 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l20 (sK1 ◇ (sK2 ◇ sK0)) sK1 sK0]
  have l30 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l27 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l31 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l29 sK1 sK2 sK0]
    conv => enter [1]; rw [← l14 sK1 (sK1 ◇ sK1) sK2 sK0]
  have l32 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l31 sK1 sK2 sK0]
  have l33 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK0)) (sK0 ◇ sK0)]
  have l34 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l33 sK1 sK1 sK1]
  have l35 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l34 sK1]
  have l36 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l35 sK1]
  have l37 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l36 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l38 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l37 sK1 X0]
  have l39 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54185 sK1 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) (sK1 ◇ sK1)]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h54185 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l40 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1]
    conv => enter [1]; rw [l41 sK1 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l42 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l45 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [h54185 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l46 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l45 sK1 sK2 sK0 X0]
  have l47 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l39 sK1 sK2 sK0]
    conv => enter [1]; rw [l46 sK1 sK2 sK0 X0]
  have l48 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54185 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h54185 (sK1 ◇ sK1) sK0 X0]
  have l49 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l50 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [h54185 (sK1 ◇ sK1) sK0 X0]
  have l51 : ∀ X1 X0 sK1 : G, ((X1 ◇ (X0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((X1 ◇ (X0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l9 (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) sK1]
    conv => enter [1, 2]; rw [← h54185 (sK1 ◇ sK1) X0 X1]
  have l52 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h54185 X0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l9 X0 sK1]
  have l53 : ∀ X0 X1 sK1 : G, ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l9 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ sK1) ◇ (X0 ◇ X1))]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l55 : ∀ X0 X1 sK1 : G, ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l53 X0 X1 sK1]
    conv => enter [1]; rw [← l30 X0 (sK1 ◇ sK1) X1 X1]
  have l56 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l19 X0 sK1]
    conv => enter [1]; rw [l52 X0 sK1]
  have l57 : ∀ X1 X0 sK1 : G, ((X1 ◇ (X0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (X1 ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l51 X1 X0 sK1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ sK1) ◇ (X0 ◇ X0))]
  have l58 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l50 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l59 : ∀ X0 X1 sK1 : G, ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l55 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l38 sK1 X1]
  have l60 : ∀ X1 X0 sK1 : G, ((X1 ◇ (X0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l57 X1 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (X0 ◇ X0))]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l58 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l62 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l59 X0 X1 sK1]
  have l63 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 sK1
    conv => enter [1, 2]; rw [l8 X0 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l60 X1 X0 sK1]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l49 sK0 sK1 sK0]
  have l65 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l63 X1 X0 sK1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54185 sK0 sK0 sK0]
    conv => enter [1]; rw [← l64 sK0 sK1]
  have l67 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l65 X1 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l69 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l67 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l19 X0 sK1]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l68 sK0 sK1]
  have l71 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54185 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l54 sK0 sK1]
  have l72 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l73 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l24 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l71 sK0 sK1 X0]
  have l74 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [l73 sK0 X0 sK1]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [h54185 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l70 sK0 sK1]
  have l76 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l44 sK0 sK1]
  have l78 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 sK1 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK1))]
  have l79 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l74 sK0 sK1 X0]
    conv => enter [1]; rw [← h54185 (sK0 ◇ (sK1 ◇ sK1)) X0 sK0]
  have l80 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l79 sK0 sK1 X0]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [← l76 sK0 sK1 sK1]
  have l82 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l47 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l83 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l82 sK0 sK1 sK2 X0]
  have l84 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [l83 sK0 sK1 sK2 X0]
  have l85 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l84 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [h54185 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [← l84 sK0 sK1 sK2 sK0]
  have l86 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l78 sK0 sK1 sK2]
    conv => enter [1]; rw [l85 sK0 sK1 sK2 X0]
  have l87 : ∀ X0 sK1 X1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1, 1]; rw [l19 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) X1]
  have l88 : ∀ X0 sK1 X1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l87 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X1]
  have l89 : ∀ X0 sK1 X1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l88 X0 sK1 X1]
    conv => enter [1, 2]; rw [← l38 sK1 X1]
  have l90 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l62 X0 X1 sK1]
    conv => enter [1]; rw [← l89 X0 sK1 X1]
  have l91 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l90 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l92 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54185 sK0 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [h54185 (sK1 ◇ (sK2 ◇ sK0)) sK0 X0]
  have l93 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l92 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l94 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [l93 sK0 sK1 sK2 X0]
  have l95 : ∀ X0 sK0 sK1 sK2 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [h54185 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X1]
    conv => enter [1, 2, 2]; rw [← l94 sK0 sK1 sK2 X0]
  have l96 : ∀ X0 sK0 sK1 sK2 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [l95 X0 sK0 sK1 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) (X1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l97 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l86 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l96 X0 sK0 sK1 sK2 X0]
  have l98 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l97 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l99 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l98 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l69 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
  have l100 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l99 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l91 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
  have l101 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l100 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l102 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [l101 sK0 sK1 sK2]
  have l103 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l102 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0]
  have l104 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l72 sK0 sK1 (X1 ◇ (X0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54185 sK0 X0 X1]
  have l105 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l72 sK0 sK1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l104 sK0 sK1 X1 X0]
  have l106 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l80 sK0 sK1 X0]
    conv => enter [1]; rw [l105 sK0 sK1 X0 X1]
  have l107 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [l106 sK0 sK1 X1 X0]
  have l108 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l107 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [← l103 sK0 sK1 (X0 ◇ sK0) sK0]
  have l109 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54185 sK0 X0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l108 sK0 sK1 X0]
  have l110 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [← l109 sK0 X0 sK1]
  have l111 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l110 sK0 sK1 sK2]
    conv => enter [1]; rw [h54185 sK0 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l111 x y y z]

theorem Equation4512_54185_implies_Equation54167 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54185 : Equation54185 G) : Equation54167 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l3 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l4 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54185 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l5 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 sK2
    conv => enter [1]; rw [h54185 X0 sK2 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l6 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X0 sK2
    conv => enter [1]; rw [h54185 X0 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK2 X0]
  have l7 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [h4512 X0 (X2 ◇ (X1 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54185 X0 X1 X2]
  have l8 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X1 ◇ (X0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54185 sK0 X0 X1]
  have l9 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l8 sK1 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ X0)]
  have l10 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l7 X0 X2 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l11 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [l6 X0 sK2]
    conv => enter [1]; rw [← h54185 X0 (sK2 ◇ sK2) sK2]
  have l12 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l10 X0 X2 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l13 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l12 X0 X2 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ X0) X3]
  have l14 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l13 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l15 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h54185 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l16 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [h54185 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l17 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h54185 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1, 2]; rw [← h54185 sK2 sK2 X0]
  have l18 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l17 sK2 X0]
  have l19 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l16 sK2 X0]
  have l20 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54185 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l18 sK2 X0]
  have l21 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l15 sK2]
    conv => enter [1]; rw [l19 sK2 X0]
  have l22 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h54185 sK2 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l23 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l22 sK2 sK0]
  have l24 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l15 sK2]
    conv => enter [1]; rw [l23 sK2 sK0]
  have l25 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l15 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l26 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l15 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l27 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l26 sK2 X0]
  have l28 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [l25 sK0 sK2]
  have l29 : ∀ X1 X0 sK2 : G, ((X1 ◇ (X0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((X1 ◇ (X0 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X0))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l5 (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) sK2]
    conv => enter [1, 2]; rw [← h54185 (sK2 ◇ sK2) X0 X1]
  have l30 : ∀ X0 sK2 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [h54185 X0 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l5 X0 sK2]
  have l31 : ∀ X0 X1 sK2 : G, ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1)))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l5 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK2 ◇ sK2) ◇ (X0 ◇ X1))]
  have l32 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) sK0]
  have l33 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK2) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK2 ◇ sK2) ◇ sK0)]
  have l34 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 (sK0 ◇ (sK1 ◇ sK0)) sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 (sK0 ◇ (sK1 ◇ sK0)) sK2]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK2)]
  have l37 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l34 sK1 sK0 sK2]
    conv => enter [1]; rw [← l0 sK1 sK0 (sK2 ◇ sK2)]
  have l38 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK2) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l33 sK1 sK0 sK2]
  have l39 : ∀ X0 X1 sK2 : G, ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l31 X0 X1 sK2]
    conv => enter [1]; rw [← l14 X0 (sK2 ◇ sK2) X1 X1]
  have l40 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [l11 X0 sK2]
    conv => enter [1]; rw [l30 X0 sK2]
  have l41 : ∀ X1 X0 sK2 : G, ((X1 ◇ (X0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (X1 ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X0)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l29 X1 X0 sK2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (sK2 ◇ sK2)) ((sK2 ◇ sK2) ◇ (X0 ◇ X0))]
  have l42 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l37 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← h54185 (sK1 ◇ sK0) sK0 (sK2 ◇ sK2)]
  have l43 : ∀ X0 X1 sK2 : G, ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l39 X0 X1 sK2]
    conv => enter [1, 2]; rw [← l27 sK2 X1]
  have l44 : ∀ X1 X0 sK2 : G, ((X1 ◇ (X0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X0))))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l41 X1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ (X0 ◇ X0))]
  have l45 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l9 sK1 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l42 sK1 sK0 sK2]
  have l46 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l43 X0 X1 sK2]
  have l47 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 sK2
    conv => enter [1, 2]; rw [l4 X0 X0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l44 X1 X0 sK2]
  have l48 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l40 (sK1 ◇ sK0) sK2]
    conv => enter [1]; rw [← l45 sK1 sK0 sK2]
  have l49 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l47 X1 X0 sK2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l50 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l49 X1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l51 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l50 X1 X0 sK2]
    conv => enter [1, 2]; rw [← l11 X0 sK2]
  have l52 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l32 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) sK0 X0]
  have l53 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [l20 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (X0 ◇ X0)]
  have l54 : ∀ sK2 X1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l20 sK2 X0]
    conv => enter [1]; rw [h54185 (sK2 ◇ sK2) X0 X1]
  have l55 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [l53 sK0 sK2 X0]
  have l56 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((X0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1, 2, 2]; rw [l21 sK2 X0]
    conv => enter [1]; rw [← h54185 (X0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X1]
  have l57 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l56 X0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l58 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((X0 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l51 X0 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l57 X0 sK2 X1]
  have l59 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l58 X0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) (X1 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
  have l60 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1, 2]; rw [l54 sK2 X0 sK2]
    conv => enter [1]; rw [← l59 X0 sK2 X0]
  have l61 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l60 X0 sK2]
    conv => enter [1]; rw [← l11 X0 sK2]
  have l62 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = (X0 ◇ (((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1, 1]; rw [l11 X0 sK2]
    conv => enter [1]; rw [← h4512 X0 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) X1]
  have l63 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l11 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l64 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l62 X0 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X1]
  have l65 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l64 X0 sK2 X1]
    conv => enter [1, 2]; rw [← l27 sK2 X1]
  have l66 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l46 X0 X1 sK2]
    conv => enter [1]; rw [← l65 X0 sK2 X1]
  have l67 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l66 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l68 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l63 sK0 sK2]
    conv => enter [1]; rw [← l28 sK0 sK2]
  have l69 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l63 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X0]
  have l70 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h54185 (sK1 ◇ sK0) sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK0))]
  have l71 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l48 sK1 sK0 sK2]
    conv => enter [1]; rw [l70 sK1 sK0 X0 X1]
  have l72 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [← l36 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 sK0 ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l73 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l71 sK1 sK0 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l72 sK1 sK0 sK2]
  have l74 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l73 sK1 sK0 sK2]
    conv => enter [1]; rw [← l1 sK1 sK0 (sK2 ◇ sK2)]
  have l75 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h54185 sK0 (sK2 ◇ sK2) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l38 sK1 sK0 sK2]
  have l76 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l75 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ sK2)]
  have l77 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l76 sK0 sK2 sK1]
  have l78 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l63 sK0 sK2]
    conv => enter [1]; rw [l77 sK0 sK2 sK1]
  have l79 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l78 sK0 sK2 sK1]
  have l80 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l79 sK0 sK1 sK2]
  have l81 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l80 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK2 ◇ sK2))]
  have l82 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l74 sK1 sK0 sK2]
    conv => enter [1]; rw [l81 sK1 sK0 sK2]
  have l83 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l82 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK2 ◇ sK2))]
  have l84 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l83 sK0 sK1 sK2]
  have l85 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l78 sK0 sK2 sK1]
    conv => enter [1]; rw [l84 sK0 sK1 sK2]
  have l86 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h54185 (sK0 ◇ (sK2 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l85 sK0 sK2 sK1]
  have l87 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l55 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l86 sK0 sK2 sK0 X0]
  have l88 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l68 sK0 sK2]
    conv => enter [1]; rw [l87 sK0 sK2 X0]
  have l89 : ∀ X0 sK0 sK2 X1 : G, ((X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h54185 (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) (sK0 ◇ (sK2 ◇ sK2)) X1]
    conv => enter [1, 2, 2]; rw [← l88 sK0 sK2 X0]
  have l90 : ∀ X0 sK0 sK2 X1 : G, ((X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l89 X0 sK0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK2 ◇ sK2)) (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l91 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l88 sK0 sK2 X0]
    conv => enter [1]; rw [← l90 X0 sK0 sK2 X0]
  have l92 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l91 X0 sK0 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK2 ◇ sK2)) ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l93 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l92 X0 sK0 sK2]
    conv => enter [1]; rw [l51 X0 (sK0 ◇ (sK2 ◇ sK2)) sK2]
  have l94 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l93 X0 sK0 sK2]
    conv => enter [1]; rw [l67 X0 (sK0 ◇ (sK2 ◇ sK2)) sK2]
  have l95 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK0
    conv => enter [1, 2]; rw [l24 sK2 sK0]
    conv => enter [1]; rw [← l94 X0 sK0 sK2]
  have l96 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l95 X0 sK2 sK0]
    conv => enter [1]; rw [l61 X0 sK2]
  have l97 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [l52 sK0 sK2 (X1 ◇ (X0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54185 sK0 X0 X1]
  have l98 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l52 sK0 sK2 (X0 ◇ X0)]
    conv => enter [1]; rw [← l97 sK0 sK2 X1 X0]
  have l99 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [l55 sK0 sK2 X0]
    conv => enter [1]; rw [l98 sK0 sK2 X0 X1]
  have l100 : ∀ sK0 sK2 X1 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [l68 sK0 sK2]
    conv => enter [1]; rw [l99 sK0 sK2 X1 X0]
  have l101 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l100 sK0 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [← l69 sK0 sK2 (X0 ◇ sK0)]
  have l102 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54185 sK0 X0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l101 sK0 sK2 X0]
  have l103 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l96 sK0 sK0 sK2]
    conv => enter [1]; rw [← l102 sK0 X0 sK2]
  have l104 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l103 sK0 sK2 sK1]
    conv => enter [1]; rw [h54185 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l104 x y x z]

theorem Equation4512_54185_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54185 : Equation54185 G) : Equation53818 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54185 ((sK0 ◇ sK0) ◇ X0) sK0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54185 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2]; rw [l3 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54185 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54185 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54185 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54185 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54185 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54185 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l8 sK0 X0]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (X0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54185 sK0 X0 X1]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l17 sK0 X1 X0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l16 X0 sK0]
    conv => enter [1]; rw [← h54185 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 X0 sK0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l11 sK0 X0]
  have l22 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [h54185 (sK0 ◇ sK0) sK0 X0]
  have l24 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l25 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l19 X0 sK0]
  have l26 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 sK0]
    conv => enter [1]; rw [← l15 X0 sK0]
  have l27 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l12 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l29 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← h54185 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l30 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1, 2]; rw [← l25 X0 sK0]
  have l31 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1, 2]; rw [← l25 X0 sK0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l30 sK0 X0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l31 sK0 X0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l36 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54185 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l34 sK0 sK0]
  have l37 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0 sK0 sK0]
    conv => enter [1]; rw [← l35 sK0 sK0]
  have l38 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l36 sK0]
  have l39 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l37 sK0]
  have l40 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54185 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l38 sK0]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l39 sK0]
  have l42 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l40 sK0]
    conv => enter [1]; rw [← l41 sK0]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l42 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l44 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l42 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l45 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l43 sK0]
  have l46 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h54185 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l47 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h54185 sK0 sK0 X0]
    conv => enter [1]; rw [← h54185 (sK0 ◇ sK0) X0 sK0]
  have l48 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [l47 sK0 X0]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l46 sK0 X0]
  have l50 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l48 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X0) X1]
  have l51 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l50 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l52 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1, 2, 2]; rw [l49 sK0 X0]
    conv => enter [1]; rw [← h54185 (X0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X1]
  have l53 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l52 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l54 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l53 X0 sK0 X1]
    conv => enter [1, 2]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l55 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l44 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l54 X0 sK0 X1]
  have l56 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l55 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l57 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l28 sK0 X0]
    conv => enter [1]; rw [← l56 X0 sK0 X0]
  have l58 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l57 X0 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l59 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l58 X0 sK0]
    conv => enter [1, 2]; rw [← l45 sK0]
  have l60 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l26 X0 sK0]
    conv => enter [1]; rw [l59 X0 sK0]
  have l61 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X0 ◇ X0)) = (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54185 ((sK0 ◇ sK0) ◇ X0) X0 X1]
    conv => enter [1, 2, 2]; rw [← l13 X0 sK0]
  have l62 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l61 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l63 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (((sK0 ◇ sK0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 (sK0 ◇ sK0) X0 X0 sK0]
    conv => enter [1]; rw [← l62 sK0 X0 sK0]
  have l64 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l63 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X0 ◇ X0)]
  have l65 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l51 sK0 X0 X0]
    conv => enter [1]; rw [← l64 sK0 X0]
  have l66 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 X0]
    conv => enter [1]; rw [← l65 sK0 X0]
  have l67 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54185 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l66 sK0 (X1 ◇ X0)]
  have l68 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l67 X0 X1 sK0]
    conv => enter [1]; rw [← l60 X0 sK0]
  have l69 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l68 sK0 sK0 sK2]
    conv => enter [1]; rw [h54185 sK0 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l69 x y z]

theorem Equation4512_53903_implies_Equation53917 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53903 : Equation53903 G) : Equation53917 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X1))) = ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h53903 X1 (X2 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h53903 X0 X1 X2]
  have l1 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [h53903 sK2 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK1) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X2 X1 (X0 ◇ (X0 ◇ X1))]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h53903 X0 X1 X0]
    conv => enter [1]; rw [← l2 X1 X2 X0]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1]; rw [← h53903 X1 X1 X2]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h53903 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK2 sK1 sK0 sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK1]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK1 X0]
  have l8 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l4 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK1 X0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK0 (sK1 ◇ X0)]
  have l9 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l8 X0 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l4 X1 X0 X0]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK0 X0]
  have l11 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h53903 X0 X0 X0]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK0 X0]
  have l12 : ∀ X1 X0 sK1 sK2 sK0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro X1 X0 sK1 sK2 sK0
    conv => enter [1]; rw [h53903 X1 X0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK0 X0 X1]
  have l13 : ∀ X1 X0 sK1 sK2 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro X1 X0 sK1 sK2 sK0
    conv => enter [1]; rw [l12 X1 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0 X0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_53903_implies_Equation53921 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53903 : Equation53903 G) : Equation53921 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK2 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X1))) = ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h53903 X1 (X2 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h53903 X0 X1 X2]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h53903 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53903 (sK1 ◇ sK1) X0 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l2 sK1 sK2 X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53903 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53903 sK1 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l5 sK1 X0 sK1]
  have l9 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l3 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X2 X1 (X0 ◇ (X0 ◇ X1))]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l8 sK1 X0]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h53903 X0 X1 X0]
    conv => enter [1]; rw [← l9 X1 X2 X0]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l12 X2 X0 X1]
    conv => enter [1]; rw [← h53903 X1 X1 X2]
  have l14 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l15 : ∀ X0 sK1 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((X0 ◇ (X1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h53903 X0 (sK1 ◇ sK1) X1]
    conv => enter [1]; rw [l4 sK1 (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h53903 X0 (sK1 ◇ sK1) X1]
  have l16 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l4 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ sK1) ◇ (X0 ◇ X1))]
  have l17 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l16 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h53903 (sK1 ◇ sK1) X1 X0]
  have l18 : ∀ X0 sK1 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l15 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK1 ◇ sK1)) (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))]
  have l19 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l20 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l17 sK1 X0 X1]
    conv => enter [1, 2]; rw [← l11 sK1 X1]
  have l21 : ∀ X0 sK1 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l18 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK1 ◇ sK1) (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))]
  have l22 : ∀ X0 sK1 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l21 X0 sK1 X1]
    conv => enter [1, 2, 2]; rw [← h53903 X0 (sK1 ◇ sK1) X0]
  have l23 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l22 X0 sK1 X0]
    conv => enter [1, 2]; rw [l13 X0 X0 (sK1 ◇ sK1)]
  have l24 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l23 X0 sK1]
    conv => enter [1]; rw [l13 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l25 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l24 X0 sK1]
  have l26 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [l25 sK1 X0]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [l20 sK1 sK0 (sK1 ◇ sK1)]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1, 2]; rw [← l19 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l31 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h53903 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l32 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l13 sK0 X0 sK1]
    conv => enter [1]; rw [l31 sK0 X0 sK1]
  have l33 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l32 sK1 sK0 X0]
  have l34 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l33 sK1 sK0 X0]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h53903 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53903 sK0 sK1 sK0]
    conv => enter [1]; rw [l35 sK1 sK0]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l36 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l34 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l30 sK1 sK0]
  have l42 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53903 X0 (sK1 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l40 sK0 sK1]
  have l43 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l26 sK1 X0]
    conv => enter [1]; rw [l42 X0 sK1 sK0]
  have l44 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [l43 sK1 X0 sK0]
  have l45 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l44 sK0 sK1 X0]
    conv => enter [1]; rw [← l42 X0 sK1 sK0]
  have l46 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l44 sK0 sK1 X0]
    conv => enter [1]; rw [l4 sK1 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l44 sK0 sK1 X0]
  have l47 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l46 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l48 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l47 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l37 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l50 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53903 X0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l49 sK0 sK1]
  have l51 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l50 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l48 sK0 sK1 X0]
  have l52 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53903 sK0 sK1 sK0]
    conv => enter [1]; rw [← l51 X0 sK1 sK0]
  have l53 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l52 sK0 sK1 X0]
    conv => enter [1]; rw [h53903 X0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [l53 x y z]

theorem Equation4512_53903_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53903 : Equation53903 G) : Equation53818 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X2)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h53903 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [h53903 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53903 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l10 sK0 X0]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 (X0 ◇ (X1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h53903 X0 sK0 X1]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (X1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h53903 X0 sK0 X1]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h53903 X0 sK0 X1]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53903 X0 sK0 X0]
    conv => enter [1]; rw [← l16 sK0 X0 X1]
  have l18 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1]; rw [l15 sK0 X0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53903 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53903 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l21 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l17 X0 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 X0 X1]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0 sK0]
    conv => enter [1]; rw [← l21 X0 sK0 sK0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l28 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [h53903 X0 sK0 X1]
  intro x y z
  conv => enter [1]; rw [l28 x y z]

@[equational_result]
theorem Equation54180_implies_Equation54173 (G : Type*) [Magma G] (h54180 : Equation54180 G) : Equation54173 G := by
  intro x y z
  conv => enter [1]; rw [h54180 x y x z]

@[equational_result]
theorem Equation54180_implies_Equation54178 (G : Type*) [Magma G] (h54180 : Equation54180 G) : Equation54178 G := by
  intro x y z
  conv => enter [1]; rw [h54180 x y z y]

@[equational_result]
theorem Equation54180_implies_Equation54177 (G : Type*) [Magma G] (h54180 : Equation54180 G) : Equation54177 G := by
  intro x y z
  conv => enter [1]; rw [h54180 x y z x]

theorem Equation4512_54180_implies_Equation54179 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54180 : Equation54180 G) : Equation54179 G := by
  have l0 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h54180 X1 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) X0]
  have l1 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [h54180 X1 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) X0]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h54180 X0 (sK1 ◇ (sK2 ◇ sK2)) sK2 sK2]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l3 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_54180_implies_Equation53811 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54180 : Equation54180 G) : Equation53811 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54180 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_54180_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54180 : Equation54180 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54180 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54180_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54180 : Equation54180 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54180 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation53985_implies_Equation53951 (G : Type*) [Magma G] (h53985 : Equation53985 G) : Equation53951 G := by
  intro x y z
  conv => enter [1]; rw [h53985 x y z y]

@[equational_result]
theorem Equation53985_implies_Equation53880 (G : Type*) [Magma G] (h53985 : Equation53985 G) : Equation53880 G := by
  intro x y z
  conv => enter [1]; rw [h53985 x y x z]

@[equational_result]
theorem Equation53985_implies_Equation53917 (G : Type*) [Magma G] (h53985 : Equation53985 G) : Equation53917 G := by
  intro x y z
  conv => enter [1]; rw [h53985 x y y z]

theorem Equation4512_53985_implies_Equation53968 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53985 : Equation53985 G) : Equation53968 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h53985 sK2 (sK0 ◇ sK1) sK2 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53985 sK0 sK1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK2]
    conv => enter [1]; rw [← l0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation53985_implies_Equation53842 (G : Type*) [Magma G] (h53985 : Equation53985 G) : Equation53842 G := by
  intro x y z
  conv => enter [1]; rw [h53985 x x y z]

@[equational_result]
theorem Equation53985_implies_Equation53812 (G : Type*) [Magma G] (h53985 : Equation53985 G) : Equation53812 G := by
  intro x y
  conv => enter [1]; rw [h53985 x x x y]

theorem Equation4512_53985_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53985 : Equation53985 G) : Equation53832 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53985 sK1 (sK0 ◇ sK0) sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53985 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_54179_implies_Equation54176 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54179 : Equation54179 G) : Equation54176 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK2)]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK2]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK2 X0]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54179 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK2]
  have l8 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54179 X0 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l9 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54179 X0 (sK1 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK2]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54179 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ X0)]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54179 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ X0)]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (X0 ◇ X0)]
    conv => enter [1]; rw [← h54179 sK1 (sK1 ◇ sK2) X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h54179 (sK1 ◇ sK1) sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X0)]
  have l14 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54179 (sK1 ◇ sK1) (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l3 sK1 sK2 (X0 ◇ X0)]
  have l15 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2 sK1]
    conv => enter [1]; rw [← h54179 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l16 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1 sK1]
  have l17 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l18 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l11 sK1 sK2 X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
  have l20 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [h54179 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l21 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l16 sK1]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l3 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l20 sK1 sK2]
  have l23 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l21 sK1]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK1 sK2]
    conv => enter [1]; rw [l22 sK1 sK2]
  have l25 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l23 sK1]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l17 sK1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l27 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) = (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← l27 sK0 sK1 sK2]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK1) X0]
  have l30 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l3 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l18 sK1 sK2 X0]
  have l31 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l30 sK1 sK2 X0]
    conv => enter [1]; rw [l3 sK1 sK2 sK2]
  have l32 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l31 sK1 sK2 X0]
    conv => enter [1]; rw [← l9 sK1 sK1 sK2]
  have l33 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l25 sK1]
    conv => enter [1]; rw [← l32 sK1 sK2 X0]
  have l34 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l33 sK1 sK2 sK1]
    conv => enter [1]; rw [← h54179 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l35 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l34 sK1 sK2]
    conv => enter [1]; rw [h54179 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l36 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1 sK1]
    conv => enter [1]; rw [← l35 sK1 sK1]
  have l37 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [l18 sK1 sK2 sK1]
  have l38 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK1)]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l36 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1, 2]; rw [l38 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK1)]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54179 sK0 sK1 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l44 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 sK2]
  have l45 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [l45 sK0 sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 sK1 sK2]
    conv => enter [1]; rw [l42 sK0 sK1 sK2]
  have l48 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l47 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK1) X0]
  have l49 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l7 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) ((sK1 ◇ sK2) ◇ sK2)]
  have l50 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 sK1 sK2]
    conv => enter [1]; rw [l29 sK0 sK1 sK2 sK2]
  have l51 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l48 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [← l50 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK1)]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
    conv => enter [1]; rw [← l52 sK0 sK1 sK2]
  have l54 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l54 x y z]

@[equational_result]
theorem Equation54179_implies_Equation54171 (G : Type*) [Magma G] (h54179 : Equation54179 G) : Equation54171 G := by
  intro x y
  conv => enter [1]; rw [h54179 x y x]

theorem Equation4512_54179_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54179 : Equation54179 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54179 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l3 x y]

end Semigroup5
