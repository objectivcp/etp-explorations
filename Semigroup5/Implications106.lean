import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53808_53900_implies_Equation53833 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53900 : Equation53900 G) : Equation53833 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53808 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53900 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l13 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))]
  have l16 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [l16 sK0 X0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [← l19 sK0 sK1 X0]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation4512_53808_53900_implies_Equation53840 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53900 : Equation53900 G) : Equation53840 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h53808 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l4 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 X0]
  have l5 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h53808 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53808 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l4 sK2 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l13 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l5 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 sK2]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53900 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53900 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l12 sK0 (X0 ◇ X0)]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [l16 sK0 X0]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1, 2]; rw [← l14 sK1 sK2]
  have l19 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l17 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l8 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l19 sK2 sK0]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l17 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l20 sK2 sK0]
  have l22 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1, 2]; rw [l21 sK2 sK0]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l22 sK1 sK2 sK0]
  have l24 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1, 2]; rw [← l23 sK0 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l24 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l25 x y z]

theorem Equation4512_53808_53900_implies_Equation53823 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53900 : Equation53900 G) : Equation53823 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h53900 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h53900 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53900 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X0]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l5 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l6 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53808 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h53808 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h53900 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h53808 X1 X0]
    conv => enter [1, 2]; rw [h53900 X1 X0]
  have l13 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [l9 (X0 ◇ X1) X0 (X1 ◇ X2)]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l14 X0 X1 X2]
    conv => enter [1]; rw [l3 (X0 ◇ X1) X0 X1]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2, 2]; rw [← h53808 X0 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 2, 2]; rw [← h53900 X0 X1]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h53808 X0 X1]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1]; rw [l9 (X0 ◇ X1) X0 (X0 ◇ X0)]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [l9 (X0 ◇ (X1 ◇ X1)) X1 (X0 ◇ (X0 ◇ X1))]
  have l22 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [l9 (X0 ◇ (X0 ◇ X1)) X0 (X0 ◇ (X0 ◇ X0))]
  have l23 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l24 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l25 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
  have l26 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h53808 X0 X0]
  have l27 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l28 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) X0 X1]
    conv => enter [1]; rw [l26 X0 X1]
  have l30 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l27 X0 X1]
    conv => enter [1, 2, 2]; rw [← h53808 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h53808 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [← l28 X0 X1]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l29 X0 X1]
  have l33 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l30 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ (X1 ◇ X1)) X0 (X1 ◇ X1)]
  have l34 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l31 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ (X0 ◇ X1)) X0 (X0 ◇ X1)]
  have l35 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l33 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))))]
  have l36 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l34 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))))]
  have l37 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l35 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))]
  have l38 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l36 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))))]
  have l39 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))]
  have l40 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l38 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))))]
  have l41 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l39 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 X1 (X0 ◇ (X1 ◇ X1))]
  have l42 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l40 X0 X1]
    conv => enter [1]; rw [l16 X0 X1 (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))))]
  have l43 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l42 X0 X1]
    conv => enter [1]; rw [l32 X0 X1]
  have l44 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l42 X0 X1]
    conv => enter [1]; rw [← l16 X0 X1 X2]
  have l45 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l44 X1 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))]
    conv => enter [1]; rw [← l41 X1 X0]
  have l46 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l43 X0 X1]
    conv => enter [1, 2]; rw [← l45 X1 X0]
  have l47 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l46 X1 X0]
    conv => enter [1]; rw [← l45 X0 X1]
  have l48 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h53900 X0 X1]
    conv => enter [1]; rw [l9 X1 X0 (X1 ◇ X1)]
  have l49 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [l47 X0 X2]
    conv => enter [1, 2]; rw [l12 X0 X1]
  have l50 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h53808 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X1 X0]
  have l51 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X1 X0]
    conv => enter [1, 2]; rw [l9 X1 X1 X0]
    conv => enter [1, 2]; rw [l7 X1 X1 X0]
  have l52 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1 X1]
    conv => enter [1]; rw [← l9 X0 X1 X1]
  have l53 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l52 X0 X1]
    conv => enter [1]; rw [l49 X0 X1 X2]
    conv => enter [1, 2]; rw [l52 X0 X1]
  have l54 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l48 X0 X1]
    conv => enter [1]; rw [← l51 X0 X1]
  have l55 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l50 X1 X0]
    conv => enter [1]; rw [← l53 X1 X0 X0]
  have l56 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l54 X0 X1]
    conv => enter [1]; rw [← l53 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l55 x y]
  conv => enter [1]; rw [← l56 y x]

theorem Equation4512_53822_54013_implies_Equation54088 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h54013 : Equation54013 G) : Equation54088 G := by
  have l0 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2]; rw [h54013 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2, 2, 2]; rw [← h54013 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h54013 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h54013 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54013 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h54013 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_53808_54020_implies_Equation54022 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54020 : Equation54020 G) : Equation54022 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54020 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54020 sK0 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ (sK0 ◇ X0))]
    conv => enter [1, 2]; rw [← h53808 sK0 X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ X0)]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 sK0 sK1 X0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4512_53822_53860_implies_Equation53934 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53860 : Equation53860 G) : Equation53934 G := by
  have l0 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h53860 X0 X2]
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h53860 X0 X2]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h53860 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← h53860 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53860 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h53860 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_53808_54175_implies_Equation54176 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54175 : Equation54175 G) : Equation54176 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK2]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [← h53808 sK1 X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
  have l4 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ (sK1 ◇ sK1)) X1]
    conv => enter [1, 1]; rw [← h54175 X0 sK1]
  have l5 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l4 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l6 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l5 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X1]
  have l7 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1, 2]; rw [← l3 sK1 X1]
    conv => enter [1]; rw [← l6 X0 sK1 X1]
  have l8 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h54175 X0 sK1]
    conv => enter [1]; rw [l7 X0 sK1 X1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_53822_54175_implies_Equation4272 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h54175 : Equation54175 G) : Equation4272 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X0))) = (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h53822 X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X0))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [← h54175 sK1 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h54175 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_53822_54175_implies_Equation54186 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h54175 : Equation54175 G) : Equation54186 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53822 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53822 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1, 2]; rw [h53822 X0 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (X0 ◇ (X0 ◇ X0))]
  have l3 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [← h54175 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) X0]
  have l4 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l3 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [← h54175 sK0 X0]
  have l5 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l1 sK1]
  have l6 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l5 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l5 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l9 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l6 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l10 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l9 sK2 sK1]
  have l11 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l10 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l5 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1, 2]; rw [l5 sK1]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK1]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) sK1]
  have l15 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l5 sK1]
    conv => enter [1]; rw [l14 sK1 sK2]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) sK1]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 sK0 sK2 sK1]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK0 sK1 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1, 2]; rw [← l22 sK0 sK1]
  have l24 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← h54175 X0 sK1]
  have l25 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← l5 sK1]
    conv => enter [1]; rw [l24 X0 sK1]
  have l26 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l25 X0 sK1]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [l26 X0 sK0 sK1]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l27 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l28 x y z]

theorem Equation4512_53822_54175_implies_Equation53842 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h54175 : Equation54175 G) : Equation53842 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h54175 X0 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_53808_53860_implies_Equation4268 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53860 : Equation53860 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53808 X0 X1]
    conv => enter [1]; rw [← h53860 X0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h53860 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_53808_53860_implies_Equation53864 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53860 : Equation53860 G) : Equation53864 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h53808 sK0 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h53808 sK0 (sK1 ◇ sK2)]
  have l3 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [h53808 sK0 (sK1 ◇ sK2)]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [← l3 sK0 X0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h53860 sK0 X0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53808 sK0 sK1]
    conv => enter [1]; rw [h53808 sK0 (sK1 ◇ sK2)]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK0 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation4512_53808_53860_implies_Equation53866 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53860 : Equation53860 G) : Equation53866 G := by
  have l0 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h53808 sK0 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK2 ◇ sK1) X0]
  have l1 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l2 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l1 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [h53808 sK0 (sK2 ◇ sK1)]
  have l3 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) ◇ X0) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [h53808 sK0 (sK2 ◇ sK1)]
  have l4 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1]; rw [← l3 sK0 X0 sK2 sK1]
  have l5 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h53860 sK0 X0]
  have l7 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l2 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [l6 sK0 sK2 sK1 X0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53808 sK0 sK1]
    conv => enter [1]; rw [h53808 sK0 (sK2 ◇ sK1)]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l7 sK0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l7 sK0 sK0 sK1 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation4512_53808_53860_implies_Equation53811 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53860 : Equation53860 G) : Equation53811 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53860 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53860 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_53822_54023_implies_Equation54088 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h54023 : Equation54023 G) : Equation54088 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54023 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h54023 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l8 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54023 (X0 ◇ X1) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h54023 X1 X0]
    conv => enter [1]; rw [← l11 X0 X1]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← l12 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [← l12 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h54023 X1 X0]
    conv => enter [1]; rw [← l15 X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1]; rw [← l13 X0 X1 X1]
  have l18 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1, 2]; rw [← l17 X1 X0]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

theorem Equation4512_53822_54023_implies_Equation54060 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h54023 : Equation54023 G) : Equation54060 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54023 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h54023 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l8 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54023 (X0 ◇ X1) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2]; rw [← h54023 X1 X0]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2]; rw [l12 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [l12 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X1 X0]
    conv => enter [1, 2, 2]; rw [← l12 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l9 X0 X1 X1]
    conv => enter [1]; rw [← l15 X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l14 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1 X1]
    conv => enter [1]; rw [l16 X1 X0]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h54023 X1 X0]
    conv => enter [1]; rw [← l17 X1 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1]; rw [← l13 X0 X1 X1]
  have l21 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1, 2]; rw [← l20 X1 X0]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [← l21 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l22 y x]

theorem Equation4512_53808_54023_implies_Equation54022 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54023 : Equation54023 G) : Equation54022 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54023 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h54023 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [← l2 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h54023 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h53808 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2]; rw [← h54023 X1 X0]
  have l11 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l6 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ X3))]
  have l12 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l11 X2 X0 X1 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l10 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← l6 X0 (X0 ◇ X1) X1]
  have l14 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l10 X0 X1]
    conv => enter [1]; rw [h54023 (X1 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1, 2, 2]; rw [l10 X0 X1]
  have l15 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← l15 X0 X1 X2]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l16 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0))) X2]
  have l20 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l21 X0 X1]
  have l25 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l22 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h53808 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← l23 X1 X0]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ ((X0 ◇ X1) ◇ X0))]
  have l28 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l25 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 X2]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l26 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l27 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X0]
  have l31 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l28 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h53808 X0 X2]
  have l32 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l29 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l33 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l30 X0 X1]
    conv => enter [1, 2]; rw [← l6 X1 X0 X0]
  have l34 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l31 X0 X1 X2]
  have l35 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l32 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l36 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l35 X1 X0]
    conv => enter [1]; rw [← l12 X1 X0 X0 (X0 ◇ X1)]
  have l37 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l36 X1 X0]
    conv => enter [1]; rw [← l6 X1 X0 (X0 ◇ X1)]
  have l38 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h53808 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l3 X1 X0 X0]
  have l39 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X0 X1]
    conv => enter [1]; rw [← l6 X1 X0 (X0 ◇ (X1 ◇ X0))]
  have l40 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0 X0]
    conv => enter [1]; rw [l39 X1 X0]
  have l41 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l40 X0 X1]
    conv => enter [1]; rw [l33 X0 X1]
  have l42 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l38 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l43 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h54023 X0 X1]
    conv => enter [1]; rw [← l38 X0 X1]
  have l44 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l42 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l45 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l44 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← l41 X1 X0]
  have l46 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l45 X2 X0 X1]
    conv => enter [1, 2]; rw [← l41 X0 X1]
  have l47 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54023 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [l46 X2 X0 X1]
  have l48 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l47 X2 X0 X1]
  have l49 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l41 X0 X1]
    conv => enter [1]; rw [← l48 X0 X1 X0]
  have l50 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1]; rw [← l48 X1 X0 X1]
  have l51 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l43 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l52 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l43 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) X2]
  have l53 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l52 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l54 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l51 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l55 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l53 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l56 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l54 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← l48 X1 X0 X1]
  have l57 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l55 X0 X1 X2]
    conv => enter [1, 2]; rw [← h53808 X1 X2]
  have l58 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l56 X2 X0 X1]
  have l59 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1]; rw [l57 X0 X1 X2]
  have l60 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [l59 X0 X1 X2]
  have l61 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l58 X2 X0 X1]
    conv => enter [1, 2]; rw [l60 X0 X1 (X1 ◇ X1)]
  have l62 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l34 X0 X1 X2]
    conv => enter [1]; rw [← l61 X0 X1 X0]
  have l63 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l43 X0 X1]
    conv => enter [1]; rw [l50 X0 X1]
  have l64 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l63 X0 X1]
    conv => enter [1]; rw [← l49 X0 X1]
  have l65 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l63 X0 X1]
    conv => enter [1]; rw [← l62 X0 X1 X2]
  have l66 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l64 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l67 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← l66 X0 X1 X2]
  have l68 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l67 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l69 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [← l68 X0 X1 X2]
  have l70 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l69 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l71 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l65 X0 X1 X2]
    conv => enter [1]; rw [← l70 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l71 x y z]

theorem Equation4512_53808_54023_implies_Equation54024 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54023 : Equation54023 G) : Equation54024 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53808 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53808 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l3 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1]; rw [← l7 sK1 X0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l8 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK0]
    conv => enter [1]; rw [h54023 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 (sK1 ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54023 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation4512_53822_54020_implies_Equation54053 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h54020 : Equation54020 G) : Equation54053 G := by
  have l0 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h53822 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54020 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54020 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 sK0]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [← h54020 sK0 (sK2 ◇ sK0)]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54020 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK2]
  have l8 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l9 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l7 sK0 sK2]
  have l10 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l7 sK0 sK2]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [l7 sK0 sK2]
  have l11 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [l10 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK2]
  have l12 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l9 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l13 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l8 sK1 sK0 sK2]
    conv => enter [1]; rw [← l12 sK1 sK0 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l13 sK1 sK0 sK2]
    conv => enter [1]; rw [← h54020 sK0 (sK1 ◇ sK0)]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l11 sK0 sK2 sK1]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l18 x y z]
  conv => enter [1]; rw [l11 x z y]

theorem Equation4512_53808_54013_implies_Equation54031 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54013 : Equation54013 G) : Equation54031 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h53808 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h54013 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h54013 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53808 X0 X2]
    conv => enter [1]; rw [← l4 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [l6 x z y]

theorem Equation4512_53822_53900_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53900 : Equation53900 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53822 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53822 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [l14 sK0 ((sK1 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 ((sK1 ◇ sK0) ◇ X0) sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 X0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [l20 sK0 sK1 X0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l32 sK1 sK0]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← l30 sK0 sK1]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [← l34 sK0 sK1 X0]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l37 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l36 sK0 sK1 X0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53900 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53900 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 (sK1 ◇ sK0)]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h53900 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1 (sK1 ◇ sK0)]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l38 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK1 (sK1 ◇ sK0)]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [l44 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l45 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l47 sK0 sK1]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) X0]
  have l52 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l51 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l53 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l54 sK0 sK1]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l56 sK1 sK0]
    conv => enter [1]; rw [← l52 sK0 sK1 (sK1 ◇ sK0)]
  have l58 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l57 sK1 sK0]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l58 sK1 sK0]
  have l60 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0 (sK1 ◇ sK0)]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l60 sK1 sK0]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1]
  have l64 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l63 sK0 sK1]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [l66 sK0 sK1]
  have l68 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53900 X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l64 sK0 sK1 X0]
    conv => enter [1]; rw [← l68 X0 sK0 sK1]
  have l70 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l69 sK0 sK1 X0]
  have l71 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [l70 sK0 sK1 X0]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l73 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [← h53900 sK1 (sK1 ◇ sK0)]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l73 sK1 sK0]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [l74 sK0 sK1]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [← h53900 sK1 sK0]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l76 sK0 sK1]
  have l78 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1, 2]; rw [← l77 sK0 sK1]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l78 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0 sK0]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1]; rw [h53900 (sK1 ◇ sK0) sK0]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l82 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l81 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l82 x y]

theorem Equation4512_53822_53900_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53900 : Equation53900 G) : Equation53832 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53900 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_53822_53900_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53900 : Equation53900 G) : Equation53815 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53900 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h53900 X0 X1]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK0]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l5 X0 sK0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l6 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l11 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1, 2, 2]; rw [l9 sK0 X1]
    conv => enter [1]; rw [← l10 X0 X1 (sK0 ◇ sK0)]
  have l12 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l11 X1 X0 sK0]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l12 X1 sK0 X0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [← h53900 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation4512_53822_53900_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53900 : Equation53900 G) : Equation53835 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53900 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h53900 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_53808_54164_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54164 : Equation54164 G) : Equation53812 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← h54164 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0))))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l4 X2 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h54164 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53808 X0 (X1 ◇ (X0 ◇ X2))]
    conv => enter [1, 2]; rw [← l4 X0 X1 X2]
  have l7 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l6 X3 X0 (X1 ◇ (X0 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← l4 X0 X1 X2]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0 X1]
    conv => enter [1]; rw [← h54164 (X0 ◇ X1) X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1 (X0 ◇ X1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l12 X0 X1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation4512_53808_54164_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54164 : Equation54164 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54164 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_53808_54164_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54164 : Equation54164 G) : Equation53815 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54164 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h54164 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← h54164 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1)))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1)))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X1))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ (X1 ◇ X1))]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))))) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ X0)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 (X0 ◇ X0)]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54164 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h53808 X0 X1]
  have l13 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53808 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1, 2]; rw [l8 X1 (X0 ◇ X1) X2]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l16 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X1 ◇ X2)]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l16 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ (X0 ◇ X0))]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1, 2]; rw [h54164 X1 (X0 ◇ X1)]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l21 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ X0)]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 X1]
    conv => enter [1, 2]; rw [l22 X1 X0 (X1 ◇ X1)]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X0)]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l25 X0 X1]
    conv => enter [1, 2, 2]; rw [l22 X1 X0 X0]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l24 X0 X1]
    conv => enter [1]; rw [← l26 X0 X1]
  have l28 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l8 X0 X2 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2, 2]; rw [← h54164 X0 X1]
  have l29 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l8 X1 X0 (X1 ◇ X2)]
    conv => enter [1, 2, 2]; rw [l8 X0 X1 X2]
  have l30 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53808 X0 (X1 ◇ (X0 ◇ X2))]
    conv => enter [1, 2]; rw [← l8 X0 X1 X2]
  have l31 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l30 X1 X0 (X1 ◇ (X0 ◇ X2))]
    conv => enter [1]; rw [← l29 X1 X0 X2]
  have l32 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l31 X0 X2 (X1 ◇ X0)]
    conv => enter [1]; rw [l28 X0 X2 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l32 X0 X1 X0]
    conv => enter [1]; rw [l27 X0 X1]
  intro x y
  conv => enter [1]; rw [l33 x y]
  conv => enter [1]; rw [← l8 x y x]

theorem Equation4512_53808_54164_implies_Equation53816 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54164 : Equation54164 G) : Equation53816 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53808 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53808 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53808 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1]; rw [← l8 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l9 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54164 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation4512_53822_53899_implies_Equation53833 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53899 : Equation53899 G) : Equation53833 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53899 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 X0]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l6 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l11 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l13 X2 X0 X1]
    conv => enter [1]; rw [← l9 X1 X2 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l14 sK0 X0]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53822 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l16 sK0 (X0 ◇ (X0 ◇ X0))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l19 sK0 sK1]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l22 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l15 sK1 sK1 (sK0 ◇ sK1)]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1, 2]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l30 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l31 x y]

theorem Equation4512_53808_54201_implies_Equation53826 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54201 : Equation54201 G) : Equation53826 G := by
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
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l5 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53808 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53808 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))]
    conv => enter [1, 2]; rw [← h53808 (sK0 ◇ sK0) X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 X0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53808 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53808 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l16 sK1 X0]
  have l24 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1, 2]; rw [l5 sK0]
  have l28 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [← l5 sK0]
    conv => enter [1]; rw [l24 sK0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l28 sK0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l7 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l31 sK0 X0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [← l33 sK0 X0]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l34 sK0 sK0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l19 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0]
    conv => enter [1]; rw [← l36 sK0 X0]
  have l38 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h54201 (sK1 ◇ X0) sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l9 sK0 sK1]
  have l40 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
    conv => enter [1]; rw [← h54201 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l41 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l40 sK0 X0]
    conv => enter [1, 2]; rw [← l35 sK0]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)))]
    conv => enter [1]; rw [← l39 sK1 sK0]
  have l43 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l38 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK1 ◇ sK1) ◇ X0)]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l45 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l43 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l23 sK1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l47 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l45 sK1 X0]
    conv => enter [1]; rw [← h54201 X0 (sK1 ◇ sK1)]
  have l48 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l47 sK1 X0]
    conv => enter [1, 2]; rw [← l18 sK1]
  have l49 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l48 sK1 X0]
    conv => enter [1, 2]; rw [l46 sK1 sK0]
  have l50 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 X0]
    conv => enter [1]; rw [← l49 sK1 X0 sK0]
  have l51 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l50 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l51 x y x]

theorem Equation53934_54472_implies_Equation54550 (G : Type*) [Magma G] (h53934 : Equation53934 G) (h54472 : Equation54472 G) : Equation54550 G := by
  have l0 : ∀ sK3 sK1 sK2 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 sK1 sK2 X0
    conv => enter [1, 2]; rw [h54472 sK1 sK2 sK3]
    conv => enter [1]; rw [h53934 sK3 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1, 2, 2]; rw [← h54472 sK1 sK2 sK3]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [h54472 sK1 sK2 sK3]
    conv => enter [1]; rw [l0 sK3 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h54472 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_54022_54337_implies_Equation54340 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54022 : Equation54022 G) (h54337 : Equation54337 G) : Equation54340 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) sK0]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h54022 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [← l1 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l2 X2 X0 X1 X3]
    conv => enter [1]; rw [← h54337 X2 X0 X1]
  have l4 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [h54337 X0 sK2 sK3]
    conv => enter [1, 2]; rw [h4512 sK2 sK3 X0]
  have l5 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h54337 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
  have l6 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ ((sK2 ◇ sK3) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [h54337 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) (X0 ◇ sK1)]
  have l7 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [l6 sK1 sK2 sK3 X0]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l9 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l3 X0 X1 X2 X3]
    conv => enter [1]; rw [← l9 X0 X1 X2 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X3]
  have l13 : ∀ sK1 sK2 sK3 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) ◇ X1) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((X0 ◇ sK1) ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1, 1]; rw [l7 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK3)) (X0 ◇ sK1) X1]
  have l14 : ∀ sK1 sK2 sK3 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) ◇ X1) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l13 sK1 sK2 sK3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l15 : ∀ sK1 sK2 sK3 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) ◇ X1) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l14 sK1 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← l12 (sK1 ◇ (sK2 ◇ sK3)) X0 sK1 X1]
  have l16 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) ◇ X1) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← l15 sK1 sK2 sK3 X0 X1]
  have l17 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l16 sK1 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK3)) X0 X1]
  have l18 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l4 sK1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) sK1]
  have l19 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [l18 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK3)) sK1 X0]
  have l20 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l19 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← l17 sK1 sK2 sK3 sK1 X0]
  have l21 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l18 sK1 sK2 sK3]
    conv => enter [1]; rw [← l20 sK1 sK2 sK3 X0]
  have l22 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l0 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l22 x y z w]

theorem Equation4512_53807_53822_53869_implies_Equation53834 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53807 : Equation53807 G) (h53822 : Equation53822 G) (h53869 : Equation53869 G) : Equation53834 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53869 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53869 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l9 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1 X0]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ X0))) X3]
    conv => enter [1, 1]; rw [← l0 X0 X1 X2]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h53807 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X3]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l15 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X0)) X3]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ X0) X3]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 X3]
  have l19 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l13 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← l13 X0 X1]
  have l21 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
  have l22 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l21 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l23 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l24 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l22 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l25 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1]; rw [← l18 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0)) X0]
  have l26 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l24 X0 X2 X1]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← l25 X0 X1]
  have l28 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l26 X0 X2 X1]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l27 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l29 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l30 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l31 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1 ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l33 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l32 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
  have l34 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l33 X0 X1]
    conv => enter [1, 2]; rw [← l18 X0 X1 X1 (X1 ◇ X0)]
  have l35 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l34 X0 X1]
    conv => enter [1, 2, 2]; rw [← l8 X1 X0 X0]
  have l36 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l35 X0 X1]
    conv => enter [1, 2]; rw [← l8 X1 X0 X0]
  have l37 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l36 X0 X1]
    conv => enter [1]; rw [← l8 X1 X0 X0]
  have l38 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l0 X0 X0 X1]
  have l39 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h53869 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [← l5 X0 (X0 ◇ (X0 ◇ X1)) X1]
  have l40 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l39 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))]
  have l41 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l38 X0 X2 X1]
    conv => enter [1]; rw [← l5 X0 X2 (X0 ◇ X1)]
  have l42 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l40 X0 X1]
    conv => enter [1]; rw [← l5 X0 (X0 ◇ X1) ((X0 ◇ (X0 ◇ X1)) ◇ X1)]
  have l43 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l28 X0 X1 X2]
    conv => enter [1]; rw [← l41 X0 X2 X1]
  have l44 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l42 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ (X0 ◇ X1)) ◇ X1)]
  have l45 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l43 X0 X1 X2]
    conv => enter [1]; rw [← l9 X0 X0 X2 X1]
  have l46 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l44 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X1]
  have l47 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l46 X0 X1]
    conv => enter [1]; rw [← l45 X0 (X0 ◇ ((X0 ◇ X1) ◇ X1)) X1]
  have l48 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l47 X0 X1]
    conv => enter [1]; rw [← l45 X0 ((X0 ◇ X1) ◇ X1) X0]
  have l49 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l45 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← l48 X0 X1]
  have l50 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l49 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) ((X0 ◇ (X0 ◇ X1)) ◇ X0)]
  have l51 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l50 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ (X0 ◇ X1)) ◇ X0)]
  have l52 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← l51 X0 X1]
  have l53 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l52 X0 X1]
    conv => enter [1]; rw [← l37 X1 X0]
  have l54 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X2 X1
    conv => enter [1, 2, 2]; rw [h53869 X0 X1]
    conv => enter [1]; rw [← l9 X0 X2 X0 X1]
  have l55 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l28 X0 X1 X2]
    conv => enter [1]; rw [← l54 X0 X2 X1]
  have l56 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l52 X0 X1]
    conv => enter [1]; rw [l55 X0 X1 X2]
  have l57 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l56 X0 X1 X2]
    conv => enter [1]; rw [← l5 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l53 x y]
  conv => enter [1]; rw [l57 y x z]

theorem Equation4512_53822_53869_implies_Equation53823 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53869 : Equation53869 G) : Equation53823 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53869 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h53869 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53869 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l8 X0 X1 X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h53822 X0 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l11 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X1 X0 X0]
    conv => enter [1, 2]; rw [l9 X0 X1 (X0 ◇ (X1 ◇ X0))]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l12 X0 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h53822 X0 X0]
    conv => enter [1]; rw [l15 X1 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h53822 X0 X1]
    conv => enter [1]; rw [l16 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2]; rw [← h53869 X0 X1]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation4512_53808_54209_implies_Equation53830 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54209 : Equation54209 G) : Equation53830 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54209 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54209 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h54209 X0 X1]
    conv => enter [1]; rw [← h53808 X1 (X1 ◇ (X0 ◇ X1))]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h54209 X0 X1]
    conv => enter [1]; rw [← h53808 X1 (X0 ◇ X1)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l3 X1 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h53808 X1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l9 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1, 2]; rw [← l9 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← l11 X1 X0]
  have l13 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l3 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l14 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [← l13 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l11 X1 X2]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l14 X1 X0 X1 X2]
    conv => enter [1]; rw [← l6 X0 X1 (X2 ◇ X1)]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l16 X0 X1 X2]
    conv => enter [1, 2]; rw [← h54209 X2 X1]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l8 X1 X2]
    conv => enter [1]; rw [l17 X0 X1 X2]
  have l19 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l18 X0 X2 X1]
    conv => enter [1]; rw [← l15 X3 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l19 y x z x]

theorem Equation4512_53808_54209_implies_Equation53823 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54209 : Equation54209 G) : Equation53823 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← h54209 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [h54209 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54209 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X0) X2]
    conv => enter [1, 1]; rw [h54209 X1 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54209 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X0]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X2))]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 X0]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l5 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l9 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l6 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← h53808 X0 (X0 ◇ X0)]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l8 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l10 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l11 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 2, 2]; rw [l4 (X0 ◇ X0) X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h53808 X0 (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [← l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h53808 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h54209 X0 X1]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l15 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l17 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l19 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l16 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l20 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h53808 X1 (X2 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l4 X1 X2 X0]
  have l21 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h4512 X2 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← l4 X0 X1 X2]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3)))) = (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))]
  have l23 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3)))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l22 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l24 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l21 X2 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) X3]
  have l25 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l23 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 (X2 ◇ X3)]
  have l26 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l24 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X2) X3]
  have l27 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l26 X2 X0 X1 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X2 X3]
  have l28 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = (X2 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l27 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l29 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l28 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l30 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l29 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l31 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [h54209 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l13 X0 (X0 ◇ X1) X1]
  have l32 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2)))) = ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l4 X1 X0 (X0 ◇ X2)]
    conv => enter [1, 2, 2]; rw [← l13 X0 X1 X2]
  have l33 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2)))) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l32 X1 X0 X2]
    conv => enter [1]; rw [l30 (X0 ◇ X2) (X0 ◇ X2) X0 (X1 ◇ (X0 ◇ X2))]
  have l34 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 (X0 ◇ X1) X0 X0]
    conv => enter [1]; rw [← l31 X0 X1]
  have l35 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 X0 (X0 ◇ X2) X1]
    conv => enter [1]; rw [← l33 X1 X0 X2]
  have l36 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l34 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l37 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l35 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 (X0 ◇ X2)]
  have l38 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l36 X0 X1]
  have l39 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l38 X0 X1]
  have l40 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l25 X0 X1 X0 X1]
    conv => enter [1]; rw [l39 X0 X1]
  have l41 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l40 X0 X1]
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1, 2]; rw [l40 X0 X1]
  have l42 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l37 X0 X0 X1]
    conv => enter [1]; rw [← l41 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [l42 x y]
  conv => enter [1]; rw [l13 x y y]

theorem Equation4512_53822_53863_implies_Equation53913 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53863 : Equation53863 G) : Equation53913 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h53822 sK1 sK0]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← h53822 (sK2 ◇ sK1) sK1]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53822 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← l2 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l9 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l2 sK1 sK2]
    conv => enter [1]; rw [l8 sK1 sK2]
  have l10 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK1 sK2]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53863 sK1 sK1]
    conv => enter [1]; rw [← l10 sK1 sK2]
  have l12 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l11 sK1 sK2]
    conv => enter [1]; rw [← l0 sK2 sK1 (sK1 ◇ sK1)]
  have l13 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l12 sK2 sK1]
    conv => enter [1]; rw [← h53863 (sK2 ◇ sK1) sK1]
  have l14 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l13 sK2 sK1]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [l14 sK2 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53863 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h53863 X0 X1]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l22 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l24 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l23 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l25 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l20 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK2 ◇ sK1) X0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l27 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [← l25 sK1 sK2 (sK2 ◇ sK1)]
  have l28 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 sK2]
    conv => enter [1]; rw [← l27 sK2 sK1]
  have l29 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [h53822 (sK2 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l28 sK1 sK2]
  have l30 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l29 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l31 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l30 sK1 sK2]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l29 sK1 sK2 sK1]
    conv => enter [1]; rw [← l31 sK1 sK2]
  have l33 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [← h53863 X0 (sK1 ◇ (sK2 ◇ sK1))]
  have l34 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l29 sK1 sK2 X0]
    conv => enter [1]; rw [l33 X0 sK1 sK2]
  have l35 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l29 sK1 sK2 X0]
    conv => enter [1]; rw [l34 X0 sK1 sK2]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l35 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l37 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l36 sK1 sK2]
    conv => enter [1]; rw [← h53863 sK2 (sK2 ◇ sK1)]
  have l38 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l37 sK2 sK1]
  have l39 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l30 sK1 sK2]
    conv => enter [1]; rw [l38 sK2 sK1]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← l26 sK0 sK1 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0]
  have l42 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l41 sK0 sK1]
  have l43 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [h53822 sK1 X0]
    conv => enter [1, 2]; rw [← l41 sK0 sK1]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
    conv => enter [1]; rw [← l42 sK2 sK1 sK0]
  have l45 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h53863 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l44 sK0 sK1 sK2]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l45 sK2 sK1 sK0]
  have l47 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [← l24 X0 (sK2 ◇ sK1) sK1]
  have l48 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l46 sK0 sK1 sK2]
    conv => enter [1]; rw [← l24 X0 (sK2 ◇ sK1) sK1]
  have l49 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l43 sK0 sK1 X0]
    conv => enter [1]; rw [l48 X0 sK0 sK1 sK2]
  have l50 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l24 X0 sK1 sK1]
    conv => enter [1]; rw [l47 X0 sK1 sK2]
  have l51 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l43 sK0 sK1 X0]
    conv => enter [1]; rw [l49 X0 sK0 sK1 sK2]
  have l52 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← l50 X0 sK1 sK2]
    conv => enter [1]; rw [← h53863 X0 sK1]
  have l53 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l51 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l52 X0 sK0 sK1]
  have l54 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l39 sK1 sK2]
    conv => enter [1, 2]; rw [l53 sK2 sK1 sK0]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
    conv => enter [1]; rw [← l54 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l55 x y z]

theorem Equation4512_53808_54165_implies_Equation54181 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54165 : Equation54165 G) : Equation54181 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK2 ◇ sK2)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h53808 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53808 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h54165 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h53808 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h54165 X0 X1]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h54165 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (X0 ◇ X0))]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X0)]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53808 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h54165 X0 sK0]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l15 X0 sK0]
    conv => enter [1]; rw [← h54165 X0 sK0]
  have l17 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h54165 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l18 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h54165 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK2 ◇ sK2)]
  have l19 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [h53808 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h54165 X0 sK2]
  have l20 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l19 X0 sK2]
    conv => enter [1]; rw [← h54165 X0 sK2]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l18 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK2 ◇ sK2))]
  have l22 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l16 X0 sK0]
    conv => enter [1]; rw [l20 X0 sK2]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l21 sK0 sK2]
  have l24 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54165 sK0 sK2]
    conv => enter [1]; rw [← l23 sK0 sK2]
  have l25 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l2 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← h54165 sK0 sK2]
  have l26 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l22 (sK1 ◇ (sK0 ◇ sK0)) sK0 sK2]
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
  have l27 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [l26 sK1 sK0 sK2]
  have l28 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l24 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l29 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK2 X0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l30 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l24 sK0 sK2]
    conv => enter [1]; rw [← l29 sK0 sK2 X0]
  have l31 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X0) X1]
  have l32 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l31 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l33 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l32 sK0 X1 X0]
  have l34 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l6 sK0 X1]
    conv => enter [1]; rw [l33 sK0 X1 X0]
  have l35 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l24 sK0 sK2]
    conv => enter [1]; rw [l34 sK0 X0 X1]
  have l36 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l35 sK0 sK2 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h54165 sK1 sK0]
  have l37 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l36 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← h54165 sK1 sK0]
  have l38 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l37 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l37 sK0 sK2 sK1]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0 sK1]
    conv => enter [1]; rw [← l39 sK1 sK0 sK1]
  have l41 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l38 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
  have l42 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK2 X0]
    conv => enter [1]; rw [l41 sK0 sK2 X0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l45 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l42 sK0 sK2 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l46 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l45 sK0 sK2 sK1]
    conv => enter [1]; rw [← l44 sK0 sK1]
  have l47 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 sK0 (sK0 ◇ sK0)]
  have l49 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l48 sK1 sK0]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l16 sK1 sK0]
    conv => enter [1]; rw [← l49 sK1 sK0]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l46 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l52 x z y]

theorem Equation4512_53822_53862_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53862 : Equation53862 G) : Equation4277 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53862 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK1]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53862 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l2 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) sK1]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) sK1 X0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53822 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 (X0 ◇ (X0 ◇ X0))]
  have l11 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK2 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [← l9 sK1 sK2 sK1]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← l12 sK1 sK2 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l13 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

end Semigroup5
