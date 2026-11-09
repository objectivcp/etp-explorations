import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54234_implies_Equation54291 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54234 : Equation54234 G) : Equation54291 G := by
  have l0 : ∀ X0 sK2 sK1 X1 X2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 sK2 sK1 X1 X2
    conv => enter [1]; rw [h54234 X0 sK2 sK1 X1 X2]
    conv => enter [1]; rw [h4512 sK2 sK1 (X1 ◇ X2)]
  have l1 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l0 X0 sK2 X0 X0 X0]
    conv => enter [1]; rw [← l0 X1 sK2 X0 X0 X0]
  have l2 : ∀ sK2 sK1 X1 X2 sK0 : G, ((sK2 ◇ sK1) ◇ (X1 ◇ X2)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X1 X2 sK0
    conv => enter [1]; rw [← l0 sK2 sK2 sK1 X1 X2]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 sK0 (sK2 ◇ sK1)]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK0 (sK2 ◇ sK1)]
  have l4 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l5 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l2 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1)) X0 sK0]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← l5 sK1 sK2 X0 sK1]
  have l7 : ∀ sK1 sK2 X0 X1 X2 X3 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 X0 X1 X2 X3
    conv => enter [1]; rw [l6 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1]; rw [h54234 (sK1 ◇ (sK2 ◇ sK2)) X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w y x]

theorem Equation4512_54291_implies_Equation54242 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54242 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l0 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l1 sK2 X0]
    conv => enter [1]; rw [← h54291 X0 sK2 sK2 (sK2 ◇ sK2)]
  have l3 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [← l2 sK2 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l4 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l3 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l5 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1, 2]; rw [l4 sK2]
    conv => enter [1]; rw [l0 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l5 sK2]
    conv => enter [1]; rw [← h54291 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2 (sK2 ◇ sK2)]
  have l7 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [← l2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l6 sK2]
  have l8 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l7 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l9 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l4 sK2]
    conv => enter [1]; rw [← l8 sK2]
  have l10 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l9 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l11 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l10 sK2 X0]
    conv => enter [1]; rw [l2 sK2 X0]
  have l12 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l11 sK2 X0]
  have l13 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l12 sK2 X0]
  have l14 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [← l2 sK2 X0]
    conv => enter [1]; rw [l13 sK2 X0]
  have l15 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l16 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [l16 sK2 sK1]
  have l18 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l12 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l15 sK2 sK1]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [← l18 sK1 sK2]
  have l20 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h54291 X0 sK2 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l21 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h54291 X0 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 X0]
  have l22 : ∀ X0 X1 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK3 (sK1 ◇ (sK2 ◇ sK0)) (X1 ◇ X0)]
  have l23 : ∀ X0 sK2 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [h54291 X0 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1]; rw [← l21 X0 sK2 X0]
  have l24 : ∀ X0 X1 sK2 sK0 sK3 sK1 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro X0 X1 sK2 sK0 sK3 sK1
    conv => enter [1]; rw [← h54291 sK0 sK2 X0 X1]
    conv => enter [1]; rw [l22 sK0 sK2 sK3 sK1 sK2 sK0]
  have l25 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54291 sK2 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l23 X0 sK2]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l19 sK1 sK2]
    conv => enter [1]; rw [← l25 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l27 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [l25 sK2 X0]
  have l28 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l29 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l28 sK1 sK2 X0]
    conv => enter [1]; rw [← l20 X0 sK2 sK2]
  have l30 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l27 sK1 sK2 X0]
    conv => enter [1]; rw [← l29 sK1 sK2 X0]
  have l31 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ sK2) X1]
    conv => enter [1, 1]; rw [l27 X0 sK2 sK1]
  have l32 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l30 sK1 sK2 X1]
    conv => enter [1]; rw [← l31 X0 sK2 X1 sK1]
  have l33 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l32 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK0]
  have l34 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [l24 sK1 sK2 sK2 sK0 sK3 sK1]
  have l35 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l34 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l24 X0 sK1 sK2 sK0 sK1 sK1]
  intro x y z w
  conv => enter [1]; rw [l35 x y z w]

theorem Equation4512_54242_implies_Equation54291 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54242 : Equation54242 G) : Equation54291 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK1]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 sK1]
  have l4 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) X0]
  have l5 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) X0]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l1 sK1 sK2]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) sK2 X0]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) = (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l7 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2 X0]
    conv => enter [1]; rw [← h54242 sK2 (sK2 ◇ sK2) sK1 X0]
  have l10 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l0 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l11 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54242 (sK2 ◇ sK2) sK2 sK2 X0]
    conv => enter [1]; rw [l10 sK2 X0]
  have l12 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l0 sK2 sK2]
    conv => enter [1]; rw [l11 sK2 X0]
  have l13 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l12 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l14 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l13 sK2 X0]
  have l15 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l14 sK2 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l16 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [← l14 sK2 X0]
  have l17 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l18 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l15 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l19 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l17 sK1 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK2 X0]
  have l20 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l9 sK1 sK2 ((sK2 ◇ sK2) ◇ sK2)]
    conv => enter [1]; rw [← l19 sK1 sK2 sK2]
  have l21 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l18 sK2]
    conv => enter [1]; rw [l20 sK2 sK1]
  have l22 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l4 sK2 sK1 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) X0]
  have l23 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l4 sK2 sK1 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l1 sK1 sK2]
  have l24 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l4 sK2 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l2 sK1 sK2]
  have l25 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l24 sK2 sK1]
    conv => enter [1]; rw [← h54242 (sK2 ◇ sK1) sK2 sK2 (sK2 ◇ sK1)]
  have l26 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l23 sK2 sK1]
    conv => enter [1]; rw [← h54242 (sK2 ◇ sK1) sK2 sK2 (sK2 ◇ sK2)]
  have l27 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54242 (sK2 ◇ sK1) (sK2 ◇ sK2) sK2 X0]
    conv => enter [1]; rw [l22 sK2 sK1 X0]
  have l28 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l5 sK2 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l27 sK2 sK1 X0]
  have l29 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l25 sK2 sK1]
  have l30 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l26 sK2 sK1]
  have l31 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [l21 sK2 sK1]
    conv => enter [1]; rw [l28 sK2 sK1 X0]
  have l32 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l18 sK2]
    conv => enter [1]; rw [l31 sK2 sK1 X0]
  have l33 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l30 sK2 sK1]
    conv => enter [1]; rw [← l32 sK2 sK1 sK2]
  have l34 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54242 sK1 sK2 X0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK1 sK2]
  have l35 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l32 sK2 sK2 (X0 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54242 X0 X1 (sK2 ◇ (sK2 ◇ sK2)) sK2]
  have l36 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l35 sK2 X0 X1]
    conv => enter [1]; rw [← h54242 X0 X1 (sK2 ◇ sK2) X1]
  have l37 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l33 sK2 sK1]
    conv => enter [1]; rw [l36 sK2 X0 X1]
  have l38 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h54242 X0 X1 X2 ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l34 sK1 sK2 X1]
  have l39 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l34 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l29 sK2 sK1]
  have l40 : ∀ sK2 sK1 X2 X0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X2 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1 X2 X0
    conv => enter [1]; rw [l37 sK2 sK1 X0 sK2]
    conv => enter [1]; rw [l38 X0 sK2 X2 sK1 sK2]
  have l41 : ∀ sK1 sK2 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X2 X0
    conv => enter [1]; rw [l39 sK1 sK2]
    conv => enter [1]; rw [l40 sK2 sK1 X2 X0]
  have l42 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l41 sK1 sK2 sK1 X0]
    conv => enter [1]; rw [← l38 X0 X1 sK1 sK1 sK2]
  have l43 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l42 sK1 sK2 sK0 sK2]
    conv => enter [1]; rw [h54242 sK0 sK2 X0 sK1]
  intro x y z w
  conv => enter [1]; rw [l43 x y z w]

theorem Equation4512_54291_implies_Equation54251 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54251 G := by
  have l0 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ X0)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l1 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK3) sK3]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK3]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0)) = (((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK3 ◇ sK3)) X0]
    conv => enter [1, 1]; rw [← l1 sK2 sK3]
  have l3 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l2 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK3)) sK3 X0]
  have l4 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ X0)) = (sK2 ◇ (sK3 ◇ ((sK3 ◇ sK3) ◇ X0))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← l3 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← h4512 sK3 (sK3 ◇ sK3) X0]
  have l5 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ X0)) = (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0]
    conv => enter [1]; rw [← h54291 X0 (sK3 ◇ sK3) sK2 sK3]
  have l6 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ X0))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← l0 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l7 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [← l6 sK3 X0]
    conv => enter [1]; rw [← h54291 X0 sK3 sK3 (sK3 ◇ sK3)]
  have l8 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [← l7 sK3 sK3]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK3]
  have l9 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l8 sK3]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK3)]
  have l10 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)))) := by
    intro sK3
    conv => enter [1, 2]; rw [l9 sK3]
    conv => enter [1]; rw [l0 sK3 ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))]
  have l11 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l10 sK3]
    conv => enter [1]; rw [← h54291 (sK3 ◇ sK3) (sK3 ◇ sK3) sK3 (sK3 ◇ sK3)]
  have l12 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [← l7 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l11 sK3]
  have l13 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l12 sK3]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK3)]
  have l14 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3
    conv => enter [1]; rw [l9 sK3]
    conv => enter [1]; rw [← l13 sK3]
  have l15 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1, 2]; rw [l14 sK3]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK3) (sK3 ◇ sK3)]
  have l16 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1, 1]; rw [l14 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK3 ◇ sK3) X0]
  have l17 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [l16 sK3 X0]
    conv => enter [1]; rw [l7 sK3 X0]
  have l18 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l1 sK2 sK3]
    conv => enter [1]; rw [l15 sK2 sK3]
  have l19 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ sK3) X0]
    conv => enter [1]; rw [l17 sK3 X0]
  have l20 : ∀ sK3 X0 : G, (((sK3 ◇ sK3) ◇ X0) ◇ (sK3 ◇ sK3)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0
    conv => enter [1]; rw [← l19 sK3 ((sK3 ◇ sK3) ◇ X0)]
    conv => enter [1, 2]; rw [l7 sK3 X0]
  have l21 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 ((sK3 ◇ sK3) ◇ X0)]
    conv => enter [1, 2]; rw [l19 sK3 X0]
  have l22 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [← l7 sK3 X0]
    conv => enter [1]; rw [l21 sK3 X0]
  have l23 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0
    conv => enter [1]; rw [h4512 (sK3 ◇ sK3) X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l20 sK3 X0]
  have l24 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [l22 X0 sK3]
    conv => enter [1]; rw [← l23 sK3 X0]
  have l25 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = (sK3 ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l18 sK2 sK3]
    conv => enter [1]; rw [l22 (sK2 ◇ (sK3 ◇ sK3)) sK3]
    conv => enter [1, 2]; rw [← l18 sK2 sK3]
  have l26 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 X0
    conv => enter [1, 2]; rw [l22 X0 sK3]
    conv => enter [1]; rw [l0 sK3 (X0 ◇ (sK3 ◇ sK3))]
  have l27 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) = ((X0 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [l26 sK3 X0]
    conv => enter [1]; rw [l19 sK3 (X0 ◇ (sK3 ◇ sK3))]
  have l28 : ∀ X0 sK3 : G, (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [h4512 X0 (sK3 ◇ sK3) (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l27 sK3 X0]
  have l29 : ∀ X0 sK3 : G, (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3
    conv => enter [1]; rw [l28 X0 sK3]
    conv => enter [1]; rw [← l24 X0 sK3]
  have l30 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [← l29 X0 sK3]
    conv => enter [1, 2]; rw [← l14 sK3]
  have l31 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l22 sK2 sK3]
    conv => enter [1]; rw [l0 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l32 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l22 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l33 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l22 sK2 sK3]
    conv => enter [1]; rw [l32 sK3 sK2]
  have l34 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← l19 sK3 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [← l31 sK3 sK2]
  have l35 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l33 sK2 sK3]
    conv => enter [1]; rw [← l34 sK2 sK3]
  have l36 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1, 1]; rw [l33 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK2 ◇ (sK3 ◇ sK3)) X0]
  have l37 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) := by
    intro sK2 sK3
    conv => enter [1]; rw [l35 sK2 sK3]
    conv => enter [1]; rw [← l18 sK2 sK3]
  have l38 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l25 sK2 sK3]
    conv => enter [1]; rw [l0 sK3 ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)]
  have l39 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) = (((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [l38 sK3 sK2]
    conv => enter [1]; rw [l19 sK3 ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)]
  have l40 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l39 sK3 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK3)) sK3 (sK3 ◇ sK3)]
  have l41 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [← l5 sK2 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l40 sK3 sK2]
  have l42 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l36 sK2 sK3 sK3]
    conv => enter [1]; rw [← l41 sK3 sK2]
  have l43 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l42 sK2 sK3]
    conv => enter [1]; rw [l7 sK3 (sK3 ◇ sK3)]
  have l44 : ∀ sK3 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) := by
    intro sK3 sK2
    conv => enter [1]; rw [l14 sK3]
    conv => enter [1]; rw [← l43 sK2 sK3]
  have l45 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l37 sK2 sK3]
    conv => enter [1]; rw [← l44 sK3 sK2]
  have l46 : ∀ X0 sK3 sK2 : G, (X0 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3 sK2
    conv => enter [1]; rw [l30 X0 sK3]
    conv => enter [1, 2]; rw [← l45 sK2 sK3]
  have l47 : ∀ X0 X1 sK3 : G, ((X0 ◇ X1) ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ sK3)))) := by
    intro X0 X1 sK3
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l30 X1 sK3]
  have l48 : ∀ sK3 X0 X1 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((X0 ◇ X1) ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [h54291 (sK3 ◇ sK3) sK3 X0 X1]
    conv => enter [1]; rw [← l47 X0 X1 sK3]
  have l49 : ∀ sK3 X0 X1 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [l48 sK3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ sK3)]
  have l50 : ∀ sK3 X0 X1 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [← l0 sK3 sK3]
    conv => enter [1]; rw [l49 sK3 X0 X1]
  have l51 : ∀ sK3 X0 X1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [← l19 sK3 sK3]
    conv => enter [1]; rw [l50 sK3 X0 X1]
  have l52 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l45 sK2 sK3]
    conv => enter [1]; rw [l51 sK3 X0 X1]
  have l53 : ∀ X0 X1 sK3 X2 sK2 : G, (X0 ◇ ((X1 ◇ (sK3 ◇ sK3)) ◇ X2)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) := by
    intro X0 X1 sK3 X2 sK2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (sK3 ◇ sK3)) X2]
    conv => enter [1, 1]; rw [← l52 sK2 sK3 X0 X1]
  have l54 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l52 sK2 sK3 (sK3 ◇ sK3) X0]
    conv => enter [1]; rw [← l24 X0 sK3]
  have l55 : ∀ sK2 sK3 X2 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK3 ◇ sK3) ◇ X2))) := by
    intro sK2 sK3 X2 X0 X1
    conv => enter [1]; rw [← l53 X0 X1 sK3 X2 sK2]
    conv => enter [1, 2]; rw [← h4512 X1 (sK3 ◇ sK3) X2]
  have l56 : ∀ sK2 sK3 X2 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) = (X2 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X2
    conv => enter [1]; rw [l55 sK2 sK3 X2 sK2 sK2]
    conv => enter [1]; rw [← h54291 X2 (sK3 ◇ sK3) sK2 sK2]
  have l57 : ∀ sK2 sK3 X2 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) := by
    intro sK2 sK3 X2
    conv => enter [1]; rw [l52 sK2 sK3 X2 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l56 sK2 sK3 X2]
  have l58 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [h54291 X0 X1 sK2 (sK3 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK3) (X1 ◇ X0)]
  have l59 : ∀ X0 X1 sK3 : G, (X0 ◇ (X1 ◇ X1)) = ((sK3 ◇ sK3) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK3
    conv => enter [1]; rw [h54291 X0 X1 sK3 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (X1 ◇ X0)]
  have l60 : ∀ X0 X1 sK4 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK4 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK4 sK2 sK1 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK4 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK4 (sK2 ◇ (sK1 ◇ sK0)) (X1 ◇ X0)]
  have l61 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l57 sK2 sK3 (X1 ◇ X0)]
    conv => enter [1]; rw [← l58 X0 X1 sK2 sK3]
  have l62 : ∀ X0 X1 sK1 sK0 sK4 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) = ((sK4 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK1 sK0 sK4 sK2
    conv => enter [1]; rw [← h54291 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l60 sK0 sK1 sK4 sK2 sK1 sK0]
  have l63 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l61 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ X0)]
  have l64 : ∀ sK1 sK2 sK3 X0 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [l63 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l59 (sK1 ◇ sK0) X0 sK3]
  have l65 : ∀ sK1 sK2 sK3 sK4 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK4 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK4 sK0
    conv => enter [1]; rw [l64 sK1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l62 (sK3 ◇ sK3) sK1 sK1 sK0 sK4 sK2]
  have l66 : ∀ sK1 sK3 sK4 sK2 sK0 : G, (sK1 ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK3 sK4 sK2 sK0
    conv => enter [1]; rw [l46 sK1 sK3 sK2]
    conv => enter [1]; rw [l65 sK1 sK2 sK3 sK4 sK0]
  have l67 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l54 sK2 sK3 sK1]
    conv => enter [1]; rw [l66 sK1 sK3 sK4 sK2 sK0]
  have l68 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l67 sK2 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [← l62 X0 sK2 sK1 sK0 sK2 sK2]
  intro x y z w u
  conv => enter [1]; rw [l68 x y z w u]

theorem Equation4512_54251_implies_Equation54291 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54251 : Equation54251 G) : Equation54291 G := by
  have l0 : ∀ X2 X0 X1 X3 sK0 sK2 sK1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X3 ◇ (X2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X2 X0 X1 X3 sK0 sK2 sK1
    conv => enter [1, 2]; rw [h54251 X0 X1 (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h54251 X2 (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) X3 sK0 (sK2 ◇ sK1)]
  have l1 : ∀ X2 X0 X1 sK2 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X2 X0 X1 sK2
    conv => enter [1]; rw [l0 X2 X0 X1 X2 X2 sK2 X2]
    conv => enter [1]; rw [← h54251 X2 sK2 X2 X2 (sK2 ◇ X2)]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h54251 X0 X1 X0 X0 (sK2 ◇ X0)]
    conv => enter [1]; rw [← h54251 X0 sK2 X0 X0 (sK2 ◇ X0)]
  have l3 : ∀ X0 sK2 X1 X2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK2 X1 X2 sK0 sK1
    conv => enter [1]; rw [h54251 X0 sK2 (X1 ◇ X2) sK0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l4 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h54251 X0 sK2 (sK2 ◇ sK1) sK0 (sK2 ◇ sK1)]
  have l5 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h54251 X0 sK2 (sK0 ◇ (sK2 ◇ X0)) sK0 (sK2 ◇ X0)]
    conv => enter [1]; rw [l4 sK0 sK2 X0 X0]
  have l6 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l3 X0 sK2 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h54251 X0 sK2 X0 X0 (sK2 ◇ X0)]
  have l7 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [h54251 (sK0 ◇ (sK2 ◇ sK1)) sK2 X1 sK0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h54251 X1 (sK0 ◇ (sK2 ◇ sK1)) X0 sK1 (sK2 ◇ sK2)]
  have l8 : ∀ X0 X1 X2 X3 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 X1 X2 X3 sK1 sK2
    conv => enter [1]; rw [h54251 X0 X1 (X2 ◇ X3) sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l9 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1, 2]; rw [h54251 X0 X1 (sK2 ◇ sK2) sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l1 sK1 X0 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 X0 sK1 sK2]
  have l11 : ∀ X0 sK2 X2 X3 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X3 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK2 X2 X3 sK1
    conv => enter [1]; rw [l2 X0 sK2 X0]
    conv => enter [1]; rw [l8 X0 X0 X2 X3 sK1 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK1]
    conv => enter [1]; rw [← l7 sK0 sK2 sK1 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l13 : ∀ X0 sK2 X2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X2 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X2 sK0 sK1
    conv => enter [1]; rw [l11 X0 sK2 X2 X0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK2 sK1 X0 X0]
  have l14 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l6 (sK0 ◇ (sK2 ◇ sK1)) sK2 sK0]
    conv => enter [1]; rw [← l13 X0 sK2 sK0 sK0 sK1]
  have l15 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2 sK1]
    conv => enter [1]; rw [l14 sK1 sK2 sK1 X0]
  have l16 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l5 (sK2 ◇ sK2) sK2 sK0]
    conv => enter [1]; rw [h54251 sK0 (sK2 ◇ sK2) X0 sK2 sK1]
  have l17 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l15 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l16 sK2 X0 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l17 x y z w]

theorem Equation4512_54291_implies_Equation54255 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54255 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l0 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l1 sK2 X0]
    conv => enter [1]; rw [← h54291 X0 sK2 sK2 (sK2 ◇ sK2)]
  have l3 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [← l2 sK2 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l4 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l2 sK2 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 (sK1 ◇ sK0)]
  have l5 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [l2 sK2 X0]
  have l6 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l5 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l7 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l3 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l9 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l6 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) X0 X1]
  have l10 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l9 X0 sK2 X1]
    conv => enter [1]; rw [l2 sK2 (X0 ◇ X1)]
  have l11 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l10 X0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l12 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l7 sK1 sK0 sK2]
  have l13 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l11 sK2 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK2 sK1 sK0]
  have l14 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l13 sK2 sK1 sK0]
    conv => enter [1]; rw [l2 sK2 (sK2 ◇ (sK1 ◇ sK0))]
  have l15 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l14 sK2 sK1 sK0]
  have l16 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l15 sK2 sK1 sK0]
  have l17 : ∀ sK3 sK2 sK1 sK0 : G, ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) = (sK3 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK2 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l16 sK2 sK1 sK0]
  have l18 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1, 2]; rw [l8 sK2]
    conv => enter [1]; rw [l0 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l19 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l18 sK2]
    conv => enter [1]; rw [← h54291 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2 (sK2 ◇ sK2)]
  have l20 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [← l2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l19 sK2]
  have l21 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l20 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l22 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l8 sK2]
    conv => enter [1]; rw [← l21 sK2]
  have l23 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l22 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l24 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l23 sK2 X0]
    conv => enter [1]; rw [l2 sK2 X0]
  have l25 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l24 sK2 X0]
  have l26 : ∀ sK2 X0 : G, (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l25 sK2 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l2 sK2 X0]
  have l27 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l25 sK2 X0]
  have l28 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [← l2 sK2 X0]
    conv => enter [1]; rw [l27 sK2 X0]
  have l29 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l26 sK2 X0]
  have l30 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [l28 X0 sK2]
    conv => enter [1]; rw [← l29 sK2 X0]
  have l31 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l32 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l33 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [l32 sK2 sK1]
  have l34 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l25 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l31 sK2 sK1]
  have l35 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l33 sK1 sK2]
    conv => enter [1]; rw [← l34 sK1 sK2]
  have l36 : ∀ sK2 sK1 sK0 sK3 X0 X1 : G, (((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [h54291 ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0))) sK3 X0 X1]
    conv => enter [1, 2, 2]; rw [← l17 sK3 sK2 sK1 sK0]
  have l37 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h54291 X0 sK2 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l38 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h54291 X0 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 X0]
  have l39 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro X1 X0 sK2
    conv => enter [1, 2]; rw [l30 X0 sK2]
    conv => enter [1]; rw [← h54291 (sK2 ◇ sK2) X0 X1 (sK2 ◇ sK2)]
  have l40 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h54291 X0 X1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ X0)]
  have l41 : ∀ X0 X1 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK2 sK1 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) (X1 ◇ X0)]
  have l42 : ∀ sK2 X2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (X2 ◇ (X1 ◇ X0))) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (X2 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54291 X0 X1 sK2 X2]
  have l43 : ∀ X0 X1 sK3 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK3 sK2 sK1 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK3 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK3 (sK2 ◇ (sK1 ◇ sK0)) (X1 ◇ X0)]
  have l44 : ∀ X0 sK2 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [h54291 X0 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1]; rw [← l38 X0 sK2 X0]
  have l45 : ∀ sK2 sK1 sK0 sK3 : G, (((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ sK3)) = ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK1 sK0 sK3
    conv => enter [1]; rw [l36 sK2 sK1 sK0 sK3 sK2 sK2]
    conv => enter [1]; rw [← h54291 (sK2 ◇ sK2) (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2 sK2]
  have l46 : ∀ X0 X1 sK3 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK3 sK2 sK1 sK0
    conv => enter [1]; rw [← h54291 (sK2 ◇ (sK1 ◇ sK0)) sK3 X0 X1]
    conv => enter [1]; rw [l41 (sK2 ◇ (sK1 ◇ sK0)) sK3 sK2 sK1 sK0]
  have l47 : ∀ X0 X1 sK1 sK0 sK3 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h54291 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l43 sK0 sK1 sK3 sK2 sK1 sK0]
  have l48 : ∀ sK2 sK1 sK0 sK3 : G, (((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ sK3)) = ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0 sK3
    conv => enter [1]; rw [l45 sK2 sK1 sK0 sK3]
    conv => enter [1]; rw [l40 (sK2 ◇ sK2) (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2]
  have l49 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54291 sK2 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l44 X0 sK2]
  have l50 : ∀ sK3 sK2 sK1 sK0 : G, ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) = (((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [l30 (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2]
    conv => enter [1]; rw [← l48 sK2 sK1 sK0 sK3]
  have l51 : ∀ sK3 sK2 sK1 sK0 : G, ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [l50 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ (sK1 ◇ sK0)) (sK3 ◇ sK3)]
  have l52 : ∀ sK3 sK2 sK1 sK0 : G, ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [l51 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [l42 sK2 (sK2 ◇ (sK1 ◇ sK0)) sK3 sK3]
  have l53 : ∀ sK3 sK2 sK1 sK0 : G, ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [l52 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [← h54291 sK3 sK3 sK2 sK3]
  have l54 : ∀ sK3 sK2 sK1 sK0 : G, ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [l53 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [l43 sK3 sK3 sK3 sK2 sK1 sK0]
  have l55 : ∀ sK3 sK2 sK1 sK0 : G, ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [l54 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [l43 (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK3 sK3 sK2 sK1 sK0]
  have l56 : ∀ sK3 sK2 sK1 sK0 : G, ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [l55 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [l46 (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK3 sK3 sK2 sK1 sK0]
  have l57 : ∀ sK2 sK1 sK0 sK3 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0 sK3
    conv => enter [1]; rw [l49 sK2 (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l56 sK3 sK2 sK1 sK0]
  have l58 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l35 sK1 sK2]
    conv => enter [1]; rw [← l49 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l59 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l58 sK1 sK2]
    conv => enter [1]; rw [l49 sK2 X0]
  have l60 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l58 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l61 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l60 sK1 sK2 X0]
    conv => enter [1]; rw [← l37 X0 sK2 sK2]
  have l62 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l59 sK1 sK2 X0]
    conv => enter [1]; rw [← l61 sK1 sK2 X0]
  have l63 : ∀ sK3 sK2 sK1 sK0 : G, ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK3 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK2 ◇ (sK1 ◇ sK0)) (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l57 sK2 sK1 sK0 sK3]
  have l64 : ∀ sK2 sK3 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← l39 sK3 sK2 sK2]
    conv => enter [1]; rw [← l63 sK3 sK2 sK1 sK0]
  have l65 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← l0 sK2 sK2]
    conv => enter [1]; rw [l64 sK2 sK3 sK1 sK0]
  have l66 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← l25 sK2 sK2]
    conv => enter [1]; rw [l65 sK2 sK3 sK1 sK0]
  have l67 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l58 sK1 sK2]
    conv => enter [1]; rw [l66 sK2 sK3 sK1 sK0]
  have l68 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1, 1]; rw [l67 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l69 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l62 sK1 sK2 X0]
    conv => enter [1]; rw [l68 sK1 sK2 X0 sK3 sK0]
  have l70 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l69 sK1 sK2 sK3 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l47 (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1 sK0 sK3 sK2]
  have l71 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l70 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l47 X0 sK2 sK1 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l71 x y z w]

theorem Equation4512_54255_implies_Equation54291 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54255 : Equation54255 G) : Equation54291 G := by
  have l0 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ X0) X1]
  have l1 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l2 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l1 sK2 X0 X1]
    conv => enter [1]; rw [← h54255 X0 sK2 sK2 X1]
  have l3 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l2 sK2 X0 X1]
  have l4 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 sK1]
  have l5 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) X0]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l3 sK2 sK1 X0]
    conv => enter [1]; rw [l5 sK2 sK1 X0]
  have l7 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 X0]
  have l8 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l7 sK2 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ sK1) sK2]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l8 sK2 sK1]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l11 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l11 sK1 sK2 X0]
    conv => enter [1]; rw [l3 sK2 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l13 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l12 sK1 sK2 X0]
    conv => enter [1]; rw [← l12 sK1 sK2 X1]
  have l14 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l3 sK2 (sK2 ◇ sK2) (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK2 X0 sK2]
  have l15 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l15 sK2 sK1]
  have l17 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [← l3 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l14 sK2 X0]
  have l18 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [← l17 X0 sK2]
  have l19 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l18 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l13 sK1 sK2 (sK2 ◇ sK2) X0]
  have l20 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l19 sK1 sK2 (X1 ◇ (X0 ◇ sK1))]
    conv => enter [1]; rw [← h54255 X0 X1 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l21 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l20 sK1 sK2 sK2 X0]
    conv => enter [1]; rw [h54255 sK2 X0 X1 sK1]
  intro x y z w
  conv => enter [1]; rw [l21 x y z w]

theorem Equation4512_54291_implies_Equation54264 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54264 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l0 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l1 sK2 X0]
    conv => enter [1]; rw [← h54291 X0 sK2 sK2 (sK2 ◇ sK2)]
  have l3 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [← l2 sK2 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l4 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l3 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l5 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1, 2]; rw [l4 sK2]
    conv => enter [1]; rw [l0 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l5 sK2]
    conv => enter [1]; rw [← h54291 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2 (sK2 ◇ sK2)]
  have l7 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [← l2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l6 sK2]
  have l8 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l7 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l9 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l4 sK2]
    conv => enter [1]; rw [← l8 sK2]
  have l10 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l9 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l11 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l10 sK2 X0]
    conv => enter [1]; rw [l2 sK2 X0]
  have l12 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l11 sK2 X0]
  have l13 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l12 sK2 X0]
  have l14 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [← l2 sK2 X0]
    conv => enter [1]; rw [l13 sK2 X0]
  have l15 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l16 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [l16 sK2 sK1]
  have l18 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l12 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l15 sK2 sK1]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [← l18 sK1 sK2]
  have l20 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h54291 X0 sK2 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l21 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h54291 X0 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 X0]
  have l22 : ∀ X0 sK2 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [h54291 X0 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1]; rw [← l21 X0 sK2 X0]
  have l23 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54291 sK2 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l22 X0 sK2]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l19 sK1 sK2]
    conv => enter [1]; rw [← l23 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l25 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [l23 sK2 X0]
  have l26 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l27 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l26 sK1 sK2 X0]
    conv => enter [1]; rw [← l20 X0 sK2 sK2]
  have l28 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l25 sK1 sK2 X0]
    conv => enter [1]; rw [← l27 sK1 sK2 X0]
  have l29 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l28 sK1 sK2 (sK1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h54291 X0 X1 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l30 : ∀ sK1 sK2 X2 X3 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X3 ◇ (X1 ◇ X0))) := by
    intro sK1 sK2 X2 X3 X1 X0
    conv => enter [1]; rw [l29 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h54291 X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l30 x y z y w x]

theorem Equation4512_54264_implies_Equation54291 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54264 : Equation54264 G) : Equation54291 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ X0) X1]
  have l2 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l3 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l2 sK2 X0 X1]
    conv => enter [1]; rw [← h54264 X1 sK2 sK2 X0]
  have l4 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l3 sK2 X0 X1]
  have l5 : ∀ X2 sK2 X0 X1 : G, (X2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 sK2 X0 X1
    conv => enter [1]; rw [← l4 sK2 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ sK2 X0 sK1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← l4 sK2 sK1 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) X0]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l4 sK2 (sK2 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK1]
  have l8 : ∀ sK2 X1 X0 X2 : G, ((sK2 ◇ sK2) ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X2) := by
    intro sK2 X1 X0 X2
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l4 sK2 X1 X0]
  have l9 : ∀ sK2 X1 X0 X2 : G, ((sK2 ◇ sK2) ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X2)) := by
    intro sK2 X1 X0 X2
    conv => enter [1]; rw [l8 sK2 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X2]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK1)]
  have l11 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [← l4 sK2 (X0 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [← l6 sK2 X0 X0]
  have l12 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l4 sK2 sK2 sK2]
    conv => enter [1]; rw [← l4 sK2 sK1 (sK2 ◇ sK2)]
  have l13 : ∀ X2 sK2 X1 : G, (X2 ◇ (sK2 ◇ sK2)) = ((X1 ◇ X2) ◇ (sK2 ◇ sK2)) := by
    intro X2 sK2 X1
    conv => enter [1]; rw [l5 X2 sK2 X2 X1]
    conv => enter [1]; rw [l4 sK2 X2 (X1 ◇ X2)]
  have l14 : ∀ X2 sK2 X0 : G, (X2 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X2)) := by
    intro X2 sK2 X0
    conv => enter [1]; rw [← l4 sK2 (X2 ◇ X0) X2]
    conv => enter [1]; rw [l9 sK2 X2 X0 X2]
  have l15 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [l11 X0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) X0 (sK2 ◇ sK2)]
  have l16 : ∀ X2 sK2 X1 : G, (X2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro X2 sK2 X1
    conv => enter [1]; rw [l13 X2 sK2 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK2)]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← l14 (sK2 ◇ sK1) sK2 sK2]
  have l18 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l15 X0 sK2]
    conv => enter [1]; rw [l4 sK2 X0 (sK2 ◇ sK2)]
  have l19 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l4 sK2 (sK2 ◇ sK2) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l4 sK2 sK2 sK1]
  have l20 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l12 sK2 sK1]
    conv => enter [1]; rw [← l19 sK2 sK1]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [← l20 sK2 sK1]
  have l22 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l4 sK2 sK2 sK2]
    conv => enter [1]; rw [← l18 X0 sK2]
  have l23 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l21 sK1 sK2]
    conv => enter [1]; rw [l22 sK2 X0]
  have l24 : ∀ X0 X1 X2 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X0) ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 X2 sK2
    conv => enter [1]; rw [h54264 X0 X1 (sK2 ◇ sK2) X2]
    conv => enter [1]; rw [l4 sK2 X1 (X2 ◇ X0)]
  have l25 : ∀ X0 X1 X2 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 X2 sK2
    conv => enter [1]; rw [l24 X0 X1 X2 sK2]
    conv => enter [1]; rw [← h4512 X2 X0 (sK2 ◇ sK2)]
  have l26 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l16 X0 sK2 X0]
    conv => enter [1]; rw [← l25 X0 X1 X0 sK2]
  have l27 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l23 sK1 sK2 X0]
    conv => enter [1]; rw [l26 X0 sK2 X1]
  have l28 : ∀ sK1 sK2 X2 X1 X3 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X1 ◇ (X3 ◇ X0))) := by
    intro sK1 sK2 X2 X1 X3 X0
    conv => enter [1]; rw [l27 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h54264 X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l28 x y z w y x]

theorem Equation4512_54291_implies_Equation54268 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54268 G := by
  have l0 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ X0)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l1 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ X0))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← l0 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l2 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [← l1 sK3 X0]
    conv => enter [1]; rw [← h54291 X0 sK3 sK3 (sK3 ◇ sK3)]
  have l3 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [← l2 sK3 sK3]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK3]
  have l4 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l3 sK3]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK3)]
  have l5 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)))) := by
    intro sK3
    conv => enter [1, 2]; rw [l4 sK3]
    conv => enter [1]; rw [l0 sK3 ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))]
  have l6 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l5 sK3]
    conv => enter [1]; rw [← h54291 (sK3 ◇ sK3) (sK3 ◇ sK3) sK3 (sK3 ◇ sK3)]
  have l7 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [← l2 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l6 sK3]
  have l8 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l7 sK3]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK3)]
  have l9 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3
    conv => enter [1]; rw [l4 sK3]
    conv => enter [1]; rw [← l8 sK3]
  have l10 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1, 1]; rw [l9 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK3 ◇ sK3) X0]
  have l11 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [l10 sK3 X0]
    conv => enter [1]; rw [l2 sK3 X0]
  have l12 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ sK3) X0]
    conv => enter [1]; rw [l11 sK3 X0]
  have l13 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 ((sK3 ◇ sK3) ◇ X0)]
    conv => enter [1, 2]; rw [l12 sK3 X0]
  have l14 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [← l2 sK3 X0]
    conv => enter [1]; rw [l13 sK3 X0]
  have l15 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l14 sK2 sK3]
    conv => enter [1]; rw [l0 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l16 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l14 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l17 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l14 sK2 sK3]
    conv => enter [1]; rw [l16 sK3 sK2]
  have l18 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← l12 sK3 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [← l15 sK3 sK2]
  have l19 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l17 sK2 sK3]
    conv => enter [1]; rw [← l18 sK2 sK3]
  have l20 : ∀ sK0 X0 sK1 X1 X2 : G, ((sK0 ◇ X0) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1 X1 X2
    conv => enter [1]; rw [h54291 (sK0 ◇ X0) sK1 X1 X2]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l21 : ∀ X1 X0 sK3 : G, (X1 ◇ (X0 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (X0 ◇ X0)) := by
    intro X1 X0 sK3
    conv => enter [1, 2]; rw [l14 X0 sK3]
    conv => enter [1]; rw [← h54291 (sK3 ◇ sK3) X0 X1 sK3]
  have l22 : ∀ X0 sK3 X1 : G, (X0 ◇ (sK3 ◇ sK3)) = (X1 ◇ (sK3 ◇ ((sK3 ◇ sK3) ◇ X0))) := by
    intro X0 sK3 X1
    conv => enter [1]; rw [h54291 X0 sK3 X1 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 sK3 X0]
  have l23 : ∀ X0 X1 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK3 sK1 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK3 (sK1 ◇ sK0) (X1 ◇ X0)]
  have l24 : ∀ X0 X1 sK4 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK4 sK3 sK1 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK4 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK4 (sK3 ◇ (sK1 ◇ sK0)) (X1 ◇ X0)]
  have l25 : ∀ X0 X1 sK3 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (sK3 ◇ sK3)) := by
    intro X0 X1 sK3
    conv => enter [1]; rw [h54291 X0 X1 (sK3 ◇ sK3) (sK3 ◇ sK3)]
    conv => enter [1]; rw [l2 sK3 (X1 ◇ X0)]
  have l26 : ∀ X0 X1 sK3 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 X1 sK3
    conv => enter [1]; rw [l25 X0 X1 sK3]
    conv => enter [1]; rw [← h4512 X1 X0 (sK3 ◇ sK3)]
  have l27 : ∀ X0 sK3 : G, (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3
    conv => enter [1]; rw [h54291 X0 (sK3 ◇ sK3) X0 sK3]
    conv => enter [1]; rw [← l22 X0 sK3 X0]
  have l28 : ∀ X0 X1 sK4 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))))) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK4 sK3 sK1 sK0
    conv => enter [1]; rw [← h54291 (sK3 ◇ (sK1 ◇ sK0)) sK4 X0 X1]
    conv => enter [1]; rw [l23 (sK3 ◇ (sK1 ◇ sK0)) sK4 sK3 sK1 sK0]
  have l29 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ X0) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54291 X0 (sK1 ◇ sK0) X0 X0]
    conv => enter [1]; rw [← l20 sK0 X0 sK1 X0 X0]
  have l30 : ∀ X0 X1 sK1 sK0 sK4 sK3 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK1 sK0 sK4 sK3
    conv => enter [1]; rw [← h54291 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l24 sK0 sK1 sK4 sK3 sK1 sK0]
  have l31 : ∀ sK3 X0 X1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [h54291 sK3 sK3 X1 X0]
    conv => enter [1]; rw [← l26 X0 X1 sK3]
  have l32 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l29 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK1 ◇ sK1)]
  have l33 : ∀ sK3 X0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [h54291 sK3 sK3 X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l27 X0 sK3]
  have l34 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l32 X0 sK1 sK0]
    conv => enter [1]; rw [← h54291 sK1 sK1 sK0 X0]
  have l35 : ∀ X0 sK1 sK0 sK4 sK3 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0 sK4 sK3
    conv => enter [1]; rw [l34 X0 sK1 sK0]
    conv => enter [1]; rw [l24 sK1 sK1 sK4 sK3 sK1 sK0]
  have l36 : ∀ X0 sK1 sK0 sK4 sK3 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0 sK4 sK3
    conv => enter [1]; rw [l35 X0 sK1 sK0 sK4 sK3]
    conv => enter [1]; rw [l24 (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) sK1 sK4 sK3 sK1 sK0]
  have l37 : ∀ X0 sK1 sK0 sK3 sK4 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l36 X0 sK1 sK0 sK4 sK3]
    conv => enter [1]; rw [l28 (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) sK1 sK4 sK3 sK1 sK0]
  have l38 : ∀ sK3 sK1 sK0 sK4 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l31 sK3 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l37 sK3 sK1 sK0 sK3 sK4]
  have l39 : ∀ sK4 sK3 sK1 sK0 : G, ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (sK4 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK4 sK3 sK1 sK0
    conv => enter [1]; rw [← h4512 sK4 (sK3 ◇ (sK1 ◇ sK0)) (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l38 sK3 sK1 sK0 sK4]
  have l40 : ∀ sK3 sK4 sK1 sK0 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l21 sK4 sK3 sK3]
    conv => enter [1]; rw [← l39 sK4 sK3 sK1 sK0]
  have l41 : ∀ sK3 sK4 sK1 sK0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ sK3)) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l0 sK3 sK3]
    conv => enter [1]; rw [l40 sK3 sK4 sK1 sK0]
  have l42 : ∀ sK3 sK4 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l12 sK3 sK3]
    conv => enter [1]; rw [l41 sK3 sK4 sK1 sK0]
  have l43 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l19 sK2 sK3]
    conv => enter [1]; rw [← l33 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l44 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l43 sK2 sK3]
    conv => enter [1]; rw [l33 sK3 X0]
  have l45 : ∀ sK3 X0 sK4 sK1 sK0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK3 X0 sK4 sK1 sK0
    conv => enter [1, 1]; rw [l42 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) X0]
  have l46 : ∀ sK3 X0 sK4 sK1 sK0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ sK3) X0]
    conv => enter [1]; rw [l45 sK3 X0 sK4 sK1 sK0]
  have l47 : ∀ X0 sK3 sK4 sK1 sK0 : G, (X0 ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro X0 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l12 sK3 X0]
    conv => enter [1]; rw [l46 sK3 X0 sK4 sK1 sK0]
  have l48 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l44 sK2 sK3 X0]
    conv => enter [1]; rw [l47 X0 sK3 sK4 sK1 sK0]
  have l49 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l48 sK2 sK3 sK4 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l30 (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) sK1 sK0 sK4 sK3]
  have l50 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l49 sK2 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [← l30 X0 sK3 sK1 sK0 sK2 sK3]
  intro x y z w u
  conv => enter [1]; rw [l50 x y z w u]

theorem Equation4512_54268_implies_Equation54291 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54268 : Equation54268 G) : Equation54291 G := by
  have l0 : ∀ X0 sK2 X1 X2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro X0 sK2 X1 X2
    conv => enter [1]; rw [h54268 X0 sK2 sK2 X1 X2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ X2)]
  have l1 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l0 X0 sK2 X0 X0]
    conv => enter [1]; rw [← l0 X1 sK2 X0 X0]
  have l2 : ∀ sK2 X1 X2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (X1 ◇ X2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 X1 X2 sK0 sK1
    conv => enter [1]; rw [← l0 sK2 sK2 X1 X2]
    conv => enter [1]; rw [l0 sK2 sK2 sK0 (sK2 ◇ sK1)]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l0 (sK2 ◇ sK1) sK2 sK0 (sK2 ◇ sK1)]
  have l4 : ∀ sK2 sK1 X1 X2 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro sK2 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK2]
    conv => enter [1]; rw [← l2 sK2 X1 X2 sK2 sK1]
  have l5 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ sK2) X1]
    conv => enter [1, 1]; rw [l0 X0 sK2 sK1 (sK2 ◇ sK2)]
  have l6 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l5 X0 sK2 X1 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2)) X1]
  have l7 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l4 sK2 sK1 (sK1 ◇ (sK2 ◇ sK2)) X1]
    conv => enter [1]; rw [← l6 X0 sK2 X1 sK1]
  have l8 : ∀ X0 sK2 X1 X2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK2)]
  have l9 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l8 X0 sK2 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK2 sK1]
  have l10 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l9 sK1 sK2 X1 sK1]
  have l11 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ sK2) X1]
    conv => enter [1, 1]; rw [l1 X0 sK2 sK1]
  have l12 : ∀ sK2 sK1 X1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK2 sK1 X1
    conv => enter [1]; rw [l7 sK2 sK1 sK2 X1]
    conv => enter [1]; rw [l11 sK2 sK2 X1 sK1]
  have l13 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l10 sK1 sK2 sK2]
    conv => enter [1]; rw [l12 sK2 sK1 X1]
  have l14 : ∀ sK1 sK2 X1 X0 X2 X3 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 X1 X0 X2 X3
    conv => enter [1]; rw [l13 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1]; rw [h54268 (sK1 ◇ (sK2 ◇ sK2)) X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l14 x y z w y x]

theorem Equation4512_54291_implies_Equation54290 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54290 G := by
  have l0 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ X0)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l1 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK3) sK3]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK3]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0)) = (((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK3 ◇ sK3)) X0]
    conv => enter [1, 1]; rw [← l1 sK2 sK3]
  have l3 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l2 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK3)) sK3 X0]
  have l4 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ X0)) = (sK2 ◇ (sK3 ◇ ((sK3 ◇ sK3) ◇ X0))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← l3 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← h4512 sK3 (sK3 ◇ sK3) X0]
  have l5 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ X0)) = (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0]
    conv => enter [1]; rw [← h54291 X0 (sK3 ◇ sK3) sK2 sK3]
  have l6 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ X0))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← l0 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l7 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [← l6 sK3 X0]
    conv => enter [1]; rw [← h54291 X0 sK3 sK3 (sK3 ◇ sK3)]
  have l8 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [← l7 sK3 sK3]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK3]
  have l9 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l8 sK3]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK3)]
  have l10 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)))) := by
    intro sK3
    conv => enter [1, 2]; rw [l9 sK3]
    conv => enter [1]; rw [l0 sK3 ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))]
  have l11 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l10 sK3]
    conv => enter [1]; rw [← h54291 (sK3 ◇ sK3) (sK3 ◇ sK3) sK3 (sK3 ◇ sK3)]
  have l12 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [← l7 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l11 sK3]
  have l13 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l12 sK3]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK3)]
  have l14 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3
    conv => enter [1]; rw [l9 sK3]
    conv => enter [1]; rw [← l13 sK3]
  have l15 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1, 2]; rw [l14 sK3]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK3) (sK3 ◇ sK3)]
  have l16 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1, 1]; rw [l14 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK3 ◇ sK3) X0]
  have l17 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [l16 sK3 X0]
    conv => enter [1]; rw [l7 sK3 X0]
  have l18 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l1 sK2 sK3]
    conv => enter [1]; rw [l15 sK2 sK3]
  have l19 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ sK3) X0]
    conv => enter [1]; rw [l17 sK3 X0]
  have l20 : ∀ sK3 X0 : G, (((sK3 ◇ sK3) ◇ X0) ◇ (sK3 ◇ sK3)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0
    conv => enter [1]; rw [← l19 sK3 ((sK3 ◇ sK3) ◇ X0)]
    conv => enter [1, 2]; rw [l7 sK3 X0]
  have l21 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 ((sK3 ◇ sK3) ◇ X0)]
    conv => enter [1, 2]; rw [l19 sK3 X0]
  have l22 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [← l7 sK3 X0]
    conv => enter [1]; rw [l21 sK3 X0]
  have l23 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0
    conv => enter [1]; rw [h4512 (sK3 ◇ sK3) X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l20 sK3 X0]
  have l24 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [l22 X0 sK3]
    conv => enter [1]; rw [← l23 sK3 X0]
  have l25 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = (sK3 ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l18 sK2 sK3]
    conv => enter [1]; rw [l22 (sK2 ◇ (sK3 ◇ sK3)) sK3]
    conv => enter [1, 2]; rw [← l18 sK2 sK3]
  have l26 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 X0
    conv => enter [1, 2]; rw [l22 X0 sK3]
    conv => enter [1]; rw [l0 sK3 (X0 ◇ (sK3 ◇ sK3))]
  have l27 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) = ((X0 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [l26 sK3 X0]
    conv => enter [1]; rw [l19 sK3 (X0 ◇ (sK3 ◇ sK3))]
  have l28 : ∀ X0 sK3 : G, (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [h4512 X0 (sK3 ◇ sK3) (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l27 sK3 X0]
  have l29 : ∀ X0 sK3 : G, (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3
    conv => enter [1]; rw [l28 X0 sK3]
    conv => enter [1]; rw [← l24 X0 sK3]
  have l30 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [← l29 X0 sK3]
    conv => enter [1, 2]; rw [← l14 sK3]
  have l31 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l22 sK2 sK3]
    conv => enter [1]; rw [l0 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l32 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l22 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l33 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l22 sK2 sK3]
    conv => enter [1]; rw [l32 sK3 sK2]
  have l34 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← l19 sK3 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [← l31 sK3 sK2]
  have l35 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l33 sK2 sK3]
    conv => enter [1]; rw [← l34 sK2 sK3]
  have l36 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1, 1]; rw [l33 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK2 ◇ (sK3 ◇ sK3)) X0]
  have l37 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) := by
    intro sK2 sK3
    conv => enter [1]; rw [l35 sK2 sK3]
    conv => enter [1]; rw [← l18 sK2 sK3]
  have l38 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l25 sK2 sK3]
    conv => enter [1]; rw [l0 sK3 ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)]
  have l39 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) = (((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [l38 sK3 sK2]
    conv => enter [1]; rw [l19 sK3 ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)]
  have l40 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l39 sK3 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK3)) sK3 (sK3 ◇ sK3)]
  have l41 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [← l5 sK2 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l40 sK3 sK2]
  have l42 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l36 sK2 sK3 sK3]
    conv => enter [1]; rw [← l41 sK3 sK2]
  have l43 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l42 sK2 sK3]
    conv => enter [1]; rw [l7 sK3 (sK3 ◇ sK3)]
  have l44 : ∀ sK3 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) := by
    intro sK3 sK2
    conv => enter [1]; rw [l14 sK3]
    conv => enter [1]; rw [← l43 sK2 sK3]
  have l45 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l37 sK2 sK3]
    conv => enter [1]; rw [← l44 sK3 sK2]
  have l46 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l1 sK2 sK3]
    conv => enter [1, 2]; rw [← l45 sK2 sK3]
  have l47 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l37 sK2 sK3]
    conv => enter [1]; rw [l46 sK2 sK3]
  have l48 : ∀ X0 X1 sK3 : G, ((X0 ◇ X1) ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ sK3)))) := by
    intro X0 X1 sK3
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l30 X1 sK3]
  have l49 : ∀ sK3 X0 X1 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((X0 ◇ X1) ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [h54291 (sK3 ◇ sK3) sK3 X0 X1]
    conv => enter [1]; rw [← l48 X0 X1 sK3]
  have l50 : ∀ sK3 X0 X1 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [l49 sK3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ sK3)]
  have l51 : ∀ sK3 X0 X1 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [← l0 sK3 sK3]
    conv => enter [1]; rw [l50 sK3 X0 X1]
  have l52 : ∀ sK3 X0 X1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [← l19 sK3 sK3]
    conv => enter [1]; rw [l51 sK3 X0 X1]
  have l53 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l45 sK2 sK3]
    conv => enter [1]; rw [l52 sK3 X0 X1]
  have l54 : ∀ X0 X1 sK3 X2 sK2 : G, (X0 ◇ ((X1 ◇ (sK3 ◇ sK3)) ◇ X2)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) := by
    intro X0 X1 sK3 X2 sK2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (sK3 ◇ sK3)) X2]
    conv => enter [1, 1]; rw [← l53 sK2 sK3 X0 X1]
  have l55 : ∀ sK2 sK3 X2 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK3 ◇ sK3) ◇ X2))) := by
    intro sK2 sK3 X2 X0 X1
    conv => enter [1]; rw [← l54 X0 X1 sK3 X2 sK2]
    conv => enter [1, 2]; rw [← h4512 X1 (sK3 ◇ sK3) X2]
  have l56 : ∀ sK2 sK3 X2 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) = (X2 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X2
    conv => enter [1]; rw [l55 sK2 sK3 X2 sK2 sK2]
    conv => enter [1]; rw [← h54291 X2 (sK3 ◇ sK3) sK2 sK2]
  have l57 : ∀ sK2 sK3 X2 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) := by
    intro sK2 sK3 X2
    conv => enter [1]; rw [l53 sK2 sK3 X2 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l56 sK2 sK3 X2]
  have l58 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [h54291 X0 X1 sK2 (sK3 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK3) (X1 ◇ X0)]
  have l59 : ∀ X0 X1 sK3 : G, (X0 ◇ (X1 ◇ X1)) = ((sK3 ◇ sK3) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK3
    conv => enter [1]; rw [h54291 X0 X1 sK3 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (X1 ◇ X0)]
  have l60 : ∀ X0 X1 sK4 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK4 sK1 sK2 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK4 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ (sK2 ◇ sK0)) (X1 ◇ X0)]
  have l61 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l57 sK2 sK3 (X1 ◇ X0)]
    conv => enter [1]; rw [← l58 X0 X1 sK2 sK3]
  have l62 : ∀ X0 X1 sK2 sK0 sK4 sK1 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro X0 X1 sK2 sK0 sK4 sK1
    conv => enter [1]; rw [← h54291 sK0 sK2 X0 X1]
    conv => enter [1]; rw [l60 sK0 sK2 sK4 sK1 sK2 sK0]
  have l63 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l61 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 sK0 (X0 ◇ X0)]
  have l64 : ∀ sK2 sK3 X0 sK0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 X0 sK0
    conv => enter [1]; rw [l63 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l59 (sK2 ◇ sK0) X0 sK3]
  have l65 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l64 sK2 sK3 sK2 sK0]
    conv => enter [1]; rw [l62 (sK3 ◇ sK3) sK2 sK2 sK0 sK4 sK1]
  have l66 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l47 sK2 sK3]
    conv => enter [1]; rw [l65 sK2 sK3 sK4 sK1 sK0]
  have l67 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l66 sK2 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [← l62 X0 sK1 sK2 sK0 sK2 sK1]
  intro x y z w u
  conv => enter [1]; rw [l67 x y z w u]

theorem Equation4512_54290_implies_Equation54291 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54290 : Equation54290 G) : Equation54291 G := by
  have l0 : ∀ X2 X3 X0 X4 sK1 sK2 : G, (X2 ◇ (X3 ◇ (X0 ◇ X4))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X2 X3 X0 X4 sK1 sK2
    conv => enter [1]; rw [← h54290 X0 (X2 ◇ (sK1 ◇ (sK2 ◇ sK2))) X2 X3 X4]
    conv => enter [1, 2]; rw [← h54290 sK1 sK2 (X2 ◇ (sK1 ◇ (sK2 ◇ sK2))) X2 (sK2 ◇ sK2)]
  have l1 : ∀ X0 X1 sK1 sK2 X2 : G, (X0 ◇ ((X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2) := by
    intro X0 X1 sK1 sK2 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X2]
    conv => enter [1, 1]; rw [← h54290 sK1 sK2 X0 X1 (sK2 ◇ sK2)]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54290 sK1 sK2 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
  have l3 : ∀ sK1 sK2 X2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [← l1 X0 X1 sK1 sK2 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (sK1 ◇ (sK2 ◇ sK2)) X2]
  have l4 : ∀ sK1 sK2 X2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2) := by
    intro sK1 sK2 X2
    conv => enter [1]; rw [← l0 sK1 sK1 (sK1 ◇ (sK2 ◇ sK2)) X2 sK1 sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 X2 sK1 sK1]
  have l5 : ∀ sK1 sK2 X2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2) := by
    intro sK1 sK2 X2
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 sK2 X2]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ (X0 ◇ sK1))]
    conv => enter [1]; rw [← h54290 X0 X1 (sK1 ◇ (sK2 ◇ sK2)) sK1 sK1]
  have l7 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK2 sK1]
    conv => enter [1]; rw [h54290 sK2 sK1 X1 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

theorem Equation4512_54291_implies_Equation54295 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54295 G := by
  have l0 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ X0)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l1 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ X0))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← l0 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l2 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [← l1 sK3 X0]
    conv => enter [1]; rw [← h54291 X0 sK3 sK3 (sK3 ◇ sK3)]
  have l3 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [← l2 sK3 sK3]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK3]
  have l4 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l3 sK3]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK3)]
  have l5 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)))) := by
    intro sK3
    conv => enter [1, 2]; rw [l4 sK3]
    conv => enter [1]; rw [l0 sK3 ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))]
  have l6 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l5 sK3]
    conv => enter [1]; rw [← h54291 (sK3 ◇ sK3) (sK3 ◇ sK3) sK3 (sK3 ◇ sK3)]
  have l7 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [← l2 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l6 sK3]
  have l8 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l7 sK3]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK3)]
  have l9 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3
    conv => enter [1]; rw [l4 sK3]
    conv => enter [1]; rw [← l8 sK3]
  have l10 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1, 1]; rw [l9 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK3 ◇ sK3) X0]
  have l11 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [l10 sK3 X0]
    conv => enter [1]; rw [l2 sK3 X0]
  have l12 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ sK3) X0]
    conv => enter [1]; rw [l11 sK3 X0]
  have l13 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 ((sK3 ◇ sK3) ◇ X0)]
    conv => enter [1, 2]; rw [l12 sK3 X0]
  have l14 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [← l2 sK3 X0]
    conv => enter [1]; rw [l13 sK3 X0]
  have l15 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l14 sK2 sK3]
    conv => enter [1]; rw [l0 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l16 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l14 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l17 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l14 sK2 sK3]
    conv => enter [1]; rw [l16 sK3 sK2]
  have l18 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← l12 sK3 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [← l15 sK3 sK2]
  have l19 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l17 sK2 sK3]
    conv => enter [1]; rw [← l18 sK2 sK3]
  have l20 : ∀ X0 sK3 X1 : G, (X0 ◇ (sK3 ◇ sK3)) = (X1 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro X0 sK3 X1
    conv => enter [1]; rw [h54291 X0 sK3 X1 sK3]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l21 : ∀ X0 sK3 X1 : G, (X0 ◇ (sK3 ◇ sK3)) = (X1 ◇ (sK3 ◇ ((sK3 ◇ sK3) ◇ X0))) := by
    intro X0 sK3 X1
    conv => enter [1]; rw [h54291 X0 sK3 X1 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 sK3 X0]
  have l22 : ∀ X0 X1 sK4 sK1 sK3 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK4 sK1 sK3 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK4 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ (sK3 ◇ sK0)) (X1 ◇ X0)]
  have l23 : ∀ X0 sK3 : G, (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3
    conv => enter [1]; rw [h54291 X0 (sK3 ◇ sK3) X0 sK3]
    conv => enter [1]; rw [← l21 X0 sK3 X0]
  have l24 : ∀ X0 X1 sK3 sK0 sK4 sK1 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 sK3 sK0 sK4 sK1
    conv => enter [1]; rw [← h54291 sK0 sK3 X0 X1]
    conv => enter [1]; rw [l22 sK0 sK3 sK4 sK1 sK3 sK0]
  have l25 : ∀ sK3 X0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [h54291 sK3 sK3 X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l23 X0 sK3]
  have l26 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l19 sK2 sK3]
    conv => enter [1]; rw [← l25 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l27 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l26 sK2 sK3]
    conv => enter [1]; rw [l25 sK3 X0]
  have l28 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1, 1]; rw [l26 sK2 sK3]
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK3) X0]
  have l29 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l28 sK2 sK3 X0]
    conv => enter [1]; rw [← l20 X0 sK3 sK3]
  have l30 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l27 sK2 sK3 X0]
    conv => enter [1]; rw [← l29 sK2 sK3 X0]
  have l31 : ∀ X0 sK3 X1 sK2 : G, (X0 ◇ ((sK3 ◇ sK3) ◇ X1)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X1) := by
    intro X0 sK3 X1 sK2
    conv => enter [1]; rw [h4512 X0 (sK3 ◇ sK3) X1]
    conv => enter [1, 1]; rw [l27 X0 sK3 sK2]
  have l32 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ ((sK3 ◇ sK3) ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l30 sK2 sK3 X1]
    conv => enter [1]; rw [← l31 X0 sK3 X1 sK2]
  have l33 : ∀ sK2 sK3 X0 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 X0 sK0
    conv => enter [1]; rw [l32 sK2 sK3 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK0]
  have l34 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l33 sK2 sK3 sK2 sK0]
    conv => enter [1]; rw [l24 sK2 sK3 sK3 sK0 sK4 sK1]
  have l35 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l34 sK2 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [← l24 X0 sK1 sK3 sK0 sK2 sK1]
  intro x y z w u
  conv => enter [1]; rw [l35 x y z w u]

@[equational_result]
theorem Equation54295_implies_Equation54291 (G : Type*) [Magma G] (h54295 : Equation54295 G) : Equation54291 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54295 sK1 sK2 sK1 sK1 sK2]
    conv => enter [1]; rw [← h54295 X0 sK2 sK1 sK1 sK2]
  have l1 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [h54295 sK1 sK2 X1 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_54291_implies_Equation54306 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54306 G := by
  have l0 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ X0)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l1 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK3) sK3]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK3]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0)) = (((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK3 ◇ sK3)) X0]
    conv => enter [1, 1]; rw [← l1 sK2 sK3]
  have l3 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l2 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK3)) sK3 X0]
  have l4 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ X0)) = (sK2 ◇ (sK3 ◇ ((sK3 ◇ sK3) ◇ X0))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← l3 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← h4512 sK3 (sK3 ◇ sK3) X0]
  have l5 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ X0)) = (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0]
    conv => enter [1]; rw [← h54291 X0 (sK3 ◇ sK3) sK2 sK3]
  have l6 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ X0))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← l0 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l7 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [← l6 sK3 X0]
    conv => enter [1]; rw [← h54291 X0 sK3 sK3 (sK3 ◇ sK3)]
  have l8 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [← l7 sK3 sK3]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK3]
  have l9 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l8 sK3]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK3)]
  have l10 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)))) := by
    intro sK3
    conv => enter [1, 2]; rw [l9 sK3]
    conv => enter [1]; rw [l0 sK3 ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))]
  have l11 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l10 sK3]
    conv => enter [1]; rw [← h54291 (sK3 ◇ sK3) (sK3 ◇ sK3) sK3 (sK3 ◇ sK3)]
  have l12 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [← l7 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l11 sK3]
  have l13 : ∀ sK3 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3
    conv => enter [1]; rw [l12 sK3]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK3)]
  have l14 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3
    conv => enter [1]; rw [l9 sK3]
    conv => enter [1]; rw [← l13 sK3]
  have l15 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1, 2]; rw [l14 sK3]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK3) (sK3 ◇ sK3)]
  have l16 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1, 1]; rw [l14 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK3 ◇ sK3) X0]
  have l17 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [l16 sK3 X0]
    conv => enter [1]; rw [l7 sK3 X0]
  have l18 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l1 sK2 sK3]
    conv => enter [1]; rw [l15 sK2 sK3]
  have l19 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ sK3) X0]
    conv => enter [1]; rw [l17 sK3 X0]
  have l20 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 ((sK3 ◇ sK3) ◇ X0)]
    conv => enter [1, 2]; rw [l19 sK3 X0]
  have l21 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [← l7 sK3 X0]
    conv => enter [1]; rw [l20 sK3 X0]
  have l22 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = (sK3 ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l18 sK2 sK3]
    conv => enter [1]; rw [l21 (sK2 ◇ (sK3 ◇ sK3)) sK3]
    conv => enter [1, 2]; rw [← l18 sK2 sK3]
  have l23 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l21 sK2 sK3]
    conv => enter [1]; rw [l0 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l24 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l21 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l25 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l21 sK2 sK3]
    conv => enter [1]; rw [l24 sK3 sK2]
  have l26 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← l19 sK3 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [← l23 sK3 sK2]
  have l27 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l25 sK2 sK3]
    conv => enter [1]; rw [← l26 sK2 sK3]
  have l28 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1, 1]; rw [l25 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK2 ◇ (sK3 ◇ sK3)) X0]
  have l29 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) := by
    intro sK2 sK3
    conv => enter [1]; rw [l27 sK2 sK3]
    conv => enter [1]; rw [← l18 sK2 sK3]
  have l30 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l22 sK2 sK3]
    conv => enter [1]; rw [l0 sK3 ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)]
  have l31 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) = (((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [l30 sK3 sK2]
    conv => enter [1]; rw [l19 sK3 ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)]
  have l32 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l31 sK3 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK3)) sK3 (sK3 ◇ sK3)]
  have l33 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [← l5 sK2 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l32 sK3 sK2]
  have l34 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l28 sK2 sK3 sK3]
    conv => enter [1]; rw [← l33 sK3 sK2]
  have l35 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l34 sK2 sK3]
    conv => enter [1]; rw [l7 sK3 (sK3 ◇ sK3)]
  have l36 : ∀ sK3 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) := by
    intro sK3 sK2
    conv => enter [1]; rw [l14 sK3]
    conv => enter [1]; rw [← l35 sK2 sK3]
  have l37 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l29 sK2 sK3]
    conv => enter [1]; rw [← l36 sK3 sK2]
  have l38 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l37 sK2 sK3]
    conv => enter [1]; rw [h54291 sK3 sK3 X0 X1]
  have l39 : ∀ X0 X1 sK3 X2 sK2 : G, (X0 ◇ ((X1 ◇ (sK3 ◇ sK3)) ◇ X2)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) := by
    intro X0 X1 sK3 X2 sK2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (sK3 ◇ sK3)) X2]
    conv => enter [1, 1]; rw [← l38 sK2 sK3 X0 X1]
  have l40 : ∀ X0 X1 sK3 X2 sK2 : G, (X0 ◇ (X1 ◇ ((sK3 ◇ sK3) ◇ X2))) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) := by
    intro X0 X1 sK3 X2 sK2
    conv => enter [1, 2]; rw [h4512 X1 (sK3 ◇ sK3) X2]
    conv => enter [1]; rw [l39 X0 X1 sK3 X2 sK2]
  have l41 : ∀ X2 sK3 sK2 : G, (X2 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) := by
    intro X2 sK3 sK2
    conv => enter [1]; rw [h54291 X2 (sK3 ◇ sK3) X2 X2]
    conv => enter [1]; rw [l40 X2 X2 sK3 X2 sK2]
  have l42 : ∀ sK2 sK3 X2 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) := by
    intro sK2 sK3 X2
    conv => enter [1]; rw [l38 sK2 sK3 X2 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l41 X2 sK3 sK2]
  have l43 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l42 sK2 sK3 (sK2 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h54291 X0 X1 (sK2 ◇ (sK3 ◇ sK3)) sK2]
  have l44 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l43 sK2 sK3 sK2 sK0]
    conv => enter [1]; rw [h54291 sK2 sK0 X0 sK1]
  intro x y z w u
  conv => enter [1]; rw [l44 x y z w u]

theorem Equation4512_54306_implies_Equation54291 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54306 : Equation54306 G) : Equation54291 G := by
  have l0 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← h54306 (sK2 ◇ sK1) X0 sK0 (sK2 ◇ sK1) sK0]
  have l1 : ∀ X1 X2 X0 sK3 sK0 sK2 sK1 : G, (X1 ◇ (X2 ◇ X2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X1 X2 X0 sK3 sK0 sK2 sK1
    conv => enter [1]; rw [h54306 X1 X2 (sK2 ◇ sK1) (X1 ◇ X1) X1]
    conv => enter [1]; rw [h54306 (sK2 ◇ sK1) (X1 ◇ X1) X0 sK3 sK0]
  have l2 : ∀ sK0 sK2 sK1 X1 sK3 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X1 sK3
    conv => enter [1]; rw [l0 sK0 sK2 sK1 sK0]
    conv => enter [1]; rw [h54306 (sK2 ◇ sK1) sK0 X1 sK3 sK0]
  have l3 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1]; rw [h54306 X0 X1 (sK2 ◇ sK1) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← l0 sK0 sK2 sK1 (X0 ◇ X0)]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l2 sK0 sK2 sK1 sK1 sK1]
  have l5 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l3 sK1 sK0 sK0 sK2 sK1]
    conv => enter [1]; rw [h54306 sK1 sK0 X0 sK0 sK2]
  have l6 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK2 sK1 X0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

theorem Equation4512_54291_implies_Equation54311 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54311 G := by
  have l0 : ∀ sK4 X0 : G, ((sK4 ◇ sK4) ◇ (sK4 ◇ X0)) = (sK4 ◇ ((sK4 ◇ sK4) ◇ X0)) := by
    intro sK4 X0
    conv => enter [1]; rw [← h4512 sK4 sK4 (sK4 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK4 sK4 X0]
  have l1 : ∀ sK3 sK4 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4) = (sK3 ◇ (sK4 ◇ (sK4 ◇ sK4))) := by
    intro sK3 sK4
    conv => enter [1]; rw [← h4512 sK3 (sK4 ◇ sK4) sK4]
    conv => enter [1, 2]; rw [← h4512 sK4 sK4 sK4]
  have l2 : ∀ sK3 sK4 X0 : G, (sK3 ◇ ((sK4 ◇ (sK4 ◇ sK4)) ◇ X0)) = (((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4) ◇ X0) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ (sK4 ◇ sK4)) X0]
    conv => enter [1, 1]; rw [← l1 sK3 sK4]
  have l3 : ∀ sK3 sK4 X0 : G, (sK3 ◇ ((sK4 ◇ (sK4 ◇ sK4)) ◇ X0)) = ((sK3 ◇ (sK4 ◇ sK4)) ◇ (sK4 ◇ X0)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l2 sK3 sK4 X0]
    conv => enter [1]; rw [← h4512 (sK3 ◇ (sK4 ◇ sK4)) sK4 X0]
  have l4 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ (sK4 ◇ X0)) = (sK3 ◇ (sK4 ◇ ((sK4 ◇ sK4) ◇ X0))) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [← l3 sK3 sK4 X0]
    conv => enter [1, 2]; rw [← h4512 sK4 (sK4 ◇ sK4) X0]
  have l5 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ (sK4 ◇ X0)) = (X0 ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4))) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l4 sK3 sK4 X0]
    conv => enter [1]; rw [← h54291 X0 (sK4 ◇ sK4) sK3 sK4]
  have l6 : ∀ sK4 X0 : G, (sK4 ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ X0))) = ((sK4 ◇ sK4) ◇ ((sK4 ◇ sK4) ◇ X0)) := by
    intro sK4 X0
    conv => enter [1]; rw [← l0 sK4 (sK4 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK4 sK4 X0]
  have l7 : ∀ sK4 X0 : G, ((sK4 ◇ sK4) ◇ ((sK4 ◇ sK4) ◇ X0)) = (X0 ◇ (sK4 ◇ sK4)) := by
    intro sK4 X0
    conv => enter [1]; rw [← l6 sK4 X0]
    conv => enter [1]; rw [← h54291 X0 sK4 sK4 (sK4 ◇ sK4)]
  have l8 : ∀ sK4 : G, (sK4 ◇ (sK4 ◇ sK4)) = ((sK4 ◇ sK4) ◇ (sK4 ◇ (sK4 ◇ sK4))) := by
    intro sK4
    conv => enter [1]; rw [← l7 sK4 sK4]
    conv => enter [1, 2]; rw [← h4512 sK4 sK4 sK4]
  have l9 : ∀ sK4 : G, (sK4 ◇ (sK4 ◇ sK4)) = (sK4 ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4))) := by
    intro sK4
    conv => enter [1]; rw [l8 sK4]
    conv => enter [1]; rw [l0 sK4 (sK4 ◇ sK4)]
  have l10 : ∀ sK4 : G, ((sK4 ◇ sK4) ◇ (sK4 ◇ (sK4 ◇ sK4))) = (sK4 ◇ ((sK4 ◇ sK4) ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4)))) := by
    intro sK4
    conv => enter [1, 2]; rw [l9 sK4]
    conv => enter [1]; rw [l0 sK4 ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4))]
  have l11 : ∀ sK4 : G, ((sK4 ◇ sK4) ◇ (sK4 ◇ (sK4 ◇ sK4))) = ((sK4 ◇ sK4) ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4))) := by
    intro sK4
    conv => enter [1]; rw [l10 sK4]
    conv => enter [1]; rw [← h54291 (sK4 ◇ sK4) (sK4 ◇ sK4) sK4 (sK4 ◇ sK4)]
  have l12 : ∀ sK4 : G, ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4)) = ((sK4 ◇ sK4) ◇ (sK4 ◇ (sK4 ◇ sK4))) := by
    intro sK4
    conv => enter [1]; rw [← l7 sK4 (sK4 ◇ sK4)]
    conv => enter [1]; rw [← l11 sK4]
  have l13 : ∀ sK4 : G, ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4)) = (sK4 ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4))) := by
    intro sK4
    conv => enter [1]; rw [l12 sK4]
    conv => enter [1]; rw [l0 sK4 (sK4 ◇ sK4)]
  have l14 : ∀ sK4 : G, (sK4 ◇ (sK4 ◇ sK4)) = ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4)) := by
    intro sK4
    conv => enter [1]; rw [l9 sK4]
    conv => enter [1]; rw [← l13 sK4]
  have l15 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ (sK4 ◇ sK4))) = ((sK3 ◇ (sK4 ◇ sK4)) ◇ (sK4 ◇ sK4)) := by
    intro sK3 sK4
    conv => enter [1, 2]; rw [l14 sK4]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK4) (sK4 ◇ sK4)]
  have l16 : ∀ sK4 X0 : G, ((sK4 ◇ (sK4 ◇ sK4)) ◇ X0) = ((sK4 ◇ sK4) ◇ ((sK4 ◇ sK4) ◇ X0)) := by
    intro sK4 X0
    conv => enter [1, 1]; rw [l14 sK4]
    conv => enter [1]; rw [← h4512 (sK4 ◇ sK4) (sK4 ◇ sK4) X0]
  have l17 : ∀ sK4 X0 : G, ((sK4 ◇ (sK4 ◇ sK4)) ◇ X0) = (X0 ◇ (sK4 ◇ sK4)) := by
    intro sK4 X0
    conv => enter [1]; rw [l16 sK4 X0]
    conv => enter [1]; rw [l7 sK4 X0]
  have l18 : ∀ sK3 sK4 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4) = ((sK3 ◇ (sK4 ◇ sK4)) ◇ (sK4 ◇ sK4)) := by
    intro sK3 sK4
    conv => enter [1]; rw [l1 sK3 sK4]
    conv => enter [1]; rw [l15 sK3 sK4]
  have l19 : ∀ sK4 X0 : G, (sK4 ◇ ((sK4 ◇ sK4) ◇ X0)) = (X0 ◇ (sK4 ◇ sK4)) := by
    intro sK4 X0
    conv => enter [1]; rw [h4512 sK4 (sK4 ◇ sK4) X0]
    conv => enter [1]; rw [l17 sK4 X0]
  have l20 : ∀ sK4 X0 : G, (((sK4 ◇ sK4) ◇ X0) ◇ (sK4 ◇ sK4)) = (sK4 ◇ (X0 ◇ (sK4 ◇ sK4))) := by
    intro sK4 X0
    conv => enter [1]; rw [← l19 sK4 ((sK4 ◇ sK4) ◇ X0)]
    conv => enter [1, 2]; rw [l7 sK4 X0]
  have l21 : ∀ sK4 X0 : G, ((sK4 ◇ sK4) ◇ ((sK4 ◇ sK4) ◇ X0)) = (sK4 ◇ (X0 ◇ (sK4 ◇ sK4))) := by
    intro sK4 X0
    conv => enter [1]; rw [← h4512 sK4 sK4 ((sK4 ◇ sK4) ◇ X0)]
    conv => enter [1, 2]; rw [l19 sK4 X0]
  have l22 : ∀ X0 sK4 : G, (X0 ◇ (sK4 ◇ sK4)) = (sK4 ◇ (X0 ◇ (sK4 ◇ sK4))) := by
    intro X0 sK4
    conv => enter [1]; rw [← l7 sK4 X0]
    conv => enter [1]; rw [l21 sK4 X0]
  have l23 : ∀ sK4 X0 : G, ((sK4 ◇ sK4) ◇ (X0 ◇ (sK4 ◇ sK4))) = (sK4 ◇ (X0 ◇ (sK4 ◇ sK4))) := by
    intro sK4 X0
    conv => enter [1]; rw [h4512 (sK4 ◇ sK4) X0 (sK4 ◇ sK4)]
    conv => enter [1]; rw [l20 sK4 X0]
  have l24 : ∀ X0 sK4 : G, (X0 ◇ (sK4 ◇ sK4)) = ((sK4 ◇ sK4) ◇ (X0 ◇ (sK4 ◇ sK4))) := by
    intro X0 sK4
    conv => enter [1]; rw [l22 X0 sK4]
    conv => enter [1]; rw [← l23 sK4 X0]
  have l25 : ∀ sK3 sK4 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4) = (sK4 ◇ ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4)) := by
    intro sK3 sK4
    conv => enter [1]; rw [l18 sK3 sK4]
    conv => enter [1]; rw [l22 (sK3 ◇ (sK4 ◇ sK4)) sK4]
    conv => enter [1, 2]; rw [← l18 sK3 sK4]
  have l26 : ∀ sK4 X0 : G, ((sK4 ◇ sK4) ◇ (X0 ◇ (sK4 ◇ sK4))) = (sK4 ◇ ((sK4 ◇ sK4) ◇ (X0 ◇ (sK4 ◇ sK4)))) := by
    intro sK4 X0
    conv => enter [1, 2]; rw [l22 X0 sK4]
    conv => enter [1]; rw [l0 sK4 (X0 ◇ (sK4 ◇ sK4))]
  have l27 : ∀ sK4 X0 : G, ((sK4 ◇ sK4) ◇ (X0 ◇ (sK4 ◇ sK4))) = ((X0 ◇ (sK4 ◇ sK4)) ◇ (sK4 ◇ sK4)) := by
    intro sK4 X0
    conv => enter [1]; rw [l26 sK4 X0]
    conv => enter [1]; rw [l19 sK4 (X0 ◇ (sK4 ◇ sK4))]
  have l28 : ∀ X0 sK4 : G, (X0 ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4))) = ((sK4 ◇ sK4) ◇ (X0 ◇ (sK4 ◇ sK4))) := by
    intro X0 sK4
    conv => enter [1]; rw [h4512 X0 (sK4 ◇ sK4) (sK4 ◇ sK4)]
    conv => enter [1]; rw [← l27 sK4 X0]
  have l29 : ∀ X0 sK4 : G, (X0 ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4))) = (X0 ◇ (sK4 ◇ sK4)) := by
    intro X0 sK4
    conv => enter [1]; rw [l28 X0 sK4]
    conv => enter [1]; rw [← l24 X0 sK4]
  have l30 : ∀ X0 sK4 : G, (X0 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK4 ◇ (sK4 ◇ sK4))) := by
    intro X0 sK4
    conv => enter [1]; rw [← l29 X0 sK4]
    conv => enter [1, 2]; rw [← l14 sK4]
  have l31 : ∀ sK4 sK3 : G, ((sK4 ◇ sK4) ◇ (sK3 ◇ (sK4 ◇ sK4))) = (sK4 ◇ ((sK4 ◇ sK4) ◇ (sK3 ◇ (sK4 ◇ sK4)))) := by
    intro sK4 sK3
    conv => enter [1, 2]; rw [l22 sK3 sK4]
    conv => enter [1]; rw [l0 sK4 (sK3 ◇ (sK4 ◇ sK4))]
  have l32 : ∀ sK4 sK3 : G, (sK4 ◇ (sK3 ◇ (sK4 ◇ sK4))) = ((sK4 ◇ sK4) ◇ (sK3 ◇ (sK4 ◇ sK4))) := by
    intro sK4 sK3
    conv => enter [1, 2]; rw [l22 sK3 sK4]
    conv => enter [1]; rw [h4512 sK4 sK4 (sK3 ◇ (sK4 ◇ sK4))]
  have l33 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK4)) = ((sK4 ◇ sK4) ◇ (sK3 ◇ (sK4 ◇ sK4))) := by
    intro sK3 sK4
    conv => enter [1]; rw [l22 sK3 sK4]
    conv => enter [1]; rw [l32 sK4 sK3]
  have l34 : ∀ sK3 sK4 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ (sK4 ◇ sK4)) = ((sK4 ◇ sK4) ◇ (sK3 ◇ (sK4 ◇ sK4))) := by
    intro sK3 sK4
    conv => enter [1]; rw [← l19 sK4 (sK3 ◇ (sK4 ◇ sK4))]
    conv => enter [1]; rw [← l31 sK4 sK3]
  have l35 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK4)) = ((sK3 ◇ (sK4 ◇ sK4)) ◇ (sK4 ◇ sK4)) := by
    intro sK3 sK4
    conv => enter [1]; rw [l33 sK3 sK4]
    conv => enter [1]; rw [← l34 sK3 sK4]
  have l36 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ X0) = ((sK4 ◇ sK4) ◇ ((sK3 ◇ (sK4 ◇ sK4)) ◇ X0)) := by
    intro sK3 sK4 X0
    conv => enter [1, 1]; rw [l33 sK3 sK4]
    conv => enter [1]; rw [← h4512 (sK4 ◇ sK4) (sK3 ◇ (sK4 ◇ sK4)) X0]
  have l37 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK4)) = ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4) := by
    intro sK3 sK4
    conv => enter [1]; rw [l35 sK3 sK4]
    conv => enter [1]; rw [← l18 sK3 sK4]
  have l38 : ∀ sK4 sK3 : G, ((sK4 ◇ sK4) ◇ ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4)) = (sK4 ◇ ((sK4 ◇ sK4) ◇ ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4))) := by
    intro sK4 sK3
    conv => enter [1, 2]; rw [l25 sK3 sK4]
    conv => enter [1]; rw [l0 sK4 ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4)]
  have l39 : ∀ sK4 sK3 : G, ((sK4 ◇ sK4) ◇ ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4)) = (((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4) ◇ (sK4 ◇ sK4)) := by
    intro sK4 sK3
    conv => enter [1]; rw [l38 sK4 sK3]
    conv => enter [1]; rw [l19 sK4 ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4)]
  have l40 : ∀ sK4 sK3 : G, ((sK4 ◇ sK4) ◇ ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4)) = ((sK3 ◇ (sK4 ◇ sK4)) ◇ (sK4 ◇ (sK4 ◇ sK4))) := by
    intro sK4 sK3
    conv => enter [1]; rw [l39 sK4 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ (sK4 ◇ sK4)) sK4 (sK4 ◇ sK4)]
  have l41 : ∀ sK4 sK3 : G, ((sK4 ◇ sK4) ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4))) = ((sK4 ◇ sK4) ◇ ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4)) := by
    intro sK4 sK3
    conv => enter [1]; rw [← l5 sK3 sK4 (sK4 ◇ sK4)]
    conv => enter [1]; rw [← l40 sK4 sK3]
  have l42 : ∀ sK3 sK4 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4) = ((sK4 ◇ sK4) ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4))) := by
    intro sK3 sK4
    conv => enter [1]; rw [l36 sK3 sK4 sK4]
    conv => enter [1]; rw [← l41 sK4 sK3]
  have l43 : ∀ sK3 sK4 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4) = ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4)) := by
    intro sK3 sK4
    conv => enter [1]; rw [l42 sK3 sK4]
    conv => enter [1]; rw [l7 sK4 (sK4 ◇ sK4)]
  have l44 : ∀ sK4 sK3 : G, (sK4 ◇ (sK4 ◇ sK4)) = ((sK3 ◇ (sK4 ◇ sK4)) ◇ sK4) := by
    intro sK4 sK3
    conv => enter [1]; rw [l14 sK4]
    conv => enter [1]; rw [← l43 sK3 sK4]
  have l45 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK3 sK4
    conv => enter [1]; rw [l37 sK3 sK4]
    conv => enter [1]; rw [← l44 sK4 sK3]
  have l46 : ∀ X0 sK4 sK3 : G, (X0 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK3 ◇ (sK4 ◇ sK4))) := by
    intro X0 sK4 sK3
    conv => enter [1]; rw [l30 X0 sK4]
    conv => enter [1, 2]; rw [← l45 sK3 sK4]
  have l47 : ∀ X0 X1 sK4 : G, ((X0 ◇ X1) ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK4 ◇ (sK4 ◇ sK4)))) := by
    intro X0 X1 sK4
    conv => enter [1]; rw [← h4512 X0 X1 (sK4 ◇ sK4)]
    conv => enter [1, 2]; rw [l30 X1 sK4]
  have l48 : ∀ sK4 X0 X1 : G, ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4)) = ((X0 ◇ X1) ◇ (sK4 ◇ sK4)) := by
    intro sK4 X0 X1
    conv => enter [1]; rw [h54291 (sK4 ◇ sK4) sK4 X0 X1]
    conv => enter [1]; rw [← l47 X0 X1 sK4]
  have l49 : ∀ sK4 X0 X1 : G, ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK4 ◇ sK4))) := by
    intro sK4 X0 X1
    conv => enter [1]; rw [l48 sK4 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK4 ◇ sK4)]
  have l50 : ∀ sK4 X0 X1 : G, (sK4 ◇ ((sK4 ◇ sK4) ◇ sK4)) = (X0 ◇ (X1 ◇ (sK4 ◇ sK4))) := by
    intro sK4 X0 X1
    conv => enter [1]; rw [← l0 sK4 sK4]
    conv => enter [1]; rw [l49 sK4 X0 X1]
  have l51 : ∀ sK4 X0 X1 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK4 ◇ sK4))) := by
    intro sK4 X0 X1
    conv => enter [1]; rw [← l19 sK4 sK4]
    conv => enter [1]; rw [l50 sK4 X0 X1]
  have l52 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK4 ◇ sK4))) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l45 sK3 sK4]
    conv => enter [1]; rw [l51 sK4 X0 X1]
  have l53 : ∀ X0 X1 sK4 X2 sK3 : G, (X0 ◇ ((X1 ◇ (sK4 ◇ sK4)) ◇ X2)) = ((sK3 ◇ (sK4 ◇ sK4)) ◇ X2) := by
    intro X0 X1 sK4 X2 sK3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (sK4 ◇ sK4)) X2]
    conv => enter [1, 1]; rw [← l52 sK3 sK4 X0 X1]
  have l54 : ∀ sK3 sK4 X0 : G, (sK3 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK4 ◇ sK4)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l52 sK3 sK4 (sK4 ◇ sK4) X0]
    conv => enter [1]; rw [← l24 X0 sK4]
  have l55 : ∀ sK3 sK4 X2 X0 X1 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK4 ◇ sK4) ◇ X2))) := by
    intro sK3 sK4 X2 X0 X1
    conv => enter [1]; rw [← l53 X0 X1 sK4 X2 sK3]
    conv => enter [1, 2]; rw [← h4512 X1 (sK4 ◇ sK4) X2]
  have l56 : ∀ sK3 sK4 X2 : G, ((sK3 ◇ (sK4 ◇ sK4)) ◇ X2) = (X2 ◇ ((sK4 ◇ sK4) ◇ (sK4 ◇ sK4))) := by
    intro sK3 sK4 X2
    conv => enter [1]; rw [l55 sK3 sK4 X2 sK3 sK3]
    conv => enter [1]; rw [← h54291 X2 (sK4 ◇ sK4) sK3 sK3]
  have l57 : ∀ sK3 sK4 X2 : G, (sK3 ◇ (sK4 ◇ sK4)) = ((sK3 ◇ (sK4 ◇ sK4)) ◇ X2) := by
    intro sK3 sK4 X2
    conv => enter [1]; rw [l52 sK3 sK4 X2 (sK4 ◇ sK4)]
    conv => enter [1]; rw [← l56 sK3 sK4 X2]
  have l58 : ∀ X0 X1 sK3 sK4 : G, (X0 ◇ (X1 ◇ X1)) = ((sK3 ◇ (sK4 ◇ sK4)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK3 sK4
    conv => enter [1]; rw [h54291 X0 X1 sK3 (sK4 ◇ sK4)]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK4) (X1 ◇ X0)]
  have l59 : ∀ X0 X1 sK4 : G, (X0 ◇ (X1 ◇ X1)) = ((sK4 ◇ sK4) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK4
    conv => enter [1]; rw [h54291 X0 X1 sK4 sK4]
    conv => enter [1]; rw [h4512 sK4 sK4 (X1 ◇ X0)]
  have l60 : ∀ X0 X1 sK5 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [h54291 X0 X1 sK5 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (X1 ◇ X0)]
  have l61 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l57 sK3 sK4 (X1 ◇ X0)]
    conv => enter [1]; rw [← l58 X0 X1 sK3 sK4]
  have l62 : ∀ X0 X1 sK0 sK1 sK5 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1 sK5 sK2
    conv => enter [1]; rw [← h54291 sK1 sK0 X0 X1]
    conv => enter [1]; rw [l60 sK1 sK0 sK5 sK2 sK0 sK1]
  have l63 : ∀ sK0 sK3 sK4 sK1 X0 : G, (sK0 ◇ (sK3 ◇ (sK4 ◇ sK4))) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK3 sK4 sK1 X0
    conv => enter [1, 2]; rw [l61 sK3 sK4 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l64 : ∀ sK0 sK3 sK4 X0 sK1 : G, (sK0 ◇ (sK3 ◇ (sK4 ◇ sK4))) = ((sK4 ◇ sK4) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK3 sK4 X0 sK1
    conv => enter [1]; rw [l63 sK0 sK3 sK4 sK1 X0]
    conv => enter [1]; rw [l59 (sK0 ◇ sK1) X0 sK4]
  have l65 : ∀ sK0 sK3 sK4 sK5 sK2 sK1 : G, (sK0 ◇ (sK3 ◇ (sK4 ◇ sK4))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK3 sK4 sK5 sK2 sK1
    conv => enter [1]; rw [l64 sK0 sK3 sK4 sK0 sK1]
    conv => enter [1]; rw [l62 (sK4 ◇ sK4) sK0 sK0 sK1 sK5 sK2]
  have l66 : ∀ sK0 sK4 sK5 sK2 sK1 : G, (sK0 ◇ (sK4 ◇ sK4)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK4 sK5 sK2 sK1
    conv => enter [1]; rw [l46 sK0 sK4 sK0]
    conv => enter [1]; rw [l65 sK0 sK0 sK4 sK5 sK2 sK1]
  have l67 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK4)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l54 sK3 sK4 sK0]
    conv => enter [1]; rw [l66 sK0 sK4 sK5 sK2 sK1]
  have l68 : ∀ sK3 sK4 X0 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 X0 sK2 sK0 sK1
    conv => enter [1]; rw [l67 sK3 sK4 sK3 sK2 sK0 sK1]
    conv => enter [1]; rw [← l62 X0 sK2 sK0 sK1 sK3 sK2]
  intro x y z w u v
  conv => enter [1]; rw [l68 x y z w u v]

@[equational_result]
theorem Equation54311_implies_Equation54291 (G : Type*) [Magma G] (h54311 : Equation54311 G) : Equation54291 G := by
  have l0 : ∀ X0 sK2 X5 : G, (X0 ◇ (sK2 ◇ sK2)) = (X5 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X5
    conv => enter [1]; rw [h54311 X0 sK2 X0 X0 X0 X0]
    conv => enter [1]; rw [← h54311 X5 sK2 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [h54311 sK1 sK2 X1 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_54236_implies_Equation54227 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54236 : Equation54236 G) : Equation54227 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h54236 X1 (X2 ◇ X2) X3]
    conv => enter [1, 2, 2]; rw [h54236 X1 X2 X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54236 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [← l0 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X2 (X2 ◇ X2)]
  have l3 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [l2 X3 X1 X0 X2]
    conv => enter [1]; rw [← l1 X2 X2 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54236 X0 X1 X0]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l1 X2 X3 X0 X1]
    conv => enter [1]; rw [l4 X2 X3 X4]
    conv => enter [1, 2]; rw [l1 X2 X3 X0 X1]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l5 X1 X0 X1 X2 X1]
    conv => enter [1]; rw [l3 X1 X1 X0 X2]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0 X0]
    conv => enter [1]; rw [← l1 X1 X0 X1 X0]
  intro x y z
  conv => enter [1]; rw [← l7 y x]
  conv => enter [1]; rw [l7 y z]
  conv => enter [1]; rw [h54236 z y y]

theorem Equation4512_54227_implies_Equation54236 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54227 : Equation54227 G) : Equation54236 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54227 X0 X1 X0]
    conv => enter [1]; rw [← h54227 X2 X1 X0]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
  intro x y z
  conv => enter [1]; rw [h54227 x y x]
  conv => enter [1]; rw [l4 y x y z]

theorem Equation4512_54236_implies_Equation54302 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54236 : Equation54236 G) : Equation54302 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54236 X1 X2 X0]
    conv => enter [1]; rw [h54236 X1 X2 X3]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h54236 X1 (X2 ◇ X2) X3]
    conv => enter [1, 2, 2]; rw [h54236 X1 X2 X0]
  have l2 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h4512 X2 (X0 ◇ (X0 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h54236 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54236 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l2 X2 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l5 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [← l1 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X2 (X2 ◇ X2)]
  have l6 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l4 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l7 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [l5 X3 X1 X0 X2]
    conv => enter [1]; rw [← l3 X2 X2 X1 X2]
  have l8 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l6 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l9 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l8 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l10 : ∀ X2 X3 X0 X1 X4 : G, (X2 ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X4)) = ((X0 ◇ (X1 ◇ X1)) ◇ X4) := by
    intro X2 X3 X0 X1 X4
    conv => enter [1]; rw [h4512 X2 (X3 ◇ (X0 ◇ (X0 ◇ X1))) X4]
    conv => enter [1, 1]; rw [← l3 X0 X1 X2 X3]
  have l11 : ∀ X2 X3 X0 X1 X4 : G, (X2 ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X4)) = (X0 ◇ ((X1 ◇ X1) ◇ X4)) := by
    intro X2 X3 X0 X1 X4
    conv => enter [1]; rw [l10 X2 X3 X0 X1 X4]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X4]
  have l12 : ∀ X2 X3 X0 X1 X4 : G, (X2 ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X4)) = (X0 ◇ (X1 ◇ (X1 ◇ X4))) := by
    intro X2 X3 X0 X1 X4
    conv => enter [1]; rw [l11 X2 X3 X0 X1 X4]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X4]
  have l13 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X4))) = (X2 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l12 X2 X3 X0 X1 X4]
    conv => enter [1, 2]; rw [← h4512 X3 (X0 ◇ (X0 ◇ X1)) X4]
  have l14 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X4))) = (X2 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l13 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X4]
  have l15 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X4))) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X4))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l14 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X4]
  have l16 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l7 X3 X1 X1 X2]
    conv => enter [1, 2]; rw [l0 X1 X1 (X1 ◇ X2) X0]
  have l17 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3))))) = (X4 ◇ (X5 ◇ (X6 ◇ (X5 ◇ (X5 ◇ X3))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
    conv => enter [1]; rw [← l7 X4 X5 X6 X3]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1 X1 X0]
    conv => enter [1]; rw [← h54236 X1 (X1 ◇ (X1 ◇ X0)) X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [← l3 X1 X0 X1 (X1 ◇ (X1 ◇ X0))]
  have l20 : ∀ X2 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X2 X1
    conv => enter [1]; rw [l16 X2 X2 X2 X1]
    conv => enter [1]; rw [← l15 X1 X1 X2 X2 X2]
  have l21 : ∀ X3 X1 X2 X4 X0 : G, (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X3 X1 X2 X4 X0
    conv => enter [1]; rw [l9 X3 X1 (X1 ◇ X2) X4]
    conv => enter [1, 2, 2]; rw [l0 X3 X1 X2 X0]
  have l22 : ∀ X1 X2 X4 X3 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X1 X2 X4 X3 X0
    conv => enter [1]; rw [l9 X1 X1 X2 X3]
    conv => enter [1]; rw [l21 X3 X1 X2 X4 X0]
  have l23 : ∀ X4 X5 X6 X3 X1 : G, (X4 ◇ (X5 ◇ (X6 ◇ (X5 ◇ (X5 ◇ X3))))) = (X1 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X4 X5 X6 X3 X1
    conv => enter [1]; rw [l17 X4 X5 X6 X3 X4 X1 X4]
    conv => enter [1]; rw [← l22 X1 X3 X4 X1 X4]
  have l24 : ∀ X1 X3 X5 : G, (X1 ◇ (X1 ◇ (X1 ◇ X3))) = (X5 ◇ (X5 ◇ (X5 ◇ X3))) := by
    intro X1 X3 X5
    conv => enter [1]; rw [l22 X1 X3 X1 X1 X1]
    conv => enter [1]; rw [l23 X1 X1 X1 X3 X5]
  have l25 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l19 X1 X0]
    conv => enter [1]; rw [l19 X1 X2]
  intro x y z w
  conv => enter [1]; rw [h54236 x y (x ◇ x)]
  conv => enter [1]; rw [← h4512 x x (x ◇ (x ◇ y))]
  conv => enter [1]; rw [← l9 x x y x]
  conv => enter [1]; rw [← l20 y x]
  conv => enter [1]; rw [l25 y y w]
  conv => enter [1]; rw [h54236 w y z]

theorem Equation4512_54302_implies_Equation54236 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54302 : Equation54302 G) : Equation54236 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54302 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X1)]
  have l5 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l4 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 X1]
  have l6 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l5 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [h54302 sK0 sK1 X1 sK0]
  have l7 : ∀ X1 sK1 X2 sK0 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X1 sK1 X2 sK0 X0
    conv => enter [1]; rw [h54302 X1 sK1 X2 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l6 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK0 sK1 X0 X1]
  have l12 : ∀ sK0 sK1 X2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (X2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X2 X0
    conv => enter [1]; rw [← l5 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1 X2 sK0 X0]
  have l13 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 X2 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (X2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X2 sK2
    conv => enter [1]; rw [l12 sK0 sK1 X2 sK0]
    conv => enter [1, 2]; rw [← l11 sK2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l15 : ∀ sK2 sK0 sK1 X2 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l14 sK0 sK1 X2 sK2]
  have l16 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l18 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l13 sK2 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2]
  have l19 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l16 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l20 : ∀ X0 sK1 X1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK1 X1 sK0 sK2
    conv => enter [1]; rw [h54302 X0 (sK1 ◇ sK1) X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l18 sK2 sK0 sK1]
  have l21 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l20 X0 sK1 X0 sK0 sK2]
    conv => enter [1]; rw [← l19 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l22 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l15 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l21 X0 sK1 sK2 sK0]
  have l23 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l22 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK2 (sK1 ◇ sK1) sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54302 X0 sK1 (sK0 ◇ sK1) sK1]
  have l25 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l23 sK2 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [← l25 z x y x]

theorem Equation4512_54236_implies_Equation54278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54236 : Equation54236 G) : Equation54278 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h54236 X1 (X2 ◇ X2) X3]
    conv => enter [1, 2, 2]; rw [h54236 X1 X2 X0]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h4512 X2 (X0 ◇ (X0 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h54236 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54236 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X0 ◇ X1))]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l1 X2 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l4 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [← l0 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X2 (X2 ◇ X2)]
  have l5 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l3 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l6 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [l4 X3 X1 X0 X2]
    conv => enter [1]; rw [← l2 X2 X2 X1 X2]
  have l7 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l5 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l8 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l7 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54236 X0 X1 X0]
  have l10 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l2 X2 X3 X0 X1]
    conv => enter [1]; rw [l9 X2 X3 X4]
    conv => enter [1, 2]; rw [l2 X2 X3 X0 X1]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l10 X1 X0 X1 X2 X1]
    conv => enter [1]; rw [l6 X1 X1 X0 X2]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X1 X0 X0]
    conv => enter [1]; rw [← l2 X1 X0 X1 X0]
  intro x y z
  conv => enter [1]; rw [← l12 y x]
  conv => enter [1]; rw [← l11 z z y]
  conv => enter [1]; rw [← l8 z z y z]

theorem Equation4512_54278_implies_Equation54236 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54278 : Equation54278 G) : Equation54236 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54278 X0 X1 X0]
    conv => enter [1]; rw [h54278 X0 X1 X2]
  have l1 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [h4512 X2 (X1 ◇ X1) X3]
    conv => enter [1, 1]; rw [h54278 X2 X1 X0]
  have l2 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l1 X2 X1 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X3]
  have l3 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l2 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l4 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l3 X2 X1 X3 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3)))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l6 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ (X3 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X2 X1]
    conv => enter [1]; rw [← l5 X0 X1 X2 X1]
  intro x y z
  conv => enter [1]; rw [h54278 x y x]
  conv => enter [1]; rw [l6 x y x x]
  conv => enter [1]; rw [l5 x x y z]

theorem Equation4512_54241_implies_Equation54249 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation54249 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54241 X2 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h54241 X0 X1 X2]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54241 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54241 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l1 sK1 sK2]
  have l5 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54241 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54241 (X1 ◇ X2) X3 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X3)]
  have l7 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
    conv => enter [1, 1]; rw [← h54241 X0 X1 X2]
  have l8 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ sK2)) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (X0 ◇ sK2)]
    conv => enter [1]; rw [← h54241 sK2 X0 sK2]
  have l9 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l7 X2 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l10 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l6 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l11 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l5 sK2 X0]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l8 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l3 sK1 sK2 X0]
  have l14 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l15 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l9 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l16 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l11 sK2 X0]
  have l17 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l10 X2 X0 X1 X1]
    conv => enter [1]; rw [← l14 X2 X0 X1]
  have l18 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l15 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l19 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l18 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X3]
  have l20 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l16 sK2 sK2]
    conv => enter [1]; rw [← l0 sK2 sK2]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l20 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l22 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [l21 sK1 sK2]
  have l23 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l0 sK2 ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l12 sK1 sK2]
  have l24 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l12 sK1 sK2]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [h54241 sK2 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l12 sK1 sK2]
  have l26 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [l24 sK2 sK1]
  have l27 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l17 sK2 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l23 sK2 sK1]
  have l28 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l27 sK2 sK1]
    conv => enter [1]; rw [l26 sK2 sK1]
  have l29 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h54241 (sK2 ◇ sK2) sK2 sK2]
    conv => enter [1]; rw [l28 sK2 sK1]
  have l30 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l20 sK2]
    conv => enter [1]; rw [l29 sK2 sK1]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1, 2]; rw [← l25 sK1 sK2]
  have l32 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [h54241 X0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l25 sK1 sK2]
  have l33 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l34 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54241 X0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l31 sK1 sK2]
  have l35 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l34 X0 sK2 sK1]
    conv => enter [1]; rw [← l32 X0 sK1 sK2]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [← l30 sK2 sK1]
  have l37 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1, 2]; rw [← l36 sK1 sK2]
  have l38 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l35 sK1 sK2 sK1]
    conv => enter [1]; rw [← l37 sK1 sK2]
  have l39 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l13 sK1 sK2 (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
    conv => enter [1, 2]; rw [← h54241 X0 X1 (sK1 ◇ (sK2 ◇ sK2))]
  have l40 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l39 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (X0 ◇ (X1 ◇ X1))]
  have l41 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l40 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK1 ◇ (sK2 ◇ sK2)) (X0 ◇ (X1 ◇ X1))]
  have l42 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ X1)))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l41 sK1 sK2 sK1 X1]
    conv => enter [1]; rw [← l19 X1 (sK1 ◇ (sK2 ◇ sK2)) (X1 ◇ X1) sK1]
  have l43 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ X1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l42 sK1 sK2 X1]
    conv => enter [1]; rw [← l10 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2)) X1 X1]
  have l44 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l43 sK1 sK2 X1]
    conv => enter [1]; rw [← l33 sK1 sK2 (X1 ◇ X1)]
  have l45 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [l44 sK1 sK2 X1]
  have l46 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l38 sK1 sK2]
    conv => enter [1]; rw [l45 sK1 sK2 X1]
  have l47 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l46 sK1 sK2 X0]
    conv => enter [1]; rw [h54241 (sK1 ◇ (sK2 ◇ sK2)) X0 X0]
    conv => enter [1, 2]; rw [← l46 sK1 sK2 X0]
  have l48 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l47 sK1 sK2 X0]
    conv => enter [1]; rw [← l35 X0 sK2 sK1]
  have l49 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h54241 X0 X1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l47 sK1 sK2 X1]
  have l50 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l49 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l32 X0 sK1 sK2]
  have l51 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l50 X0 X1 X0 sK2]
    conv => enter [1]; rw [← l35 X0 sK2 X0]
  have l52 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l51 X0 X1 sK2]
    conv => enter [1]; rw [l48 X0 sK2 sK1]
  have l53 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l52 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [h54241 sK1 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l53 x y z w]

@[equational_result]
theorem Equation54249_implies_Equation54241 (G : Type*) [Magma G] (h54249 : Equation54249 G) : Equation54241 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h54249 X0 X1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← h54249 X0 sK1 (sK1 ◇ sK1) X0]
  have l1 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [h54249 X0 X1 X2 X2]
    conv => enter [1, 2]; rw [l0 X0 X2 sK1]
  have l2 : ∀ X0 sK1 X2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X2
    conv => enter [1]; rw [l0 X0 sK1 X0]
    conv => enter [1]; rw [l1 X0 X0 X2 sK1]
  have l3 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h54249 sK0 sK2 sK2 sK1]
    conv => enter [1]; rw [h54249 sK0 sK2 sK1 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← l3 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_54241_implies_Equation54254 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation54254 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54241 X2 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h54241 X0 X1 X2]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54241 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54241 (X1 ◇ X2) X3 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X3)]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54241 sK1 X0 sK1]
  have l7 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l5 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 X0]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l7 X2 X0 X1 X1]
    conv => enter [1]; rw [← l10 X2 X0 X1]
  have l13 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1 sK1]
    conv => enter [1]; rw [← l0 sK1 sK1]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h54241 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l12 sK1 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54241 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [l20 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
  have l23 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h54241 X0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l16 sK0 sK1]
  have l24 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54241 X0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l22 sK0 sK1]
  have l25 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l24 X0 sK1 sK0]
    conv => enter [1]; rw [← l23 X0 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l21 sK1 sK0]
  have l27 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54241 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l26 sK0 sK1]
  have l28 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l27 X0 sK1 X0]
    conv => enter [1, 2]; rw [← l25 X0 sK1 X0]
  have l29 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h54241 X0 sK1 sK1]
  have l30 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l28 X0 sK1]
    conv => enter [1]; rw [← l29 sK1 X0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [h54241 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l31 x y z]

theorem Equation4512_54254_implies_Equation54241 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54254 : Equation54254 G) : Equation54241 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 sK2]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l1 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54254 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l8 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54254 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l9 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54254 sK2 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l3 sK1 sK2 X0]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = (X2 ◇ (X3 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54254 (X2 ◇ X3) X1 X0]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X1)]
  have l11 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h4512 X2 (X1 ◇ (X0 ◇ X2)) X3]
    conv => enter [1, 1]; rw [← h54254 X0 X1 X2]
  have l12 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h54254 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54254 X0 sK2 sK1]
  have l14 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54254 X0 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l3 sK1 sK2 (X0 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l11 X2 X1 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l16 : ∀ X2 X3 X1 X0 : G, (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X2 X3 X1 X0
    conv => enter [1]; rw [← l10 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X0]
  have l17 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK1 sK2]
    conv => enter [1]; rw [← h54254 (sK1 ◇ sK2) sK1 sK2]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 X0]
  have l19 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l15 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l13 sK1 sK2 sK1]
    conv => enter [1]; rw [← l17 sK2 sK1]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l18 sK1 X0]
  have l22 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l19 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l23 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l20 sK1 sK2]
  have l24 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l22 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 X3]
  have l25 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l12 X0 sK1]
    conv => enter [1]; rw [← h54254 X0 (sK1 ◇ sK1) sK1]
  have l26 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (X1 ◇ X1)) = ((X0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h54254 (sK1 ◇ sK1) X1 (X0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l12 X0 sK1]
  have l27 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ sK1) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (X0 ◇ sK1) X1]
    conv => enter [1, 1]; rw [← l12 X0 sK1]
  have l28 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ sK1) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l27 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l29 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l26 sK1 X1 X0]
    conv => enter [1]; rw [← h4512 X0 sK1 (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
  have l30 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l28 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l31 : ∀ sK1 X1 : G, ((sK1 ◇ sK1) ◇ (X1 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X1
    conv => enter [1]; rw [l29 sK1 X1 sK1]
    conv => enter [1]; rw [← l24 X1 sK1 (sK1 ◇ sK1) sK1]
  have l32 : ∀ sK1 X1 : G, ((sK1 ◇ sK1) ◇ (X1 ◇ X1)) = (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l31 sK1 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l33 : ∀ sK1 X1 : G, ((sK1 ◇ sK1) ◇ (X1 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l32 sK1 X1]
    conv => enter [1, 2]; rw [← l12 sK1 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l34 sK0 sK1]
  have l36 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54254 (sK1 ◇ sK2) X0 X0]
    conv => enter [1, 2]; rw [← l8 sK2 sK1 X0]
  have l37 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [h4512 X0 ((sK1 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l8 sK2 sK1 X0]
  have l38 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = (sK2 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l37 X0 sK1 sK2 X1]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) X1]
  have l39 : ∀ sK2 sK1 X1 X0 : G, (sK2 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [← l38 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 X1]
  have l40 : ∀ X0 sK1 X1 : G, (X0 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h4512 X0 ((sK1 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l21 sK1 X0]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l42 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l21 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK1 ◇ sK1) ◇ sK2)]
  have l43 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l8 sK2 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l21 sK1 (sK1 ◇ sK2)]
  have l44 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l43 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK1))]
  have l45 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l42 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK2]
  have l46 : ∀ X0 sK1 X1 : G, (X0 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l40 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X1]
  have l47 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l44 sK2 sK1]
    conv => enter [1]; rw [← l30 (sK1 ◇ sK2) sK1 (sK1 ◇ sK1)]
  have l48 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l45 sK1 sK2]
  have l49 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l46 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l50 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l47 sK2 sK1]
    conv => enter [1]; rw [l36 sK1 sK2 (sK1 ◇ sK1)]
  have l51 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK1]
    conv => enter [1]; rw [l48 sK1 sK2]
  have l52 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l50 sK2 sK1]
    conv => enter [1]; rw [l3 sK1 sK2 (sK1 ◇ sK1)]
  have l53 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l54 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l53 sK1 X0 sK0]
  have l55 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l8 sK2 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l51 sK1 sK2]
  have l56 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l51 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l57 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l51 sK1 sK2]
    conv => enter [1]; rw [← h54254 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l58 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h54254 sK1 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l57 sK1 sK2]
  have l59 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l56 sK0 sK1 sK2]
  have l60 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l55 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK1))]
  have l61 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l58 sK1 sK2]
    conv => enter [1]; rw [← l33 sK1 (sK1 ◇ sK2)]
  have l62 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2 sK1]
    conv => enter [1]; rw [← l60 sK2 sK1]
  have l63 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l52 sK2 sK1]
    conv => enter [1]; rw [l61 sK1 sK2]
  have l64 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l62 sK1 sK2]
  have l65 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54254 X0 sK0 X0]
    conv => enter [1, 2]; rw [h54254 sK0 X0 (sK1 ◇ sK1)]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54254 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l67 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54254 X0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54254 sK0 X0 (sK1 ◇ sK1)]
  have l68 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro X0 sK1
    conv => enter [1]; rw [l67 X0 sK1 X0]
    conv => enter [1]; rw [← l54 sK1 (X0 ◇ X0) X0]
  have l69 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l49 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l65 X0 sK0 sK1]
  have l70 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK1]
    conv => enter [1]; rw [l68 X0 sK1]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l72 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54254 (sK1 ◇ sK1) sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l66 sK0 sK1]
  have l73 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l72 sK1 sK0]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54254 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l71 sK1 sK0]
  have l75 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK1]
    conv => enter [1]; rw [l73 sK1 sK0]
  have l76 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l74 sK0 sK1]
  have l77 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [← l64 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK2 X0]
  have l78 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l77 sK2 sK1 X0]
  have l79 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l76 sK0 sK1]
  have l80 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l79 sK0 sK1]
  have l81 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [l79 sK0 sK1]
  have l82 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l81 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l83 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l84 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l83 sK0 sK1]
  have l85 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l84 sK0 sK1]
    conv => enter [1]; rw [l76 sK0 sK1]
  have l86 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 2, 2]; rw [l84 sK0 sK1]
    conv => enter [1]; rw [← h54254 (sK0 ◇ (sK1 ◇ sK1)) X0 (sK1 ◇ sK1)]
  have l87 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l85 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l88 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l85 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l89 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l85 sK0 sK1]
    conv => enter [1]; rw [l87 sK1 sK0]
  have l90 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l89 sK0 sK1]
  have l91 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l89 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l92 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l75 sK1 sK0]
    conv => enter [1]; rw [l90 sK0 sK1]
  have l93 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l92 sK1 sK0]
    conv => enter [1]; rw [← h54254 sK0 sK0 (sK1 ◇ sK1)]
  have l94 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l92 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l95 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l94 sK1 X0 sK0]
  have l96 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l93 sK1 sK0]
    conv => enter [1]; rw [← l69 sK1 sK0 sK0]
  have l97 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l96 sK1 sK0]
  have l98 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l97 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l99 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l98 sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 sK1]
  have l100 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l99 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l101 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l100 sK0 sK1]
    conv => enter [1]; rw [← l12 sK1 sK1]
  have l102 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l52 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))]
  have l103 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l8 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l102 sK1 sK2]
  have l104 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l103 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK1)]
  have l105 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l23 sK1 sK2]
    conv => enter [1, 2]; rw [← l100 sK0 sK1]
  have l106 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l64 sK1 sK2]
    conv => enter [1]; rw [l105 sK1 sK2 sK0]
  have l107 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l106 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK1))]
  have l108 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l107 sK1 sK2 sK0]
  have l109 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l104 sK2 sK1]
    conv => enter [1]; rw [l108 sK1 sK2 sK0]
  have l110 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54254 sK0 (sK1 ◇ sK2) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l109 sK2 sK1 sK0]
  have l111 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l110 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK1 sK2 (sK1 ◇ sK1)]
  have l112 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l111 sK0 sK1 sK2]
    conv => enter [1]; rw [← l52 sK2 sK1]
  have l113 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l112 sK0 sK1 sK2]
  have l114 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54254 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l113 sK0 sK1 sK2]
  have l115 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54254 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l59 sK0 sK1 sK2]
  have l116 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l115 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1))]
  have l117 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l116 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l16 X0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK2) sK1]
  have l118 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l117 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l86 sK1 (sK1 ◇ sK2) sK0]
  have l119 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l118 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h54254 sK0 (sK1 ◇ sK2) (sK1 ◇ sK1)]
  have l120 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l119 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l121 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1, 2]; rw [← l113 sK0 sK1 sK2]
    conv => enter [1]; rw [← l120 sK0 sK1 sK2 X0]
  have l122 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l21 sK1 ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l63 sK2 sK1]
  have l123 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l122 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) (sK2 ◇ (sK1 ◇ sK1))]
  have l124 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l123 sK1 sK2]
    conv => enter [1]; rw [← l114 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l125 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l124 sK1 sK1 sK2]
    conv => enter [1]; rw [← l121 (sK1 ◇ sK2) sK2 sK1 sK1]
  have l126 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l125 sK1 sK2]
    conv => enter [1]; rw [← l78 sK2 sK1 (sK1 ◇ sK1)]
  have l127 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l126 sK1 sK2]
    conv => enter [1]; rw [← l25 sK1 sK2]
  have l128 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l127 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK1)]
  have l129 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l101 sK0 sK1]
    conv => enter [1]; rw [l128 sK1 sK2]
  have l130 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l129 sK0 sK1 sK2]
    conv => enter [1]; rw [← l104 sK2 sK1]
  have l131 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l130 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) X0]
  have l132 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54254 X0 sK0 X0]
    conv => enter [1, 2]; rw [h54254 sK0 X0 (sK1 ◇ sK2)]
  have l133 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l132 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l39 sK2 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l134 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l133 X0 sK0 sK2 sK1]
    conv => enter [1]; rw [← l131 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2)) sK2]
  have l135 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h54254 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l134 X0 sK0 sK1 sK2]
  have l136 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← l134 (X0 ◇ X1) sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l137 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l134 sK1 sK0 sK1 sK2]
  have l138 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l91 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l137 sK1 sK0 sK2]
  have l139 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l136 sK0 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [l134 sK0 sK0 sK1 sK2]
  have l140 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l135 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l141 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [← l138 sK0 sK1 sK2]
  have l142 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l140 X0 X1 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l139 sK0 sK1 sK2 X1]
  have l143 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l141 sK0 sK1 sK2]
  have l144 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l142 X0 X1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l95 sK1 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l145 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l79 sK0 sK1]
    conv => enter [1]; rw [l143 sK0 sK1 sK2]
  have l146 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l144 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l147 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l85 sK0 sK1]
    conv => enter [1]; rw [l145 sK1 sK0 sK2]
  have l148 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [l146 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [l82 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l149 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l148 X0 X1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l88 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l150 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l149 X0 X1 sK0 sK1 X0]
    conv => enter [1]; rw [← l147 sK0 sK1 X0]
  have l151 : ∀ X2 X1 X0 sK0 sK1 : G, (X2 ◇ (X1 ◇ (X0 ◇ X2))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X2 X1 X0 sK0 sK1
    conv => enter [1]; rw [← h54254 X0 X1 X2]
    conv => enter [1]; rw [l150 X0 X1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l151 z x y x y]

end Semigroup5
