import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54483_implies_Equation54398 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54483 : Equation54483 G) : Equation54398 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK1]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l4 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l5 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 sK2]
  have l6 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h54483 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h54483 (sK1 ◇ sK2) sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l8 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h54483 (sK2 ◇ sK1) sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l9 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54483 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK2]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ X0)) = (X0 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54483 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 sK1]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54483 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ X0))]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X0)]
    conv => enter [1]; rw [← h54483 X0 (sK1 ◇ sK2) sK0]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54483 X0 sK2 sK1]
  have l14 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X0)))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l2 sK1 sK2 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54483 X0 X1 sK1]
  have l15 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X0))) = (sK2 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54483 X0 X1 sK1]
  have l16 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54483 X0 sK1 sK2]
  have l17 : ∀ sK2 sK1 X1 X0 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ (X1 ◇ (X0 ◇ X0)))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [← l3 sK2 sK1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54483 X0 X1 sK2]
  have l18 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ (X1 ◇ (X0 ◇ X0))) = (sK1 ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54483 X0 X1 sK2]
  have l19 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ X0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l2 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54483 X0 sK1 (sK1 ◇ sK2)]
  have l20 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X0))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l3 sK2 sK1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54483 X0 sK2 (sK2 ◇ sK1)]
  have l21 : ∀ sK0 sK2 sK1 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ X0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54483 X0 X1 (sK2 ◇ sK1)]
  have l22 : ∀ sK0 X0 X1 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 X0 X1 sK2 sK1
    conv => enter [1]; rw [← l21 sK0 sK2 sK1 X1 X0]
    conv => enter [1]; rw [← h54483 X0 X1 (sK0 ◇ (sK2 ◇ sK1))]
  have l23 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54483 X0 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [l20 sK2 sK1 X0]
  have l24 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54483 X0 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l19 sK1 sK2 X0]
  have l25 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ (X1 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [← l18 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← h54483 X0 X1 (sK1 ◇ sK2)]
  have l26 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l17 sK2 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h54483 X0 X1 (sK1 ◇ sK2)]
  have l27 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ (X0 ◇ (X1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [← l15 sK2 sK1 X1 X0]
    conv => enter [1]; rw [← h54483 X0 X1 (sK2 ◇ sK1)]
  have l28 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l14 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h54483 X0 X1 (sK2 ◇ sK1)]
  have l29 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h54483 X0 X1 X3]
  have l30 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [l10 sK1 sK2 X0]
  have l31 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [l9 sK2 sK1 X0]
  have l32 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (X3 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l6 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h54483 X2 X1 X0]
  have l33 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ X3))) = (X3 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l32 X2 X0 X1 X3]
  have l34 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l16 sK2 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 sK1 sK2]
  have l35 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l16 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
  have l36 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [h54483 X0 (sK2 ◇ sK1) X1]
    conv => enter [1, 2]; rw [l16 sK2 sK1 X0]
  have l37 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l34 sK2 sK1]
    conv => enter [1]; rw [l23 sK2 sK1 sK2]
  have l38 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l13 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
  have l39 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [l13 sK1 sK2 X0]
  have l40 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [h54483 X0 (sK1 ◇ sK2) X1]
    conv => enter [1, 2]; rw [l13 sK1 sK2 X0]
  have l41 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l38 sK1 sK2]
    conv => enter [1]; rw [l24 sK1 sK2 sK1]
  have l42 : ∀ sK2 sK1 : G, (((sK2 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l13 sK1 sK2 ((sK2 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [← l30 sK1 sK2 ((sK2 ◇ sK1) ◇ sK1)]
  have l43 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l30 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK2 ◇ sK1) ◇ sK1)]
  have l44 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) sK1]
  have l45 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 sK1 sK2 ((sK2 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [← l30 sK1 sK2 sK1]
  have l46 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l30 sK1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ sK1)]
  have l47 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l3 sK2 sK1 ((sK2 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [← l30 sK1 sK2 sK2]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l30 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK2 ◇ sK1) ◇ sK1)]
  have l49 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l48 sK0 sK1 sK2]
    conv => enter [1]; rw [l24 (sK0 ◇ (sK1 ◇ sK2)) sK2 sK1]
  have l50 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l47 sK2 sK1]
    conv => enter [1]; rw [l23 (sK2 ◇ sK1) sK1 sK2]
  have l51 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l46 sK2 sK1]
    conv => enter [1]; rw [l24 (sK2 ◇ sK1) sK2 sK1]
  have l52 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l45 sK1 sK2]
    conv => enter [1]; rw [l40 (sK1 ◇ sK2) sK1 sK2 sK1]
  have l53 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l43 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [l24 X1 sK2 sK1]
  have l54 : ∀ sK2 sK1 : G, (((sK2 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l42 sK2 sK1]
    conv => enter [1]; rw [l28 sK1 sK2 (sK1 ◇ sK2) (sK2 ◇ sK1)]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 sK1 sK2]
    conv => enter [1]; rw [← l36 sK1 sK2 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l56 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ sK1))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l50 sK2 sK1]
    conv => enter [1]; rw [l3 sK2 sK1 (sK2 ◇ sK1)]
  have l57 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l51 sK2 sK1]
    conv => enter [1]; rw [← l36 sK1 sK2 sK1 (sK2 ◇ sK1)]
  have l58 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l52 sK1 sK2]
    conv => enter [1]; rw [l33 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1) sK1]
  have l59 : ∀ sK2 sK1 : G, (((sK2 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l54 sK2 sK1]
    conv => enter [1]; rw [← h54483 (sK2 ◇ sK1) (sK1 ◇ sK2) sK1]
  have l60 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
  have l61 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l27 sK2 (sK1 ◇ sK2) (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l56 sK2 sK1]
  have l62 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l40 sK2 sK1 sK2 sK1]
    conv => enter [1]; rw [l57 sK2 sK1]
  have l63 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l58 sK1 sK2]
    conv => enter [1]; rw [← h54483 (sK2 ◇ sK1) sK1 sK1]
  have l64 : ∀ sK2 sK1 : G, (((sK2 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l59 sK2 sK1]
    conv => enter [1]; rw [l40 (sK2 ◇ sK1) sK1 sK2 sK1]
  have l65 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l13 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l61 sK1 sK2]
  have l66 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l62 sK1 sK2]
  have l67 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l16 sK2 sK1 sK1]
    conv => enter [1]; rw [← l63 sK1 sK2]
  have l68 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l64 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) sK1 (sK2 ◇ sK1)]
  have l69 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l40 sK1 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l68 sK1 sK2]
  have l70 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l66 sK1 sK2]
    conv => enter [1]; rw [← l69 sK1 sK2]
  have l71 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l67 sK1 sK2]
    conv => enter [1]; rw [← l70 sK1 sK2]
  have l72 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [← l44 sK1 sK2 sK0]
  have l73 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l44 sK1 sK2 sK0]
  have l74 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l72 sK2 sK1 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2 (sK2 ◇ sK1)]
  have l75 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l39 sK0 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l74 sK2 sK1 sK0]
  have l76 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1]; rw [l75 sK0 sK2 sK1]
  have l77 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l71 sK1 sK2]
  have l78 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l71 sK1 sK2]
  have l79 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l78 sK1 sK2 X0]
  have l80 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l77 sK0 sK1 sK2]
    conv => enter [1]; rw [← l36 sK1 sK2 sK1 sK0]
  have l81 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l13 sK1 sK2 ((sK1 ◇ sK2) ◇ sK2)]
    conv => enter [1, 2]; rw [← l31 sK2 sK1 ((sK1 ◇ sK2) ◇ sK2)]
  have l82 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l16 sK2 sK1 ((sK1 ◇ sK2) ◇ sK2)]
    conv => enter [1, 2]; rw [← l31 sK2 sK1 ((sK1 ◇ sK2) ◇ sK2)]
  have l83 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l31 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK2]
  have l84 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l31 sK2 sK1 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 ((sK1 ◇ sK2) ◇ sK2)]
  have l85 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l3 sK2 sK1 ((sK1 ◇ sK2) ◇ sK2)]
    conv => enter [1, 2]; rw [← l31 sK2 sK1 sK2]
  have l86 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l31 sK2 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK1 ◇ sK2) ◇ sK2)]
  have l87 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l31 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) ((sK1 ◇ sK2) ◇ sK2)]
  have l88 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l31 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) ((sK1 ◇ sK2) ◇ sK2)]
  have l89 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l88 sK1 sK2 sK0]
    conv => enter [1]; rw [l23 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK1 sK2]
  have l90 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l87 sK0 sK2 sK1]
    conv => enter [1]; rw [l23 (sK0 ◇ (sK2 ◇ sK1)) sK1 sK2]
  have l91 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l86 sK1 sK2]
    conv => enter [1]; rw [l23 (sK1 ◇ sK2) sK1 sK2]
  have l92 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l85 sK2 sK1]
    conv => enter [1]; rw [l36 (sK2 ◇ sK1) sK2 sK1 sK2]
  have l93 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l84 sK2 sK1]
    conv => enter [1]; rw [l23 (sK2 ◇ sK1) sK1 sK2]
  have l94 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l82 sK1 sK2]
    conv => enter [1]; rw [l26 sK2 sK1 (sK2 ◇ sK1) (sK1 ◇ sK2)]
  have l95 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l81 sK1 sK2]
    conv => enter [1]; rw [← l79 sK1 sK2 ((sK1 ◇ sK2) ◇ sK2)]
  have l96 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l89 sK1 sK2 sK0]
    conv => enter [1]; rw [← l40 sK2 sK1 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l97 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l90 sK0 sK2 sK1]
    conv => enter [1]; rw [← l40 sK2 sK1 sK2 (sK0 ◇ (sK2 ◇ sK1))]
  have l98 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l91 sK1 sK2]
    conv => enter [1]; rw [← l40 sK2 sK1 sK2 (sK1 ◇ sK2)]
  have l99 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l92 sK2 sK1]
    conv => enter [1]; rw [l33 sK2 (sK1 ◇ sK2) (sK1 ◇ sK2) sK2]
  have l100 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l93 sK2 sK1]
    conv => enter [1]; rw [l3 sK2 sK1 (sK2 ◇ sK1)]
  have l101 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l94 sK1 sK2]
    conv => enter [1]; rw [← h54483 (sK1 ◇ sK2) (sK2 ◇ sK1) sK2]
  have l102 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l95 sK1 sK2]
    conv => enter [1]; rw [l25 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2) sK2]
  have l103 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l96 sK1 sK2 sK0]
  have l104 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1]; rw [l97 sK0 sK2 sK1]
  have l105 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK2 sK1 sK2]
    conv => enter [1]; rw [l98 sK1 sK2]
  have l106 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l99 sK2 sK1]
    conv => enter [1]; rw [← h54483 (sK1 ◇ sK2) sK2 sK2]
  have l107 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l65 sK2 sK1]
    conv => enter [1]; rw [← l100 sK2 sK1]
  have l108 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) = (((sK1 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l79 sK1 sK2 sK2]
    conv => enter [1]; rw [← l101 sK1 sK2]
  have l109 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) = (((sK1 ◇ sK2) ◇ sK2) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l13 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l102 sK1 sK2]
  have l110 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l103 sK1 sK2 sK0]
  have l111 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l105 sK1 sK2]
  have l112 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l13 sK1 sK2 sK2]
    conv => enter [1]; rw [← l106 sK2 sK1]
  have l113 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l107 sK2 sK1]
    conv => enter [1]; rw [l24 sK2 sK2 sK1]
  have l114 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l108 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK2 (sK1 ◇ sK2)]
  have l115 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l109 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK2 (sK2 ◇ sK1)]
  have l116 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l113 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ sK2)]
  have l117 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l114 sK1 sK2]
    conv => enter [1]; rw [← l36 sK2 sK2 sK1 (sK1 ◇ sK2)]
  have l118 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l115 sK1 sK2]
    conv => enter [1]; rw [← l40 sK2 sK1 sK2 (sK1 ◇ sK2)]
  have l119 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l112 sK2 sK1]
    conv => enter [1]; rw [← l117 sK1 sK2]
  have l120 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l111 sK1 sK2]
    conv => enter [1]; rw [← l118 sK1 sK2]
  have l121 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l119 sK2 sK1]
    conv => enter [1]; rw [l23 sK1 sK1 sK2]
  have l122 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l120 sK1 sK2]
    conv => enter [1]; rw [← l71 sK1 sK2]
  have l123 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l121 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ sK1)]
  have l124 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l71 sK1 sK2]
    conv => enter [1]; rw [← l123 sK2 sK1]
  have l125 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l83 sK2 sK1 sK0]
  have l126 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l116 sK2 sK1]
  have l127 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l116 sK2 sK1]
    conv => enter [1]; rw [← l13 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l116 sK2 sK1]
  have l128 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l127 sK2 sK1]
    conv => enter [1]; rw [← l79 sK1 sK2 (sK1 ◇ sK2)]
  have l129 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l126 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK1 ◇ sK2)]
  have l130 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← l122 sK1 sK2]
    conv => enter [1]; rw [← l128 sK2 sK1]
  have l131 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l41 sK1 sK2]
    conv => enter [1]; rw [l130 sK1 sK2]
  have l132 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l124 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 sK1 (sK2 ◇ sK1)]
  have l133 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l65 sK2 sK1]
    conv => enter [1]; rw [← l132 sK2 sK1]
  have l134 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l133 sK2 sK1]
    conv => enter [1]; rw [← l36 sK1 sK2 sK1 (sK2 ◇ sK1)]
  have l135 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l134 sK2 sK1]
    conv => enter [1]; rw [← l66 sK1 sK2]
  have l136 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l135 sK2 sK1]
    conv => enter [1]; rw [← l71 sK1 sK2]
  have l137 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l129 sK0 sK2 sK1]
  have l138 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l137 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK1 ◇ sK2)]
  have l139 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l131 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK1 ◇ sK2)]
  have l140 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l139 sK0 sK1 sK2]
  have l141 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1, 2, 2]; rw [l124 sK1 sK2]
    conv => enter [1]; rw [l29 X0 X1 sK2 (sK2 ◇ sK1)]
  have l142 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [← l29 X0 X1 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l129 sK0 sK2 sK1]
  have l143 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK1) ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1, 2]; rw [l30 sK1 sK2 X0]
    conv => enter [1]; rw [l29 X1 X0 (sK2 ◇ sK1) sK1]
  have l144 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK2) ◇ (X1 ◇ (X0 ◇ sK2))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1, 2]; rw [l31 sK2 sK1 X0]
    conv => enter [1]; rw [l29 X1 X0 (sK1 ◇ sK2) sK2]
  have l145 : ∀ X0 X1 sK1 sK2 : G, ((X0 ◇ X1) ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK1) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [← l16 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [l29 (sK2 ◇ sK1) (X0 ◇ X1) X0 X1]
  have l146 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (X1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1))) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [l29 X0 sK0 X1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 sK2]
  have l147 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) = (sK0 ◇ (sK1 ◇ (X0 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l29 sK0 sK1 X0 (sK2 ◇ sK1)]
  have l148 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54483 X0 X2 X1]
    conv => enter [1]; rw [l29 X1 X2 X0 X0]
  have l149 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [l29 sK0 (sK1 ◇ sK2) X0 X1]
  have l150 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ ((sK2 ◇ sK1) ◇ X1))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (X0 ◇ X1)]
    conv => enter [1]; rw [l29 sK0 (sK2 ◇ sK1) X0 X1]
  have l151 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [l29 sK1 sK2 X0 X1]
  have l152 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X1))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1]; rw [l29 sK1 (sK0 ◇ (sK2 ◇ sK1)) X0 X1]
  have l153 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ X1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [l29 sK2 sK1 X0 X1]
  have l154 : ∀ sK1 sK2 X1 X0 X2 : G, ((sK1 ◇ sK2) ◇ (X1 ◇ (X0 ◇ X2))) = (sK1 ◇ (X0 ◇ (sK2 ◇ (X1 ◇ X2)))) := by
    intro sK1 sK2 X1 X0 X2
    conv => enter [1]; rw [← h4512 sK1 sK2 (X1 ◇ (X0 ◇ X2))]
    conv => enter [1, 2]; rw [l29 sK2 X1 X0 X2]
  have l155 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h54483 X1 X0 X2]
    conv => enter [1]; rw [← l29 X0 X1 X2 X1]
  have l156 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← l29 sK1 X0 sK2 X1]
  have l157 : ∀ sK1 sK2 X1 X0 X2 : G, ((sK1 ◇ sK2) ◇ (X1 ◇ (X0 ◇ X2))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X1 X0 X2
    conv => enter [1]; rw [l154 sK1 sK2 X1 X0 X2]
    conv => enter [1]; rw [← l156 sK2 sK1 X0 (X1 ◇ X2)]
  have l158 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l153 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X1]
  have l159 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l152 sK1 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) X1]
  have l160 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l151 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X1]
  have l161 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l150 sK0 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK1) X1]
  have l162 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l149 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X1]
  have l163 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l147 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 sK0 sK1 X0 sK2 sK1]
  have l164 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (X1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1, 2]; rw [← l22 sK0 X1 sK1 sK2 sK1]
    conv => enter [1]; rw [l146 X0 sK0 X1 sK1 sK2]
  have l165 : ∀ X0 X1 sK1 sK2 : G, ((X0 ◇ X1) ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l145 X0 X1 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X1]
  have l166 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) = (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l33 (sK1 ◇ sK2) X1 X0 sK2]
    conv => enter [1]; rw [← l144 X1 sK2 sK1 X0]
  have l167 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ X1))) = (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l33 (sK2 ◇ sK1) X1 X0 sK1]
    conv => enter [1]; rw [← l143 X1 sK1 sK2 X0]
  have l168 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l140 sK0 sK1 sK2]
    conv => enter [1]; rw [← l142 sK0 sK2 sK1 X0 X1]
  have l169 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l53 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l141 X0 X1 sK1 sK2]
  have l170 : ∀ X0 X1 sK1 sK2 : G, ((X0 ◇ X1) ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l165 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [l157 sK2 sK1 X0 X1 X1]
  have l171 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X0))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l168 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK2 ◇ sK1)) X0 X1 (sK2 ◇ sK1)]
  have l172 : ∀ X0 X1 sK1 sK2 : G, ((X0 ◇ X1) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l170 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l155 X1 (sK1 ◇ sK2) X0]
  have l173 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X0))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l171 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [l4 sK2 sK1 sK0 (X1 ◇ X0)]
  have l174 : ∀ X0 X1 sK1 sK2 : G, ((X0 ◇ X1) ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l172 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l148 X0 (sK1 ◇ sK2) X1]
  have l175 : ∀ X1 X0 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X0))) := by
    intro X1 X0 sK1 sK0 sK2
    conv => enter [1]; rw [l164 X1 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l173 X0 X1 sK0 sK1 sK2]
  have l176 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l174 X0 X1 sK1 sK2]
  have l177 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l136 sK2 sK1]
    conv => enter [1]; rw [l116 sK2 sK1]
  have l178 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l136 sK2 sK1]
  have l179 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [← l136 sK2 sK1]
    conv => enter [1]; rw [l16 sK2 sK1 (sK2 ◇ sK1)]
  have l180 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h54483 (sK2 ◇ sK1) X0 X1]
    conv => enter [1, 2, 2]; rw [l136 sK2 sK1]
  have l181 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l180 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← l53 sK1 sK2 X1 X0]
  have l182 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l131 sK1 sK2]
    conv => enter [1]; rw [← l179 sK2 sK1]
  have l183 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l178 sK0 sK2 sK1]
    conv => enter [1]; rw [← l36 sK1 sK2 sK1 sK0]
  have l184 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l182 sK1 sK2]
    conv => enter [1]; rw [l158 sK2 sK1 sK1 (sK1 ◇ sK2)]
  have l185 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l183 sK0 sK2 sK1]
    conv => enter [1]; rw [← l80 sK0 sK1 sK2]
  have l186 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l184 sK1 sK2]
    conv => enter [1]; rw [l176 sK1 (sK2 ◇ sK1) sK1 sK2]
  have l187 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l186 sK1 sK2]
    conv => enter [1]; rw [← l67 sK1 sK2]
  have l188 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l140 sK0 sK1 sK2]
  have l189 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l140 sK0 sK1 sK2]
  have l190 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l140 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK1)) (sK1 ◇ sK2) X0]
  have l191 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l190 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l161 sK0 sK2 sK1 (sK1 ◇ sK2) X0]
  have l192 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l189 sK1 sK0 sK2]
    conv => enter [1]; rw [l163 sK1 sK0 sK1 sK2]
  have l193 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l158 sK0 (sK1 ◇ sK2) (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [← l188 sK2 sK1 sK0]
  have l194 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) sK1 X0]
    conv => enter [1]; rw [l191 sK0 sK1 sK2 X0]
  have l195 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ sK1)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l193 sK0 sK1 sK2]
    conv => enter [1]; rw [l176 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK1 sK2]
  have l196 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l194 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l162 sK0 sK1 sK2 sK1 X0]
  have l197 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l110 sK1 sK2 sK0]
    conv => enter [1]; rw [← l195 sK0 sK1 sK2]
  have l198 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l197 sK1 sK2 sK0]
    conv => enter [1]; rw [l24 (sK0 ◇ (sK1 ◇ sK2)) sK2 sK1]
  have l199 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l198 sK1 sK2 sK0]
    conv => enter [1]; rw [l162 sK0 sK1 sK2 sK1 (sK1 ◇ sK2)]
  have l200 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l199 sK1 sK2 sK0]
    conv => enter [1]; rw [l176 sK1 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l201 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l177 sK1 sK2]
  have l202 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l201 sK0 sK2 sK1]
    conv => enter [1]; rw [← l36 sK1 sK2 sK1 sK0]
  have l203 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l202 sK0 sK2 sK1]
    conv => enter [1]; rw [← l80 sK0 sK1 sK2]
  have l204 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l140 sK0 sK1 sK2]
    conv => enter [1]; rw [l203 sK0 sK2 sK1]
  have l205 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l185 sK0 sK2 sK1]
  have l206 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l185 sK0 sK2 sK1]
  have l207 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l185 sK0 sK2 sK1]
  have l208 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l207 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ sK1) X0]
  have l209 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l206 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l204 sK0 sK1 sK2]
  have l210 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l158 sK0 (sK1 ◇ sK2) (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l205 sK2 sK1 sK0]
  have l211 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← l161 sK0 sK2 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l208 sK0 sK2 sK1 X0]
  have l212 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l209 sK1 sK0 sK2]
    conv => enter [1]; rw [l163 sK1 sK0 sK1 sK2]
  have l213 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l210 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l138 sK1 sK0 sK2]
  have l214 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [l211 sK2 sK1 sK0 X0]
  have l215 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l213 sK0 sK1 sK2]
    conv => enter [1]; rw [l176 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK1 sK2]
  have l216 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l110 sK1 sK2 sK0]
    conv => enter [1]; rw [← l215 sK0 sK1 sK2]
  have l217 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l216 sK1 sK2 sK0]
    conv => enter [1]; rw [l39 sK0 sK1 sK2 (sK2 ◇ sK1)]
  have l218 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l217 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l219 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l187 sK1 sK2]
  have l220 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l187 sK1 sK2]
  have l221 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l220 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
  have l222 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l219 sK0 sK1 sK2]
    conv => enter [1]; rw [← l36 sK1 sK2 sK1 sK0]
  have l223 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l222 sK0 sK1 sK2]
    conv => enter [1]; rw [l221 sK1 sK2 sK0]
  have l224 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l223 sK0 sK1 sK2]
    conv => enter [1]; rw [← l176 sK1 sK0 sK1 sK2]
  have l225 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l192 sK1 sK0 sK2]
  have l226 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l225 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0]
  have l227 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l159 sK1 sK0 sK2 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l226 sK1 sK0 sK2 X0]
  have l228 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l204 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ sK1) X0]
  have l229 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) ◇ X0) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l214 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← l228 sK0 sK1 sK2 X0]
  have l230 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l229 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK1 X0]
  have l231 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l230 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [l162 sK0 sK1 sK2 sK1 X0]
  have l232 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l218 sK1 sK2 sK0]
    conv => enter [1]; rw [l185 sK0 sK2 sK1]
  have l233 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l218 sK1 sK2 sK0]
  have l234 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [← l29 X0 X1 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l218 sK1 sK2 sK0]
  have l235 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l218 sK1 sK2 sK0]
  have l236 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1]; rw [← l235 sK0 sK2 sK1 X0]
  have l237 : ∀ sK2 sK1 sK0 X1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))) := by
    intro sK2 sK1 sK0 X1 X0
    conv => enter [1]; rw [← l33 (sK0 ◇ (sK2 ◇ sK1)) X0 X1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l234 sK0 sK2 sK1 X0 X1]
  have l238 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l138 sK1 sK0 sK2]
    conv => enter [1]; rw [l233 sK1 sK0 sK2]
  have l239 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← l161 sK0 sK2 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [← l236 sK1 sK2 sK0 X0]
  have l240 : ∀ sK2 sK1 sK0 X1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))) := by
    intro sK2 sK1 sK0 X1 X0
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 (X1 ◇ X0)]
    conv => enter [1]; rw [l237 sK2 sK1 sK0 X1 X0]
  have l241 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l192 sK1 sK0 sK2]
    conv => enter [1]; rw [l238 sK1 sK0 sK2]
  have l242 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l239 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [l227 sK1 sK2 sK0 X0]
  have l243 : ∀ X1 X0 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))) := by
    intro X1 X0 sK1 sK0 sK2
    conv => enter [1]; rw [l175 X1 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l240 sK2 sK1 sK0 X1 X0]
  have l244 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l242 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [l181 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l245 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l204 sK0 sK1 sK2]
    conv => enter [1]; rw [← l232 sK1 sK2 sK0]
  have l246 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l232 sK1 sK2 sK0]
  have l247 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1]; rw [← l246 sK0 sK1 sK2 X0]
  have l248 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l245 sK0 sK1 sK2]
    conv => enter [1]; rw [l224 sK0 sK1 sK2]
  have l249 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l214 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← l247 sK1 sK2 sK0 X0]
  have l250 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l249 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [l227 sK1 sK2 sK0 X0]
  have l251 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l231 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [l250 sK2 sK1 sK0 X0]
  have l252 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l248 sK1 sK2 sK0]
  have l253 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [← l35 sK2 sK1 sK0]
    conv => enter [1]; rw [l3 sK2 sK1 ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l254 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l253 sK2 sK1 sK0]
    conv => enter [1]; rw [l166 sK2 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) (sK0 ◇ (sK2 ◇ sK1))]
  have l255 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l254 sK2 sK1 sK0]
    conv => enter [1]; rw [l161 sK0 sK2 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l256 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l255 sK2 sK1 sK0]
    conv => enter [1]; rw [l4 sK2 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l257 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l256 sK2 sK1 sK0]
    conv => enter [1]; rw [l231 sK2 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l258 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l257 sK2 sK1 sK0]
  have l259 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l231 sK2 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l258 sK2 sK1 sK0]
  have l260 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l176 sK1 (sK1 ◇ sK2) sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l259 sK1 sK0 sK2]
  have l261 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l200 sK1 sK2 sK0]
    conv => enter [1]; rw [l260 sK1 sK2 sK0]
  have l262 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l248 sK1 sK2 sK0]
    conv => enter [1]; rw [l261 sK1 sK2 sK0]
  have l263 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l37 sK2 sK1]
    conv => enter [1, 2]; rw [l124 sK2 sK1]
  have l264 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l263 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ sK2)]
  have l265 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l131 sK1 sK2]
    conv => enter [1]; rw [← l264 sK2 sK1]
  have l266 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l265 sK2 sK1]
    conv => enter [1]; rw [l187 sK1 sK2]
  have l267 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l5 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [l266 sK2 sK1]
  have l268 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l266 sK2 sK1]
  have l269 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l268 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
  have l270 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l267 sK0 sK2 sK1]
    conv => enter [1]; rw [← l36 sK1 sK2 sK1 sK0]
  have l271 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l270 sK0 sK2 sK1]
    conv => enter [1]; rw [← l80 sK0 sK1 sK2]
  have l272 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l204 sK0 sK1 sK2]
    conv => enter [1]; rw [← l271 sK0 sK2 sK1]
  have l273 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l272 sK0 sK2 sK1]
    conv => enter [1]; rw [l224 sK0 sK1 sK2]
  have l274 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [l273 sK0 sK2 sK1]
  have l275 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l60 sK0 sK1 sK2]
    conv => enter [1]; rw [← l29 sK1 (sK2 ◇ sK1) X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l276 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l275 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l167 sK1 sK2 X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l277 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l276 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l162 sK0 sK1 sK2 (sK1 ◇ sK2) X0]
  have l278 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l176 X0 (sK1 ◇ sK2) sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l277 X0 sK0 sK1 sK2]
  have l279 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l104 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l280 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l279 sK1 sK0 sK2]
    conv => enter [1]; rw [← l244 sK1 sK0 sK2 (sK1 ◇ sK2)]
  have l281 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l280 sK1 sK0 sK2]
    conv => enter [1]; rw [← l251 sK1 sK0 sK2 (sK1 ◇ sK2)]
  have l282 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l281 sK1 sK0 sK2]
    conv => enter [1]; rw [l176 sK1 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l283 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l200 sK1 sK2 sK0]
    conv => enter [1]; rw [← l282 sK1 sK0 sK2]
  have l284 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l283 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
  have l285 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l284 sK1 sK2 sK0]
    conv => enter [1]; rw [l212 sK1 sK0 sK2]
  have l286 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l285 sK1 sK2 sK0]
    conv => enter [1]; rw [l248 sK1 sK2 sK0]
  have l287 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l2 sK1 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l286 sK1 sK0 sK2]
  have l288 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l286 sK1 sK0 sK2]
  have l289 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l288 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l290 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l287 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l291 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l60 sK0 sK1 sK2]
    conv => enter [1]; rw [← l290 sK1 sK2 sK0]
  have l292 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l291 sK0 sK1 sK2]
    conv => enter [1]; rw [l221 sK1 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l293 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l292 sK0 sK1 sK2]
    conv => enter [1]; rw [← l241 sK1 sK0 sK2]
  have l294 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l293 sK0 sK1 sK2]
    conv => enter [1]; rw [l286 sK1 sK0 sK2]
  have l295 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l289 sK2 sK1 sK0]
  have l296 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l295 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2))]
  have l297 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [← l294 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
  have l298 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l297 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l162 sK0 sK1 sK2 (sK1 ◇ sK2) X0]
  have l299 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l298 sK1 sK0 sK2 X0]
  have l300 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l296 sK0 sK2 sK1]
  have l301 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l296 sK0 sK2 sK1]
  have l302 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l301 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK2))]
  have l303 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l300 sK2 sK1 sK0]
    conv => enter [1]; rw [l4 sK2 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l304 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l303 sK2 sK1 sK0]
    conv => enter [1]; rw [l231 sK2 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l305 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l231 sK2 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l304 sK2 sK1 sK0]
  have l306 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l262 sK1 sK0 sK2]
    conv => enter [1]; rw [l305 sK1 sK0 sK2]
  have l307 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l33 X0 X1 (sK1 ◇ sK2) sK1]
  have l308 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X1))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1, 2, 2]; rw [l218 sK1 sK2 sK0]
    conv => enter [1]; rw [l33 X0 X1 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
  have l309 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [← l33 X1 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l310 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l33 X0 sK0 sK1 (sK2 ◇ sK1)]
  have l311 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l33 sK0 (sK2 ◇ sK1) sK1 X0]
  have l312 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [← l33 sK2 X0 sK1 X1]
  have l313 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) = (sK2 ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l3 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← l33 sK2 X1 X0 (sK2 ◇ sK1)]
  have l314 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l313 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← l169 sK1 sK2 X1 X0]
  have l315 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ (X0 ◇ X1))) = (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l29 sK2 X0 sK1 X1]
    conv => enter [1]; rw [← l312 X1 sK2 sK1 X0]
  have l316 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK1 ◇ X0)]
    conv => enter [1]; rw [← l311 X0 sK0 sK1 sK2]
  have l317 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (X0 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l310 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l157 sK2 sK1 X0 sK1 sK0]
  have l318 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l176 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [l309 X0 X1 sK1 sK2 sK0]
  have l319 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l157 sK1 sK2 (sK0 ◇ (sK2 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [← l308 X0 X1 sK1 sK2 sK0]
  have l320 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1, 2, 2]; rw [← l187 sK1 sK2]
    conv => enter [1]; rw [l307 X0 X1 sK1 sK2]
  have l321 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l314 sK2 sK1 X0 X1]
    conv => enter [1]; rw [l269 sK2 sK1 (X0 ◇ X1)]
  have l322 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [l315 sK1 sK2 X0 X1]
  have l323 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l316 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [l224 sK0 sK1 sK2]
  have l324 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l317 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ sK0)]
  have l325 : ∀ X1 X0 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK1 sK0 sK2
    conv => enter [1]; rw [l243 X1 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l319 sK1 sK2 sK0 X0 X1]
  have l326 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l53 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l320 X0 X1 sK1 sK2]
  have l327 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l161 sK0 sK2 sK1 sK1 X0]
    conv => enter [1]; rw [l323 sK0 sK2 sK1 X0]
  have l328 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l167 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l324 X0 sK0 sK1 sK2]
  have l329 : ∀ X1 X0 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK1 sK0 sK2
    conv => enter [1]; rw [l325 X1 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l196 sK1 sK2 sK0 (X0 ◇ X1)]
  have l330 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l327 sK1 sK0 sK2 X0]
  have l331 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l328 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l224 sK0 sK1 sK2]
  have l332 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l331 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l330 sK1 sK0 sK2 X0]
  have l333 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l332 sK0 sK1 sK2 X0]
  have l334 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l333 sK0 sK1 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l302 sK1 sK0 sK2]
  have l335 : ∀ X1 X0 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54483 X1 X0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l333 sK0 sK1 sK2 (X0 ◇ (X1 ◇ X1))]
  have l336 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l31 sK2 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l333 sK0 sK1 sK2 ((sK1 ◇ sK2) ◇ sK2)]
  have l337 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l336 sK2 sK1 sK0]
    conv => enter [1]; rw [l162 sK0 sK1 sK2 (sK1 ◇ sK2) sK2]
  have l338 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54483 X1 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l335 X1 X0 sK1 sK0 sK2]
  have l339 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l334 sK0 sK1 sK2]
    conv => enter [1]; rw [← l333 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l340 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l337 sK2 sK1 sK0]
    conv => enter [1]; rw [← l278 sK2 sK1 sK2 sK0]
  have l341 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l340 sK2 sK1 sK0]
    conv => enter [1]; rw [l269 sK2 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l342 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l200 sK1 sK2 sK0]
    conv => enter [1]; rw [← l341 sK2 sK1 sK0]
  have l343 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l342 sK1 sK2 sK0]
    conv => enter [1]; rw [l248 sK1 sK2 sK0]
  have l344 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l343 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l345 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l344 sK0 sK1 sK2]
    conv => enter [1]; rw [l296 sK0 sK2 sK1]
  have l346 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l252 sK0 sK1 sK2]
    conv => enter [1]; rw [l345 sK0 sK1 sK2]
  have l347 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l346 sK0 sK1 sK2]
    conv => enter [1]; rw [l339 sK0 sK1 sK2]
  have l348 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l345 sK0 sK1 sK2]
    conv => enter [1]; rw [l347 sK0 sK2 sK1]
  have l349 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l348 sK0 sK1 sK2]
    conv => enter [1]; rw [l318 sK0 sK1 sK0 sK1 sK2]
  have l350 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l347 sK0 sK2 sK1]
  have l351 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l306 sK1 sK0 sK2]
    conv => enter [1]; rw [← l350 sK1 sK0 sK2]
  have l352 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l351 sK1 sK0 sK2]
    conv => enter [1]; rw [← l333 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l353 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h54483 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1, 2, 2]; rw [← l352 sK1 sK0 sK2]
  have l354 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l353 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l330 sK1 sK0 sK2 X0]
  have l355 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l354 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l333 sK0 sK1 sK2 X0]
  have l356 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK0))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l2 sK1 sK2 ((sK1 ◇ sK2) ◇ sK0)]
    conv => enter [1, 2]; rw [← l73 sK1 sK0 sK2]
  have l357 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ X0)) = (((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 sK1 ((sK1 ◇ sK2) ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l73 sK1 sK0 sK2]
  have l358 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l357 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK1 X0]
  have l359 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l356 sK1 sK2 sK0]
    conv => enter [1]; rw [l227 sK1 sK2 sK0 sK1]
  have l360 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK1 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l159 sK1 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l358 sK1 sK2 sK0 X0]
  have l361 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l251 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l359 sK1 sK2 sK0]
  have l362 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l360 sK1 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) sK0 X0]
  have l363 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l361 sK1 sK0 sK2]
    conv => enter [1]; rw [← l326 sK1 sK2 (sK2 ◇ sK1) sK0]
  have l364 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l362 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l321 sK1 sK2 X0 sK0]
  have l365 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l79 sK1 sK2 sK0]
    conv => enter [1]; rw [← l363 sK1 sK0 sK2]
  have l366 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l322 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l364 sK1 sK0 sK2 X0]
  have l367 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l365 sK1 sK2 sK0]
    conv => enter [1]; rw [← l318 sK1 sK1 sK0 sK1 sK2]
  have l368 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l366 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l251 sK1 sK0 sK2 X0]
  have l369 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l274 sK1 sK0 sK2]
    conv => enter [1]; rw [← l367 sK1 sK2 sK0]
  have l370 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l368 sK0 sK2 sK1 X0]
  have l371 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l369 sK1 sK0 sK2]
    conv => enter [1]; rw [← l73 sK1 sK0 sK2]
  have l372 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l333 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l371 sK1 sK0 sK2]
  have l373 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l372 sK0 sK1 sK2]
    conv => enter [1]; rw [← l333 sK0 sK1 sK2 sK2]
  have l374 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l373 sK0 sK1 sK2]
    conv => enter [1]; rw [l224 sK0 sK1 sK2]
  have l375 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l76 sK0 sK2 sK1]
    conv => enter [1]; rw [l3 sK2 sK1 ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1)]
  have l376 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l76 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1)]
  have l377 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l376 sK1 sK0 sK2]
    conv => enter [1]; rw [l227 sK1 sK2 sK0 sK1]
  have l378 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l166 sK2 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l375 sK2 sK1 sK0]
  have l379 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l377 sK1 sK0 sK2]
    conv => enter [1]; rw [← l251 sK1 sK0 sK2 sK1]
  have l380 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l378 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK2 sK1 sK0 (sK2 ◇ sK1)]
  have l381 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l370 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [← l379 sK1 sK0 sK2]
  have l382 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l380 sK1 sK2 sK0]
    conv => enter [1]; rw [l231 sK2 sK1 sK0 (sK2 ◇ sK1)]
  have l383 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l381 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
  have l384 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l370 sK0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l382 sK1 sK2 sK0]
  have l385 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l383 sK0 sK2 sK1]
    conv => enter [1]; rw [l212 sK1 sK0 sK2]
  have l386 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l384 sK0 sK2 sK1]
    conv => enter [1]; rw [l221 sK1 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l387 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l385 sK0 sK2 sK1]
    conv => enter [1]; rw [l286 sK1 sK0 sK2]
  have l388 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l386 sK0 sK2 sK1]
    conv => enter [1]; rw [← l241 sK1 sK0 sK2]
  have l389 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l388 sK0 sK2 sK1]
    conv => enter [1]; rw [l286 sK1 sK0 sK2]
  have l390 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 sK0]
    conv => enter [1]; rw [l387 sK0 sK2 sK1]
  have l391 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l129 sK0 sK2 sK1]
    conv => enter [1]; rw [l389 sK0 sK2 sK1]
  have l392 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) sK0 X0]
    conv => enter [1, 1]; rw [l390 sK1 sK2 sK0]
  have l393 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l392 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l394 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l370 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l393 sK1 sK2 sK0 X0]
  have l395 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l160 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l394 sK0 sK2 sK1 X0]
  have l396 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l395 sK0 sK1 sK2 X0]
  have l397 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK1)) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l391 sK0 sK2 sK1]
  have l398 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l397 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l399 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l370 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l398 sK0 sK2 sK1 X0]
  have l400 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l399 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [l161 sK0 sK2 sK1 (sK1 ◇ sK2) X0]
  have l401 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l396 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l400 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [l396 sK0 sK2 sK1 X0]
  have l402 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l396 sK0 sK1 sK2 ((sK2 ◇ sK1) ◇ sK1)]
    conv => enter [1]; rw [← l30 sK1 sK2 (sK0 ◇ (sK2 ◇ sK1))]
  have l403 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l402 sK0 sK1 sK2]
    conv => enter [1]; rw [l355 sK0 sK1 sK2 (sK2 ◇ sK1) sK1]
  have l404 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l370 sK0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l403 sK1 sK2 sK0]
  have l405 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l404 sK0 sK2 sK1]
    conv => enter [1]; rw [l389 sK0 sK2 sK1]
  have l406 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l405 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK2 ◇ sK1))]
  have l407 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l406 sK0 sK1 sK2]
    conv => enter [1]; rw [l318 sK0 sK1 sK0 sK1 sK2]
  have l408 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l407 sK0 sK1 sK2]
    conv => enter [1]; rw [← l349 sK0 sK1 sK2]
  have l409 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l352 sK1 sK0 sK2]
    conv => enter [1]; rw [← l408 sK0 sK1 sK2]
  have l410 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l125 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [l374 sK0 sK1 sK2]
  have l411 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l410 sK0 sK2 sK1]
    conv => enter [1]; rw [← l252 sK0 sK1 sK2]
  have l412 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l411 sK0 sK2 sK1]
    conv => enter [1]; rw [l339 sK0 sK1 sK2]
  have l413 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l412 sK0 sK2 sK1]
    conv => enter [1]; rw [← l352 sK1 sK0 sK2]
  have l414 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l413 sK0 sK2 sK1]
    conv => enter [1]; rw [l396 sK0 sK2 sK1 sK0]
  have l415 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l414 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
  have l416 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l415 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l162 sK0 sK1 sK2 sK0 X0]
  have l417 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l416 sK1 sK0 sK2 X0]
  have l418 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l370 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [l417 sK1 sK0 sK2 X0]
  have l419 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l396 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l418 sK0 sK2 sK1 X0]
  have l420 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l401 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l277 X0 sK0 sK1 sK2]
  have l421 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l420 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l176 X0 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l422 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l200 sK1 sK2 sK0]
    conv => enter [1]; rw [l33 X0 sK1 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l423 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l422 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l29 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK1 ◇ sK2) sK1]
  have l424 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l423 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l299 sK1 sK0 sK2 (X0 ◇ sK1)]
  have l425 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l424 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l329 sK1 X0 sK1 sK0 sK2]
  have l426 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l425 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l338 sK1 X0 sK0 sK1 sK2]
  have l427 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l338 X0 (sK1 ◇ sK2) sK0 sK1 sK2]
    conv => enter [1]; rw [l426 X0 sK1 sK2 sK0]
  have l428 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l421 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l427 X0 sK1 sK2 sK0]
  have l429 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l13 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK1 sK2 sK0 sK0]
  have l430 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l429 sK0 sK2 sK1]
    conv => enter [1]; rw [← l419 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l431 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l430 sK0 sK2 sK1]
    conv => enter [1]; rw [l294 sK0 sK1 sK2]
  have l432 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l431 sK0 sK2 sK1]
    conv => enter [1]; rw [← l428 sK0 sK1 sK2 sK1]
  have l433 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l432 sK1 sK0 sK2]
    conv => enter [1]; rw [l224 sK0 sK1 sK2]
  have l434 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l431 sK0 sK2 sK1]
    conv => enter [1]; rw [← l433 sK1 sK0 sK2]
  have l435 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l16 sK2 sK1 sK0]
    conv => enter [1]; rw [l8 sK2 sK1 sK0 sK0]
  have l436 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l435 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l129 sK0 sK2 sK1]
  have l437 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l436 sK0 sK1 sK2]
    conv => enter [1]; rw [l176 sK0 (sK0 ◇ (sK2 ◇ sK1)) sK1 sK2]
  have l438 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l437 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK2 ◇ sK1))]
  have l439 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l438 sK0 sK1 sK2]
    conv => enter [1]; rw [← l409 sK1 sK0 sK2]
  have l440 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l439 sK0 sK1 sK2]
    conv => enter [1]; rw [← l431 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l440 x y z]
  conv => enter [1]; rw [l434 x z y]

theorem Equation4512_54398_implies_Equation54484 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54398 : Equation54398 G) : Equation54484 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l9 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l10 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2]
  have l11 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [l9 sK1 sK0 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l10 sK1 sK0 sK2]
  have l13 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54398 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l14 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X0)) = ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h54398 X1 (X2 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h54398 X0 X1 X2]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54398 (sK0 ◇ sK1) X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 X0]
  have l16 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h54398 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X1)) X3]
  have l17 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54398 (sK1 ◇ sK2) sK0 X0]
  have l18 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54398 sK2 sK1 X0]
  have l19 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (X0 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54398 X0 sK2 X1]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (X0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h54398 sK2 (sK0 ◇ sK1) X0]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54398 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l2 sK0 sK1 X0]
    conv => enter [1]; rw [l21 sK0 sK1 X0]
  have l23 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X1) X3]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← h54398 sK0 X0 (sK1 ◇ (sK0 ◇ sK1))]
  have l25 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l14 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X2 X1 (X0 ◇ (X1 ◇ X2))]
  have l26 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [← h54398 X0 (sK1 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [l9 sK1 sK0 sK2]
  have l27 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l23 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X3]
  have l28 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l25 X1 X2 X0]
    conv => enter [1]; rw [← l13 X1 X2 X0 X1]
  have l29 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l27 X0 X1 X2 X3]
  have l30 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l28 X1 X2 X0]
    conv => enter [1]; rw [← h54398 X2 X1 X0]
  have l31 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l29 X0 X1 X2 X3]
  have l32 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l30 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X1 X0]
  have l33 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h54398 X0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l34 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54398 X0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l33 sK0 X0 sK1 sK2]
  have l35 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l34 (X0 ◇ X1) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK2))]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l34 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54398 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l37 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54398 X1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l34 X0 sK0 sK1 sK2]
  have l38 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [l37 X1 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK2)) (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l39 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l34 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l36 sK0 sK1 sK2 X0]
  have l40 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l35 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54398 X0 (sK0 ◇ (sK1 ◇ sK2)) X1]
  have l41 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X1 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l31 (sK0 ◇ (sK1 ◇ sK2)) X0 X1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l38 X1 X0 sK0 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l41 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l40 X1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK1 sK2]
  have l43 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l34 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2 X0 X1]
  have l44 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [l43 X1 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54398 X0 (sK0 ◇ (sK1 ◇ sK2)) X1]
  have l45 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54398 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l39 X0 sK0 sK1 sK2]
  have l46 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54398 X1 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l39 X0 sK0 sK1 sK2]
  have l47 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l46 X1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) X0 (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l48 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l34 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l45 sK0 sK1 sK2 X0]
  have l49 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l47 X1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l13 X0 (sK0 ◇ (sK1 ◇ sK2)) X1 X0]
  have l50 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X1 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h54398 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [← l49 X1 sK0 sK1 sK2 X0]
  have l51 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l50 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l40 X1 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l51 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l39 X0 sK0 sK1 sK2]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l48 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l54 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l48 (sK1 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l55 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l48 (sK1 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
  have l56 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l48 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1 sK2]
  have l57 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l56 sK0 sK1 sK2]
  have l58 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l55 sK2 sK1 sK0]
  have l59 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l54 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l40 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
  have l60 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l53 sK0 sK1 sK2]
  have l61 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54398 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l62 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l58 sK2 sK1 sK0]
    conv => enter [1]; rw [l40 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
  have l63 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l59 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l44 (sK1 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1 sK2]
  have l64 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l34 (sK1 ◇ sK2) sK0 sK1 sK2]
    conv => enter [1]; rw [← l60 sK0 sK1 sK2]
  have l65 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l26 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l61 sK0 sK1 sK2]
  have l66 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l62 sK2 sK1 sK0]
    conv => enter [1]; rw [← l44 (sK1 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1 sK2]
  have l67 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l63 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l40 (sK1 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1 sK2]
  have l68 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l65 sK0 sK1 sK2]
    conv => enter [1]; rw [← l34 (sK1 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
  have l69 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l66 sK2 sK1 sK0]
    conv => enter [1]; rw [l40 (sK1 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1 sK2]
  have l70 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [← l26 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l67 sK1 sK2 sK0]
  have l71 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l34 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [l68 sK0 sK1 sK2]
  have l72 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l26 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l69 sK2 sK1 sK0]
  have l73 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l70 sK1 sK0 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l74 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l34 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [l72 sK0 sK1 sK2]
  have l75 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l73 sK1 sK0 sK2]
    conv => enter [1]; rw [l40 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1 sK2]
  have l76 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 (sK0 ◇ (sK1 ◇ sK2)) sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l75 sK1 sK0 sK2]
  have l77 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l34 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [l76 sK0 sK1 sK2]
  have l78 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h54398 sK2 sK1 sK0]
  have l79 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h54398 (sK1 ◇ sK2) sK1 sK0]
  have l80 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54398 X0 sK1 sK0]
  have l81 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54398 X0 sK0 sK1]
    conv => enter [1]; rw [← l80 sK0 sK1 X0]
  have l82 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l79 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))]
  have l83 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l78 sK0 sK1 sK2]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2 sK1 (sK0 ◇ sK1)]
  have l84 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l24 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l82 sK0 sK1 sK2]
  have l85 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← l83 sK0 sK1 sK2]
  have l86 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l84 sK0 sK1 sK2]
    conv => enter [1]; rw [l17 sK0 sK1 sK2 sK1]
  have l87 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l85 sK0 sK1 sK2]
    conv => enter [1]; rw [l17 sK0 sK1 sK2 sK1]
  have l88 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l86 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK1 sK2 sK0]
  have l89 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l87 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK1 sK2 sK0]
  have l90 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l88 sK0 sK1 sK2]
    conv => enter [1]; rw [h54398 sK2 sK1 sK0]
  have l91 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l89 sK0 sK1 sK2]
    conv => enter [1]; rw [h54398 sK2 sK1 sK0]
  have l92 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l90 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ sK1)]
  have l93 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l91 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ sK1)]
  have l94 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l92 sK0 sK1 sK2]
  have l95 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l52 sK0 sK1 sK2 (sK1 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [l93 sK0 sK1 sK2]
  have l96 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l95 sK2 sK1 sK0]
  have l97 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l74 sK1 sK0 sK2]
    conv => enter [1]; rw [l96 sK2 sK1 sK0]
  have l98 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l94 sK0 sK1 sK2]
  have l99 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l10 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l94 sK0 sK1 sK2]
  have l100 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l39 (sK1 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l94 sK0 sK1 sK2]
  have l101 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l94 sK0 sK1 sK2]
  have l102 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l101 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ sK1) X0]
  have l103 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l100 sK1 sK0 sK2]
    conv => enter [1]; rw [l20 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l104 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l99 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l97 sK1 sK0 sK2]
  have l105 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l24 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l98 sK0 sK1 sK2]
  have l106 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l71 sK1 sK0 sK2]
    conv => enter [1]; rw [l103 sK1 sK0 sK2]
  have l107 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l48 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l104 sK1 sK0 sK2]
  have l108 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l105 sK0 sK1 sK2]
  have l109 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l108 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l107 sK1 sK0 sK2]
  have l110 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l109 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l111 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l110 sK0 sK1 sK2]
    conv => enter [1]; rw [l94 sK0 sK1 sK2]
  have l112 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l97 sK1 sK0 sK2]
    conv => enter [1]; rw [← l111 sK0 sK1 sK2]
  have l113 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l97 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l114 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l97 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ sK1) X0]
  have l115 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l114 sK1 sK0 sK2 X0]
  have l116 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l113 sK0 sK1 sK2]
  have l117 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l112 sK1 sK0 sK2]
    conv => enter [1]; rw [l116 sK0 sK1 sK2]
  have l118 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l64 sK1 sK2 sK0]
  have l119 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l118 sK0 sK1 sK2 X0]
  have l120 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l39 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l119 sK1 sK2 sK0 X0]
  have l121 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l71 sK1 sK0 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l122 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l121 sK1 sK2 sK0]
    conv => enter [1]; rw [l40 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1 sK2]
  have l123 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l77 sK1 sK0 sK2]
    conv => enter [1]; rw [← l122 sK1 sK2 sK0]
  have l124 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l123 sK1 sK0 sK2]
    conv => enter [1]; rw [← h54398 sK1 (sK1 ◇ sK2) sK0]
  have l125 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l107 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l126 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK2) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l11 sK2 sK1 sK0]
    conv => enter [1]; rw [l125 sK2 sK1 sK0]
  have l127 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l126 sK2 sK1 sK0]
    conv => enter [1]; rw [l8 sK0 sK1 sK2 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l128 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l127 sK0 sK1 sK2]
    conv => enter [1]; rw [l102 sK0 sK1 sK2 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l129 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l128 sK0 sK1 sK2]
    conv => enter [1]; rw [← l115 sK1 sK0 sK2 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l130 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l77 sK1 sK0 sK2]
    conv => enter [1]; rw [← l129 sK0 sK1 sK2]
  have l131 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l130 sK1 sK0 sK2]
    conv => enter [1]; rw [l8 sK0 sK1 sK2 sK2]
  have l132 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l131 sK1 sK0 sK2]
    conv => enter [1]; rw [l102 sK0 sK1 sK2 sK2]
  have l133 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l132 sK1 sK0 sK2]
    conv => enter [1]; rw [← l115 sK1 sK0 sK2 sK2]
  have l134 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l133 sK1 sK0 sK2]
    conv => enter [1]; rw [← l40 sK1 sK2 sK0 sK1 sK2]
  have l135 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l134 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l136 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l135 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l137 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l136 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l120 X0 sK0 sK1 sK2]
  have l138 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l137 sK1 sK0 sK2 X0]
  have l139 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l81 sK2 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
  have l140 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l81 X0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l141 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← l140 sK0 sK1 X0]
  have l142 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l117 sK1 sK0 sK2]
    conv => enter [1]; rw [← l139 sK2 sK0 sK1]
  have l143 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l141 sK0 sK1 X0]
    conv => enter [1]; rw [← l81 X0 sK0 sK1]
  have l144 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l142 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) X0]
  have l145 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l144 sK1 sK0 sK2 X0]
  have l146 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l138 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l145 sK1 sK0 sK2 X0]
  have l147 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK2 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l106 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) X0]
  have l148 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK2 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l147 sK1 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK2) X0]
  have l149 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (((sK1 ◇ sK2) ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l148 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l146 ((sK1 ◇ sK2) ◇ X0) sK0 sK1 sK2]
  have l150 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l149 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l151 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l150 sK1 sK0 sK2 X0]
  have l152 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l138 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l151 sK1 sK0 sK2 X0]
  have l153 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← h54398 (sK0 ◇ sK1) sK2 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK2 ◇ sK1)]
  have l154 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h54398 X0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (sK1 ◇ sK2))]
  have l155 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54398 X0 sK1 sK2]
    conv => enter [1]; rw [l154 sK1 X0 sK2]
  have l156 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l153 sK0 sK1 sK2]
    conv => enter [1]; rw [l143 sK0 sK1 (sK2 ◇ sK1)]
  have l157 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l156 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK0 ◇ sK1)]
  have l158 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l157 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))]
  have l159 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l158 sK2 sK1 sK0]
    conv => enter [1]; rw [l52 sK0 sK1 sK2 (sK0 ◇ sK1) (sK1 ◇ sK2)]
  have l160 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l159 sK2 sK1 sK0]
    conv => enter [1]; rw [← l152 (sK0 ◇ sK1) sK0 sK1 sK2]
  have l161 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l160 sK2 sK1 sK0]
    conv => enter [1]; rw [← l112 sK1 sK0 sK2]
  have l162 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l11 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l161 sK2 sK1 sK0]
  have l163 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l161 sK2 sK1 sK0]
  have l164 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l161 sK2 sK1 sK0]
    conv => enter [1]; rw [l48 sK1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l161 sK2 sK1 sK0]
  have l165 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l161 sK2 sK1 sK0]
    conv => enter [1]; rw [l34 sK1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l161 sK2 sK1 sK0]
  have l166 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54398 sK1 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [← l161 sK2 sK1 sK0]
  have l167 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l124 sK1 sK0 sK2]
    conv => enter [1]; rw [l166 sK1 sK2 sK0]
  have l168 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l112 sK1 sK0 sK2]
    conv => enter [1]; rw [l163 sK0 sK1 sK2]
  have l169 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l161 sK2 sK1 sK0]
    conv => enter [1]; rw [l167 sK1 sK0 sK2]
  have l170 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l161 sK2 sK1 sK0]
    conv => enter [1]; rw [l168 sK1 sK0 sK2]
  have l171 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l164 sK2 sK1 sK0]
  have l172 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l170 sK2 sK1 sK0]
    conv => enter [1]; rw [← l171 sK0 sK1 sK2]
  have l173 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l162 sK2 sK1 sK0]
  have l174 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l173 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l175 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l165 sK2 sK1 sK0]
    conv => enter [1]; rw [← l174 sK0 sK1 sK2]
  have l176 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l175 sK2 sK1 sK0]
    conv => enter [1]; rw [l102 sK0 sK1 sK2 sK2]
  have l177 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l176 sK2 sK1 sK0]
    conv => enter [1]; rw [← l115 sK1 sK0 sK2 sK2]
  have l178 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l177 sK2 sK1 sK0]
    conv => enter [1]; rw [l138 sK1 sK0 sK2 sK2]
  have l179 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h54398 sK2 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [← l178 sK2 sK1 sK0]
  have l180 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l169 sK2 sK1 sK0]
    conv => enter [1]; rw [← l179 sK2 sK1 sK0]
  have l181 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l180 sK2 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 ((sK1 ◇ sK2) ◇ sK0)]
  have l182 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l181 sK0 sK1 sK2]
    conv => enter [1]; rw [l17 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l183 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l155 sK0 sK1 sK2]
    conv => enter [1]; rw [← l182 sK0 sK1 sK2]
  have l184 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l183 sK0 sK1 sK2]
    conv => enter [1]; rw [← l172 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l184 x y z]

theorem Equation4512_54484_implies_Equation54398 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54484 : Equation54484 G) : Equation54398 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK2 ◇ X0) ◇ X1)) = (X1 ◇ ((sK2 ◇ X0) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h54484 sK1 (sK2 ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h54484 X1 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h54484 X0 X1 (X0 ◇ X1)]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ sK2)]
    conv => enter [1]; rw [← h54484 X0 sK2 sK1]
  have l4 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54484 X0 sK1 sK2]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1, 2]; rw [← h54484 X0 X1 X0]
  have l6 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [h54484 sK2 sK1 X0]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK2 ◇ X0) ◇ X1)) = (X1 ◇ (sK2 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 ((sK1 ◇ sK2) ◇ X0)]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [h54484 sK1 sK2 X0]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l5 X1 X0 X2]
    conv => enter [1]; rw [← h54484 X1 X0 X2]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK2 ◇ X0) ◇ X1)) = (X1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h54484 (sK1 ◇ sK2) X0 sK2]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l9 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l12 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK2 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l10 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [l3 sK1 sK2 X0]
  have l13 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [h4512 sK2 X0 X1]
    conv => enter [1]; rw [l12 sK1 sK2 X0 X1]
  have l14 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [l13 sK1 sK2 X0 X1]
  have l15 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l6 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
  have l16 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l15 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← l6 sK2 sK1 X1]
  have l17 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54484 sK2 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 (sK1 ◇ sK2)]
  have l18 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK1 ◇ sK2))]
  have l19 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l19 sK1 sK2]
  have l21 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l18 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 X1]
  have l22 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l4 sK2 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 sK1 sK1]
  have l23 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l22 sK2 sK1]
    conv => enter [1]; rw [l17 sK2 sK1 sK1]
  have l24 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l23 sK2 sK1]
    conv => enter [1, 2]; rw [← l20 sK1 sK2]
  have l25 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l24 sK2 sK1]
    conv => enter [1]; rw [← l6 sK2 sK1 sK1]
  have l26 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54484 (sK2 ◇ sK1) sK1 X0]
    conv => enter [1, 2, 2]; rw [← l25 sK2 sK1]
  have l27 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l26 sK2 sK1 X0]
  have l28 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l16 sK2 sK1 sK1 X0]
    conv => enter [1]; rw [← l27 X0 sK1 sK2]
  have l29 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l28 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l20 sK1 sK2]
  have l30 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l6 sK2 sK1 X0]
    conv => enter [1]; rw [← l29 sK1 sK2 X0]
  have l31 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ X0)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l11 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X0]
  have l32 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l11 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ X0)]
  have l33 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l32 sK1 sK2 X0]
    conv => enter [1]; rw [l21 sK1 sK2 sK1 X0]
  have l34 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (sK1 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l30 sK2 sK1 X0]
    conv => enter [1]; rw [← l31 sK1 sK2 X0]
  have l35 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [l33 sK1 sK2 X0]
  have l36 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK2 ◇ sK1) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [← l34 sK2 sK1 X0]
  have l37 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l4 sK2 sK1 X0]
    conv => enter [1]; rw [l36 sK2 sK1 (X0 ◇ sK1)]
  have l38 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [h54484 X1 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l36 sK2 sK1 (X0 ◇ (X1 ◇ X0))]
  have l39 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [h54484 X1 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l38 X1 X0 sK2 sK1]
  have l40 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l37 X0 sK1 sK2]
    conv => enter [1]; rw [l14 sK1 sK2 X0 sK1]
  have l41 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l40 X0 sK1 sK2]
    conv => enter [1]; rw [l39 sK1 X0 sK2 sK1]
  have l42 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← l3 sK1 sK2 X0]
    conv => enter [1]; rw [l35 sK1 sK2 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 X0]
  have l43 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l42 X0 sK2 sK1]
    conv => enter [1]; rw [l39 sK1 X0 sK2 sK1]
  have l44 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l41 X0 sK1 sK2]
    conv => enter [1]; rw [← l43 X0 sK2 sK1]
  have l45 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l44 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l45 x y z]

theorem Equation4512_54398_implies_Equation54501 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54398 : Equation54398 G) : Equation54501 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK0]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK0 X0]
  have l2 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l4 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 (sK1 ◇ sK2)]
  have l5 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l8 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l5 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l10 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l7 sK1 sK2 sK0]
  have l11 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l12 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54398 X0 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK2 sK0]
  have l13 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h54398 sK2 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 X0]
  have l14 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK2 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h54398 (sK2 ◇ sK0) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l3 sK2 sK0 sK1 X0]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h54398 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X1)) X3]
  have l16 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h54398 (sK1 ◇ sK2) sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ sK0)]
  have l17 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK1)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54398 (sK2 ◇ sK0) sK1 X0]
  have l18 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (X0 ◇ sK2)]
    conv => enter [1]; rw [← h54398 sK0 sK2 X0]
  have l19 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l16 sK1 sK2 sK0 X0]
  have l20 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X1) X3]
  have l21 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l14 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [← h54398 sK2 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h54398 X0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l23 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h54398 X0 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK0]
  have l24 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X3]
  have l25 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l24 X0 X1 X2 X3]
  have l26 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l25 X0 X1 X2 X3]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l23 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l1 sK1 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l23 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [← l23 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l30 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [l29 sK0 sK1 sK2 X0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
  have l32 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK0]
  have l33 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
  have l34 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK2 ◇ sK1) ◇ (X1 ◇ (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [h54398 X1 (sK2 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [h54398 X0 sK2 sK1]
  have l35 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [h54398 (sK2 ◇ sK0) sK2 sK1]
  have l36 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK2 ◇ sK0) ◇ (sK1 ◇ sK2))]
  have l37 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ (sK1 ◇ (X1 ◇ (sK2 ◇ (X0 ◇ (sK1 ◇ sK2)))))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [l34 X1 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 sK1 (X1 ◇ (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))))]
  have l38 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l36 sK1 sK2 sK0]
    conv => enter [1]; rw [← l13 sK2 (sK1 ◇ sK2) sK0]
  have l39 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK2 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [l37 X1 sK2 sK1 X0]
    conv => enter [1]; rw [← l26 sK1 sK2 X1 (X0 ◇ (sK1 ◇ sK2))]
  have l40 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l38 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK0]
  have l41 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK2) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [l39 X1 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X1 ◇ (X0 ◇ (sK1 ◇ sK2)))]
  have l42 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l40 sK1 sK2 sK0]
    conv => enter [1]; rw [l17 sK1 sK2 sK0 sK2]
  have l43 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h54398 X1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l41 X1 sK2 sK1 X0]
  have l44 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l18 sK2 sK0 sK1]
    conv => enter [1]; rw [← l42 sK2 sK1 sK0]
  have l45 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X1 ◇ (sK2 ◇ (sK1 ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [l43 X1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 X0]
  have l46 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h54398 sK0 sK2 sK1]
    conv => enter [1]; rw [l44 sK0 sK2 sK1]
  have l47 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l46 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK2 ◇ sK0))]
  have l48 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l47 sK1 sK2 sK0]
  have l49 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l11 sK1 sK2 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l33 sK1 sK2 sK0]
  have l50 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK0)) X0]
  have l51 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l50 sK1 sK2 sK0 X0]
  have l52 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l49 sK1 sK2 sK0]
    conv => enter [1]; rw [l9 sK1 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l23 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [← l52 sK1 sK2 sK0]
  have l54 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [← l30 sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK0))]
  have l55 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 (sK1 ◇ (sK2 ◇ sK0)) sK0 sK1 sK2]
    conv => enter [1]; rw [← l54 sK0 sK1 sK2]
  have l56 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [← l55 sK1 sK2 sK0]
  have l57 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← l56 sK1 sK2 sK0]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l48 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ (sK2 ◇ sK0))]
  have l59 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [← l58 sK0 sK1 sK2]
  have l60 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l59 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l61 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1]; rw [l60 sK1 sK2 sK0]
  have l62 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l61 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 sK1 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l63 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l62 sK1 sK2 sK0]
    conv => enter [1]; rw [← l30 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l64 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l63 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l7 sK1 sK2 sK0]
  have l65 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l64 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l66 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← l65 sK1 sK2 sK0]
  have l67 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l66 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK0))]
  have l68 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l67 sK0 sK1 sK2]
    conv => enter [1]; rw [← l51 sK1 sK2 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l69 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l68 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l31 sK0 sK1 sK2]
  have l70 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l69 sK0 sK1 sK2]
    conv => enter [1]; rw [l23 sK1 sK2 sK0 sK0]
  have l71 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l70 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  have l72 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54398 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h54398 sK0 sK2 sK1]
  have l73 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [← h54398 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) X0]
  have l74 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (sK2 ◇ (sK1 ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l73 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 X0]
  have l75 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l72 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l76 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l45 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l74 sK2 sK0 sK1 X0]
  have l77 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
    conv => enter [1]; rw [← l57 sK0 sK1 sK2]
  have l78 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l76 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l79 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l77 sK0 sK1 sK2]
    conv => enter [1]; rw [← l70 sK0 sK1 sK2]
  have l80 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l78 sK0 sK1 sK2 X0]
  have l81 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l79 sK0 sK1 sK2]
    conv => enter [1]; rw [l69 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l79 sK0 sK1 sK2]
  have l82 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l81 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l83 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l82 sK2 sK0 sK1]
    conv => enter [1]; rw [← l80 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l84 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l61 sK0 sK1 sK2]
    conv => enter [1]; rw [← l83 sK2 sK0 sK1]
  have l85 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l70 sK0 sK1 sK2]
    conv => enter [1]; rw [l84 sK0 sK1 sK2]
  have l86 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l79 sK0 sK1 sK2]
    conv => enter [1]; rw [l85 sK0 sK1 sK2]
  have l87 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l86 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l88 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l86 sK0 sK1 sK2]
  have l89 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [l88 sK1 sK2 sK0]
  have l90 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l87 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l79 sK0 sK1 sK2]
  have l91 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l70 sK0 sK1 sK2]
    conv => enter [1]; rw [l89 sK0 sK1 sK2]
  have l92 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l79 sK0 sK1 sK2]
    conv => enter [1]; rw [l91 sK0 sK1 sK2]
  have l93 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK1)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h54398 (sK2 ◇ sK0) (sK2 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l71 sK2 sK0 sK1]
  have l94 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2, 2]; rw [l79 sK0 sK1 sK2]
    conv => enter [1]; rw [← l93 sK2 sK0 sK1]
  have l95 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l94 sK2 sK0 sK1]
    conv => enter [1]; rw [l21 sK2 sK0 sK2 sK1]
  have l96 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2, 2]; rw [l79 sK0 sK1 sK2]
    conv => enter [1]; rw [← l95 sK2 sK0 sK1]
  have l97 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l90 sK0 sK1 sK2]
    conv => enter [1]; rw [l96 sK2 sK0 sK1]
  have l98 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l90 sK0 sK1 sK2]
    conv => enter [1]; rw [l97 sK2 sK0 sK1]
  have l99 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l98 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54398 (sK2 ◇ sK0) sK1 (sK2 ◇ sK0)]
  have l100 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l92 sK0 sK1 sK2]
    conv => enter [1]; rw [l99 sK1 sK0 sK2]
  have l101 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1, 2]; rw [h54398 X0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (X0 ◇ (sK2 ◇ sK0))]
  have l102 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h54398 X0 sK2 sK0]
    conv => enter [1]; rw [l101 sK2 X0 sK0]
  have l103 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l100 sK0 sK1 sK2]
    conv => enter [1]; rw [← l102 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l103 z x y]
  conv => enter [1]; rw [l79 z x y]

theorem Equation4512_54501_implies_Equation54398 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54501 : Equation54501 G) : Equation54398 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h54501 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X2 ◇ (X0 ◇ X1)) X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54501 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 ((X2 ◇ X3) ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ X1) X3]
  have l4 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1]; rw [← h54501 (X0 ◇ X1) X3 X2]
  have l5 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ X2)]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l6 X0 X1 X2 X3]
  have l8 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h54501 X0 X1 X2]
    conv => enter [1]; rw [l7 X3 X2 X2 (X0 ◇ X1)]
  have l9 : ∀ X1 X3 X2 X0 : G, (X1 ◇ ((X3 ◇ X2) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X1 X3 X2 X0
    conv => enter [1]; rw [h54501 X1 (X3 ◇ X2) X0]
    conv => enter [1, 2]; rw [l7 X0 X1 X3 X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X0 X1 X2]
    conv => enter [1]; rw [← h54501 X2 X1 X0]
  have l11 : ∀ X1 X3 X2 X0 : G, (X1 ◇ ((X3 ◇ X2) ◇ X0)) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := by
    intro X1 X3 X2 X0
    conv => enter [1]; rw [l9 X1 X3 X2 X0]
    conv => enter [1]; rw [← h54501 X1 (X2 ◇ X3) X0]
  have l12 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l8 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l13 : ∀ X1 X3 X2 X0 : G, (X1 ◇ ((X3 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ X0))) := by
    intro X1 X3 X2 X0
    conv => enter [1]; rw [l11 X1 X3 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X3 X0]
  have l14 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (X3 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X2 X3 X0]
    conv => enter [1]; rw [l13 X1 X2 X3 X0]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l10 X2 X1 X0]
    conv => enter [1]; rw [← h54501 X1 X0 X2]
  have l16 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h54501 X1 X2 X0]
    conv => enter [1]; rw [l14 X0 X0 X1 X2]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X0 (X1 ◇ X2) (X1 ◇ X2)]
    conv => enter [1]; rw [← l2 X1 X2 X0 (X1 ◇ X2)]
  have l18 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l12 X1 X0 X1 X2]
    conv => enter [1]; rw [← l17 X0 X1 X2]
  have l19 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l18 X1 X0 X2]
    conv => enter [1]; rw [← h54501 (X1 ◇ X2) (X1 ◇ X2) X0]
  have l20 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l19 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
  have l21 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l20 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X0]
  have l22 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X2 ◇ X0) ◇ X1)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l21 X1 X0 X2]
    conv => enter [1]; rw [← l16 X2 (X2 ◇ X0) X1]
  have l23 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X2 X0 X1]
    conv => enter [1]; rw [← l22 X1 X0 X2]
  have l24 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l16 X0 X2 X1]
    conv => enter [1]; rw [← l23 X2 X0 X1]
  have l25 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l24 X0 X1 X2]
    conv => enter [1]; rw [l10 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [l15 x y z]
  conv => enter [1]; rw [← l25 x z y]
  conv => enter [1]; rw [h54501 x z y]
  conv => enter [1]; rw [l14 y y x z]
  conv => enter [1]; rw [l7 y x y z]

end Semigroup5
