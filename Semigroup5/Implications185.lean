import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54527_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54527 : Equation54527 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1]; rw [h54527 X0 X1 (sK0 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) X0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h54527 X0 X1 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54527 X0 X1 sK0 sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54527 X0 X1 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h54527 X0 X1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ X0)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l11 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h54527 sK2 sK0 sK0 X0]
    conv => enter [1]; rw [l9 sK2 sK0 sK0 sK2]
  have l12 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l11 sK0 sK0 sK2]
  have l13 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK2)]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK0) sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l11 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l16 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l12 sK0 sK2]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l17 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← l12 sK0 sK2]
  have l18 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l12 sK0 sK2]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l12 sK0 sK2]
  have l19 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l18 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK2)]
  have l20 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l17 sK1 sK0 sK2]
    conv => enter [1]; rw [l5 sK1 (sK0 ◇ sK0) sK0 sK2 sK1]
  have l21 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l19 sK0 sK2]
    conv => enter [1]; rw [l16 sK0 sK2 sK1]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK2))]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
  have l25 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l10 sK0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l27 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1]; rw [h54527 X0 sK0 sK0 X1]
  have l28 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 sK0 sK0]
  have l29 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = ((sK0 ◇ sK2) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [l10 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK2 (X0 ◇ sK0)]
  have l30 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l10 sK0 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (X0 ◇ sK0)]
  have l31 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l30 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l9 (sK1 ◇ (sK0 ◇ sK2)) sK1 sK0 sK2]
  have l32 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l29 sK0 sK2 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK2) sK0]
  have l33 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l34 : ∀ sK0 X2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l25 sK0 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l10 sK0 X0 sK0]
  have l35 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l5 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK2 sK1]
    conv => enter [1]; rw [l31 sK1 sK0 sK2]
  have l36 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l32 sK0 sK2]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK2)]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l33 sK0]
  have l38 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l20 sK1 sK0 sK2]
    conv => enter [1]; rw [l35 sK0 sK2 sK1]
  have l39 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l40 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l39 sK0 sK2]
    conv => enter [1]; rw [← l13 sK0 sK2]
  have l41 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l40 sK0 sK2]
    conv => enter [1]; rw [l21 sK0 sK2 sK1]
  have l42 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK0 sK2]
    conv => enter [1]; rw [l41 sK0 sK2 sK1]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l42 sK0 sK1 sK2]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
  have l45 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l46 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1, 2, 2]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54527 (sK1 ◇ (sK0 ◇ sK2)) X1 sK0 X0]
  have l47 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l46 sK0 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l9 (sK1 ◇ (sK0 ◇ sK2)) sK0 sK0 sK2]
  have l48 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0 sK1 sK2]
    conv => enter [1]; rw [← l24 sK0 sK1 sK2]
  have l49 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [← l38 sK1 sK0 sK2]
  have l50 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0 sK0 sK0]
    conv => enter [1]; rw [← l48 sK0 sK0 sK0]
  have l51 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54527 sK0 sK0 sK0 X0]
  have l52 : ∀ X2 sK0 X3 X1 X0 : G, ((X2 ◇ (sK0 ◇ sK0)) ◇ (X3 ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro X2 sK0 X3 X1 X0
    conv => enter [1]; rw [h54527 (X2 ◇ (sK0 ◇ sK0)) X3 sK0 X1]
    conv => enter [1, 2, 2]; rw [← h54527 sK0 X0 sK0 X2]
  have l53 : ∀ sK0 X0 X2 X3 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = ((X2 ◇ (sK0 ◇ sK0)) ◇ (X3 ◇ sK0)) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [l27 sK0 (X0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l52 X2 sK0 X3 sK0 X0]
  have l54 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l51 sK0 X0]
  have l55 : ∀ sK0 X0 X2 X3 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X3 ◇ sK0))) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [l53 sK0 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X2 (sK0 ◇ sK0) (X3 ◇ sK0)]
  have l56 : ∀ sK0 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = (X2 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l55 sK0 X0 X2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 (sK0 ◇ sK0) sK0]
  have l57 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro X2 sK0 X0
    conv => enter [1, 2]; rw [l54 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l56 sK0 X0 X2]
  have l58 : ∀ sK0 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l57 X2 sK0 sK0]
  have l59 : ∀ X2 sK0 sK1 sK2 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro X2 sK0 sK1 sK2
    conv => enter [1]; rw [← l58 sK0 X2]
    conv => enter [1]; rw [l49 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK2]
  have l60 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l59 X0 sK0 X0 X0]
    conv => enter [1]; rw [← l59 X1 sK0 X0 X0]
  have l61 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l10 sK0 X0 sK0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l62 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l60 X0 sK0 X1]
    conv => enter [1]; rw [← l26 sK0 X1]
  have l63 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l50 sK0]
    conv => enter [1]; rw [l60 (sK0 ◇ sK0) sK0 X0]
  have l64 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l63 sK0 sK0]
    conv => enter [1]; rw [l62 sK0 sK0 X1]
  have l65 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l64 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X0 sK0]
  have l66 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1, 2]; rw [l64 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54527 X1 X2 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l67 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l61 X0 sK0]
    conv => enter [1]; rw [l66 X0 sK0 X1 X2]
  have l68 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l65 sK0 X0]
    conv => enter [1]; rw [l67 X0 sK0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l68 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54610 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54610 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 sK2]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK2]
  have l2 : ∀ X1 sK0 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK0 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 X0]
  have l3 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 X2 X0]
  have l4 : ∀ sK3 sK0 sK2 X1 X2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK3 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 X1 X2]
  have l5 : ∀ sK3 sK0 sK2 X1 X0 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK2 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK2) sK3]
  have l6 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK3 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w z (w ◇ x)]

theorem Equation4512_54610_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54610 : Equation54610 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54610 X0 X1 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l4 sK0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0 sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l8 : ∀ sK0 X2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l5 sK0 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X0 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l9 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l13 sK0 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))]
    conv => enter [1]; rw [← h54610 X1 X2 X0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l14 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54665 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54665 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK1 sK0 X2 X0]
  have l4 : ∀ sK4 sK1 sK0 X1 X2 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK4 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK4 sK1 sK0 X1 X2]
  have l5 : ∀ sK4 sK1 sK0 X1 X0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK4]
  have l6 : ∀ X0 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK4 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK1 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK4 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK4 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u (w ◇ x)]

theorem Equation4512_54665_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54665 : Equation54665 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54665 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 sK0 X0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) sK0 X0 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l4 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l12 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l13 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l12 sK1 sK0 sK2]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54430 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54430 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 sK2]
  have l2 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK2]
  have l3 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK2) sK1 sK2 X0]
  have l4 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l2 X0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l3 X1 sK1 sK2 X2 X0]
  have l5 : ∀ sK0 sK1 sK2 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X1 X2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 sK1 sK0 sK2]
  have l7 : ∀ X0 sK1 sK2 X1 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1 sK0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK2) sK1 sK2 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 sK0 sK0]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 (sK1 ◇ sK2) sK0 sK1 sK2 X0]
  have l10 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  have l11 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l9 sK0 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [l10 sK0 sK1 sK2 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

theorem Equation4512_54430_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54430 : Equation54430 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54430 X1 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 X0]
  have l2 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [← l0 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 X0 X2]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X1]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 X0 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 sK0]
  have l7 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54430 X0 sK0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l7 X0 sK0 sK2]
  have l9 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l8 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54449 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54449 G := by
  have l0 : ∀ X0 sK2 sK4 X1 : G, (X0 ◇ (sK2 ◇ sK4)) = (X1 ◇ (sK2 ◇ sK4)) := by
    intro X0 sK2 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK4]
    conv => enter [1]; rw [h4274 sK2 X1 sK4]
  have l1 : ∀ X0 sK2 sK4 X1 : G, (X0 ◇ (sK2 ◇ sK4)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK4))) := by
    intro X0 sK2 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK4]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK4]
  have l2 : ∀ X1 sK2 sK4 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK4) ◇ X2)) = ((sK2 ◇ sK4) ◇ (X0 ◇ (sK2 ◇ sK4))) := by
    intro X1 sK2 sK4 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK4) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK4) sK2 sK4 X0]
  have l3 : ∀ X0 sK2 sK4 X1 X2 : G, (X0 ◇ (sK2 ◇ sK4)) = (X1 ◇ ((sK2 ◇ sK4) ◇ X2)) := by
    intro X0 sK2 sK4 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK4 (sK2 ◇ sK4)]
    conv => enter [1]; rw [← l2 X1 sK2 sK4 X2 X0]
  have l4 : ∀ sK3 sK2 sK4 X1 X2 : G, (sK3 ◇ (sK2 ◇ sK4)) = (X1 ◇ ((sK2 ◇ sK4) ◇ X2)) := by
    intro sK3 sK2 sK4 X1 X2
    conv => enter [1]; rw [l3 sK3 sK2 sK4 X1 X2]
  have l5 : ∀ sK3 sK2 sK4 : G, (sK3 ◇ (sK2 ◇ sK4)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK2 sK4
    conv => enter [1]; rw [← h4274 sK2 sK3 sK4]
  have l6 : ∀ sK3 sK2 sK4 X0 : G, (sK3 ◇ (sK2 ◇ sK4)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK4))) := by
    intro sK3 sK2 sK4 X0
    conv => enter [1]; rw [l4 sK3 sK2 sK4 X0 (sK2 ◇ sK4)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK4) sK2 sK4 sK3]
  have l7 : ∀ sK3 sK2 sK4 X0 X1 : G, (sK3 ◇ (sK2 ◇ sK4)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK3 sK2 sK4 X0 X1
    conv => enter [1]; rw [l5 sK3 sK2 sK4]
    conv => enter [1]; rw [h4274 sK2 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u]
  conv => enter [1]; rw [l6 w y u y]

theorem Equation4512_54449_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54449 : Equation54449 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54449 X0 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [← h54449 X1 sK0 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l0 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK0 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 sK0 X1]
  have l4 : ∀ X2 X0 X3 X1 sK0 : G, (X2 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X0 X3 X1 sK0
    conv => enter [1]; rw [h54449 X2 X0 X3 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 X0 sK0 sK0]
  have l5 : ∀ X0 sK0 X2 X3 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ X3)) := by
    intro X0 sK0 X2 X3
    conv => enter [1, 2]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← l4 X2 X0 X3 X0 sK0]
  have l6 : ∀ sK0 X2 X0 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X0 ◇ X3)) := by
    intro sK0 X2 X0 X3
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [l5 X0 sK0 X2 X3]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h54449 X0 sK0 sK2 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54494 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54494 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 sK3]
  have l1 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK3]
  have l2 : ∀ X1 sK1 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) = ((sK1 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X1 sK1 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 X0]
  have l3 : ∀ X0 sK1 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro X0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK3 (sK1 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK1 sK3 X2 X0]
  have l4 : ∀ sK2 sK1 sK3 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro sK2 sK1 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK3 X1 X2]
  have l5 : ∀ sK2 sK1 sK3 X1 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK3) sK2]
  have l6 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X0 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 sK2]
  have l7 : ∀ X0 sK2 sK1 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK2 sK1 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK1 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK1 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z y z w]
  conv => enter [1]; rw [l6 y z w z]

theorem Equation4512_54494_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54494 : Equation54494 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54494 X0 (sK0 ◇ sK0) sK0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ X1)]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 X0 sK0 X1]
  have l2 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ ((sK0 ◇ sK2) ◇ X0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [← h54494 X1 sK0 sK2 X0]
  have l3 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [← l2 sK2 sK0 X0 X0]
    conv => enter [1]; rw [l2 sK2 sK0 X0 X2]
  have l4 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 X0 sK0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK2)]
  have l5 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [l4 X0 sK0 sK2 X1 X0]
    conv => enter [1, 2]; rw [l3 X0 sK0 sK2 sK1]
  have l6 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l5 sK1 sK0 sK2 X1 sK1]
  have l7 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← l6 sK1 sK0 sK2 sK0]
  have l8 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l7 X0 sK0 sK1 sK2]
  have l9 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← h54494 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54588 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54588 G := by
  have l0 : ∀ X0 sK2 sK4 X1 : G, (X0 ◇ (sK2 ◇ sK4)) = (X1 ◇ (sK2 ◇ sK4)) := by
    intro X0 sK2 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK4]
    conv => enter [1]; rw [h4274 sK2 X1 sK4]
  have l1 : ∀ X0 sK2 sK4 X1 : G, (X0 ◇ (sK2 ◇ sK4)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK4))) := by
    intro X0 sK2 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK4]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK4]
  have l2 : ∀ X1 sK2 sK4 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK4) ◇ X2)) = ((sK2 ◇ sK4) ◇ (X0 ◇ (sK2 ◇ sK4))) := by
    intro X1 sK2 sK4 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK4) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK4) sK2 sK4 X0]
  have l3 : ∀ X0 sK2 sK4 X1 X2 : G, (X0 ◇ (sK2 ◇ sK4)) = (X1 ◇ ((sK2 ◇ sK4) ◇ X2)) := by
    intro X0 sK2 sK4 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK4 (sK2 ◇ sK4)]
    conv => enter [1]; rw [← l2 X1 sK2 sK4 X2 X0]
  have l4 : ∀ sK3 sK2 sK4 X1 X2 : G, (sK3 ◇ (sK2 ◇ sK4)) = (X1 ◇ ((sK2 ◇ sK4) ◇ X2)) := by
    intro sK3 sK2 sK4 X1 X2
    conv => enter [1]; rw [l3 sK3 sK2 sK4 X1 X2]
  have l5 : ∀ sK3 sK2 sK4 X1 X0 : G, (sK3 ◇ (sK2 ◇ sK4)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK2 sK4 X1 X0
    conv => enter [1]; rw [l4 sK3 sK2 sK4 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK4) sK3]
  have l6 : ∀ sK3 sK2 sK4 X0 : G, (sK3 ◇ (sK2 ◇ sK4)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK4))) := by
    intro sK3 sK2 sK4 X0
    conv => enter [1]; rw [l4 sK3 sK2 sK4 X0 (sK2 ◇ sK4)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK4) sK2 sK4 sK3]
  have l7 : ∀ X0 sK3 sK2 sK4 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK2 ◇ sK4)) := by
    intro X0 sK3 sK2 sK4
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK2 sK4 X0 X0]
  have l8 : ∀ X1 X0 X2 sK3 sK2 sK4 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK2 ◇ sK4)) := by
    intro X1 X0 X2 sK3 sK2 sK4
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK3 sK2 sK4]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z y w u]
  conv => enter [1]; rw [l6 y w u w]

@[equational_result]
theorem Equation54588_implies_Equation4274 (G : Type*) [Magma G] (h54588 : Equation54588 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X5 ◇ (X1 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54588 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54588 X5 X1 X6 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x x y z]

@[equational_result]
theorem Equation4274_implies_Equation54528 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54528 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 sK3]
  have l1 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK3]
  have l2 : ∀ X1 sK1 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) = ((sK1 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X1 sK1 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 X0]
  have l3 : ∀ X0 sK1 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro X0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK3 (sK1 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK1 sK3 X2 X0]
  have l4 : ∀ sK2 sK1 sK3 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro sK2 sK1 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK3 X1 X2]
  have l5 : ∀ sK2 sK1 sK3 X1 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK3) sK2]
  have l6 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X0 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 sK2]
  have l7 : ∀ X0 sK2 sK1 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK2 sK1 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK1 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK1 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w z y]
  conv => enter [1]; rw [l6 w z y z]

theorem Equation4512_54528_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54528 : Equation54528 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54528 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ sK0) ◇ X1)]
  have l5 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h54528 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h54528 X2 sK0 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54528 X0 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54528 X0 sK0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [h54528 X0 sK0 sK0 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54528 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0]
  have l10 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l8 X0 sK0 X1]
  have l11 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l5 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l12 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l5 (sK0 ◇ sK2) sK0 X0]
  have l13 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l4 sK1 X0 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 sK2 X0]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l11 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l5 X0 sK0 sK0]
  have l15 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l13 sK0 X0 sK0 sK2]
    conv => enter [1]; rw [l7 (sK0 ◇ (sK0 ◇ sK2)) sK0 sK2]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l14 sK0 sK0 X1]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l15 sK0 X0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [l3 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l19 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l22 : ∀ sK0 X0 X1 : G, (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l21 sK0 X0]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l22 sK0 X0 X1]
  have l24 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [l23 sK0 sK0 X1]
  have l25 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 2]; rw [l24 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54528 X2 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [l25 X0 sK0 X2 X1]
  intro x y z
  conv => enter [1]; rw [l26 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54611 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54611 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 sK3]
  have l1 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK3]
  have l2 : ∀ X1 sK1 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) = ((sK1 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X1 sK1 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 X0]
  have l3 : ∀ X0 sK1 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro X0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK3 (sK1 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK1 sK3 X2 X0]
  have l4 : ∀ sK2 sK1 sK3 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro sK2 sK1 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK3 X1 X2]
  have l5 : ∀ sK2 sK1 sK3 X1 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK3) sK2]
  have l6 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X0 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 sK2]
  have l7 : ∀ X0 sK2 sK1 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK2 sK1 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK1 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK1 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z z w y]
  conv => enter [1]; rw [l6 z w y w]

theorem Equation4512_54611_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54611 : Equation54611 G) : Equation4274 G := by
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
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54611 X0 X1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X1)]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
  have l11 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54611 X0 sK0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l4 (sK0 ◇ sK2) sK0 sK0]
    conv => enter [1]; rw [← l11 X0 sK0 sK2]
  have l13 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l12 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54666 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54666 G := by
  have l0 : ∀ X0 sK2 sK4 X1 : G, (X0 ◇ (sK2 ◇ sK4)) = (X1 ◇ (sK2 ◇ sK4)) := by
    intro X0 sK2 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK4]
    conv => enter [1]; rw [h4274 sK2 X1 sK4]
  have l1 : ∀ X0 sK2 sK4 X1 : G, (X0 ◇ (sK2 ◇ sK4)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK4))) := by
    intro X0 sK2 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK4]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK4]
  have l2 : ∀ X1 sK2 sK4 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK4) ◇ X2)) = ((sK2 ◇ sK4) ◇ (X0 ◇ (sK2 ◇ sK4))) := by
    intro X1 sK2 sK4 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK4) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK4) sK2 sK4 X0]
  have l3 : ∀ X0 sK2 sK4 X1 X2 : G, (X0 ◇ (sK2 ◇ sK4)) = (X1 ◇ ((sK2 ◇ sK4) ◇ X2)) := by
    intro X0 sK2 sK4 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK4 (sK2 ◇ sK4)]
    conv => enter [1]; rw [← l2 X1 sK2 sK4 X2 X0]
  have l4 : ∀ sK3 sK2 sK4 X1 X2 : G, (sK3 ◇ (sK2 ◇ sK4)) = (X1 ◇ ((sK2 ◇ sK4) ◇ X2)) := by
    intro sK3 sK2 sK4 X1 X2
    conv => enter [1]; rw [l3 sK3 sK2 sK4 X1 X2]
  have l5 : ∀ sK3 sK2 sK4 X1 X0 : G, (sK3 ◇ (sK2 ◇ sK4)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK2 sK4 X1 X0
    conv => enter [1]; rw [l4 sK3 sK2 sK4 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK4) sK3]
  have l6 : ∀ sK3 sK2 sK4 X0 : G, (sK3 ◇ (sK2 ◇ sK4)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK4))) := by
    intro sK3 sK2 sK4 X0
    conv => enter [1]; rw [l4 sK3 sK2 sK4 X0 (sK2 ◇ sK4)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK4) sK2 sK4 sK3]
  have l7 : ∀ X0 sK3 sK2 sK4 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK2 ◇ sK4)) := by
    intro X0 sK3 sK2 sK4
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK2 sK4 X0 X0]
  have l8 : ∀ X1 X0 X2 sK3 sK2 sK4 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK2 ◇ sK4)) := by
    intro X1 X0 X2 sK3 sK2 sK4
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK3 sK2 sK4]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z u w y]
  conv => enter [1]; rw [l6 u w y w]

theorem Equation4512_54666_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54666 : Equation54666 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54666 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X1)]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54666 X0 X1 X2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ X1)]
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54666 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ sK0) ◇ X1)]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l9 : ∀ X2 sK0 sK2 X1 : G, (X2 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X2 sK0 sK2 X1
    conv => enter [1]; rw [h54666 X2 sK0 sK2 X2 X1]
    conv => enter [1]; rw [l7 X2 X1 (X2 ◇ sK0) sK0]
  have l10 : ∀ X2 sK0 X1 : G, (X2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X2 sK0 X1
    conv => enter [1]; rw [h54666 X2 sK0 sK0 X2 X1]
    conv => enter [1]; rw [l7 X2 X1 (X2 ◇ sK0) sK0]
  have l11 : ∀ sK0 X2 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [← l6 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← l9 X2 sK0 sK2 sK0]
  have l12 : ∀ sK0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [← l6 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← l10 X2 sK0 sK0]
  have l13 : ∀ sK0 X2 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X2 sK2]
  have l14 : ∀ sK0 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 sK0 X2]
  have l15 : ∀ sK0 X2 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l13 sK0 X2 sK2]
  have l16 : ∀ sK0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l14 sK0 X2]
  have l17 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
    conv => enter [1]; rw [l15 sK0 X0 sK2]
  have l18 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l17 sK1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l19 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l18 sK1 sK0 sK2 sK1 X1]
    conv => enter [1]; rw [l8 sK1 X1 (sK0 ◇ sK2) sK0]
  have l20 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l19 sK1 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l20 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54531 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54531 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 sK2]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK2]
  have l2 : ∀ X1 sK0 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK0 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 X0]
  have l3 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 X2 X0]
  have l4 : ∀ sK1 sK0 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK1 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 X1 X2]
  have l5 : ∀ sK1 sK0 sK2 X1 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK2) sK1]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 sK1]
  have l7 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK2 X0 X0]
  have l8 : ∀ X1 X0 X2 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK1 sK0 sK2]
  have l9 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK2 ◇ sK4))) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK2]
    conv => enter [1, 2]; rw [l8 sK1 sK0 sK2 sK3 sK2 sK4]
  intro x y z w u
  conv => enter [1]; rw [l9 x y z w u]

theorem Equation4512_54531_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54531 : Equation54531 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54531 sK0 sK0 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [h54531 sK0 (sK0 ◇ sK0) sK0 X0 sK0]
  have l3 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h54531 sK1 (sK0 ◇ sK2) sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0 sK0]
  have l9 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 X1 sK2
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h54531 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 X1 sK2]
  have l10 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54531 sK0 sK0 sK0 X0 sK2]
  have l11 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h54531 sK0 sK2 sK0 X0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 sK0]
  have l12 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK0 sK2]
    conv => enter [1]; rw [l11 sK0 sK0 sK2]
  have l13 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l9 X0 sK0 X0 sK2]
    conv => enter [1]; rw [l11 sK0 X0 sK2]
  have l14 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 sK2]
  have l15 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l8 sK0]
    conv => enter [1]; rw [l13 X0 sK0 sK2]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [← l15 X0 sK0 sK0]
  have l17 : ∀ X0 X1 sK0 X2 X3 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X2 ◇ (X3 ◇ X0)) := by
    intro X0 X1 sK0 X2 X3
    conv => enter [1, 2, 2]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← h54531 X2 X3 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ X0 sK0 X2 X3 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X3 ◇ X0)) := by
    intro X0 sK0 X2 X3
    conv => enter [1, 2]; rw [l16 sK0 X0]
    conv => enter [1]; rw [l17 X0 X0 sK0 X2 X3]
  have l19 : ∀ sK0 X2 X3 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X3 ◇ X0)) := by
    intro sK0 X2 X3 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [l18 X0 sK0 X2 X3]
  intro x y z
  conv => enter [1]; rw [l19 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54614 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54614 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK3]
    conv => enter [1]; rw [h4274 sK0 X1 sK3]
  have l1 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK3]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK3]
  have l2 : ∀ X1 sK0 sK3 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) = ((sK0 ◇ sK3) ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X1 sK0 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 X0]
  have l3 : ∀ X0 sK0 sK3 X1 X2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro X0 sK0 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 (sK0 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 X2 X0]
  have l4 : ∀ sK1 sK0 sK3 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro sK1 sK0 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK3 X1 X2]
  have l5 : ∀ sK1 sK0 sK3 X1 X0 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK3) sK1]
  have l6 : ∀ X0 sK1 sK0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK1 sK0 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro X1 X0 X2 sK1 sK0 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w z (w ◇ u)]

theorem Equation4512_54614_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54614 : Equation54614 G) : Equation4274 G := by
  have l0 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54614 X1 X2 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 X2 X0 sK0 sK1 sK2 : G, (X1 ◇ (X2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54614 X1 X2 X0 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 X0 (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l2 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l1 X1 X2 X0 sK0 X1 X1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ X1)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l3 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [← h54614 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 X2 X0 sK0]
  have l4 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [← h54614 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X1 X2 X0]
  have l5 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h54614 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X1 X2 X0]
  have l6 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X1 X2 X0]
  have l7 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l6 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l6 sK0 X0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l7 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54670 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54670 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK2 sK0 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X1 X2]
  have l5 : ∀ sK2 sK0 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l7 x y z w u (w ◇ v)]

@[equational_result]
theorem Equation54670_implies_Equation4274 (G : Type*) [Magma G] (h54670 : Equation54670 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 X6 X7 X8 : G, (X0 ◇ (X1 ◇ X2)) = (X6 ◇ (X7 ◇ X8)) := by
    intro X0 X1 X2 X6 X7 X8
    conv => enter [1]; rw [h54670 X0 X1 X2 X0 X0 X0]
    conv => enter [1]; rw [← h54670 X6 X7 X8 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54390 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54390 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 sK2]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK2]
  have l2 : ∀ X1 sK0 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK0 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 X0]
  have l3 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 X2 X0]
  have l4 : ∀ sK1 sK0 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK1 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 X1 X2]
  have l5 : ∀ sK1 sK0 sK2 X1 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK2) sK1]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 sK1]
  have l7 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK2 X0 X0]
  have l8 : ∀ X1 X0 X2 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK1 sK0 sK2]
  have l9 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK0]
    conv => enter [1, 2]; rw [l8 sK1 sK0 sK2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_54390_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54390 : Equation54390 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l7 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l12 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l13 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [h54390 (sK0 ◇ sK0) sK0 (X0 ◇ X1)]
  have l15 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ sK0)]
  have l16 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [l11 sK0 sK0]
  have l17 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l18 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l17 sK0 X0 X1]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l18 sK0 X0 X1]
  have l20 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 (sK0 ◇ sK2)]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0]
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
  have l22 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l23 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 sK1 (sK0 ◇ sK2)]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 sK0 sK0]
    conv => enter [1]; rw [← l24 sK0 X0 sK0 sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l27 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l28 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 sK2 X0]
  have l30 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l29 sK0 sK2 X0]
    conv => enter [1]; rw [h54390 sK0 sK0 ((sK0 ◇ sK2) ◇ X0)]
  have l31 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l30 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l31 sK0 sK2 X0]
  have l33 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l32 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 sK0 sK0]
  have l34 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [← l28 sK0]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l34 sK0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l35 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [← l26 sK0 X0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [← l37 sK0 X0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l38 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ X0)]
  have l41 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l40 sK0 X0]
  have l42 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h54390 X1 (sK0 ◇ sK0) (sK0 ◇ X0)]
  have l43 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l41 sK0 X0]
    conv => enter [1]; rw [h54390 X0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l44 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54390 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l45 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54390 sK0 sK0 X0]
  have l46 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [h54390 sK0 X0 X1]
  have l47 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l46 sK0 X0 X1]
    conv => enter [1]; rw [h54390 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ (sK0 ◇ X0))]
  have l48 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l44 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l50 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l42 X1 sK0 X0]
    conv => enter [1]; rw [← l43 X1 sK0]
  have l51 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l47 sK0 X0 X1]
    conv => enter [1, 2]; rw [l19 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l52 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l53 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l49 sK0 X0]
    conv => enter [1]; rw [← l5 sK0]
  have l54 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l51 sK0 X0 X1]
    conv => enter [1]; rw [l50 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l55 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l52 sK0 X0]
    conv => enter [1]; rw [← l5 sK0]
  have l56 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [l54 sK0 X0 sK0]
  have l57 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l55 sK0 sK0]
  have l58 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
    conv => enter [1]; rw [l55 sK0 sK2]
  have l59 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l57 sK0]
    conv => enter [1]; rw [← l58 sK0 sK2]
  have l60 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54390 sK0 X0 X1]
    conv => enter [1, 2]; rw [l53 sK0 X0]
  have l61 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l56 sK0 X0]
    conv => enter [1]; rw [← l60 sK0 X0 X1]
  have l62 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l58 sK0 sK2]
    conv => enter [1]; rw [l61 sK0 X0 X1]
  have l63 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l62 sK0 sK0 X0 X1]
  have l64 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l63 sK0 X0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54390 X0 sK0 X1]
  intro x y z
  conv => enter [1]; rw [l64 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54546 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54546 G := by
  have l0 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK1]
    conv => enter [1]; rw [h4274 sK2 X1 sK1]
  have l1 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK1]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK1]
  have l2 : ∀ X1 sK2 sK1 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X2)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X1 sK2 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK1) sK2 sK1 X0]
  have l3 : ∀ X0 sK2 sK1 X1 X2 : G, (X0 ◇ (sK2 ◇ sK1)) = (X1 ◇ ((sK2 ◇ sK1) ◇ X2)) := by
    intro X0 sK2 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK2 sK1 X2 X0]
  have l4 : ∀ sK2 sK1 X1 X2 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X1 ◇ ((sK2 ◇ sK1) ◇ X2)) := by
    intro sK2 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK2 sK1 X1 X2]
  have l5 : ∀ sK2 sK1 X1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK1) sK2]
  have l6 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK1) sK2 sK1 sK2]
  have l7 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l8 x y z x w]
  conv => enter [1]; rw [l6 x w w]

theorem Equation4512_54546_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54546 : Equation54546 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54546 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l2 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54546 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [← l5 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54432 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54432 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK2 sK0 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X1 X2]
  have l5 : ∀ sK2 sK0 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z y z (z ◇ y)]

theorem Equation4512_54432_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54432 : Equation54432 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54432 X0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h54432 X1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54432 X0 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54432 X0 (sK0 ◇ sK0) sK0]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54432 (X2 ◇ X3) X0 X1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ X1)]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l15 sK0 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l11 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X1]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X0]
  have l22 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54432 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l11 sK0 X0]
  have l23 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l23 sK0 X0 X1]
  have l25 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l22 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l26 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l25 X1 sK0 X0]
  have l27 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l26 sK0 X1 X0]
    conv => enter [1, 2]; rw [l10 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l28 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l27 X1 sK0 X0]
    conv => enter [1, 2]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l28 X1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l30 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1, 2]; rw [l19 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l29 X1 sK0 X0]
  have l31 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l24 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l30 sK0 X1 X0]
  have l32 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l32 sK0 X0 X1]
  have l34 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l33 sK0 X0 X1]
  have l35 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l20 (X0 ◇ X1) sK0 X2]
  have l36 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l35 X0 X1 sK0 sK0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0 sK0]
  have l38 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54432 X0 sK0 sK2]
    conv => enter [1, 2]; rw [h54432 sK2 sK2 sK0]
  have l39 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l38 X0 sK0 sK2]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ sK2) sK0 sK2]
  have l40 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l39 X0 sK0 sK2]
    conv => enter [1, 2]; rw [l10 (sK0 ◇ sK2) (sK0 ◇ sK2) sK0]
  have l41 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [l31 sK0 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l40 X0 sK0 sK2]
  have l42 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l34 sK0 sK0 sK0]
    conv => enter [1]; rw [l41 sK0 X0 sK2]
  have l43 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l37 sK0 sK0]
    conv => enter [1]; rw [l42 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l43 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54456 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54456 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK1 sK0 X2 X0]
  have l4 : ∀ sK3 sK1 sK0 X1 X2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK3 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK1 sK0 X1 X2]
  have l5 : ∀ sK3 sK1 sK0 X1 X0 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK3]
  have l6 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK3 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l7 x y z y w (w ◇ y)]

theorem Equation4512_54456_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54456 : Equation54456 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54456 X0 sK0 X1 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK0 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l6 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54577 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54577 G := by
  have l0 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK1]
    conv => enter [1]; rw [h4274 sK2 X1 sK1]
  have l1 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK1]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK1]
  have l2 : ∀ X1 sK2 sK1 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X2)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X1 sK2 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK1) sK2 sK1 X0]
  have l3 : ∀ X0 sK2 sK1 X1 X2 : G, (X0 ◇ (sK2 ◇ sK1)) = (X1 ◇ ((sK2 ◇ sK1) ◇ X2)) := by
    intro X0 sK2 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK2 sK1 X2 X0]
  have l4 : ∀ sK2 sK1 X1 X2 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X1 ◇ ((sK2 ◇ sK1) ◇ X2)) := by
    intro sK2 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK2 sK1 X1 X2]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4274 sK2 sK2 sK1]
  have l6 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK1) sK2 sK1 sK2]
  have l7 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l5 sK2 sK1]
    conv => enter [1]; rw [h4274 sK2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [← l7 y w x z]
  conv => enter [1]; rw [l6 y w w]

theorem Equation4512_54577_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54577 : Equation54577 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54577 X0 sK0 X1 sK0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← h54577 X0 (sK0 ◇ sK0) X1 sK0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54577 X0 sK0 X1 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l8 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54577 X1 sK0 (sK0 ◇ sK0) X0]
  have l16 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 X1 sK2
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54577 X1 sK0 sK2 X0]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54577 X1 sK0 sK0 X0]
  have l18 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l4 sK0]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0 X0 X1]
  have l22 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l19 sK0 X0 X1]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0 sK0 sK0]
    conv => enter [1]; rw [← l21 sK0 sK0 sK0]
  have l24 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [← l16 X0 sK0 X0 sK2]
    conv => enter [1]; rw [l16 X0 sK0 X2 sK2]
  have l25 : ∀ X0 sK0 X2 X1 sK2 : G, ((X0 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ X2) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 sK0 X2 X1 sK2
    conv => enter [1, 1]; rw [l16 X0 sK0 X1 sK2]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK2) X2]
  have l26 : ∀ X0 sK0 X2 X1 sK2 : G, (X0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 sK0 X2 X1 sK2
    conv => enter [1]; rw [h4512 X0 ((sK0 ◇ sK0) ◇ X0) X2]
    conv => enter [1]; rw [l25 X0 sK0 X2 X1 sK2]
  have l27 : ∀ X0 sK0 X2 X1 sK2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X2))) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 sK0 X2 X1 sK2
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ sK0) X0 X2]
    conv => enter [1]; rw [l26 X0 sK0 X2 X1 sK2]
  have l28 : ∀ sK0 X1 sK2 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK0 X1 sK2 X2
    conv => enter [1]; rw [l22 sK0 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [l27 sK0 sK0 X2 X1 sK2]
  have l29 : ∀ sK0 X1 sK2 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK0 X1 sK2 X2
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l28 sK0 X1 sK2 X2]
  have l30 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l24 X0 sK0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK2)]
  have l31 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l24 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [← l30 X0 sK0 sK2 X1 X1]
  have l32 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [← l31 X1 sK1 sK0 sK2 sK1]
  have l33 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK2) X1]
    conv => enter [1, 1]; rw [l24 X0 sK0 sK2 sK1]
  have l34 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [← l15 (sK0 ◇ sK2) sK0 X0]
    conv => enter [1, 2]; rw [l24 (sK0 ◇ sK0) sK0 sK2 sK1]
  have l35 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l32 sK1 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l34 X0 sK0 sK2 sK1]
  have l36 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l29 sK0 sK0 sK2 X1]
    conv => enter [1]; rw [l33 sK0 sK0 sK2 X1 sK1]
  have l37 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l35 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l36 sK0 sK1 sK2 X1]
  have l38 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l37 sK1 sK0 sK2 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [l17 (sK1 ◇ (sK0 ◇ sK2)) sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l38 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54608 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54608 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 sK2]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK2]
  have l2 : ∀ X1 sK0 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK0 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 X0]
  have l3 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 X2 X0]
  have l4 : ∀ sK3 sK0 sK2 X1 X2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK3 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 X1 X2]
  have l5 : ∀ sK3 sK0 sK2 X1 X0 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK2 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK2) sK3]
  have l6 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK3 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w z (z ◇ w)]

theorem Equation4512_54608_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54608 : Equation54608 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54608 X0 X1 (sK0 ◇ sK0) sK0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54608 X0 X1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54608 X1 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54608 X0 X1 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l12 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK0]
  have l13 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l8 X1 sK0 X1]
    conv => enter [1]; rw [← l8 X0 sK0 X1]
  have l14 : ∀ X2 X3 X1 sK0 X0 : G, (X2 ◇ (X3 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X3 X1 sK0 X0
    conv => enter [1]; rw [h54608 X2 X3 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l13 X1 sK0 X0]
  have l15 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h4512 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l13 (X1 ◇ X2) sK0 X0]
  have l16 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l15 X1 X2 sK0 sK0]
  have l17 : ∀ X2 X3 X1 sK0 : G, (X2 ◇ (X3 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X3 X1 sK0
    conv => enter [1]; rw [l14 X2 X3 X1 sK0 X2]
    conv => enter [1, 2]; rw [← l9 sK0 X1 X2]
  have l18 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l16 sK0 X1 sK0]
  have l19 : ∀ sK0 X2 X3 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X3 ◇ X1)) := by
    intro sK0 X2 X3 X1
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l17 X2 X3 X1 sK0]
  have l20 : ∀ sK0 X2 X3 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X3 ◇ X1)) := by
    intro sK0 X2 X3 X1
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l19 sK0 X2 X3 X1]
  intro x y z
  conv => enter [1]; rw [l20 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54674 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54674 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK1 sK0 X2 X0]
  have l4 : ∀ sK4 sK1 sK0 X1 X2 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK4 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK4 sK1 sK0 X1 X2]
  have l5 : ∀ sK4 sK1 sK0 X1 X0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK4]
  have l6 : ∀ X0 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK4 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK1 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK4 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK4 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u (u ◇ w)]

theorem Equation4512_54674_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54674 : Equation54674 G) : Equation4274 G := by
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
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54674 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK2) ◇ (sK2 ◇ sK0)) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [h54674 X0 X1 X2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK2 ◇ sK0)]
  have l5 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK1)) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54674 X0 X1 X2 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) ((sK0 ◇ sK2) ◇ sK1)]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l7 : ∀ sK1 sK0 sK2 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK1)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2 X2
    conv => enter [1]; rw [← l5 sK1 sK1 (sK1 ◇ sK1) sK1 sK0 sK2]
    conv => enter [1]; rw [← h54674 X2 sK0 sK2 sK1 sK1]
  have l8 : ∀ sK1 sK0 sK2 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK1)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X2
    conv => enter [1]; rw [← l5 sK1 sK1 (sK1 ◇ sK1) sK1 sK0 sK2]
    conv => enter [1]; rw [← h54674 X2 sK0 sK0 sK1 sK1]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l6 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l10 : ∀ sK0 sK2 X2 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X2
    conv => enter [1]; rw [l4 (sK0 ◇ sK2) sK2 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l7 sK0 sK0 sK2 X2]
  have l11 : ∀ sK0 sK2 X2 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X2
    conv => enter [1]; rw [l4 (sK0 ◇ sK2) sK2 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l8 sK0 sK0 sK2 X2]
  have l12 : ∀ sK0 X2 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [← l9 (sK0 ◇ sK2) sK2 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK2 X2]
  have l13 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 X2]
  have l14 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
    conv => enter [1]; rw [l13 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l14 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54389 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54389 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X1 X0 X2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z x]
  conv => enter [1]; rw [h4274 x y (x ◇ x)]

theorem Equation4512_54389_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54389 : Equation54389 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l7 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [h54389 (sK0 ◇ sK0) sK0 (X0 ◇ X1)]
  have l13 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1, 2]; rw [l7 sK0]
  have l16 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l16 sK0 X0 X1]
  have l18 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 sK2 X0]
  have l19 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK2 X0]
    conv => enter [1]; rw [h54389 sK0 sK0 ((sK0 ◇ sK2) ◇ X0)]
  have l20 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l19 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 sK2 X0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 sK0 sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l22 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l23 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1, 2]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [h54389 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l29 sK0 X0]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54389 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54389 sK0 sK0 X0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54389 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [h54389 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l37 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l32 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l40 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l38 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 X0]
    conv => enter [1]; rw [← l5 sK0]
  have l42 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l41 sK0 sK0]
  have l43 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l40 sK0 X0]
  have l44 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54389 X0 sK0 X1]
    conv => enter [1]; rw [l37 sK0 X0 (X0 ◇ X0)]
  have l45 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l43 sK0 X0]
    conv => enter [1]; rw [← l44 X0 sK0 X1]
  intro x y z
  conv => enter [1]; rw [l45 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54466 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54466 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X1 X0 X2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z x]
  conv => enter [1]; rw [h4274 x z (x ◇ x)]

theorem Equation4512_54466_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54466 : Equation54466 G) : Equation4274 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54466 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54466 X0 X1 X2]
    conv => enter [1]; rw [← h54466 X0 X3 X2]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [h54466 sK0 X1 X0]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l2 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l0 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l4 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l5 sK0 X1 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l8 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [l4 sK0 sK2 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ sK2)]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l22 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l21 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← h54466 (sK0 ◇ (sK0 ◇ sK0)) X1 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l22 X0 sK0 sK0]
  have l24 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l1 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l21 sK0 X2]
  have l25 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l24 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l23 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l25 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54543 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54543 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4274 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h4274 sK2 X0 (sK2 ◇ sK2)]
  have l2 : ∀ X1 X0 X2 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z x]
  conv => enter [1]; rw [h4274 x w (x ◇ x)]

theorem Equation4512_54543_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54543 : Equation54543 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 X4 X5 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X4 ◇ X5)) := by
    intro X0 X1 X2 X4 X5
    conv => enter [1]; rw [h54543 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54543 X0 X4 X5 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54543 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 X0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l2 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 X0 sK0]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54543 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l6 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 X0 sK0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54458 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54458 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4274 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h4274 sK2 X0 (sK2 ◇ sK2)]
  have l2 : ∀ X1 X0 X2 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1]; rw [h4274 w y (w ◇ w)]

theorem Equation4512_54458_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54458 : Equation54458 G) : Equation4274 G := by
  have l0 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h54458 X1 X0 X2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l0 X1 X0 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X1 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l1 X0 sK0 sK0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← l1 X0 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l2 X0 sK0 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54488 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54488 G := by
  intro x y z
  conv => enter [1]; rw [← h4274 y x z]
  conv => enter [1]; rw [h4274 y z (y ◇ y)]

theorem Equation4512_54488_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54488 : Equation54488 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54488 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54488 X1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54488 X0 X1 X2]
    conv => enter [1]; rw [← h54488 X3 X1 X2]
  have l5 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54488 X1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X3 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54488 (X2 ◇ X3) X1 X0]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X0)]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h54488 X0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0 sK0 sK2 sK0]
    conv => enter [1]; rw [← h54488 X0 sK0 sK2]
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l5 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l3 X1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l2 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0]
  have l13 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 X0 sK2]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l9 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l16 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l13 sK0 X0 sK2]
  have l17 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l14 X1 sK0 X0]
  have l18 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l17 sK0 X1 X0]
  have l19 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l18 sK0 X1 X0]
    conv => enter [1]; rw [l11 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1, 2]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l19 X1 sK0 X0]
  have l21 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l20 sK0 X1 X0]
  have l22 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l21 sK0 X1 X0]
  have l23 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
    conv => enter [1]; rw [l15 sK0 X0]
  have l24 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [← l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l24 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l22 sK0 sK0 X0]
  have l26 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l23 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0 sK2 X0]
  have l27 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l4 X0 sK0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l28 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [l4 X0 X1 X2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l26 sK1 sK0 sK2 (X1 ◇ X2)]
  have l29 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l28 sK1 sK0 sK2 sK1 sK0 X1]
    conv => enter [1]; rw [l27 sK1 sK0 X1]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l29 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l30 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54575 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54575 G := by
  intro x y z w
  conv => enter [1]; rw [← h4274 y x z]
  conv => enter [1]; rw [h4274 y w (y ◇ y)]

theorem Equation4512_54575_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54575 : Equation54575 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 X1 sK2
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54575 X1 sK0 sK2 X0]
  have l1 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [← l0 X0 sK0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54575 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54535 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54535 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4274 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h4274 sK2 X0 (sK2 ◇ sK2)]
  have l2 : ∀ X1 X0 X2 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1]; rw [h4274 w z (w ◇ w)]

theorem Equation4512_54535_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54535 : Equation54535 G) : Equation4274 G := by
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
  have l8 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54535 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54535 X0 X1 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l11 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l8 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l5 sK0]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l11 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l11 sK0 sK0 X0 sK0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) sK0 X0 sK0]
  have l18 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l17 sK0 sK2]
    conv => enter [1]; rw [← l11 X0 sK0 sK2 sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l16 sK0 X0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 sK0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l15 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [← l22 sK0 X0]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK2]
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54675 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54675 G := by
  have l0 : ∀ X0 X1 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro X0 X1 sK3
    conv => enter [1]; rw [h4274 X0 X1 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 sK3 X0 sK3]
  have l1 : ∀ X0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3
    conv => enter [1]; rw [l0 X0 X0 sK3]
    conv => enter [1]; rw [← h4274 sK3 X0 (sK3 ◇ sK3)]
  have l2 : ∀ X1 X0 X2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro X1 X0 X2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z u]
  conv => enter [1]; rw [h4274 u w (u ◇ u)]

theorem Equation4512_54675_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54675 : Equation54675 G) : Equation4274 G := by
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
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54675 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [h54675 X0 X1 X2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK2 ◇ sK2)]
  have l5 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54675 X0 X1 X2 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l7 : ∀ sK1 sK0 sK2 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2 X2
    conv => enter [1]; rw [← l5 sK1 sK1 (sK1 ◇ sK1) sK1 sK0 sK2]
    conv => enter [1]; rw [← h54675 X2 sK0 sK2 sK1 sK1]
  have l8 : ∀ sK1 sK0 sK2 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X2
    conv => enter [1]; rw [← l5 sK1 sK1 (sK1 ◇ sK1) sK1 sK0 sK2]
    conv => enter [1]; rw [← h54675 X2 sK0 sK0 sK1 sK1]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l6 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l10 : ∀ sK0 sK2 X2 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X2
    conv => enter [1]; rw [l4 (sK0 ◇ sK2) sK2 sK2 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l7 sK0 sK0 sK2 X2]
  have l11 : ∀ sK0 sK2 X2 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X2
    conv => enter [1]; rw [l4 (sK0 ◇ sK2) sK2 sK2 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l8 sK0 sK0 sK2 X2]
  have l12 : ∀ sK0 X2 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [← l9 (sK0 ◇ sK2) sK2 sK2 sK0]
    conv => enter [1]; rw [l10 sK0 sK2 X2]
  have l13 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 X2]
  have l14 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
    conv => enter [1]; rw [l13 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l14 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54392 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54392 G := by
  have l0 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 sK3]
  have l1 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK3]
  have l2 : ∀ X1 sK2 sK3 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X1 sK2 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK3) sK2 sK3 X0]
  have l3 : ∀ X0 sK2 sK3 X1 X2 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro X0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK2 sK3 X2 X0]
  have l4 : ∀ sK2 sK3 X1 X2 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK2 sK3 X1 X2]
  have l5 : ∀ sK2 sK3 X1 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK3) sK2]
  have l6 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK3) sK2 sK3 sK2]
  have l7 : ∀ X0 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z x w]
  conv => enter [1]; rw [l6 x w y]

theorem Equation4512_54392_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54392 : Equation54392 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54392 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54392 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← l0 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1]
  have l4 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l3 sK0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l4 sK0 X0]
    conv => enter [1]; rw [l4 sK0 X1]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l6 sK0 (X0 ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← h54392 X0 (sK0 ◇ sK0) X2 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l7 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2]; rw [← l8 sK0]
  have l12 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h54392 X1 X0 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l11 sK0 X1]
  have l13 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l12 X1 X0 X2 sK0]
    conv => enter [1, 2]; rw [← l11 sK0 X1]
  have l14 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l13 X1 X0 X2 sK0]
    conv => enter [1]; rw [← l11 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l14 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54544 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54544 G := by
  have l0 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 sK3]
  have l1 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK3]
  have l2 : ∀ X1 sK2 sK3 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X1 sK2 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK3) sK2 sK3 X0]
  have l3 : ∀ X0 sK2 sK3 X1 X2 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro X0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK2 sK3 X2 X0]
  have l4 : ∀ sK2 sK3 X1 X2 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK2 sK3 X1 X2]
  have l5 : ∀ sK2 sK3 X1 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK3) sK2]
  have l6 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK3) sK2 sK3 sK2]
  have l7 : ∀ X0 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z x y]
  conv => enter [1]; rw [l6 x y w]

theorem Equation4512_54544_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54544 : Equation54544 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54544 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l2 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ X1) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 X1 sK0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54544 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (X0 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [← l8 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54469 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54469 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK2 sK0 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X1 X2]
  have l5 : ∀ sK2 sK0 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z x (x ◇ w)]

theorem Equation4512_54469_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54469 : Equation54469 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (X2 ◇ X1)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [h54469 sK0 X2 X1 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54469 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ X1)]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l4 sK0 X1]
  have l8 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (X2 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [l5 sK0 X2 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)]
  have l10 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54469 sK0 X1 X1 sK0]
    conv => enter [1]; rw [l8 sK0 X1 X1 X0]
  have l11 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [← h54469 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l9 sK0 sK0 X1]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK0]
  have l13 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) = ((sK2 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [← l1 sK0 sK2 X0]
    conv => enter [1]; rw [h54469 sK0 (sK0 ◇ sK0) (sK2 ◇ X0) sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54469 sK0 sK0 X0 sK0]
  have l15 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [h54469 sK0 sK2 X0 sK0]
  have l16 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [h54469 sK0 X1 X0 sK0]
  have l17 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (X2 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [h54469 sK0 X2 X1 X0]
    conv => enter [1, 2]; rw [h54469 sK0 sK0 X0 sK0]
  have l18 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54469 sK0 X1 X1 sK0]
    conv => enter [1]; rw [l17 sK0 X1 X1 X0]
  have l19 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54469 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l16 sK0 X1 X0]
  have l20 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54469 sK0 sK0 sK2 sK0]
    conv => enter [1]; rw [← l15 sK0 sK2 sK2]
  have l22 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l19 sK0 X1 X0]
  have l23 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l20 sK0 sK2 X0]
    conv => enter [1]; rw [← l18 sK2 sK0 X0]
  have l24 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l22 sK0 X1 X0]
  have l25 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) = ((sK0 ◇ sK2) ◇ sK2) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l23 sK0 sK2 X0]
    conv => enter [1]; rw [← l15 sK0 sK2 sK2]
  have l26 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l24 sK0 X1 X0]
  have l27 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l21 sK0 sK2]
    conv => enter [1]; rw [← l25 sK0 sK2 X0]
  have l28 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54469 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 X1 X0]
  have l29 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l27 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK2) ◇ X0)]
  have l30 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l28 sK0 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l29 sK0 sK2 sK0]
  have l31 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l30 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l32 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54469 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l31 sK0 sK2]
  have l33 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l32 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l33 sK0 X0 sK0]
  have l35 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l34 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [h54469 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0 X1]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0 sK0]
    conv => enter [1]; rw [← l10 X0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l37 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 X1 sK0 X2
    conv => enter [1, 2, 2]; rw [l36 sK0 X1]
    conv => enter [1]; rw [← h54469 X1 X2 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l38 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l18 X0 sK0 X1]
    conv => enter [1]; rw [l37 X0 X1 sK0 X2]
  have l39 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [l38 X0 sK0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l39 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54547 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54547 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK1 sK0 X2 X0]
  have l4 : ∀ sK3 sK1 sK0 X1 X2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK3 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK1 sK0 X1 X2]
  have l5 : ∀ sK3 sK1 sK0 X1 X0 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK3]
  have l6 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK3 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w x (x ◇ u)]

theorem Equation4512_54547_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54547 : Equation54547 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54547 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54547 sK0 X0 X1 sK0 sK0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54547 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54547 sK0 sK0 sK2 sK0 sK0]
  have l2 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l2 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X2 ◇ X3)) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← h54547 X0 X2 X3 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54455 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54455 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK1 sK0 X2 X0]
  have l4 : ∀ sK3 sK1 sK0 X1 X2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK3 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK1 sK0 X1 X2]
  have l5 : ∀ sK3 sK1 sK0 X1 X0 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK3]
  have l6 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK3 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l7 x y z y w (w ◇ x)]

theorem Equation4512_54455_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54455 : Equation54455 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l8 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l8 sK0 sK2]
  have l12 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l13 : ∀ sK0 X0 X1 X2 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h54455 ((sK0 ◇ sK0) ◇ X0) X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l5 sK0 X0]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54455 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54455 X0 sK0 X1 sK0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54455 X0 (sK0 ◇ sK0) X1 sK0]
  have l17 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ X0))) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [h54455 X0 (sK0 ◇ sK0) X1 sK2]
    conv => enter [1]; rw [l3 sK0 sK2 (sK2 ◇ X0)]
  have l18 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (X2 ◇ X0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l5 sK0 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1, 2]; rw [← h54455 X0 (sK0 ◇ sK0) X1 X2]
  have l19 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ X0))) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [h54455 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 sK2]
    conv => enter [1]; rw [l12 sK0 sK2 (sK2 ◇ X0)]
  have l20 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [← l18 sK0 sK0 X0 X1]
    conv => enter [1]; rw [l19 sK0 sK0 (sK0 ◇ (sK0 ◇ X0)) sK2]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l15 sK0 X0 X1]
  have l22 : ∀ sK0 X0 X1 X2 sK2 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ X1))) := by
    intro sK0 X0 X1 X2 sK2
    conv => enter [1]; rw [l13 sK0 X0 X1 X2]
    conv => enter [1]; rw [l17 X1 sK0 (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) sK2]
  have l23 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l20 sK0 X0 X1 sK2]
    conv => enter [1]; rw [h54455 (sK0 ◇ sK0) (sK0 ◇ sK2) (sK2 ◇ sK0) sK0]
  have l24 : ∀ sK0 X0 X1 X2 sK2 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ X2)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2 sK2
    conv => enter [1]; rw [l22 sK0 X0 X1 X2 sK2]
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ sK2) (sK2 ◇ X1)]
  have l25 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l23 sK0 X0 X1 sK2]
  have l26 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK2))) = (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ X2)) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l24 sK0 X0 X1 X2 sK2]
  have l27 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l25 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [h54455 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ sK0) sK0]
  have l28 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [l26 sK0 sK2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X1 ◇ X2)]
  have l29 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l21 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l27 sK0 sK2 X0]
  have l30 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK2 X0 sK0 sK0]
    conv => enter [1]; rw [h54455 (sK0 ◇ sK0) X0 (sK0 ◇ sK0) sK0]
  have l31 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l21 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l30 sK0 sK2 X0]
  have l32 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l31 sK0 X0 sK2]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ sK2)]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0 sK0]
    conv => enter [1]; rw [h54455 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
  have l34 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 sK0]
    conv => enter [1]; rw [← l29 sK0 X1 sK0]
  have l35 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l8 sK0 sK2]
    conv => enter [1]; rw [l29 sK0 sK2 sK2]
  have l36 : ∀ X1 X0 X2 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro X1 X0 X2 sK0 sK2
    conv => enter [1]; rw [h54455 X1 X0 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l29 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) sK2]
  have l37 : ∀ sK0 sK2 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 sK2 X1 X2
    conv => enter [1]; rw [l29 sK0 (sK0 ◇ sK2) (sK0 ◇ X1)]
    conv => enter [1]; rw [← h54455 X1 (sK0 ◇ (sK0 ◇ sK0)) X2 sK0]
  have l38 : ∀ sK0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l33 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l37 sK0 sK0 X1 X2]
  have l39 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l36 X1 X0 X2 sK0 X1]
    conv => enter [1, 2]; rw [l33 sK0 (sK0 ◇ X1)]
  have l40 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l35 sK0 sK2]
    conv => enter [1]; rw [l33 sK0 (sK0 ◇ sK2)]
  have l41 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l39 X1 X0 X2 sK0]
    conv => enter [1]; rw [← l38 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l42 : ∀ X1 X0 X2 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK0 sK2
    conv => enter [1]; rw [l41 X1 X0 X2 sK0]
    conv => enter [1]; rw [← l40 sK0 sK2]
  have l43 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54455 sK0 sK0 X0 sK0]
  have l44 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ X2)) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [← h54455 sK0 X0 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h54455 X1 sK0 X2 X0]
  have l45 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l42 sK0 sK0 sK0 sK0 sK2]
    conv => enter [1]; rw [← l44 X0 sK0 sK0 sK0]
  have l46 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l45 sK0 sK0 X0]
  have l47 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54455 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l46 sK0 X0]
  have l48 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l47 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l34 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l49 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h54455 X1 X0 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l48 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)]
  have l50 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l49 X1 X0 X2 sK0]
    conv => enter [1]; rw [← l47 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l50 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54574 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54574 G := by
  have l0 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 sK3]
  have l1 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK3]
  have l2 : ∀ X1 sK2 sK3 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X1 sK2 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK3) sK2 sK3 X0]
  have l3 : ∀ X0 sK2 sK3 X1 X2 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro X0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK2 sK3 X2 X0]
  have l4 : ∀ sK2 sK3 X1 X2 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK2 sK3 X1 X2]
  have l5 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4274 sK2 sK2 sK3]
  have l6 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK3) sK2 sK3 sK2]
  have l7 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l5 sK2 sK3]
    conv => enter [1]; rw [h4274 sK2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [← l7 y x x z]
  conv => enter [1]; rw [l6 y x w]

theorem Equation4512_54574_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54574 : Equation54574 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54574 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l2 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ X1) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 X1 sK0]
  have l8 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h54574 X1 X0 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (X0 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [← l8 y x z x]

end Semigroup5
