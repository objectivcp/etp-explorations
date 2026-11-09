import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4273_4512_41529_implies_Equation54239 (G : Type*) [Magma G] (h4273 : Equation4273 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation54239 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4273 sK1 sK0]
    conv => enter [1]; rw [h4273 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4273 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4273 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4273 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4273 sK0 X0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4273 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4273 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4273 X0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← l2 sK1 sK0 X0]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l4 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1]; rw [h4273 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [h4273 sK0 (sK1 ◇ sK1)]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← h4273 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l10 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l1 sK1 sK0]
  have l11 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l10 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l7 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l11 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l12 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l15 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l16 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
    conv => enter [1]; rw [l24 sK0 sK1 X0]
  have l26 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ sK1)]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4273 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l29 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l27 sK1 sK0]
    conv => enter [1, 2]; rw [l16 sK0 sK1]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [l26 sK1 X0]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l29 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l31 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← l28 sK0 sK1]
  have l34 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 sK0]
  have l35 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l34 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4273 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
    conv => enter [1, 2]; rw [← l32 sK0 sK1]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) X0]
  have l38 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4273 sK1 sK0]
    conv => enter [1]; rw [l39 sK1 sK0]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 sK0 sK1]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l42 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4273 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [l33 sK0 sK1]
  have l43 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4273 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l42 X0 sK0 sK1]
  have l44 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l43 sK1 X0 sK0]
  have l45 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l44 sK1 X0 sK0]
  have l46 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l47 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l46 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
    conv => enter [1, 1]; rw [l41 sK0 sK1]
  have l49 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l45 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l45 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1))]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1 (sK1 ◇ sK1)]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1 sK1]
  have l54 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l55 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l54 sK1 sK0 X0]
  have l56 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l57 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 sK0 sK1]
    conv => enter [1]; rw [h41529 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [l16 sK0 sK1]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41529 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l45 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41529 sK0]
    conv => enter [1, 2, 2]; rw [h4273 sK0 (sK1 ◇ sK1)]
  have l61 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h41529 sK0]
  have l62 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h41529 sK0]
  have l63 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41529 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h41529 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← h41529 (sK1 ◇ sK0)]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l65 sK0 sK1]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 (sK1 ◇ sK1)]
  have l68 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l63 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1 (sK1 ◇ sK1)]
  have l69 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l70 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [← l61 sK1 sK0]
  have l71 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l60 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
  have l72 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l73 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))]
  have l74 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1, 2]; rw [← l57 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1))]
  have l76 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← l55 sK1 sK0 sK1]
  have l77 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l69 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l78 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l70 sK1 sK0]
    conv => enter [1, 2]; rw [← l14 sK1 sK0 sK0]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l72 sK0 sK1]
  have l81 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l73 sK0 sK1]
    conv => enter [1]; rw [← l47 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l82 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [← l55 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l83 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1, 2]; rw [l20 sK0 sK1 (sK1 ◇ sK1)]
  have l84 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l76 sK1 sK0]
    conv => enter [1]; rw [← l45 sK0 sK1 sK1]
  have l85 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l77 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l86 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l78 sK1 sK0]
    conv => enter [1]; rw [l56 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l87 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l41 sK0 sK1]
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1, 2]; rw [l41 sK0 sK1]
  have l88 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l82 sK0 sK1]
    conv => enter [1, 2]; rw [l20 sK0 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l89 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l83 sK0 sK1]
    conv => enter [1, 2]; rw [l49 sK0 sK1 (sK1 ◇ sK1)]
  have l90 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l85 sK1 sK0]
    conv => enter [1]; rw [← l14 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l91 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l86 sK1 sK0]
    conv => enter [1, 2]; rw [← l25 sK0 sK1 sK0]
  have l92 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l55 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l87 sK1 sK0]
  have l93 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l88 sK0 sK1]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l89 sK0 sK1]
  have l95 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l90 sK1 sK0]
    conv => enter [1, 2]; rw [l49 sK0 sK1 (sK0 ◇ sK0)]
  have l96 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l91 sK1 sK0]
    conv => enter [1]; rw [← l38 sK0 sK1 sK0]
  have l97 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l84 sK1 sK1]
    conv => enter [1]; rw [← l92 sK1 sK1]
    conv => enter [1, 2, 1]; rw [← l84 sK1 sK1]
    conv => enter [1, 2, 2]; rw [← l84 sK1 sK1]
  have l98 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [← l93 sK0 sK1]
    conv => enter [1, 1]; rw [← l84 sK1 sK0]
  have l99 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1, 2, 2, 1]; rw [← l84 sK1 sK0]
  have l100 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l95 sK1 sK0]
    conv => enter [1]; rw [← l30 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l101 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [← l96 sK1 sK0]
  have l102 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l97 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK1 ◇ sK1)]
  have l103 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l98 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l104 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l99 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 (sK1 ◇ sK1)]
  have l105 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l100 sK1 sK0]
    conv => enter [1]; rw [l20 sK0 sK1 (sK0 ◇ sK0)]
  have l106 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK0]
    conv => enter [1]; rw [l101 sK1 sK0]
  have l107 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l102 sK1 sK1]
    conv => enter [1, 1]; rw [← l84 sK1 sK1]
  have l108 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l103 sK1 sK0]
  have l109 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l104 sK0 sK1]
  have l110 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l105 sK1 sK0]
    conv => enter [1]; rw [l49 sK0 sK1 (sK0 ◇ sK0)]
  have l111 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4273 sK1 sK0]
    conv => enter [1]; rw [l107 sK1]
  have l112 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l108 sK0 sK1]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l113 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [l109 sK0 sK1]
  have l114 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l110 sK1 sK0]
    conv => enter [1, 2, 1]; rw [← l84 sK1 sK0]
  have l115 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l84 sK1 sK1]
    conv => enter [1]; rw [l111 sK1 sK1]
  have l116 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [← l112 sK1 sK0]
  have l117 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l114 sK1 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK0 ◇ sK0)]
  have l118 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4273 sK1 sK0]
    conv => enter [1]; rw [l116 sK1 sK0]
  have l119 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l117 sK1 sK0]
    conv => enter [1, 1]; rw [← l84 sK1 sK0]
  have l120 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [l118 sK0 sK1]
  have l121 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l119 sK1 sK0]
    conv => enter [1]; rw [l35 sK1 sK0 sK0]
  have l122 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l121 sK1 sK0]
    conv => enter [1, 2]; rw [← l106 sK1 sK0]
  have l123 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l122 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK0)]
  have l124 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l120 sK1 sK0]
    conv => enter [1]; rw [← l123 sK1 sK0]
  have l125 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2]; rw [← l84 sK1 sK0]
  have l126 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l125 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK1)]
  have l127 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1]; rw [l126 sK1 sK0]
  have l128 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l120 sK1 sK0]
  have l129 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l128 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK1)]
  have l130 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l127 sK0 sK1]
    conv => enter [1]; rw [← l129 sK0 sK1]
  have l131 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [← l130 sK0 sK1]
  have l132 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [l131 sK0 sK1]
  have l133 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l124 sK1 sK0]
  have l134 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l113 sK0 sK1]
    conv => enter [1]; rw [← l133 sK0 sK1]
  have l135 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l134 sK0 sK1]
    conv => enter [1, 1]; rw [← l84 sK1 sK0]
    conv => enter [1, 2]; rw [← l84 sK1 sK0]
  have l136 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l115 sK1]
    conv => enter [1]; rw [← l135 sK0 sK1]
  have l137 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h4273 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l138 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l137 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l84 sK1 sK0]
  have l139 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4273 sK1 sK0]
    conv => enter [1]; rw [← l138 X0 sK1 sK0]
  have l140 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [l139 sK1 sK0 X0]
  have l141 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1]; rw [l140 sK1 sK0 X0]
  have l142 : ∀ sK1 X0 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l132 sK1 sK0]
    conv => enter [1]; rw [l141 sK0 X0 sK1]
  have l143 : ∀ sK1 X0 sK0 : G, (sK1 ◇ sK1) = ((X0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l142 sK1 (X0 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← h4273 X0 (sK1 ◇ sK0)]
  have l144 : ∀ sK1 X1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK1 X1 X0 sK0
    conv => enter [1, 1]; rw [l142 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ sK0) ◇ X0) X1]
  have l145 : ∀ sK1 X1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0 sK0
    conv => enter [1]; rw [l144 sK1 X1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) X0 X1]
  have l146 : ∀ sK1 X0 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l143 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK0) (X0 ◇ (X0 ◇ X0))]
  have l147 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l146 sK1 X0 sK1]
    conv => enter [1]; rw [← l145 sK1 (X0 ◇ X0) X0 sK1]
  have l148 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l147 sK1 X0]
  have l149 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l148 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (sK1 ◇ sK1)]
  have l150 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l16 sK0 sK1]
    conv => enter [1]; rw [l149 sK0 sK1 X0]
  have l151 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l41 sK0 sK1]
    conv => enter [1]; rw [l150 sK0 sK1 X0]
  have l152 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l84 sK1 sK1]
    conv => enter [1]; rw [l151 sK1 sK1 X0]
  have l153 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4273 sK1 sK0]
    conv => enter [1]; rw [l152 sK1 X0]
  have l154 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l84 sK1 sK1]
    conv => enter [1]; rw [l153 sK1 sK1 X0]
  have l155 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l156 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [l155 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l84 sK1 sK0]
  have l157 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [← l84 sK1 sK0]
    conv => enter [1]; rw [l156 sK2 sK1 sK0]
  have l158 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l154 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l157 sK2 sK0 sK1]
  have l159 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l158 sK1 sK2 sK0]
    conv => enter [1]; rw [h41529 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← l158 sK1 sK2 sK0]
  have l160 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← h4273 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [← l158 sK1 sK2 sK0]
  have l161 : ∀ sK1 X0 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1, 1]; rw [l158 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l162 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l157 sK2 sK0 sK1]
    conv => enter [1]; rw [← l160 X0 sK2 sK0 sK1]
  have l163 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l159 sK1 sK2 sK0]
    conv => enter [1]; rw [← l161 sK1 ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) sK2 sK0]
  have l164 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l163 sK1 sK2 sK0]
    conv => enter [1]; rw [← l162 sK2 sK0 sK1 (sK1 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l136 y x]
  conv => enter [1]; rw [l164 y z x]

theorem Equation4273_4512_41529_implies_Equation53939 (G : Type*) [Magma G] (h4273 : Equation4273 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation53939 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4273 X1 X0]
    conv => enter [1]; rw [h4273 X1 X2]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4273 sK0 sK1]
    conv => enter [1]; rw [h4273 sK0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4273 sK0 sK1]
    conv => enter [1]; rw [h4273 sK0 (sK0 ◇ sK1)]
  have l3 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4273 sK1 sK2]
    conv => enter [1]; rw [h4273 sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4273 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4273 sK2 X0]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ X0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4273 X0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK1]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l5 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK1 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ X0) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4273 X0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [l3 X0 sK1 sK2]
  have l8 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l7 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK2 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [h4273 sK1 sK2]
  have l10 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [h4273 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h4273 X2 (X0 ◇ X1)]
  have l12 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l10 sK2 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l13 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l9 sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK2) X0]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l12 sK2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
  have l15 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l13 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (((sK1 ◇ sK2) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [l21 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l22 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK1 X0]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h41529 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l18 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41529 sK0]
    conv => enter [1, 2, 2]; rw [h4273 sK0 sK1]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41529 sK1]
    conv => enter [1, 2, 2]; rw [h4273 sK1 sK2]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h41529 sK1]
  have l28 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h41529 sK1]
  have l29 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l28 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l31 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l26 sK1 sK1]
    conv => enter [1]; rw [← l8 sK1 sK1 sK1]
  have l32 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0 sK0]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l34 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l29 sK2 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1, 2]; rw [← l15 sK2 sK1 sK1]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l31 sK1]
    conv => enter [1]; rw [l3 sK1 sK1 sK2]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l11 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l39 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l34 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2 ((sK1 ◇ sK2) ◇ sK1)]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l42 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l39 sK2 sK1]
    conv => enter [1]; rw [← l15 sK2 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l44 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l42 sK2 sK1]
    conv => enter [1, 2, 2]; rw [h4273 sK1 sK2]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4273 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l46 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l44 sK2 sK1]
    conv => enter [1, 2]; rw [← h4273 sK2 (sK1 ◇ sK2)]
  have l47 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4273 sK1 sK2]
    conv => enter [1]; rw [l45 sK1 sK0]
  have l48 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l46 sK2 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 sK2]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK1]
    conv => enter [1]; rw [l47 sK1 sK1 sK0]
  have l50 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l48 sK2 sK1 sK2]
    conv => enter [1]; rw [l23 sK2 sK1 sK2 sK2]
  have l51 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l36 sK1 sK2]
    conv => enter [1]; rw [l50 sK2 sK1]
  have l52 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l36 sK1 sK2]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l49 sK1 sK0]
  have l55 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1]; rw [l54 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l55 sK1 sK0]
  have l57 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l51 sK1 sK2]
  have l58 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← l57 sK0 sK1 sK2]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l60 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4273 sK0 sK1]
    conv => enter [1]; rw [l59 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l60 sK1 sK0]
  have l62 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [h4273 (sK0 ◇ sK1) X0]
  have l63 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l62 sK0 sK1 X0]
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
  have l64 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l63 X0 sK0 sK1 X0]
    conv => enter [1]; rw [← l58 sK0 sK1 X0]
  have l65 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [← l64 X0 sK0 sK1]
  have l66 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (((sK0 ◇ sK1) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← l58 sK0 sK1 sK2]
  have l67 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l66 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l69 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l70 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l69 sK0 X0 sK1]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4273 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l68 sK0 sK1]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [l71 sK0 sK1]
  have l73 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l72 sK1 sK0]
  have l74 : ∀ sK0 sK1 X0 sK2 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) ((sK1 ◇ sK2) ◇ sK1) X0]
  have l75 : ∀ sK0 sK1 X0 sK2 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l74 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) sK1 X0]
  have l76 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l75 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l67 sK0 sK1 sK0 (sK1 ◇ X0)]
  have l77 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l76 sK0 sK1 X0]
    conv => enter [1]; rw [← l70 sK0 (sK1 ◇ X0) sK1]
  have l78 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← l77 sK0 sK1 X0]
  have l79 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l78 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l80 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l79 sK0 sK1 X0]
    conv => enter [1]; rw [← l70 sK0 X0 sK1]
  have l81 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l80 sK0 sK1 X0]
  have l82 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 (sK0 ◇ sK1) X0]
  have l83 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l82 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l65 sK0 sK2 sK1]
  have l84 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l81 sK0 sK1 sK1]
    conv => enter [1]; rw [← l73 sK0 sK1]
  have l85 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l84 sK0 sK1]
    conv => enter [1]; rw [← l83 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l85 x y z]

theorem Equation4273_4512_41529_implies_Equation54241 (G : Type*) [Magma G] (h4273 : Equation4273 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation54241 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h4273 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4273 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4273 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (X1 ◇ X2))]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← h4273 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4273 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X2))]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h41529 X0]
    conv => enter [1]; rw [← l3 X0 X0 X0]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l5 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 2, 2]; rw [← l4 X0]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l8 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [h4273 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l17 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X1]
    conv => enter [1]; rw [l10 X1 X0]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X0]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l12 X1 X1]
    conv => enter [1, 2]; rw [l12 X1 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2, 2]; rw [← l19 X1 X0]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← l19 X2 X1]
  have l22 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l18 X2 X1 X2]
    conv => enter [1]; rw [← l21 X0 X1 X2]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1]; rw [← l18 X1 X0 X1]
  have l24 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [← l22 X1 X1 X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l23 X0 X1]
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [l23 X0 X1]
  have l26 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1]; rw [l12 X1 X2]
  have l27 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l23 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l28 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l27 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l29 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l28 X0 X2 X1]
  have l30 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l26 X2 X1 X1]
    conv => enter [1, 2]; rw [l12 X1 X0]
  have l31 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X1 ◇ (X1 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l30 X2 X1 X0]
    conv => enter [1]; rw [← l29 X1 X0 X0]
  intro x y z
  conv => enter [1, 2]; rw [l12 y x]
  conv => enter [1, 2]; rw [l23 x y]
  conv => enter [1]; rw [← l25 x x]
  conv => enter [1]; rw [l31 x x y]
  conv => enter [1]; rw [l16 x y]
  conv => enter [1, 2]; rw [l16 x y]
  conv => enter [1, 2, 2]; rw [l16 x y]
  conv => enter [1, 2]; rw [l11 x (x ◇ y) y]
  conv => enter [1]; rw [← l9 z x y]

theorem Equation4273_4512_4695_implies_Equation2 (G : Type*) [Magma G] (h4273 : Equation4273 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4273 X1 X0]
    conv => enter [1]; rw [h4273 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h4273 X1 X0]
    conv => enter [1]; rw [h4273 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [h4273 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l0 X0 X1 X1]
    conv => enter [1]; rw [← h4695 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1, 2]; rw [← h4695 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) := by
    intro X0 X1
    conv => enter [1]; rw [h4695 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [l8 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1]; rw [← h4695 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l8 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2, 2]; rw [l8 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [l16 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l19 X1 X0]
    conv => enter [1]; rw [← h4273 X1 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [l16 X1 X1]
  have l22 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l19 X0 X0]
    conv => enter [1]; rw [l21 X0 X1]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation4272_4512_implies_Equation54186 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation54186 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4272 sK1 sK2]
    conv => enter [1]; rw [h4272 sK1 X0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l0 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4272 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) sK1 sK2]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
  have l4 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK0 X0]
  have l5 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4272 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l5 sK1 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK2]
  have l7 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l6 sK1 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l8 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l7 sK1 sK0 sK0]
  have l9 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK1]
    conv => enter [1]; rw [← l8 sK0 sK2 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4272_4512_implies_Equation54240 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation54240 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h4272 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4272 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h4272 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4272 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1, 2]; rw [h4272 sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4272 sK1 sK0]
    conv => enter [1]; rw [h4272 sK1 X0]
  have l3 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 sK1 sK0 X0]
  have l4 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4272 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l4 sK1 X0 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK1 sK0]
  have l6 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← l6 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation4268_implies_Equation53864 (G : Type*) [Magma G] (h4268 : Equation4268 G) : Equation53864 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4268_implies_Equation53866 (G : Type*) [Magma G] (h4268 : Equation4268 G) : Equation53866 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4272_4512_53842_54199_54240_implies_Equation54236 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) (h53842 : Equation53842 G) (h54199 : Equation54199 G) (h54240 : Equation54240 G) : Equation54236 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4272 X1 X0]
    conv => enter [1]; rw [h4272 X1 X2]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X0) X2]
    conv => enter [1, 1]; rw [← h4272 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l4 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h54240 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X1)) X3]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l5 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X3]
  have l7 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h54199 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h54199 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) (X1 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l9 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X1 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l10 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← l6 X0 X1 (X0 ◇ (X1 ◇ X1)) X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1, 2, 2]; rw [← h53842 X1 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X1 X1 X0]
    conv => enter [1]; rw [← l11 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1]; rw [← l6 (X0 ◇ (X0 ◇ X1)) X0 X1 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X1)) X0 X1]
    conv => enter [1]; rw [← l13 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h53842 X1 X1 X1]
    conv => enter [1]; rw [← l14 X0 X1]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l15 X1 X0]
    conv => enter [1]; rw [h53842 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l0 x y (x ◇ x)]
  conv => enter [1]; rw [h54199 (x ◇ x) y]
  conv => enter [1, 2]; rw [← h4512 x x ((x ◇ x) ◇ y)]
  conv => enter [1, 2, 2, 2]; rw [← h4512 x x y]
  conv => enter [1, 2, 2]; rw [← l15 y x]
  conv => enter [1]; rw [← l6 x y y y]
  conv => enter [1]; rw [← l16 x y x y]
  conv => enter [1]; rw [← l3 z x y]

theorem Equation4268_4512_53866_53872_implies_Equation53874 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h4512 : Equation4512 G) (h53866 : Equation53866 G) (h53872 : Equation53872 G) : Equation53874 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4268 sK1 sK2]
    conv => enter [1]; rw [h4268 sK1 X0]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4268 sK1 sK2]
    conv => enter [1]; rw [h4268 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4268 sK1 sK2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 X0]
  have l3 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 sK1 X0 sK2]
  have l4 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK1 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l3 sK1 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l5 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l4 sK1 sK2 X1 sK1]
    conv => enter [1]; rw [← h53866 sK1 X1 sK1]
  have l6 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l0 sK1 sK2 X1]
    conv => enter [1]; rw [← l5 sK1 sK2 X1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 X0]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2 X0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53872 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4272_4512_54060_implies_Equation54105 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) (h54060 : Equation54060 G) : Equation54105 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X0) X2]
    conv => enter [1, 1]; rw [← h4272 X0 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [h54060 x y]
  conv => enter [1]; rw [← l2 z y x]

theorem Equation4268_54023_implies_Equation54025 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h54023 : Equation54023 G) : Equation54025 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4268 sK1 sK2]
    conv => enter [1]; rw [h4268 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54023 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4272_54172_implies_Equation54261 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h54172 : Equation54172 G) : Equation54261 G := by
  intro x y z
  conv => enter [1]; rw [← h4272 y x]
  conv => enter [1]; rw [h4272 y z]
  conv => enter [1]; rw [h54172 z y]

theorem Equation4268_4512_53870_implies_Equation53881 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h4512 : Equation4512 G) (h53870 : Equation53870 G) : Equation53881 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 X0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h53870 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4272_54209_implies_Equation54215 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h54209 : Equation54209 G) : Equation54215 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h4272 X0 X1]
    conv => enter [1]; rw [h54209 X1 X0]
  intro x y z
  conv => enter [1]; rw [← h4272 y x]
  conv => enter [1]; rw [l0 y z]

theorem Equation4268_53869_implies_Equation53879 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h53869 : Equation53869 G) : Equation53879 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4268 sK0 X0]
    conv => enter [1]; rw [h53869 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4268 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4272_4512_53825_implies_Equation54261 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) (h53825 : Equation53825 G) : Equation54261 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4272 sK1 sK2]
    conv => enter [1]; rw [h4272 sK1 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4272 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4272 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l4 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l4 sK2 sK1 sK2]
    conv => enter [1]; rw [l2 sK2 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53825 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l9 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4268_4512_53813_implies_Equation53881 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h4512 : Equation4512 G) (h53813 : Equation53813 G) : Equation53881 G := by
  have l0 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h53813 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation54182_54261_implies_Equation54244 (G : Type*) [Magma G] (h54182 : Equation54182 G) (h54261 : Equation54261 G) : Equation54244 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54261 X0 X1 X2]
    conv => enter [1]; rw [← h54182 X2 X1 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [h54182 z y x]

theorem Equation53876_53881_implies_Equation53885 (G : Type*) [Magma G] (h53876 : Equation53876 G) (h53881 : Equation53881 G) : Equation53885 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53881 X0 X1 X2]
    conv => enter [1]; rw [← h53876 X0 X2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [h53876 x z y]

theorem Equation4272_4512_53846_implies_Equation54244 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) (h53846 : Equation53846 G) : Equation54244 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4272 sK2 sK1]
    conv => enter [1]; rw [h4272 sK2 X0]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [h4272 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 sK2]
  have l2 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
  have l3 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [h4272 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 sK2]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 sK0]
  have l5 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [h53846 sK2 sK0 X0]
  have l6 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ sK2) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [l5 sK2 sK0 X0]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 sK0 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l7 x y z x]

theorem Equation4268_4512_53817_53819_53866_implies_Equation53885 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h4512 : Equation4512 G) (h53817 : Equation53817 G) (h53819 : Equation53819 G) (h53866 : Equation53866 G) : Equation53885 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4268 sK0 sK1]
  have l2 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 sK0 X0 sK1]
  have l3 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l2 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l4 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l3 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [← h53866 sK0 X1 sK0]
  have l5 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l0 sK0 sK1 X1]
    conv => enter [1]; rw [← l4 sK0 sK1 X1]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53817 X0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l7 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l6 X0 sK0 sK1]
    conv => enter [1]; rw [h53819 X0 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_54168_54240_implies_Equation54270 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54168 : Equation54168 G) (h54240 : Equation54240 G) : Equation54270 G := by
  have l0 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X2) ◇ X3)) = ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [h4512 X0 (X2 ◇ X2) X3]
    conv => enter [1, 1]; rw [h54168 X0 X2 X1]
  have l1 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X2) ◇ X3)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l0 X0 X2 X3 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
  have l2 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X2) ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l1 X0 X2 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l3 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X2) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l2 X0 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X0 ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l3 X0 X2 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54168 X0 X2 X1]
    conv => enter [1]; rw [h54240 X0 X2 X3]
    conv => enter [1, 2]; rw [h54168 X0 X2 X1]
  intro x y z
  conv => enter [1]; rw [h54168 x y (z ◇ y)]
  conv => enter [1, 2, 2]; rw [← h4512 z y y]
  conv => enter [1, 2, 2]; rw [h54168 z y x]
  conv => enter [1]; rw [l4 x z z (x ◇ y)]
  conv => enter [1]; rw [← l5 z x y x]

theorem Equation4268_4512_53884_implies_Equation53877 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h4512 : Equation4512 G) (h53884 : Equation53884 G) : Equation53877 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 X0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53884 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK0 X0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4272_4512_53838_implies_Equation54270 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) (h53838 : Equation53838 G) : Equation54270 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4272 sK2 sK1]
    conv => enter [1]; rw [h4272 sK2 X0]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4272 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
  have l3 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4272 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 sK1]
  have l5 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ sK2) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [h53838 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK2) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [l5 sK2 X0 sK1]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4268_4512_53820_implies_Equation53877 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h4512 : Equation4512 G) (h53820 : Equation53820 G) : Equation53877 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53820 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4268 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l2 sK0 sK1 sK0 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation54178_54261_implies_Equation54253 (G : Type*) [Magma G] (h54178 : Equation54178 G) (h54261 : Equation54261 G) : Equation54253 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54261 X0 X1 X2]
    conv => enter [1]; rw [← h54178 X2 X1 X2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [h54178 z y x]

theorem Equation4268_53880_implies_Equation53871 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h53880 : Equation53880 G) : Equation53871 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4268 sK0 sK2]
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4268 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
    conv => enter [1]; rw [h53880 sK0 sK2 X0]
  have l3 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y y z]

theorem Equation4272_4512_53828_implies_Equation54253 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) (h53828 : Equation53828 G) : Equation54253 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4272 sK1 sK0]
    conv => enter [1]; rw [h4272 sK1 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4272 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4272 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l6 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53828 sK1 X0 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4268_53814_implies_Equation53871 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h53814 : Equation53814 G) : Equation53871 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4268 sK0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h53814 sK0 X0 sK2]
  have l2 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y y z]

theorem Equation4272_4512_53818_implies_Equation54219 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) (h53818 : Equation53818 G) : Equation54219 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4272 sK1 sK0]
    conv => enter [1]; rw [h4272 sK1 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4272 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4272 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l6 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53818 sK1 X0 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4268_53818_implies_Equation53875 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h53818 : Equation53818 G) : Equation53875 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4268 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h53818 sK0 X0 sK2]
  have l2 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y y z]

theorem Equation54194_54240_implies_Equation54287 (G : Type*) [Magma G] (h54194 : Equation54194 G) (h54240 : Equation54240 G) : Equation54287 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54240 X0 X1 X2]
    conv => enter [1]; rw [← h54194 X2 X1 X0 X1]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X4 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← h54194 X0 X3 X1 X2]
    conv => enter [1]; rw [l0 X0 X3 X4]
  intro x y z w
  conv => enter [1]; rw [← l1 z w x y x]

theorem Equation53871_53881_53892_implies_Equation53878 (G : Type*) [Magma G] (h53871 : Equation53871 G) (h53881 : Equation53881 G) (h53892 : Equation53892 G) : Equation53878 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53881 X0 X1 X2]
    conv => enter [1]; rw [← h53871 X0 X2 X2]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [h53892 x w y z]

theorem Equation4272_4512_53854_implies_Equation54287 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation54287 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4272 sK2 sK1]
    conv => enter [1]; rw [h4272 sK2 X0]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4272 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
  have l3 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4272 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 sK1]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 sK2]
  have l6 : ∀ sK2 X0 X1 sK1 : G, ((sK2 ◇ sK2) ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [h53854 sK2 X0 X1 sK1]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 X0 X1 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

theorem Equation4268_4512_53821_implies_Equation53878 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53878 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4268 sK1 sK2]
    conv => enter [1]; rw [h4268 sK1 X0]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h53821 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [← h4268 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l1 sK1 sK2 X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l2 sK1 sK2 sK1 sK1 X0 X1]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4291_54071_54550_implies_Equation4300 (G : Type*) [Magma G] (h4291 : Equation4291 G) (h54071 : Equation54071 G) (h54550 : Equation54550 G) : Equation4300 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54071 X0 X1 X2]
    conv => enter [1]; rw [← h54550 X2 X1 X0 X1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4291 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4291_4512_53968_54071_54550_implies_Equation54140 (G : Type*) [Magma G] (h4291 : Equation4291 G) (h4512 : Equation4512 G) (h53968 : Equation53968 G) (h54071 : Equation54071 G) (h54550 : Equation54550 G) : Equation54140 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54071 X0 X1 X2]
    conv => enter [1]; rw [← h54550 X2 X1 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53968 X0 X1 X2]
    conv => enter [1]; rw [← h54550 X2 X0 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [← h4291 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) X0]
  have l3 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK2 ◇ sK1)) X0 sK3]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 (sK2 ◇ sK1) X0 sK2]
  have l5 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 X0 sK2]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [← l1 (sK2 ◇ sK1) X0 sK0]
  have l7 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l4 sK1 sK2 X0]
  have l8 : ∀ sK0 sK2 sK1 sK3 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 sK3 X0
    conv => enter [1, 2]; rw [l3 sK3 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l3 sK3 sK0 sK2 sK1 ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l9 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [l7 sK0 sK2 sK1 ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l10 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l9 sK3 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [l7 sK0 sK2 sK1 X0]
  have l11 : ∀ sK0 sK2 sK1 sK3 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 sK3 X0
    conv => enter [1]; rw [l8 sK0 sK2 sK1 sK3 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK2 ◇ sK1)) X0 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l12 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l11 sK0 sK2 sK1 sK3 X0]
  have l13 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l12 sK3 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [l7 sK0 sK2 sK1 ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)]
  have l14 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l5 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [h4291 sK1 (sK2 ◇ sK1)]
  have l15 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l5 sK2 sK1 X0]
    conv => enter [1]; rw [← l5 sK2 sK1 (sK1 ◇ X0)]
  have l16 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 (sK2 ◇ sK1) X0 sK1]
    conv => enter [1]; rw [l15 sK1 sK2 X0]
  have l17 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l14 sK2 sK1]
    conv => enter [1]; rw [← l1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l18 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [l16 sK2 sK1 X0]
  have l19 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l17 sK2 sK1]
    conv => enter [1]; rw [← l4 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l20 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4291 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK2 sK1 (sK2 ◇ sK1)]
  have l21 : ∀ sK2 sK1 X0 : G, (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l19 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l22 : ∀ sK2 sK1 X0 sK3 sK0 : G, (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK2 sK1 X0 sK3 sK0
    conv => enter [1]; rw [l21 sK2 sK1 X0]
    conv => enter [1]; rw [← l10 sK3 sK0 sK2 sK1 X0]
  have l23 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l22 sK2 sK1 X0 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l24 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l20 sK2 sK1]
  have l25 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [← l24 sK2 sK1 X0]
  have l26 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l23 sK3 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l25 sK2 sK1 X0]
  have l27 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [← l26 sK3 sK0 sK2 sK1 X0]
  have l28 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [l18 sK1 sK2 X0]
    conv => enter [1]; rw [← l4 sK1 sK2 (sK1 ◇ X0)]
  have l29 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l1 sK1 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l28 sK2 sK1 X0]
  have l30 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l23 sK3 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l29 sK1 X0 sK2]
  have l31 : ∀ sK2 sK1 X0 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ X0) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK2 sK1 X0 sK3 sK0
    conv => enter [1]; rw [l5 sK2 sK1 X0]
    conv => enter [1]; rw [← l30 sK3 sK0 sK2 sK1 X0]
  have l32 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l31 sK2 sK1 X0 sK2 sK2]
    conv => enter [1]; rw [← l27 sK1 sK2 X0 sK2 sK2]
  have l33 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [← h4291 sK2 sK1]
    conv => enter [1]; rw [l0 (sK2 ◇ sK1) sK2 X0]
    conv => enter [1, 2]; rw [h4291 sK2 sK1]
  have l34 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l13 sK1 sK1 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l35 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l34 sK1 sK2]
    conv => enter [1]; rw [← l32 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l36 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1, 2]; rw [← l0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l33 sK2 sK1 sK3]
  have l37 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l35 sK1 sK2]
    conv => enter [1]; rw [← l36 sK3 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l37 x y z w]

theorem Equation54179_54343_implies_Equation4339 (G : Type*) [Magma G] (h54179 : Equation54179 G) (h54343 : Equation54343 G) : Equation4339 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54179 X0 X1 X2]
    conv => enter [1]; rw [← h54343 X0 X1 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4314_4512_54179_54343_implies_Equation54029 (G : Type*) [Magma G] (h4314 : Equation4314 G) (h4512 : Equation4512 G) (h54179 : Equation54179 G) (h54343 : Equation54343 G) : Equation54029 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54179 X0 X1 X2]
    conv => enter [1]; rw [← h54343 X0 X1 X2 X2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4314 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l3 sK1 sK2]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [← l2 sK1 sK2]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4314 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK2]
  have l7 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [l0 X1 sK2 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X0]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2 X0]
    conv => enter [1]; rw [← l2 sK1 sK2]
  have l10 : ∀ X1 sK2 sK1 X0 sK3 sK0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X1 sK2 sK1 X0 sK3 sK0
    conv => enter [1]; rw [← l7 X1 sK2 sK1 X0]
    conv => enter [1]; rw [l0 X1 sK2 (sK3 ◇ sK0)]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 X0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1]
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation4300_4512_implies_Equation54370 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54370 G := by
  have l0 : ∀ X0 sK0 sK2 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK0 sK2 sK3 X1
    conv => enter [1]; rw [← h4300 sK0 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [h4300 sK0 (sK2 ◇ sK3) X1]
  have l1 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4300 sK2 sK3 X0]
    conv => enter [1]; rw [h4300 sK2 sK3 X1]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK0 sK2 sK3 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK2 sK3 X0]
    conv => enter [1, 2]; rw [l2 sK0 sK2 sK3 sK1]
  have l4 : ∀ X0 sK2 sK3 X1 X2 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK3 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK3)]
  have l5 : ∀ X0 sK2 sK3 X1 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1 sK1
    conv => enter [1]; rw [l4 X0 sK2 sK3 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK2 sK3 sK1]
  have l6 : ∀ sK1 sK0 sK2 sK3 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l3 sK1 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l5 X0 sK2 sK3 sK1 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l6 sK1 sK0 sK2 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

@[equational_result]
theorem Equation4339_implies_Equation54343 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54343 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4339 X0 sK2 sK3]
    conv => enter [1]; rw [h4339 X0 sK2 (sK0 ◇ sK3)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4272_53814_implies_Equation54222 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h53814 : Equation53814 G) : Equation54222 G := by
  intro x y z
  conv => enter [1]; rw [← h4272 y x]
  conv => enter [1]; rw [h53814 y z x]

theorem Equation53819_53876_53922_implies_Equation53902 (G : Type*) [Magma G] (h53819 : Equation53819 G) (h53876 : Equation53876 G) (h53922 : Equation53922 G) : Equation53902 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53922 X0 X1 X2]
    conv => enter [1]; rw [← h53876 X1 X2 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y y]
  conv => enter [1]; rw [h53819 y x z]

theorem Equation4272_53833_implies_Equation54275 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h53833 : Equation53833 G) : Equation54275 G := by
  intro x y z
  conv => enter [1]; rw [← h4272 y x]
  conv => enter [1]; rw [h53833 y z]

theorem Equation4277_53826_implies_Equation53943 (G : Type*) [Magma G] (h4277 : Equation4277 G) (h53826 : Equation53826 G) : Equation53943 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4277 sK0 sK0 sK1]
    conv => enter [1]; rw [h4277 sK0 sK2 sK2]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h4277 sK2 X0 X0]
    conv => enter [1]; rw [h53826 X0 sK2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y z x]

theorem Equation4270_4272_54177_implies_Equation54241 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h4272 : Equation4272 G) (h54177 : Equation54177 G) : Equation54241 G := by
  intro x y z
  conv => enter [1]; rw [← h4270 x y]
  conv => enter [1]; rw [h4272 x z]
  conv => enter [1]; rw [h54177 z x y]

theorem Equation4268_53903_implies_Equation53939 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h53903 : Equation53903 G) : Equation53939 G := by
  intro x y z
  conv => enter [1]; rw [← h4268 x y]
  conv => enter [1]; rw [h4268 x z]
  conv => enter [1]; rw [h53903 x z y]

theorem Equation4280_53819_implies_Equation54239 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h53819 : Equation53819 G) : Equation54239 G := by
  have l0 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [← h4280 sK1 X1 sK1]
    conv => enter [1]; rw [h4280 sK1 X0 sK1]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4280 sK1 X0 X0]
    conv => enter [1]; rw [h53819 X0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4277_53814_implies_Equation53901 (G : Type*) [Magma G] (h4277 : Equation4277 G) (h53814 : Equation53814 G) : Equation53901 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4277 X1 X1 X2]
    conv => enter [1]; rw [h4277 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [h53814 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y x z]

theorem Equation4280_53811_implies_Equation54273 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h53811 : Equation53811 G) : Equation54273 G := by
  have l0 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4280 sK1 X0 X0]
    conv => enter [1]; rw [h53811 X0 sK1 sK2]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4280 sK1 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4277_53820_implies_Equation53904 (G : Type*) [Magma G] (h4277 : Equation4277 G) (h53820 : Equation53820 G) : Equation53904 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4277 sK0 sK0 sK1]
    conv => enter [1]; rw [h4277 sK0 sK2 sK2]
  have l1 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4277 sK2 X0 X0]
    conv => enter [1]; rw [h53820 X0 X1 sK2]
  have l2 : ∀ sK0 sK1 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y y x z]

theorem Equation4280_53858_implies_Equation54291 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h53858 : Equation53858 G) : Equation54291 G := by
  have l0 : ∀ sK2 X1 X2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 X1 X2 sK1
    conv => enter [1]; rw [h53858 sK2 X1 X2 sK2 sK1]
  have l1 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [← h4280 sK2 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 X1 X2 sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4277_53858_implies_Equation53905 (G : Type*) [Magma G] (h4277 : Equation4277 G) (h53858 : Equation53858 G) : Equation53905 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4277 X1 X1 X2]
    conv => enter [1]; rw [h4277 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 X1 X2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X1 X2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [h53858 sK1 X1 X2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y y x z w]

theorem Equation4269_4512_implies_Equation54026 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation54026 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y y z]

theorem Equation4269_4512_implies_Equation54034 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation54034 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z y]

theorem Equation4269_4512_54190_implies_Equation54182 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) (h54190 : Equation54190 G) : Equation54182 G := by
  have l0 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4269 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [← l0 X0 X2 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [h54190 x y x]
  conv => enter [1]; rw [← l3 x z y]

theorem Equation4269_4512_53888_implies_Equation53876 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) (h53888 : Equation53888 G) : Equation53876 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4269 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53888 sK0 sK1 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4269_54057_implies_Equation54118 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h54057 : Equation54057 G) : Equation54118 G := by
  intro x y z
  conv => enter [1]; rw [← h4269 x y]
  conv => enter [1]; rw [h4269 x z]
  conv => enter [1]; rw [h54057 x z]

theorem Equation4269_54014_implies_Equation54018 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h54014 : Equation54014 G) : Equation54018 G := by
  intro x y z
  conv => enter [1]; rw [← h4269 x y]
  conv => enter [1]; rw [h4269 x z]
  conv => enter [1]; rw [h54014 x z]

theorem Equation4269_54105_implies_Equation54075 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h54105 : Equation54105 G) : Equation54075 G := by
  intro x y z
  conv => enter [1]; rw [← h4269 x y]
  conv => enter [1]; rw [h4269 x z]
  conv => enter [1]; rw [h54105 x z y]

theorem Equation4269_54025_implies_Equation54039 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h54025 : Equation54025 G) : Equation54039 G := by
  intro x y z
  conv => enter [1]; rw [← h4269 x y]
  conv => enter [1]; rw [h4269 x z]
  conv => enter [1]; rw [h54025 x z y]

theorem Equation4269_53850_implies_Equation54075 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h53850 : Equation53850 G) : Equation54075 G := by
  intro x y z
  conv => enter [1]; rw [← h4269 x y]
  conv => enter [1]; rw [h53850 x y z]

theorem Equation4269_4512_53817_54031_implies_Equation54039 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) (h53817 : Equation53817 G) (h54031 : Equation54031 G) : Equation54039 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l1 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l0 sK0 X0 sK1]
  have l2 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l1 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l3 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l2 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [← h54031 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l0 sK0 sK1 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 X1]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4269 X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 sK0]
  have l7 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l5 X0 sK0 sK1]
    conv => enter [1]; rw [h53817 X0 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4269_53832_implies_Equation54118 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h53832 : Equation53832 G) : Equation54118 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h53832 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4269_4512_53810_54031_implies_Equation54018 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) (h53810 : Equation53810 G) (h54031 : Equation54031 G) : Equation54018 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4269 sK0 sK2]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l1 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l0 sK0 X0 sK2]
  have l2 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [← l1 sK0 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l3 : ∀ sK0 sK2 X1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l2 sK0 sK2 X1 sK0]
    conv => enter [1]; rw [← h54031 sK0 X1 sK0]
  have l4 : ∀ sK0 sK2 X1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l0 sK0 sK2 X1]
    conv => enter [1]; rw [← l3 sK0 sK2 X1]
  have l5 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h4269 X0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK2 X0]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK2 sK0]
  have l7 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [← l5 X0 sK0 sK2]
    conv => enter [1]; rw [h53810 X0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK0 sK2 sK1]
    conv => enter [1]; rw [← l6 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l8 x z y]

theorem Equation4269_54057_54122_implies_Equation54063 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h54057 : Equation54057 G) (h54122 : Equation54122 G) : Equation54063 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54122 X2 X1 X0]
    conv => enter [1]; rw [h54122 X2 X1 X3]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54122 X2 X1 X0]
    conv => enter [1]; rw [← h4269 X2 X1]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X4 ◇ X2))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← l1 X3 X4 X2]
  intro x y z
  conv => enter [1]; rw [h54057 x y]
  conv => enter [1]; rw [l0 y x x x]
  conv => enter [1]; rw [l2 x x x y z]

theorem Equation4269_54028_implies_Equation54035 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h54028 : Equation54028 G) : Equation54035 G := by
  intro x y z
  conv => enter [1]; rw [← h4269 x y]
  conv => enter [1]; rw [h4269 x z]
  conv => enter [1]; rw [h54028 x z y]

theorem Equation4269_53842_implies_Equation54067 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h53842 : Equation53842 G) : Equation54067 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h53842 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y y z]

theorem Equation4269_4512_53811_54031_implies_Equation54017 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) (h53811 : Equation53811 G) (h54031 : Equation54031 G) : Equation54017 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4269 sK0 sK2]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l1 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l0 sK0 X0 sK2]
  have l2 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [← l1 sK0 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l3 : ∀ sK0 sK2 X1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l2 sK0 sK2 X1 sK0]
    conv => enter [1]; rw [← h54031 sK0 X1 sK0]
  have l4 : ∀ sK0 sK2 X1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l0 sK0 sK2 X1]
    conv => enter [1]; rw [← l3 sK0 sK2 X1]
  have l5 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h4269 X0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK2 X0]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK2 sK0]
  have l7 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [← l5 X0 sK0 sK2]
    conv => enter [1]; rw [h53811 X0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK0 sK2 sK1]
    conv => enter [1]; rw [← l6 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l8 x z y]

theorem Equation4269_53838_implies_Equation54063 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h53838 : Equation53838 G) : Equation54063 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4269 sK2 sK1]
    conv => enter [1]; rw [h4269 sK2 X0]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4269 sK2 sK1]
    conv => enter [1]; rw [h53838 sK2 X0 sK1]
  have l2 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l0 sK2 sK0 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y y z]

theorem Equation4269_4512_53820_54031_implies_Equation54035 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) (h53820 : Equation53820 G) (h54031 : Equation54031 G) : Equation54035 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l1 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l0 sK0 X0 sK1]
  have l2 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l1 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l3 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l2 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [← h54031 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l0 sK0 sK1 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 X1]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4269 X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 sK0]
  have l7 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [← h53820 X0 X1 sK1]
    conv => enter [1]; rw [l5 X0 sK0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation54053_54140_implies_Equation54113 (G : Type*) [Magma G] (h54053 : Equation54053 G) (h54140 : Equation54140 G) : Equation54113 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54053 X0 X1 X2]
    conv => enter [1]; rw [← h54140 X0 X2 X1 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [h54140 x w z y]

theorem Equation54029_54031_implies_Equation54037 (G : Type*) [Magma G] (h54029 : Equation54029 G) (h54031 : Equation54031 G) : Equation54037 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54031 X0 X1 X2]
    conv => enter [1]; rw [← h54029 X0 X2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [h54029 x z y w]

theorem Equation4269_53854_implies_Equation54113 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h53854 : Equation53854 G) : Equation54113 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4269 sK1 sK0]
    conv => enter [1]; rw [h53854 sK1 X0 X1 sK0]
  have l2 : ∀ sK1 sK2 X0 X1 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z y w]

theorem Equation4269_4512_53821_implies_Equation54037 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation54037 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ ((X0 ◇ sK1) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK1 (X0 ◇ sK1) X1]
    conv => enter [1, 1]; rw [l0 sK1 X0 sK2]
  have l2 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = (sK1 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l1 sK1 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [h53821 sK1 sK1 sK1 X1]
    conv => enter [1]; rw [← l2 sK1 sK2 X1 sK1]
  have l4 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [l3 sK1 sK2 X1]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4269 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 X0]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK1]
  have l7 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [← h53821 X0 X1 sK2 sK0]
    conv => enter [1]; rw [l5 X0 sK1 sK2]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← l7 sK1 sK3 sK2 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation54190_54370_implies_Equation4360 (G : Type*) [Magma G] (h54190 : Equation54190 G) (h54370 : Equation54370 G) : Equation4360 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54190 X0 X1 X2]
    conv => enter [1]; rw [← h54370 X0 X2 X1 X2]
  have l1 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [← l0 X0 sK3 sK0]
    conv => enter [1]; rw [l0 X0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4269_4284_4512_53888_54190_54370_implies_Equation53892 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53888 : Equation53888 G) (h54190 : Equation54190 G) (h54370 : Equation54370 G) : Equation53892 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54190 X0 X1 X2]
    conv => enter [1]; rw [← h54370 X0 X2 X1 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53888 X0 X1 X2]
    conv => enter [1]; rw [← h54370 X0 X2 X1 X2]
  have l2 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4269 sK2 sK0]
    conv => enter [1]; rw [h4269 sK2 X0]
  have l3 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1]; rw [← l1 sK1 X0 (sK3 ◇ (sK0 ◇ sK2))]
  have l4 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK2 sK0 sK1]
  have l5 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK1 ◇ sK2)]
  have l6 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK3 sK0 sK2 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK3 sK0 sK2 X0]
  have l7 : ∀ sK1 X0 X1 sK3 sK0 sK2 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0) ◇ X1) := by
    intro sK1 X0 X1 sK3 sK0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l3 sK1 sK3 sK0 sK2 X0]
  have l8 : ∀ sK1 X0 X1 sK3 sK0 sK2 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1 sK3 sK0 sK2
    conv => enter [1]; rw [l7 sK1 X0 X1 sK3 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) X0 X1]
  have l9 : ∀ sK1 X0 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK3 sK0 sK2
    conv => enter [1]; rw [l1 sK1 X0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [← l6 sK1 sK3 sK0 sK2 X0]
  have l10 : ∀ sK1 sK3 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [← l8 sK1 X0 X1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l1 sK1 X1 (sK1 ◇ X0)]
  have l11 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK3 sK0 sK2 X0]
    conv => enter [1]; rw [l9 sK1 X0 sK3 sK0 sK2]
  have l12 : ∀ sK1 sK3 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X1) := by
    intro sK1 sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l10 sK1 sK3 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← l3 sK1 sK3 sK0 sK2 X1]
  have l13 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1, 1]; rw [← l3 sK1 sK3 sK0 sK2 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) sK2 X0]
  have l14 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4284 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) sK2]
    conv => enter [1, 2]; rw [l3 sK1 sK3 sK0 sK2 sK2]
  have l15 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ sK2) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l12 sK1 sK3 sK0 sK2 sK2 sK2]
    conv => enter [1]; rw [l14 sK1 sK3 sK0 sK2]
  have l16 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l13 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l12 sK1 sK3 sK0 sK2 sK2 X0]
  have l17 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l3 sK1 sK3 sK0 sK2 sK2]
    conv => enter [1]; rw [l15 sK1 sK3 sK0 sK2]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l16 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK1]
  have l19 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4284 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK3 sK0 sK2 (sK1 ◇ sK2)]
  have l20 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l11 sK1 sK3 sK0 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l19 sK1 sK3 sK0 sK2]
  have l21 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l12 sK1 sK3 sK0 sK2 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l20 sK1 sK3 sK0 sK2]
  have l22 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l21 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) sK3 sK0]
  have l23 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [← l22 sK1 sK3 sK0 sK2]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l23 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l16 sK1 sK2 (sK1 ◇ sK2) sK1 sK1]
  have l25 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l24 sK1 sK2]
  have l26 : ∀ X0 sK0 sK2 sK1 sK3 : G, (X0 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 sK1 sK3
    conv => enter [1, 2]; rw [← l5 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 X0 (sK0 ◇ sK2) sK3]
  have l27 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 X0 (sK1 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1]; rw [l26 X0 sK0 sK2 sK1 sK3]
  have l28 : ∀ X0 sK3 sK0 sK2 sK1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← l27 X0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l25 X0 sK1 sK2]
  have l29 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l28 sK1 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [← l3 sK1 sK3 sK0 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l30 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l29 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) sK3 sK0]
  have l31 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [← l30 sK1 sK3 sK0 sK2]
  have l32 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l31 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l3 sK1 sK3 sK0 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))]
  have l33 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l16 sK1 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) sK3 sK0]
  have l34 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l28 sK1 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [l33 sK1 sK2 sK3 sK0]
  have l35 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [← l3 sK1 sK3 sK0 sK2 (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h4284 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) (sK3 ◇ (sK0 ◇ sK2))]
  have l36 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l12 sK1 sK3 sK0 sK2 (sK3 ◇ (sK0 ◇ sK2)) (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l35 sK1 sK3 sK0 sK2]
  have l37 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l36 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l11 sK1 sK3 sK0 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))]
  have l38 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l37 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) sK3 sK0]
  have l39 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l34 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l38 sK1 sK3 sK0 sK2]
  have l40 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l39 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 (sK3 ◇ (sK0 ◇ sK2)) sK3 sK0]
  have l41 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l40 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [l28 (sK1 ◇ (sK1 ◇ sK2)) sK3 sK0 sK2 sK1]
  have l42 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [← l41 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l42 x y z w]

theorem Equation4360_4512_implies_Equation54343 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54343 G := by
  have l0 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [h4360 X0 sK0 sK3 X0]
    conv => enter [1]; rw [h4360 X0 X0 sK3 sK2]
  have l1 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [h4360 X0 X1 (sK2 ◇ sK3) sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK3 sK0]
  have l2 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4360 X0 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [l1 X0 X0 sK2 sK3 sK0]
  have l3 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK3)) = ((sK0 ◇ sK3) ◇ sK3) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [h4360 sK0 sK2 sK3 sK3]
    conv => enter [1]; rw [h4512 sK0 sK3 sK3]
  have l4 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ ((sK0 ◇ sK3) ◇ sK3)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4360 X0 sK1 (sK2 ◇ sK3) sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK2 sK3]
  have l5 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l4 X0 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [h4360 X0 (X0 ◇ sK3) sK3 sK2]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l5 sK1 sK1 sK2 sK3]
    conv => enter [1]; rw [l2 sK1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

theorem Equation4279_53817_implies_Equation54087 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h53817 : Equation53817 G) : Equation54087 G := by
  have l0 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h4279 X0 sK1 sK2]
    conv => enter [1]; rw [h53817 X0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4273_53840_implies_Equation54133 (G : Type*) [Magma G] (h4273 : Equation4273 G) (h53840 : Equation53840 G) : Equation54133 G := by
  intro x y z w
  conv => enter [1]; rw [← h4273 y x]
  conv => enter [1]; rw [h53840 y z w]

theorem Equation4273_53820_implies_Equation54055 (G : Type*) [Magma G] (h4273 : Equation4273 G) (h53820 : Equation53820 G) : Equation54055 G := by
  intro x y z
  conv => enter [1]; rw [← h4273 y x]
  conv => enter [1]; rw [h53820 y x z]

theorem Equation4279_53811_implies_Equation54119 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h53811 : Equation53811 G) : Equation54119 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4279 X0 sK2 sK1]
    conv => enter [1]; rw [h53811 X0 sK1 sK2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4279_53858_implies_Equation54160 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h53858 : Equation53858 G) : Equation54160 G := by
  have l0 : ∀ X1 X2 sK3 sK4 : G, (X1 ◇ (X2 ◇ X1)) = (sK3 ◇ (sK4 ◇ sK3)) := by
    intro X1 X2 sK3 sK4
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK3 sK4]
  have l1 : ∀ sK2 sK0 sK1 sK5 X1 X2 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 sK5 X1 X2
    conv => enter [1]; rw [← h4279 sK2 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h53858 sK2 X1 X2 sK0 sK1]
  have l2 : ∀ sK3 sK4 X1 X2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 X1 X2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 (sK3 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [l1 sK3 sK0 sK1 sK3 X1 X2]
  intro x y z w u v
  conv => enter [1]; rw [l2 x y z w u v]

theorem Equation3253_4512_53807_implies_Equation307 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [l3 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h53807 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l7 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l8 sK0]
  intro x
  conv => enter [1]; rw [l9 x]

theorem Equation3253_4512_53807_implies_Equation41529 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation41529 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [l3 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h53807 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l7 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l8 sK0]
  intro x
  conv => enter [1]; rw [l9 x]
  conv => enter [1, 2]; rw [h3253 x]

theorem Equation3253_4512_41529_implies_Equation307 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation307 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41529 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  intro x
  conv => enter [1]; rw [l8 x]

theorem Equation3253_4512_41529_implies_Equation54175 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation54175 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [h3253 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h3253 sK1]
    conv => enter [1]; rw [l3 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h41529 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation3253_4512_4695_implies_Equation3 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h3253 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4695 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK0]
  have l6 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l4 sK0]
  intro x
  conv => enter [1]; rw [l7 x]

theorem Equation411_4512_53807_implies_Equation3 (G : Type*) [Magma G] (h411 : Equation411 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h53807 X0]
    conv => enter [1]; rw [← h411 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [← l0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l4 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h53807 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53807 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l7 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l10 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l9 sK0]
  intro x
  conv => enter [1]; rw [l10 x]

theorem Equation411_4512_53807_implies_Equation4695 (G : Type*) [Magma G] (h411 : Equation411 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation4695 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h53807 X0]
    conv => enter [1]; rw [← h411 X0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l3 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h53807 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h53807 X0]
    conv => enter [1]; rw [l0 X0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h53807 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l4 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0]
  have l14 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l13 sK0]
  intro x
  conv => enter [1]; rw [l14 x]
  conv => enter [1]; rw [l11 x]
  conv => enter [1, 2, 2]; rw [← l0 x]

theorem Equation411_41529_implies_Equation3 (G : Type*) [Magma G] (h411 : Equation411 G) (h41529 : Equation41529 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h411 sK0]
    conv => enter [1]; rw [← h41529 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation411_4695_implies_Equation3 (G : Type*) [Magma G] (h411 : Equation411 G) (h4695 : Equation4695 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h411 X0]
    conv => enter [1]; rw [← h4695 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation307_implies_Equation41529 (G : Type*) [Magma G] (h307 : Equation307 G) : Equation41529 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [h307 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation41733_53860_implies_Equation323 (G : Type*) [Magma G] (h41733 : Equation41733 G) (h53860 : Equation53860 G) : Equation323 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41733 X0 X1]
    conv => enter [1, 2, 2]; rw [h53860 X0 X1]
    conv => enter [1, 2]; rw [← h41733 X0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41733 sK0 sK1]
    conv => enter [1, 2]; rw [← h53860 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation41733_53860_implies_Equation54335 (G : Type*) [Magma G] (h41733 : Equation41733 G) (h53860 : Equation53860 G) : Equation54335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41733 X0 X1]
    conv => enter [1, 2, 2]; rw [h53860 X0 X1]
    conv => enter [1, 2]; rw [← h41733 X0 X1]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41733 sK1 sK2]
    conv => enter [1, 2]; rw [← h53860 sK1 sK2]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1, 2]; rw [← l0 sK1 sK2]
  intro x y z
  conv => enter [1, 2]; rw [l2 y z]

theorem Equation41733_53860_implies_Equation54318 (G : Type*) [Magma G] (h41733 : Equation41733 G) (h53860 : Equation53860 G) : Equation54318 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41733 X0 X1]
    conv => enter [1, 2, 2]; rw [h53860 X0 X1]
    conv => enter [1, 2]; rw [← h41733 X0 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41733 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h53860 sK0 (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation307_41783_53860_implies_Equation326 (G : Type*) [Magma G] (h307 : Equation307 G) (h41783 : Equation41783 G) (h53860 : Equation53860 G) : Equation326 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h41783 X0 X1]
    conv => enter [1, 2]; rw [← h53860 X1 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h307 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation307_4512_41783_53860_implies_Equation54335 (G : Type*) [Magma G] (h307 : Equation307 G) (h4512 : Equation4512 G) (h41783 : Equation41783 G) (h53860 : Equation53860 G) : Equation54335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h41783 X0 X1]
    conv => enter [1, 2]; rw [← h53860 X1 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h307 X1]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation307_41783_53860_implies_Equation54339 (G : Type*) [Magma G] (h307 : Equation307 G) (h41783 : Equation41783 G) (h53860 : Equation53860 G) : Equation54339 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h41783 X0 X1]
    conv => enter [1, 2]; rw [← h53860 X1 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h307 X1]
  intro x y z
  conv => enter [1, 2]; rw [l1 y z]

theorem Equation307_4512_53860_54175_54199_54202_implies_Equation54172 (G : Type*) [Magma G] (h307 : Equation307 G) (h4512 : Equation4512 G) (h53860 : Equation53860 G) (h54175 : Equation54175 G) (h54199 : Equation54199 G) (h54202 : Equation54202 G) : Equation54172 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h307 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [h307 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h307 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h307 sK1]
    conv => enter [1]; rw [l2 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l14 sK1 sK0]
  have l17 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [l14 sK1 sK0]
  have l18 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l17 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l22 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l21 sK1 sK0 X0]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 X0]
    conv => enter [1, 1]; rw [l19 sK0 sK1]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l25 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54175 (sK1 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [l18 sK1 sK0 (sK1 ◇ sK1)]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54202 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l27 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l18 sK1 sK0 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK1]
    conv => enter [1]; rw [← l30 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l18 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l32 sK0 sK1]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l34 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l33 sK1 sK0]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l38 sK0 sK1]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l10 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l35 sK0 sK1]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l35 sK0 sK1]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l35 sK0 sK1]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l39 sK1 sK0]
    conv => enter [1]; rw [l41 sK1 sK0]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l40 sK1 sK0]
    conv => enter [1, 2]; rw [l39 sK1 sK0]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l45 sK1 sK0]
  have l47 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l37 sK0 sK1]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l47 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l49 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54199 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l15 sK1 sK0]
  have l50 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54199 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l13 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1, 2]; rw [l13 sK0 sK1 (sK0 ◇ sK1)]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1, 2]; rw [l18 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54199 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l46 sK0 sK1]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h54199 sK0 sK1]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [l48 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l56 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [l26 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l53 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l54 sK0 sK1]
  have l59 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l55 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l56 sK1 sK0]
    conv => enter [1]; rw [l43 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l57 sK0 sK1]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [l59 sK1 sK0]
  have l63 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l60 sK1 sK0]
    conv => enter [1, 2]; rw [l48 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [← l63 sK1 sK0]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [← l22 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l65 sK0 sK1]
  have l67 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l66 sK1 sK0]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l68 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l69 sK0 sK1]
  have l71 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [l71 sK0 sK1]
  have l73 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h53860 sK0 sK1]
    conv => enter [1]; rw [← h54199 sK0 (sK0 ◇ sK1)]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l73 sK0 sK1]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [← l74 sK0 sK1]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [← l70 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l76 x y]

end Semigroup5
