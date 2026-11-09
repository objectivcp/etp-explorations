import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54222_implies_Equation54263 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54263 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l2 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l1 sK0 sK2]
  have l3 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) sK2 X0]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l3 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l5 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l0 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l6 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l5 sK2 X0]
    conv => enter [1]; rw [← h54222 X0 sK2 (sK2 ◇ sK2)]
  have l7 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [← l6 sK2 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l8 : ∀ sK2 X0 : G, ((sK2 ◇ X0) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l6 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK2 X0]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l6 sK2 X0]
  have l10 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [l6 sK2 X0]
  have l11 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l10 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l12 : ∀ sK2 X0 : G, ((sK2 ◇ X0) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l8 sK2 X0]
    conv => enter [1]; rw [← h54222 X0 (sK2 ◇ sK2) sK2]
  have l13 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l7 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l14 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l11 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) X0 X1]
  have l15 : ∀ X0 sK2 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [← l12 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 X0 (sK2 ◇ sK2)]
  have l16 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l14 X0 sK2 X1]
    conv => enter [1]; rw [l6 sK2 (X0 ◇ X1)]
  have l17 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l16 X0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l18 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l9 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l19 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l9 sK0 sK2 (sK2 ◇ sK2)]
  have l20 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [← l9 sK0 sK2 sK2]
  have l21 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l20 sK0 sK2]
    conv => enter [1]; rw [l17 (sK0 ◇ (sK2 ◇ sK2)) sK2 sK2]
  have l22 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l19 sK0 sK2]
    conv => enter [1]; rw [l15 (sK0 ◇ (sK2 ◇ sK2)) sK2]
  have l23 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [← l17 sK2 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l24 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l15 sK0 sK2]
  have l25 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [← l6 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l15 (sK2 ◇ sK2) sK2]
  have l26 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l15 (sK2 ◇ sK2) sK2]
  have l27 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l26 sK0 sK2]
    conv => enter [1]; rw [← l4 sK0 sK2 (sK2 ◇ sK2)]
  have l28 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l13 sK2]
    conv => enter [1]; rw [← l25 sK2]
  have l29 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l24 sK0 sK2]
    conv => enter [1]; rw [← l17 sK2 sK2 sK0]
  have l30 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK2]
    conv => enter [1]; rw [← l27 sK0 sK2]
  have l31 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l30 sK0 sK2]
    conv => enter [1]; rw [l15 (sK0 ◇ (sK2 ◇ sK2)) sK2]
  have l32 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l31 sK0 sK2]
    conv => enter [1]; rw [← l17 sK2 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l33 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l28 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l34 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l28 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l35 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l34 sK2 X0]
    conv => enter [1]; rw [l6 sK2 X0]
  have l36 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [l33 sK0 sK2]
  have l37 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l35 sK2 X0]
  have l38 : ∀ sK0 sK2 X0 : G, (((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X0]
  have l39 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK2)) sK2 X0]
    conv => enter [1]; rw [l38 sK0 sK2 X0]
  have l40 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l29 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ sK0)]
  have l41 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l6 sK2 sK0]
    conv => enter [1]; rw [← l40 sK2 sK0]
  have l42 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l41 sK0 sK2]
    conv => enter [1]; rw [← l17 sK2 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l43 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0 sK2]
    conv => enter [1]; rw [← l23 sK0 sK2]
  have l44 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l43 sK0 sK2]
    conv => enter [1]; rw [← l36 sK0 sK2]
  have l45 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l44 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) sK2 X0]
  have l46 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l32 sK0 sK2]
  have l47 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l46 sK2 sK0]
    conv => enter [1, 2]; rw [← l44 sK0 sK2]
  have l48 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l6 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l47 sK2 sK0]
  have l49 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54222 sK0 (sK2 ◇ sK2) (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l9 sK0 sK2 sK0]
  have l50 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h54222 (sK2 ◇ sK2) sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l21 sK0 sK2]
  have l51 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h54222 X0 sK1 (sK2 ◇ (sK1 ◇ sK3))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK3)) (sK1 ◇ X0)]
  have l52 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = ((X1 ◇ ((sK2 ◇ sK2) ◇ X0)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 (sK2 ◇ sK2) X1]
    conv => enter [1]; rw [l6 sK2 (X1 ◇ ((sK2 ◇ sK2) ◇ X0))]
  have l53 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = (X1 ◇ (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l52 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 ((sK2 ◇ sK2) ◇ X0) (sK2 ◇ sK2)]
  have l54 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l50 sK2 sK0]
    conv => enter [1, 2]; rw [← l44 sK0 sK2]
  have l55 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l49 sK0 sK2]
  have l56 : ∀ sK1 X0 sK3 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ (sK1 ◇ sK3)) := by
    intro sK1 X0 sK3 sK2
    conv => enter [1]; rw [← h54222 sK3 sK1 X0]
    conv => enter [1]; rw [l51 sK3 sK1 sK2 sK3]
  have l57 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = (X1 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l53 sK2 X0 X1]
    conv => enter [1]; rw [← l17 X1 sK2 ((sK2 ◇ sK2) ◇ X0)]
  have l58 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l0 sK2 sK2]
    conv => enter [1]; rw [l54 sK2 sK0]
  have l59 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [l55 sK0 sK2]
  have l60 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l57 sK2 X0 X1]
    conv => enter [1, 2]; rw [l6 sK2 X0]
  have l61 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l37 sK2 sK2]
    conv => enter [1]; rw [l58 sK2 sK0]
  have l62 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l44 sK0 sK2]
    conv => enter [1]; rw [l59 sK0 sK2]
  have l63 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h54222 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l60 sK2 X0 X1]
  have l64 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l6 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l63 sK2 X1 X0]
  have l65 : ∀ sK2 X1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l28 sK2]
    conv => enter [1]; rw [l64 sK2 X1 X0]
  have l66 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [l48 sK0 sK2]
  have l67 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [l61 sK2 sK0]
    conv => enter [1]; rw [← l66 sK0 sK2]
  have l68 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l44 sK0 sK2]
    conv => enter [1]; rw [← l67 sK2 sK0]
  have l69 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK2]
    conv => enter [1, 2]; rw [← l68 sK0 sK2]
  have l70 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l44 sK0 sK2]
    conv => enter [1]; rw [l69 sK0 sK2]
  have l71 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [l70 sK0 sK2]
    conv => enter [1]; rw [h54222 (sK0 ◇ (sK2 ◇ sK2)) (sK0 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2, 2]; rw [← l70 sK0 sK2]
  have l72 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l70 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) (sK0 ◇ (sK2 ◇ sK2)) X0]
  have l73 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l70 sK0 sK2]
    conv => enter [1]; rw [l71 sK0 sK2 X0]
  have l74 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h54222 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2) X0]
    conv => enter [1, 2, 2]; rw [← l62 sK0 sK2]
  have l75 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [← l74 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK2)) ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l76 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l75 sK2 X0 sK0]
    conv => enter [1]; rw [← l18 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l77 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l76 sK2 X0 sK0]
    conv => enter [1]; rw [← l39 sK0 sK2 ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))]
  have l78 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l77 sK2 X0 sK0]
    conv => enter [1]; rw [← l45 sK0 sK2 ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))]
  have l79 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l72 sK0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l78 sK2 X0 sK0]
  have l80 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [l79 sK0 sK2 X0]
  have l81 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l44 sK0 sK2]
    conv => enter [1]; rw [l80 sK0 sK2 X0]
  have l82 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l81 sK0 sK2 sK2]
    conv => enter [1, 2]; rw [← l61 sK2 sK0]
  have l83 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l82 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l84 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l83 sK0 sK2]
    conv => enter [1]; rw [l37 sK2 (sK2 ◇ sK2)]
  have l85 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [← l15 X0 sK2]
    conv => enter [1, 2]; rw [← l84 sK0 sK2]
  have l86 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l65 sK2 sK2 X0]
    conv => enter [1]; rw [l85 sK2 X0 sK0]
  have l87 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l68 sK0 sK2]
    conv => enter [1]; rw [l86 sK2 X0 sK0]
  have l88 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1, 1]; rw [l87 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK2 ◇ sK2)) X1]
  have l89 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X1)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1, 1]; rw [l73 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) X1]
  have l90 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [l89 sK0 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK2 ◇ sK2)) X1]
  have l91 : ∀ sK0 sK2 X1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l90 sK0 sK2 X1 sK0]
    conv => enter [1]; rw [← h54222 X1 (sK0 ◇ (sK2 ◇ sK2)) sK0]
  have l92 : ∀ sK0 sK2 X1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l88 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2)) X1]
    conv => enter [1]; rw [← l91 sK0 sK2 X1]
  have l93 : ∀ sK0 sK2 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l70 sK0 sK2]
    conv => enter [1]; rw [l92 sK0 sK2 X1]
  have l94 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1, 2]; rw [l93 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54222 X1 X0 (sK0 ◇ (sK2 ◇ sK2))]
  have l95 : ∀ sK0 sK2 X1 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [l87 sK0 sK2 X0]
    conv => enter [1]; rw [l94 X0 sK0 sK2 X1]
  have l96 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK1 ◇ sK3)) ◇ (sK1 ◇ sK3)) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [l95 sK0 sK2 sK2 (sK1 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK3) (sK1 ◇ sK3)]
  have l97 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ (sK1 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ sK3)) (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [← l96 sK0 sK2 sK1 sK3]
  have l98 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ (sK1 ◇ sK3)) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [l87 sK0 sK2 sK1]
    conv => enter [1]; rw [← l97 sK1 sK2 sK3 sK0]
  have l99 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK3 sK2]
    conv => enter [1]; rw [← l98 sK0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [← l99 z y w x]

theorem Equation4512_54263_implies_Equation54222 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54263 : Equation54263 G) : Equation54222 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54263 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X1)]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 sK0 X0]
    conv => enter [1]; rw [← l0 X1 sK0 X0]
  have l2 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [l2 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK2]
  have l4 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l3 sK2 sK0 X1 sK2]
  have l5 : ∀ X2 X1 X0 sK2 sK0 : G, (X2 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X1 X0 sK2 sK0
    conv => enter [1]; rw [h54263 X2 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l1 X0 sK0 sK2]
  have l6 : ∀ X2 X1 X0 sK2 sK0 : G, (X2 ◇ (X1 ◇ X1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X2 X1 X0 sK2 sK0
    conv => enter [1]; rw [l5 X2 X1 X0 sK2 sK0]
    conv => enter [1, 2]; rw [← l4 sK2 sK0 X1]
  have l7 : ∀ sK2 sK0 X2 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X1)) := by
    intro sK2 sK0 X2 X1
    conv => enter [1]; rw [l4 sK2 sK0 sK2]
    conv => enter [1]; rw [← l6 X2 X1 sK2 sK2 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54263 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

theorem Equation4512_54222_implies_Equation54300 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54300 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l3 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l6 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 1]; rw [l6 sK0 X0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l11 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l12 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ sK0)]
  have l16 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l14 X0 sK0 X1]
    conv => enter [1]; rw [l6 sK0 (X0 ◇ X1)]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l16 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK1 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0 sK0]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [l17 (sK1 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [l15 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← l17 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l24 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 (sK0 ◇ sK0) sK0]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l15 (sK0 ◇ sK0) sK0]
  have l26 : ∀ X0 sK0 X1 : G, ((X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 1]; rw [l15 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l27 : ∀ X0 sK0 X1 : G, ((X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l26 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0 (sK0 ◇ sK0)]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l24 sK0]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← l17 sK0 sK0 sK1]
  have l31 : ∀ X0 sK0 X1 : G, (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [l27 X0 sK0 X1]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← l28 sK1 sK0]
  have l33 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l31 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X1]
  have l34 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [l15 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l35 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1, 2]; rw [← l6 sK0 X1]
    conv => enter [1]; rw [← l33 sK0 X0 X1]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [← l17 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l29 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l38 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l29 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l38 sK0 X0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [l37 sK1 sK0]
  have l41 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l39 sK0 X0]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK1)]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0]
    conv => enter [1]; rw [← l17 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l22 sK1 sK0]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← l40 sK1 sK0]
  have l47 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l36 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l36 sK1 sK0]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1, 2]; rw [← l46 sK1 sK0]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [← l48 sK0 sK1]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l50 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [l41 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l17 (sK0 ◇ sK0) sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l56 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l55 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l56 sK1 sK0]
    conv => enter [1]; rw [l52 sK1 sK0]
  have l58 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [l52 sK1 sK0]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [l58 sK1 sK0]
  have l60 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l57 sK0 sK1]
  have l62 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l61 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l63 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l60 sK1 sK0 X0]
    conv => enter [1]; rw [← l62 sK0 sK1 X0]
  have l64 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54222 ((sK0 ◇ sK0) ◇ sK1) sK0 X0]
    conv => enter [1, 2, 2]; rw [← l30 sK1 sK0]
  have l65 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) = (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2, 2]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [← h54222 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0 X0]
  have l66 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54222 X0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l47 sK1 sK0 X0]
  have l67 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l68 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK3 ◇ (sK2 ◇ sK4))) ◇ (sK2 ◇ X0)) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [h54222 X0 sK2 (sK3 ◇ (sK2 ◇ sK4))]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK2 ◇ sK4)) (sK2 ◇ X0)]
  have l69 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((X1 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l6 sK0 (X1 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l70 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l69 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ sK0)]
  have l71 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [l67 sK0 X0 X1]
  have l72 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l60 sK1 sK0 X0]
    conv => enter [1]; rw [← l66 X0 sK0 sK1]
  have l73 : ∀ sK2 X0 sK4 sK3 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK4))) = ((sK2 ◇ (sK3 ◇ (sK2 ◇ sK4))) ◇ (sK2 ◇ sK4)) := by
    intro sK2 X0 sK4 sK3
    conv => enter [1]; rw [← h54222 sK4 sK2 X0]
    conv => enter [1]; rw [l68 sK4 sK2 sK3 sK4]
  have l74 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l65 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l75 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l64 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l17 X0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l76 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l70 sK0 X0 X1]
    conv => enter [1]; rw [← l17 X1 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l77 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l71 sK0 X1 X0]
  have l78 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l63 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l74 sK0 X0 sK1]
  have l79 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l75 sK0 sK1 X0]
    conv => enter [1]; rw [← l35 X0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l80 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l76 sK0 X0 X1]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l81 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l77 sK0 X1 X0]
  have l82 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l78 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l17 X0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l83 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l79 sK0 sK1 X0]
    conv => enter [1]; rw [← l17 X0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l84 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l80 sK0 X0 X1]
  have l85 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l82 sK1 sK0 X0]
    conv => enter [1]; rw [← l35 X0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l86 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l83 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l57 sK0 sK1]
  have l87 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l84 sK0 X1 X0]
  have l88 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l85 sK1 sK0 X0]
    conv => enter [1]; rw [← l17 X0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l89 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l86 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l59 sK1 sK0]
  have l90 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l87 sK0 X1 X0]
  have l91 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l88 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l57 sK0 sK1]
  have l92 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l89 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 (sK0 ◇ sK0)]
  have l93 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l91 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l59 sK1 sK0]
  have l94 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l81 sK0 sK1 sK0]
    conv => enter [1]; rw [← l92 X0 sK1 sK0]
  have l95 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l47 sK1 sK0 sK0]
    conv => enter [1]; rw [l93 sK1 sK0 X0]
  have l96 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [l95 sK1 sK0 X0]
  have l97 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [← l94 sK0 sK0 sK1]
  have l98 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l15 X0 sK0]
    conv => enter [1, 2]; rw [← l72 sK1 sK0 X0]
  have l99 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l60 sK1 sK0 X0]
    conv => enter [1]; rw [← l98 X0 sK0 sK1]
  have l100 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l99 sK1 sK0 X0]
    conv => enter [1]; rw [← l90 sK0 X0 (sK0 ◇ sK0)]
  have l101 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l97 sK1 sK0]
    conv => enter [1]; rw [← l100 sK1 sK0 X0]
  have l102 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [h54222 X1 X0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l101 sK1 sK0 (X0 ◇ X1)]
  have l103 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [l102 X1 X0 sK1 sK0]
    conv => enter [1]; rw [← l96 sK1 sK0 X0]
  have l104 : ∀ sK1 sK0 sK3 sK2 sK4 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK3 ◇ (sK2 ◇ sK4)) ◇ (sK2 ◇ sK4)) := by
    intro sK1 sK0 sK3 sK2 sK4
    conv => enter [1]; rw [l103 sK1 sK0 sK3 (sK2 ◇ sK4)]
    conv => enter [1]; rw [h4512 sK3 (sK2 ◇ sK4) (sK2 ◇ sK4)]
  have l105 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ (sK2 ◇ sK4))) ◇ (sK2 ◇ sK4)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK2 ◇ sK4)) (sK2 ◇ sK4)]
    conv => enter [1, 2]; rw [← l104 sK1 sK0 sK3 sK2 sK4]
  have l106 : ∀ sK0 sK2 sK3 sK4 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK3 ◇ (sK2 ◇ sK4))) ◇ (sK2 ◇ sK4)) := by
    intro sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l94 sK0 sK2 sK0]
    conv => enter [1]; rw [← l105 sK2 sK3 sK4 sK0 sK0]
  have l107 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK3 ◇ (sK2 ◇ sK4))) ◇ (sK2 ◇ sK4)) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l97 sK1 sK0]
    conv => enter [1]; rw [l106 sK0 sK2 sK3 sK4]
  have l108 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK2 ◇ sK4))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l73 sK2 sK3 sK4 sK3]
    conv => enter [1]; rw [← l107 sK1 sK0 sK2 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [← l108 z w u x y]

theorem Equation4512_54300_implies_Equation54222 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54300 : Equation54300 G) : Equation54222 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 (sK0 ◇ sK0)]
  have l1 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h54300 X0 X1 sK0 sK1 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 sK2]
  have l2 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l1 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← l2 X1 sK0 sK0 X0 X0]
  have l4 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l3 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l5 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [l4 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l3 X0 sK0 sK2]
  have l6 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l5 sK2 sK0 X1 sK2]
  have l7 : ∀ X2 X3 X0 X1 sK2 sK0 : G, (X2 ◇ (X3 ◇ X3)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X3 X0 X1 sK2 sK0
    conv => enter [1]; rw [h54300 X2 X3 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l3 X0 sK0 sK2]
  have l8 : ∀ X2 X3 X0 sK2 sK0 : G, (X2 ◇ (X3 ◇ X3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X2 X3 X0 sK2 sK0
    conv => enter [1]; rw [l7 X2 X3 X0 X2 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK2 sK0 X2]
  have l9 : ∀ sK2 sK0 X2 X3 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X3 ◇ X3)) := by
    intro sK2 sK0 X2 X3
    conv => enter [1]; rw [l6 sK2 sK0 sK2]
    conv => enter [1]; rw [← l8 X2 X3 sK2 sK2 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54300 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

theorem Equation4512_54244_implies_Equation54297 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54244 : Equation54244 G) : Equation54297 G := by
  have l0 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ X0)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l1 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK3)) ◇ sK3) = (sK0 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK3 ◇ sK3) sK3]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK3]
  have l2 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK3 ◇ sK3) ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ X0)) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [h54244 sK0 X0 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK3 ◇ sK3) X0]
  have l3 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) = (sK3 ◇ (X0 ◇ X0)) := by
    intro sK3 X0
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 X0]
    conv => enter [1]; rw [← h54244 sK3 X0 sK3]
  have l4 : ∀ sK3 X0 : G, (sK3 ◇ (sK3 ◇ ((sK3 ◇ sK3) ◇ X0))) = ((sK3 ◇ sK3) ◇ (X0 ◇ X0)) := by
    intro sK3 X0
    conv => enter [1, 2]; rw [← l0 sK3 X0]
    conv => enter [1]; rw [← h54244 (sK3 ◇ sK3) X0 sK3]
  have l5 : ∀ sK0 sK3 X0 X1 : G, ((sK0 ◇ (sK3 ◇ sK3)) ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ X1))) = (sK0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK3 ◇ sK3) (X0 ◇ ((sK3 ◇ sK3) ◇ X1))]
    conv => enter [1, 2]; rw [← h54244 X0 X1 (sK3 ◇ sK3)]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X2) ◇ X3)) = ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ X2) X3]
    conv => enter [1, 1]; rw [h54244 X1 X2 X0]
  have l7 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X2) ◇ X3)) = (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l6 X1 X2 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X2)) X3]
  have l8 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = ((sK3 ◇ sK3) ◇ (X0 ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 ((sK3 ◇ sK3) ◇ X0)]
    conv => enter [1]; rw [l4 sK3 X0]
  have l9 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l7 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l10 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l9 X1 X2 X3 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = (X1 ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l10 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X2 X3]
  have l12 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3
    conv => enter [1]; rw [h54244 sK3 sK3 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK3 ◇ sK3)]
  have l13 : ∀ sK3 X0 : G, (sK3 ◇ (X0 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0
    conv => enter [1, 2]; rw [h54244 X0 sK3 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (X0 ◇ (sK3 ◇ sK3))]
  have l14 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [h54244 X0 sK3 sK3]
    conv => enter [1]; rw [l13 sK3 X0]
  have l15 : ∀ sK3 sK0 : G, ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK0
    conv => enter [1, 2]; rw [h54244 sK0 sK3 sK3]
    conv => enter [1]; rw [l0 sK3 (sK0 ◇ (sK3 ◇ sK3))]
  have l16 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1, 2]; rw [h54244 sK0 sK3 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK0 ◇ (sK3 ◇ sK3))]
  have l17 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK0 sK3
    conv => enter [1]; rw [h54244 sK0 sK3 sK3]
    conv => enter [1]; rw [l16 sK3 sK0]
  have l18 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3))) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK3 ◇ sK3) (sK0 ◇ (sK3 ◇ sK3))]
    conv => enter [1, 2]; rw [← l17 sK0 sK3]
  have l19 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK3
    conv => enter [1, 2]; rw [l12 sK3]
    conv => enter [1]; rw [h4512 sK0 (sK3 ◇ sK3) (sK3 ◇ sK3)]
  have l20 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1, 1]; rw [l12 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK3 ◇ sK3) X0]
  have l21 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ sK3) X0]
    conv => enter [1]; rw [l20 sK3 X0]
  have l22 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK3
    conv => enter [1]; rw [l1 sK0 sK3]
    conv => enter [1]; rw [l19 sK0 sK3]
  have l23 : ∀ X0 sK3 sK0 : G, (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = ((sK0 ◇ (sK3 ◇ sK3)) ◇ (X0 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ sK3))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [h54244 X0 (sK3 ◇ sK3) (sK0 ◇ (sK3 ◇ sK3))]
    conv => enter [1, 2, 2]; rw [← l22 sK0 sK3]
  have l24 : ∀ sK0 sK3 X0 : G, (((sK0 ◇ (sK3 ◇ sK3)) ◇ sK3) ◇ X0) = ((sK0 ◇ (sK3 ◇ sK3)) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK0 sK3 X0
    conv => enter [1, 1]; rw [l22 sK0 sK3]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK3 ◇ sK3)) (sK3 ◇ sK3) X0]
  have l25 : ∀ sK0 sK3 X0 : G, ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ X0)) = ((sK0 ◇ (sK3 ◇ sK3)) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK3 ◇ sK3)) sK3 X0]
    conv => enter [1]; rw [l24 sK0 sK3 X0]
  have l26 : ∀ X0 sK3 : G, (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3
    conv => enter [1]; rw [l23 X0 sK3 X0]
    conv => enter [1]; rw [← h54244 X0 sK3 (X0 ◇ (sK3 ◇ sK3))]
  have l27 : ∀ X0 sK3 : G, (X0 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3
    conv => enter [1]; rw [← l26 X0 sK3]
    conv => enter [1, 2]; rw [← l12 sK3]
  have l28 : ∀ X0 sK0 sK3 : G, (X0 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3)))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3))))) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [h54244 X0 (sK0 ◇ (sK3 ◇ sK3)) sK0]
    conv => enter [1, 2, 2]; rw [← l18 sK0 sK3]
  have l29 : ∀ X0 sK0 sK3 : G, (X0 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3)))) = ((sK0 ◇ (sK3 ◇ sK3)) ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3))))) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [l28 X0 sK0 sK3]
    conv => enter [1]; rw [← l5 sK0 sK3 X0 (sK0 ◇ (sK3 ◇ sK3))]
  have l30 : ∀ X0 sK0 sK3 : G, (X0 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3)))) = ((sK0 ◇ (sK3 ◇ sK3)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [l29 X0 sK0 sK3]
    conv => enter [1, 2, 2]; rw [← l17 sK0 sK3]
  have l31 : ∀ sK3 sK1 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK1 ◇ sK3) ◇ (sK1 ◇ sK3)) := by
    intro sK3 sK1
    conv => enter [1]; rw [h54244 sK3 sK3 sK1]
    conv => enter [1]; rw [h4512 sK1 sK3 (sK1 ◇ sK3)]
  have l32 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h54244 sK2 sK3 sK1]
    conv => enter [1]; rw [h54244 sK2 sK3 sK3]
    conv => enter [1, 2]; rw [h54244 sK2 sK3 sK1]
  have l33 : ∀ sK3 sK1 sK2 : G, ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))))) := by
    intro sK3 sK1 sK2
    conv => enter [1, 2]; rw [l32 sK1 sK2 sK3]
    conv => enter [1]; rw [l0 sK3 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))]
  have l34 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) = ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK3 sK1 sK2
    conv => enter [1, 2]; rw [l32 sK1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))]
  have l35 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ X0) = (sK3 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [l32 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) X0]
  have l36 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l32 sK1 sK2 sK3]
    conv => enter [1]; rw [l34 sK3 sK1 sK2]
  have l37 : ∀ sK3 sK1 sK2 : G, ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) = (sK3 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [l33 sK3 sK1 sK2]
    conv => enter [1]; rw [l3 sK3 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))]
  have l38 : ∀ sK3 sK1 sK2 : G, ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [l37 sK3 sK1 sK2]
    conv => enter [1]; rw [← l35 sK1 sK2 sK3 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))]
  have l39 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l36 sK1 sK2 sK3]
    conv => enter [1]; rw [l38 sK3 sK1 sK2]
  have l40 : ∀ sK2 sK1 sK3 : G, ((sK2 ◇ (sK1 ◇ sK3)) ◇ (sK1 ◇ sK3)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK3) (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [← l31 sK3 sK1]
  have l41 : ∀ sK2 sK1 sK3 : G, ((sK2 ◇ (sK1 ◇ sK3)) ◇ (sK1 ◇ sK3)) = (sK2 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [l40 sK2 sK1 sK3]
    conv => enter [1]; rw [← l27 sK2 sK3]
  have l42 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = ((sK2 ◇ (sK1 ◇ sK3)) ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h54244 sK2 sK3 sK1]
    conv => enter [1]; rw [← l41 sK2 sK1 sK3]
  have l43 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ X0) = ((sK2 ◇ (sK1 ◇ sK3)) ◇ ((sK1 ◇ sK3) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [l42 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK3)) (sK1 ◇ sK3) X0]
  have l44 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))))) = (X1 ◇ (sK0 ◇ (((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3))))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [← h54244 X1 ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h54244 ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) (sK3 ◇ sK3) sK0]
  have l45 : ∀ sK0 sK3 X0 : G, (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3)))) = (X0 ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h54244 sK0 (sK0 ◇ (sK3 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [← h54244 X0 (sK3 ◇ sK3) sK0]
  have l46 : ∀ sK0 sK3 X0 : G, (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3)))) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK3)))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l45 sK0 sK3 X0]
    conv => enter [1, 2, 2]; rw [← l12 sK3]
  have l47 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))))) = (X1 ◇ (sK0 ◇ ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3)))))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l44 X0 X1 sK3 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK3 ◇ sK3) (sK3 ◇ sK3) (sK0 ◇ (sK3 ◇ sK3))]
  have l48 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK3))) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro X0 sK3 sK0
    conv => enter [1, 2]; rw [l27 X0 sK3]
    conv => enter [1]; rw [← l46 sK0 sK3 X0]
  have l49 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3))))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l47 X0 X1 sK3 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK3 ◇ sK3) ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3)))]
  have l50 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l48 X0 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK3 ◇ sK3)) sK3]
  have l51 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3))))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l49 X0 X1 sK3 sK0]
    conv => enter [1, 2]; rw [← l25 sK0 sK3 (sK0 ◇ (sK3 ◇ sK3))]
  have l52 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l50 X0 sK3 sK0]
    conv => enter [1]; rw [← l8 sK3 (sK0 ◇ (sK3 ◇ sK3))]
  have l53 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))))) = (X1 ◇ (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK3)) ◇ (sK0 ◇ (sK3 ◇ sK3))))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l51 X0 X1 sK3 sK0]
    conv => enter [1, 2]; rw [← l30 sK3 sK0 sK3]
  have l54 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK3))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l52 X0 sK3 sK0]
    conv => enter [1]; rw [← l21 sK3 (sK0 ◇ (sK3 ◇ sK3))]
  have l55 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))))) = (X1 ◇ (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3))))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l53 X0 X1 sK3 sK0]
    conv => enter [1, 2]; rw [← l3 sK3 (sK0 ◇ (sK3 ◇ sK3))]
  have l56 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l54 X0 sK3 sK0]
    conv => enter [1]; rw [← l15 sK3 sK0]
  have l57 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))))) = (X1 ◇ ((sK3 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l55 X0 X1 sK3 sK0]
    conv => enter [1, 2]; rw [← l15 sK3 sK0]
  have l58 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l17 sK0 sK3]
    conv => enter [1]; rw [← l56 X0 sK3 sK0]
  have l59 : ∀ X1 sK0 sK3 X0 : G, (X1 ◇ (sK0 ◇ (sK3 ◇ sK3))) = (X0 ◇ (X1 ◇ (X0 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))))) := by
    intro X1 sK0 sK3 X0
    conv => enter [1, 2]; rw [l17 sK0 sK3]
    conv => enter [1]; rw [← l57 X0 X1 sK3 sK0]
  have l60 : ∀ X1 sK3 sK0 : G, (X1 ◇ ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)))) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro X1 sK3 sK0
    conv => enter [1]; rw [← l11 X1 X1 (sK3 ◇ sK3) (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l59 X1 sK0 sK3 X1]
  have l61 : ∀ X1 sK3 sK0 : G, (X1 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro X1 sK3 sK0
    conv => enter [1, 2]; rw [l14 (sK3 ◇ sK3) sK3]
    conv => enter [1]; rw [l60 X1 sK3 sK0]
  have l62 : ∀ X1 sK3 sK0 : G, (X1 ◇ (sK3 ◇ (sK3 ◇ sK3))) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro X1 sK3 sK0
    conv => enter [1, 2]; rw [l12 sK3]
    conv => enter [1]; rw [l61 X1 sK3 sK0]
  have l63 : ∀ X1 sK3 sK0 : G, (X1 ◇ (sK3 ◇ sK3)) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro X1 sK3 sK0
    conv => enter [1]; rw [l27 X1 sK3]
    conv => enter [1]; rw [l62 X1 sK3 sK0]
  have l64 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ (sK1 ◇ sK3)) ◇ ((sK1 ◇ sK3) ◇ (sK3 ◇ sK3))) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK3) ((sK1 ◇ sK3) ◇ (sK3 ◇ sK3))]
    conv => enter [1, 2]; rw [← l58 sK0 sK3 (sK1 ◇ sK3)]
  have l65 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK1 ◇ sK3)) ◇ ((sK1 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l63 sK2 sK3 sK2]
    conv => enter [1]; rw [← l64 sK2 sK1 sK3 sK2]
  have l66 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l65 sK2 sK3 sK1]
    conv => enter [1]; rw [← l43 sK1 sK2 sK3 (sK3 ◇ sK3)]
  have l67 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h54244 sK2 sK3 sK1]
    conv => enter [1]; rw [l66 sK2 sK3 sK1]
  have l68 : ∀ sK0 sK3 sK1 sK2 : G, (sK0 ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [l58 sK0 sK3 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))]
    conv => enter [1, 2]; rw [← l67 sK1 sK2 sK3]
  have l69 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (sK0 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l39 sK1 sK2 sK3]
    conv => enter [1]; rw [← l68 sK0 sK3 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l69 z w y x]

@[equational_result]
theorem Equation54297_implies_Equation54244 (G : Type*) [Magma G] (h54297 : Equation54297 G) : Equation54244 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54297 sK1 sK2 sK2 sK1]
    conv => enter [1]; rw [← h54297 X0 sK2 sK2 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54297 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 z x y]

theorem Equation4512_41735_implies_Equation41742 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41735 : Equation41735 G) : Equation41742 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK0) X0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41735 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41735 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41735 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41735 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41735 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41735 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l13 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h41735 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ X0))) X2]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ sK0)]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)))]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)))]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41735 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41735 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0))]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l25 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l26 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l21 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)))]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)))]
  have l29 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l26 X0 X1 X2]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0))))]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))))]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l29 (sK0 ◇ sK0) sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l29 (sK0 ◇ sK0) sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l36 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l25 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l46 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l47 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ sK0) X0]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l47 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK0 X0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [l50 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l51 sK0 sK1]
  have l53 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
  have l54 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l44 sK0 sK1]
  have l55 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l54 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
  have l56 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l52 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
  have l57 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l56 sK0 sK1 X0]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))]
  have l59 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41735 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK0 sK1]
  have l60 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) X0]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l60 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
  have l62 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1, 2]; rw [← l51 sK0 sK1]
  have l64 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l61 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l53 sK0 sK1 X0]
  have l65 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [← l53 sK0 sK1 (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l63 sK0 sK1]
  have l67 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l64 sK0 sK1 X0]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l68 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l69 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l67 sK0 sK1 X0]
  have l70 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1, 2]; rw [← l53 sK0 sK1 (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l71 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (sK0 ◇ (sK0 ◇ sK1))]
  have l72 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l48 sK0 sK1 (sK0 ◇ sK1)]
  have l73 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1, 2]; rw [← l57 sK0 sK1 (sK0 ◇ sK1)]
  have l74 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l73 sK0 sK1]
    conv => enter [1]; rw [l55 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK1))]
  have l75 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l44 sK0 sK1]
  have l76 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1, 2]; rw [l55 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l76 sK0 sK1]
  have l78 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (sK0 ◇ sK0)]
  have l79 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l78 sK0 sK1]
  have l80 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l80 sK0 sK1]
  have l82 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l81 sK0 sK1]
  have l83 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [← l69 sK0 sK1 (sK0 ◇ sK0)]
  have l84 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l83 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l84 x y]

theorem Equation4512_41742_implies_Equation41735 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41742 : Equation41742 G) : Equation41735 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41742 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41742 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41742 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41742 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41742 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK0 X0]
    conv => enter [1, 1]; rw [← l10 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2]; rw [h41742 sK0 X0]
    conv => enter [1]; rw [← l13 sK0 sK1 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41742 sK0 X0]
    conv => enter [1]; rw [← l13 sK0 sK1 (X0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l15 sK0 sK1 X0]
    conv => enter [1]; rw [l17 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [← l11 sK0 sK1 (X0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [l19 sK0 sK1 X0]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l20 sK0 sK1 X0]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [← l18 sK0 sK1 X0]
  have l26 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l25 sK0 sK1 X0]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l26 sK0 sK1 X0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l28 sK0 sK1 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← l28 sK0 sK1 (sK0 ◇ (sK0 ◇ X0))]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ X0)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 sK1 (sK0 ◇ sK0)]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l34 x y]

end Semigroup5
