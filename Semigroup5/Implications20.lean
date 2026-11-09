import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54222_implies_Equation54243 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54243 G := by
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
    conv => enter [1]; rw [← h54222 X0 sK2 (sK2 ◇ sK2)]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l2 sK2 X0]
  have l4 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [l2 sK2 X0]
  have l5 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l4 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l6 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l5 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) X0 X1]
  have l7 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l6 X0 sK2 X1]
    conv => enter [1]; rw [l2 sK2 (X0 ◇ X1)]
  have l8 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l7 X0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = ((sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK2)) ((sK2 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [l3 sK1 sK2 X0]
  have l10 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = (sK1 ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 (X0 ◇ (sK2 ◇ sK2)) X1]
  have l11 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = (sK1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l10 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l12 : ∀ sK1 X0 sK2 X1 : G, (sK1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X1))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 X0 sK2 X1
    conv => enter [1]; rw [← l11 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) X0 X1]
  have l13 : ∀ sK1 X0 sK2 X1 : G, (sK1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X1))) = (sK1 ◇ ((X0 ◇ X1) ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2 X1
    conv => enter [1]; rw [l12 sK1 X0 sK2 X1]
    conv => enter [1]; rw [l3 sK1 sK2 (X0 ◇ X1)]
  have l14 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) = (sK1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← l13 sK1 X0 sK2 X1]
  have l15 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [l14 sK1 sK2 X0 X1]
  have l16 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l8 sK1 sK2 X0]
  have l17 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [← l2 sK2 X0]
    conv => enter [1]; rw [l8 (sK2 ◇ sK2) sK2 X0]
  have l18 : ∀ sK2 X0 : G, (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l2 sK2 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l8 (sK2 ◇ sK2) sK2 X0]
  have l19 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [← l3 sK1 sK2 X0]
    conv => enter [1]; rw [l8 (sK1 ◇ (sK2 ◇ sK2)) sK2 X0]
  have l20 : ∀ sK2 X0 : G, (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l18 sK2 X0]
    conv => enter [1]; rw [l2 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l21 : ∀ sK2 X0 : G, (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l20 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l22 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l21 sK2 X0]
  have l23 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [l17 X0 sK2]
    conv => enter [1]; rw [l22 sK2 X0]
  have l24 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK2 ◇ sK2) ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1, 1]; rw [l17 X0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (X0 ◇ (sK2 ◇ sK2)) X1]
  have l25 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ sK2) X1]
    conv => enter [1]; rw [l24 X0 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l26 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l25 X0 sK2 X1]
    conv => enter [1]; rw [← h54222 X1 (sK2 ◇ sK2) X0]
  have l27 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l26 X0 sK2 X1]
    conv => enter [1]; rw [← l23 X1 sK2]
  have l28 : ∀ sK2 X0 sK1 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK2 X0 sK1 X1
    conv => enter [1]; rw [h54222 ((sK2 ◇ sK2) ◇ X0) sK1 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK2 ◇ sK2) X0]
  have l29 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) = ((X0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1 sK2 X0
    conv => enter [1, 2, 2]; rw [l16 sK1 sK2 X0]
    conv => enter [1]; rw [← h54222 (X0 ◇ (sK2 ◇ sK2)) sK1 X1]
  have l30 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X0) ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 X1 X2]
    conv => enter [1]; rw [← h54222 (X1 ◇ X0) X2 X1]
  have l31 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l30 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ X2)]
  have l32 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [l29 sK1 X1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) (sK1 ◇ sK1)]
  have l33 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [← l28 sK2 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) X0 (sK1 ◇ sK1)]
  have l34 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [l32 sK1 X1 sK2 X0]
    conv => enter [1]; rw [l27 X0 sK2 (sK1 ◇ sK1)]
  have l35 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) = (sK1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [l33 sK1 X1 sK2 X0]
    conv => enter [1]; rw [l31 (sK2 ◇ sK2) X0 sK1]
  have l36 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l34 sK1 X1 sK2 X0]
  have l37 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l15 sK1 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l35 sK1 X1 sK2 X0]
  have l38 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l16 sK1 sK2 sK1]
    conv => enter [1]; rw [l36 sK1 sK2 X1 X0]
  have l39 : ∀ sK1 X0 sK2 X1 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 X0 sK2 X1
    conv => enter [1]; rw [l19 sK1 X0 sK2]
    conv => enter [1]; rw [l37 sK1 sK2 X0 X1]
  have l40 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l16 sK1 sK2 sK1]
    conv => enter [1]; rw [l38 sK1 sK2 X1 X0]
  have l41 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l16 sK1 sK2 X0]
    conv => enter [1]; rw [l39 sK1 X0 sK2 X1]
  have l42 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l41 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← l40 sK1 sK2 sK1 X0]
  have l43 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l17 sK1 sK2]
  have l44 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [← l43 sK1 sK2]
  have l45 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l44 sK1 sK2]
    conv => enter [1]; rw [l42 sK1 sK2 (sK2 ◇ sK2)]
  have l46 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [← l42 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54222 X1 X0 (sK1 ◇ (sK2 ◇ sK2))]
  have l47 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← l42 sK1 sK2 (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1))]
    conv => enter [1]; rw [← h54222 X1 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l48 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l47 sK1 sK2 X1]
    conv => enter [1, 2]; rw [l42 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l49 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l45 sK1 sK2]
    conv => enter [1]; rw [l46 X0 sK1 sK2 X1]
  have l50 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l45 sK1 sK2]
    conv => enter [1]; rw [l48 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← l45 sK1 sK2]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h54222 sK1 sK0 sK1]
  have l52 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l49 sK0 sK1 sK2 sK1]
  have l53 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l50 sK1 sK2 sK0]
    conv => enter [1]; rw [← l52 sK0 sK1 sK2]
  have l54 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l53 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l54 z x y]

theorem Equation4512_54222_implies_Equation54183 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54183 G := by
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
    conv => enter [1]; rw [← h54222 X0 sK2 (sK2 ◇ sK2)]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l2 sK2 X0]
  have l4 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [l2 sK2 X0]
  have l5 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l4 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l6 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l5 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) X0 X1]
  have l7 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l6 X0 sK2 X1]
    conv => enter [1]; rw [l2 sK2 (X0 ◇ X1)]
  have l8 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l7 X0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l8 sK0 sK2 X0]
  have l10 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [← l2 sK2 X0]
    conv => enter [1]; rw [l8 (sK2 ◇ sK2) sK2 X0]
  have l11 : ∀ sK2 X0 : G, (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l2 sK2 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l8 (sK2 ◇ sK2) sK2 X0]
  have l12 : ∀ sK2 X0 : G, (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l11 sK2 X0]
    conv => enter [1]; rw [l2 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l13 : ∀ sK2 X0 : G, (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l12 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l14 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l13 sK2 X0]
  have l15 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [l10 X0 sK2]
    conv => enter [1]; rw [l14 sK2 X0]
  have l16 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK2 ◇ sK2) ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1, 1]; rw [l10 X0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (X0 ◇ (sK2 ◇ sK2)) X1]
  have l17 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ sK2) X1]
    conv => enter [1]; rw [l16 X0 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l18 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l17 X0 sK2 X1]
    conv => enter [1]; rw [← h54222 X1 (sK2 ◇ sK2) X0]
  have l19 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l18 X0 sK2 X1]
    conv => enter [1]; rw [← l15 X1 sK2]
  have l20 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l2 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l10 sK0 sK2]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l10 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK0 ◇ (sK2 ◇ sK2))]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK2]
    conv => enter [1]; rw [← l20 sK0 sK2]
  have l23 : ∀ X0 sK2 sK0 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l8 X0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l22 sK0 sK2]
  have l24 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l19 X0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l23 X0 sK2 sK0]
  have l25 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [l24 sK0 sK2 X0]
  have l26 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1, 1]; rw [l25 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK2 ◇ sK2)) X1]
  have l27 : ∀ X0 sK0 sK2 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ (((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54222 X0 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l3 sK0 sK2 ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)]
  have l28 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK2 ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)]
    conv => enter [1]; rw [← l27 X0 sK0 sK2]
  have l29 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l26 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [← l28 sK0 sK2 X0]
  have l30 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l26 sK0 sK2 X0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l29 sK0 sK2 X0]
  have l31 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l30 sK0 sK2 X0]
    conv => enter [1]; rw [← l21 sK0 sK2]
  have l32 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l25 sK0 sK2 sK0]
    conv => enter [1]; rw [← l31 sK0 sK2 X0]
  have l33 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1, 2]; rw [l32 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54222 X1 X0 (sK0 ◇ (sK2 ◇ sK2))]
  have l34 : ∀ sK0 sK2 X1 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [l25 sK0 sK2 X0]
    conv => enter [1]; rw [l33 X0 sK0 sK2 X1]
  have l35 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l34 sK0 sK2 sK1 sK0]
    conv => enter [1]; rw [h54222 sK1 sK0 X0]
  have l36 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l35 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l36 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l37 x z y]

theorem Equation4512_54222_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation4280 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [l8 sK0 X0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l11 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l12 sK0 X0]
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ X0)]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54222 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54222 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ sK0) sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l19 sK0 X0]
  have l27 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 sK0 X0 X1]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l10 sK0 X0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l29 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l17 sK0 X0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l30 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l15 X0 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l32 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [l27 sK0 X0 X1]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l28 sK0 X0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1, 2]; rw [← l29 X0 sK0]
  have l35 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 X1 X0]
  have l36 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l30 X0 sK0]
    conv => enter [1]; rw [← l33 sK0 X0]
  have l37 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l35 sK0 X1 X0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← l36 X0 sK0]
  have l39 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l40 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l39 sK0 X1 X0]
  have l41 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l37 sK0 sK0 X1]
    conv => enter [1]; rw [l40 sK0 sK0 X1]
  have l42 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l41 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54222 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l43 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l30 X0 sK0]
    conv => enter [1]; rw [l42 X0 sK0 X1]
  have l44 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l38 sK0 X0]
    conv => enter [1]; rw [l43 X0 sK0 X1]
  intro x y z
  conv => enter [1]; rw [l44 x y z]

theorem Equation4512_54222_implies_Equation54181 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54181 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l6 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l7 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l11 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l12 X0 sK0 X1]
    conv => enter [1]; rw [l9 sK0 (X0 ◇ X1)]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l13 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l15 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l5 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l16 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l15 sK2 X0]
    conv => enter [1]; rw [← h54222 X0 sK2 (sK2 ◇ sK2)]
  have l17 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [l16 sK2 X0]
  have l18 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l17 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l19 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l18 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) X0 X1]
  have l20 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l19 X0 sK2 X1]
    conv => enter [1]; rw [l16 sK2 (X0 ◇ X1)]
  have l21 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l20 X0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l22 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h54222 (sK2 ◇ (sK2 ◇ sK2)) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [l7 sK0 sK2]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 sK0]
  have l24 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54222 X0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54222 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54222 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l27 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [← h54222 X0 sK2 sK2]
  have l28 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54222 X0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ X0)]
  have l29 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l30 : ∀ X1 sK0 X0 : G, ((X1 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l9 sK0 (X1 ◇ ((sK0 ◇ sK0) ◇ X0))]
    conv => enter [1, 2]; rw [← h54222 X0 (sK0 ◇ sK0) X1]
  have l31 : ∀ X1 sK2 X0 : G, ((X1 ◇ ((sK2 ◇ sK2) ◇ X0)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [← l16 sK2 (X1 ◇ ((sK2 ◇ sK2) ◇ X0))]
    conv => enter [1, 2]; rw [← h54222 X0 (sK2 ◇ sK2) X1]
  have l32 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((X1 ◇ ((sK2 ◇ sK2) ◇ X0)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h54222 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [← l31 X1 sK2 X0]
  have l33 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((X1 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l30 X1 sK0 X0]
  have l34 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [l29 sK0 X0 X1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l37 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l22 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l38 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l32 sK2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 ((sK2 ◇ sK2) ◇ X0) (sK2 ◇ sK2)]
  have l39 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l33 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ sK0)]
  have l40 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l34 sK0 X1 X0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l43 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l37 sK0 X0 sK2]
    conv => enter [1]; rw [l27 sK2 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l44 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l38 sK2 X1 X0]
    conv => enter [1]; rw [← l21 X1 sK2 ((sK2 ◇ sK2) ◇ X0)]
  have l45 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l39 sK0 X1 X0]
    conv => enter [1]; rw [← l14 X1 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l46 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l40 sK0 X1 X0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l23 sK0 sK0]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l48 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l43 sK0 X0 sK2]
  have l49 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l44 sK2 X1 X0]
    conv => enter [1, 2]; rw [l16 sK2 X0]
  have l50 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l45 sK0 X1 X0]
    conv => enter [1, 2]; rw [l9 sK0 X0]
  have l51 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l46 sK0 sK0 ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)]
    conv => enter [1]; rw [← l48 sK0 sK2 sK0]
  have l52 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l16 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l49 sK2 X1 X0]
  have l53 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l50 sK0 X1 X0]
  have l54 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l51 sK0 sK2]
    conv => enter [1]; rw [l9 sK0 (sK2 ◇ sK2)]
  have l55 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [← l27 sK2 sK2]
    conv => enter [1]; rw [← l5 sK2 sK2]
  have l56 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l23 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0]
  have l57 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l16 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l54 sK0 sK2]
  have l58 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l57 sK0 sK2]
    conv => enter [1]; rw [← l53 sK0 (sK2 ◇ sK2) sK0]
  have l59 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l56 sK0]
    conv => enter [1]; rw [← l58 sK0 sK2]
  have l60 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l59 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK2 ◇ sK2)]
  have l61 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [l60 sK1 sK0 sK2]
  have l62 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l61 sK1 sK0 sK2]
    conv => enter [1]; rw [l2 sK0 sK1 (sK2 ◇ sK2)]
  have l63 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1, 2, 2]; rw [l61 sK1 sK0 sK2]
    conv => enter [1]; rw [← h54222 (sK2 ◇ sK2) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l64 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l63 sK1 sK0 X0 sK2]
    conv => enter [1]; rw [l24 (sK2 ◇ sK2) sK1 sK0]
  have l65 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l52 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l62 sK0 sK1 sK2]
  have l66 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l52 sK2 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l64 sK1 sK0 X0 sK2]
  have l67 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l65 sK2 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
  have l68 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l66 sK2 sK1 sK0 sK2]
    conv => enter [1]; rw [← h54222 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK2]
  have l69 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l47 sK0 sK0]
    conv => enter [1]; rw [← l67 sK2 sK0 sK0]
  have l70 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l68 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l71 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l55 sK2]
    conv => enter [1]; rw [← l69 sK0 sK2]
  have l72 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l41 sK0 sK0]
    conv => enter [1]; rw [← l70 sK2 sK0 sK0]
  have l73 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l71 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l74 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l56 sK0]
    conv => enter [1]; rw [← l73 sK2 sK0]
  have l75 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l72 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l76 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l75 sK0 X0 sK2]
    conv => enter [1]; rw [l16 sK2 X0]
  have l77 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l76 sK0 X0 sK2]
  have l78 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l23 sK0 X0]
    conv => enter [1]; rw [l77 sK0 X0 sK2]
  have l79 : ∀ X0 X1 sK0 sK2 : G, ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l78 X1 sK0 sK2]
  have l80 : ∀ X0 X1 sK0 sK2 : G, ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l79 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← l52 sK2 X0 X1]
  have l81 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [l55 sK2]
    conv => enter [1]; rw [← l80 X0 X1 sK0 sK2]
  have l82 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [l81 sK2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l83 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l82 sK0 X0 X1 sK0]
  have l84 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l78 sK0 sK2 sK0]
    conv => enter [1]; rw [l83 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l84 x y x z]

theorem Equation4512_54222_implies_Equation54211 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54211 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54222 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation4512_54222_implies_Equation54179 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54179 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK2 ◇ sK2)]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [← l2 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK2 ◇ sK2) X0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l4 sK1 sK2]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l9 sK1 X0]
    conv => enter [1]; rw [← h54222 X0 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l10 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l12 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l10 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK2 ◇ sK2)]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l10 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK1 X0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l10 sK1 X0]
  have l15 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 1]; rw [l10 sK1 X0]
  have l16 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l15 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 X0]
    conv => enter [1]; rw [← h54222 X0 (sK1 ◇ sK1) sK1]
  have l18 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l12 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l19 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l20 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l16 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l21 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← l17 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK1 ◇ sK1)]
  have l22 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l20 X0 sK1 X1]
    conv => enter [1]; rw [l10 sK1 (X0 ◇ X1)]
  have l23 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l22 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l24 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l18 sK2 sK1]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l23 sK1 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l24 sK1 sK2]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l27 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l26 sK1 sK2]
  have l28 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l27 sK1 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l28 sK1 sK2]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK2 ◇ sK2))]
  have l31 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l30 sK0 sK1 sK2]
  have l32 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l31 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l33 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l3 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l34 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l33 sK2 X0]
    conv => enter [1]; rw [← h54222 X0 sK2 (sK2 ◇ sK2)]
  have l35 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l34 sK2 X0]
  have l36 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [l34 sK2 X0]
  have l37 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l36 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l38 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l37 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) X0 X1]
  have l39 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l38 X0 sK2 X1]
    conv => enter [1]; rw [l34 sK2 (X0 ◇ X1)]
  have l40 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l39 X0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l41 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l44 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l21 sK2 sK1]
  have l45 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l10 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l21 (sK1 ◇ sK1) sK1]
  have l46 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l21 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l47 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK1 ◇ sK1)]
  have l48 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [← l45 sK1]
  have l49 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l44 sK2 sK1]
    conv => enter [1]; rw [← h54222 (sK1 ◇ sK1) sK2 sK1]
  have l50 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 (sK0 ◇ (sK1 ◇ sK1)) sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l47 sK0 sK1 sK2]
  have l51 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
    conv => enter [1]; rw [l32 sK0 sK1 sK2 (sK1 ◇ sK1)]
  have l52 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2)) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l49 sK2 sK1]
    conv => enter [1]; rw [l21 (sK2 ◇ sK2) sK1]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 (sK0 ◇ (sK1 ◇ sK1)) sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l54 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l52 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ sK1)]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l53 sK0 sK1 sK2]
  have l56 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l54 sK1 sK2]
  have l57 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
    conv => enter [1]; rw [l14 sK0 sK1 (sK2 ◇ sK2)]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l57 sK0 sK1 sK2]
  have l59 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l58 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ sK1)]
  have l60 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
  have l61 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l60 sK0 sK1 sK2]
  have l62 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l48 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l63 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l62 sK1 X0]
    conv => enter [1]; rw [l10 sK1 X0]
  have l64 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l63 sK1 X0]
  have l65 : ∀ sK2 X0 sK1 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK2 X0 sK1 X1
    conv => enter [1]; rw [h54222 ((sK2 ◇ sK2) ◇ X0) sK1 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK2 ◇ sK2) X0]
  have l66 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54222 (sK2 ◇ (sK2 ◇ sK2)) sK1 X0]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK2]
  have l67 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54222 (sK2 ◇ (sK2 ◇ sK2)) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [l8 sK1 sK2]
  have l68 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54222 (sK2 ◇ sK2) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK2 ◇ sK2)]
  have l69 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X0) ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 X1 X2]
    conv => enter [1]; rw [← h54222 (X1 ◇ X0) X2 X1]
  have l70 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [← h54222 X0 sK2 sK2]
  have l71 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ (sK1 ◇ X0))]
  have l72 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = ((X1 ◇ ((sK1 ◇ sK1) ◇ X0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 (sK1 ◇ sK1) X1]
    conv => enter [1]; rw [l10 sK1 (X1 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l73 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l3 sK2 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1]; rw [← h54222 X0 (sK2 ◇ sK2) sK2]
  have l74 : ∀ X1 sK2 X0 : G, ((X1 ◇ ((sK2 ◇ sK2) ◇ X0)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [← l34 sK2 (X1 ◇ ((sK2 ◇ sK2) ◇ X0))]
    conv => enter [1, 2]; rw [← h54222 X0 (sK2 ◇ sK2) X1]
  have l75 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((X1 ◇ ((sK2 ◇ sK2) ◇ X0)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h54222 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [← l74 X1 sK2 X0]
  have l76 : ∀ sK2 X0 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← l34 sK2 X0]
    conv => enter [1]; rw [l73 sK2 X0]
  have l77 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = (X1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l72 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X1 ((sK1 ◇ sK1) ◇ X0) (sK1 ◇ sK1)]
  have l78 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h54222 sK1 sK1 X0]
    conv => enter [1]; rw [l71 sK1 X0 X1]
  have l79 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l69 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ X2)]
  have l80 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l21 (sK2 ◇ sK2) sK1]
    conv => enter [1]; rw [l68 sK2 sK1 X0]
  have l81 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l67 sK2 sK1 X0]
  have l82 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [← l66 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) (sK1 ◇ sK1)]
  have l83 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [← l65 sK2 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) X0 (sK1 ◇ sK1)]
  have l84 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (((sK2 ◇ sK2) ◇ X0) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l75 sK2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 ((sK2 ◇ sK2) ◇ X0) (sK2 ◇ sK2)]
  have l85 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h54222 sK2 sK2 X0]
    conv => enter [1]; rw [l76 sK2 X0]
  have l86 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l77 sK1 X0 X1]
    conv => enter [1]; rw [← l23 X1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l87 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l78 sK1 X1 X0]
  have l88 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l80 sK1 sK2 X0]
  have l89 : ∀ sK1 sK2 X0 : G, (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l70 sK2 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l81 sK2 sK1 X0]
  have l90 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l82 sK1 X0 sK2]
    conv => enter [1]; rw [l70 sK2 (sK1 ◇ sK1)]
  have l91 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) = (sK1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [l83 sK1 X1 sK2 X0]
    conv => enter [1]; rw [l79 (sK2 ◇ sK2) X0 sK1]
  have l92 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l84 sK2 X1 X0]
    conv => enter [1]; rw [← l40 X1 sK2 ((sK2 ◇ sK2) ◇ X0)]
  have l93 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l86 sK1 X0 X1]
    conv => enter [1, 2]; rw [l10 sK1 X0]
  have l94 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l87 sK1 X1 X0]
  have l95 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [l88 sK1 sK2 X0]
  have l96 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l89 sK1 sK2 X0]
  have l97 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l90 sK1 X0 sK2]
  have l98 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 2]; rw [l85 sK2 X0]
    conv => enter [1]; rw [← l91 sK1 X1 sK2 X0]
  have l99 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l92 sK2 X1 X0]
    conv => enter [1, 2]; rw [l34 sK2 X0]
  have l100 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h54222 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l93 sK1 X0 X1]
  have l101 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l94 sK1 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l95 sK1 sK2 sK1]
  have l102 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l94 sK1 sK1 ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)]
    conv => enter [1]; rw [← l96 sK1 sK2 sK1]
  have l103 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l97 sK1 sK2 X0]
  have l104 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l98 sK1 sK2 X1 X0]
  have l105 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l34 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l99 sK2 X1 X0]
  have l106 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l10 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l100 sK1 X1 X0]
  have l107 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l102 sK1 sK2]
    conv => enter [1]; rw [l10 sK1 (sK2 ◇ sK2)]
  have l108 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l103 sK1 sK2 X0]
  have l109 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l48 sK1]
    conv => enter [1]; rw [l106 sK1 X1 X0]
  have l110 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l108 sK1 sK2 sK1]
    conv => enter [1]; rw [← l104 sK1 sK2 sK1 sK2]
  have l111 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [← l70 sK2 sK2]
    conv => enter [1]; rw [← l3 sK2 sK2]
  have l112 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l101 sK1 sK2]
  have l113 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l101 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK2 ◇ sK2))]
  have l114 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l113 sK0 sK1 sK2]
    conv => enter [1]; rw [← l61 sK0 sK1 sK2]
  have l115 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l112 sK0 sK1 sK2]
  have l116 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l114 sK0 sK1 sK2]
  have l117 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l115 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ sK1)]
  have l118 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l56 sK1 sK2]
    conv => enter [1]; rw [← l28 sK1 sK2]
  have l119 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l101 sK1 sK2]
    conv => enter [1]; rw [← l118 sK1 sK2]
  have l120 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l107 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK1 ◇ sK1) X0]
  have l121 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l120 sK1 X0 sK2]
  have l122 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l64 sK1 X0]
    conv => enter [1]; rw [l121 sK1 X0 sK2]
  have l123 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l111 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l124 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l123 sK1 sK2]
  have l125 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l110 sK1 sK2]
    conv => enter [1]; rw [l124 sK1 sK2]
  have l126 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l119 sK1 sK2]
    conv => enter [1]; rw [l125 sK1 sK2]
  have l127 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l117 sK0 sK1 sK2]
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
  have l128 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l126 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X0]
  have l129 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l128 sK1 X0 sK2]
    conv => enter [1]; rw [l35 sK1 sK2 X0]
  have l130 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l129 sK1 X0 sK2]
    conv => enter [1]; rw [← l105 sK2 sK1 X0]
  have l131 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l130 sK1 X0 sK2]
    conv => enter [1]; rw [← l111 sK2]
  have l132 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l131 sK1 X0 sK2]
  have l133 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h54222 sK2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l126 sK1 sK2]
  have l134 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l109 sK1 sK2 sK1]
    conv => enter [1]; rw [← l133 sK2 sK1]
  have l135 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [h54222 sK2 sK2 sK1]
    conv => enter [1]; rw [l3 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l136 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l135 sK2 sK1]
    conv => enter [1]; rw [l70 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l137 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l126 sK1 sK2]
    conv => enter [1]; rw [← l136 sK2 sK1]
  have l138 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l137 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ sK2)]
  have l139 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l138 sK1 sK2]
    conv => enter [1]; rw [l70 sK2 (sK2 ◇ sK2)]
  have l140 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l139 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l141 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l140 sK1 X0 sK2]
    conv => enter [1]; rw [l34 sK2 X0]
  have l142 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l141 sK1 X0 sK2]
  have l143 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l64 sK1 X0]
    conv => enter [1]; rw [l142 sK1 X0 sK2]
  have l144 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l116 sK0 sK1 sK0]
    conv => enter [1]; rw [l143 (sK0 ◇ (sK1 ◇ sK1)) sK0 sK1]
  have l145 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l144 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l146 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54222 sK1 sK1 sK0]
    conv => enter [1]; rw [← l145 sK0 sK1]
  have l147 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l143 sK1 sK2 sK1]
    conv => enter [1]; rw [l146 sK1 sK0]
  have l148 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l143 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l149 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l148 sK1 sK2 X0]
    conv => enter [1]; rw [l132 sK1 X0 sK2]
  have l150 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l149 sK1 sK2 X0]
    conv => enter [1]; rw [l134 sK2 sK1]
  have l151 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l143 sK1 sK2 sK1]
    conv => enter [1]; rw [← l150 sK1 sK2 X0]
  have l152 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1, 2]; rw [h54222 (sK2 ◇ sK2) sK1 X0]
    conv => enter [1]; rw [← h54222 (sK1 ◇ (sK2 ◇ sK2)) X0 sK1]
  have l153 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l151 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1]; rw [← l152 X0 sK2 sK1]
  have l154 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l107 sK1 sK2]
    conv => enter [1]; rw [h54222 (sK2 ◇ sK2) sK1 sK0]
  have l155 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l153 sK1 sK2 X0]
    conv => enter [1]; rw [l23 X0 sK2 (sK1 ◇ sK1)]
  have l156 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l143 sK1 sK2 sK1]
    conv => enter [1]; rw [l154 sK1 sK0 sK2]
  have l157 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l155 sK1 sK2 sK1]
    conv => enter [1]; rw [← l105 sK2 sK1 (sK1 ◇ sK1)]
  have l158 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l157 sK1 sK2]
    conv => enter [1]; rw [l143 (sK2 ◇ sK2) sK2 sK1]
  have l159 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l156 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l160 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l119 sK1 sK2]
    conv => enter [1]; rw [l159 sK1 sK2 sK0]
  have l161 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l143 sK1 sK2 sK1]
    conv => enter [1]; rw [l160 sK1 sK0 sK2]
  have l162 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l158 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK1 ◇ sK1) X0]
  have l163 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l151 sK1 sK2 X0]
    conv => enter [1]; rw [l162 sK1 sK2 X0]
  have l164 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l161 sK1 sK2 sK0]
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l165 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l161 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l166 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l164 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l167 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l166 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l168 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l165 sK0 sK1 sK2]
    conv => enter [1]; rw [← l167 sK0 sK1 sK2]
  have l169 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l168 sK0 sK1 sK2]
    conv => enter [1]; rw [← l127 sK0 sK1 sK2]
  have l170 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l147 sK1 sK2 sK0]
    conv => enter [1]; rw [← l169 sK0 sK1 sK2]
  have l171 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK2 ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l163 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) ((sK1 ◇ sK1) ◇ X0) X1]
  have l172 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l171 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l173 : ∀ X0 X1 sK1 sK2 : G, ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l122 (X0 ◇ X1) sK1 sK2]
    conv => enter [1]; rw [← l172 sK1 sK2 X1 X0]
  have l174 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l151 sK1 sK2 X1]
    conv => enter [1]; rw [← l173 X0 X1 sK1 sK2]
  have l175 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l174 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l176 : ∀ sK1 sK2 X1 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK1 sK2 X1 X0 sK0
    conv => enter [1, 1]; rw [l175 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l177 : ∀ sK1 sK2 X0 sK0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK1 sK2 X0 sK0 X1
    conv => enter [1]; rw [l151 sK1 sK2 X1]
    conv => enter [1]; rw [l176 sK1 sK2 X1 X0 sK0]
  have l178 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l177 sK1 sK2 X0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54222 X1 X0 (sK1 ◇ (sK1 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l178 x y y z]
  conv => enter [1]; rw [l170 y z x]

theorem Equation4512_54222_implies_Equation54176 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54176 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK2]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l3 sK1 X0]
    conv => enter [1]; rw [← h54222 X0 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l4 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK1 X0]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l4 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK2)]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l4 sK1 X0]
  have l8 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 1]; rw [l4 sK1 X0]
  have l9 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l8 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l10 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h54222 X0 (sK1 ◇ sK1) sK1]
  have l12 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l9 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l13 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← l11 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK1 ◇ sK1)]
  have l14 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l12 X0 sK1 X1]
    conv => enter [1]; rw [l4 sK1 (X0 ◇ X1)]
  have l15 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l14 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l16 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l10 sK1 sK2]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l16 sK1 sK2]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l18 sK1 sK2]
  have l20 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l19 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = ((sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 1]; rw [l7 sK0 sK1 X0]
  have l23 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = (sK0 ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l22 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK1 ◇ sK1)) X1]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [← l21 sK0 sK1 sK2]
  have l25 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l23 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK2]
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
  have l27 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [← l25 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l29 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1))) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l27 sK0 X0 sK1 X1]
    conv => enter [1]; rw [l7 sK0 sK1 (X0 ◇ X1)]
  have l30 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l15 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← l29 sK0 X0 sK1 X1]
  have l31 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (X0 ◇ X1)]
    conv => enter [1]; rw [l30 sK0 sK1 X0 X1]
  have l32 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54222 (sK1 ◇ sK2) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK2)]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54222 (sK1 ◇ sK1) sK1 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l34 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [← h54222 X0 sK1 sK1]
  have l35 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ (sK1 ◇ X0))]
  have l36 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ ((X1 ◇ ((sK1 ◇ sK1) ◇ X0)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [← l7 sK0 sK1 (X1 ◇ ((sK1 ◇ sK1) ◇ X0))]
    conv => enter [1, 2]; rw [← h54222 X0 (sK1 ◇ sK1) X1]
  have l37 : ∀ X1 sK1 X0 : G, ((X1 ◇ ((sK1 ◇ sK1) ◇ X0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [← l4 sK1 (X1 ◇ ((sK1 ◇ sK1) ◇ X0))]
    conv => enter [1, 2]; rw [← h54222 X0 (sK1 ◇ sK1) X1]
  have l38 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (X1 ◇ ((sK1 ◇ sK1) ◇ X0))]
    conv => enter [1, 2]; rw [← h54222 X0 (sK1 ◇ sK1) X1]
  have l39 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l31 sK0 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l38 sK0 sK1 X1 X0]
  have l40 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((X1 ◇ ((sK1 ◇ sK1) ◇ X0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h54222 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l37 X1 sK1 X0]
  have l41 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l36 sK0 X1 sK1 X0]
    conv => enter [1]; rw [← l15 sK0 sK1 (X1 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l42 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h54222 sK1 sK1 X0]
    conv => enter [1]; rw [l35 sK1 X0 X1]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l33 sK1 sK0]
  have l44 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l13 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [l32 sK1 sK2 X0]
  have l45 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l40 sK1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 ((sK1 ◇ sK1) ◇ X0) (sK1 ◇ sK1)]
  have l46 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l41 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X1 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l47 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l42 sK1 X1 X0]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l15 sK1 sK1 sK1]
    conv => enter [1]; rw [l43 sK1 sK0]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l34 sK1 sK1]
    conv => enter [1]; rw [l43 sK1 sK0]
  have l50 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l44 sK1 sK2 X0]
  have l51 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l45 sK1 X1 X0]
    conv => enter [1]; rw [← l15 X1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l52 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l39 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l46 sK0 sK1 X0 sK0]
  have l53 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l47 sK1 X1 X0]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l48 sK1 sK0]
  have l55 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK2]
    conv => enter [1]; rw [l50 sK1 sK2 X0]
  have l56 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l51 sK1 X1 X0]
    conv => enter [1, 2]; rw [l4 sK1 X0]
  have l57 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l52 sK0 sK1 X0]
    conv => enter [1]; rw [← l39 sK0 sK1 (sK1 ◇ sK1) X0]
  have l58 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l49 sK1 sK1]
    conv => enter [1]; rw [← l54 sK1 sK1]
  have l59 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l53 sK1 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l55 sK1 sK2 sK1]
  have l60 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l4 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l56 sK1 X1 X0]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l57 sK0 sK1 X0]
    conv => enter [1]; rw [l7 sK0 sK1 (sK1 ◇ sK1)]
  have l62 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l58 sK1]
    conv => enter [1]; rw [l60 sK1 X1 X0]
  have l63 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l61 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [l63 sK0 sK1 sK1]
  have l65 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l59 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK2))]
  have l66 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [← l65 sK0 sK1 sK2]
  have l67 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l66 sK0 sK1 sK2]
    conv => enter [1]; rw [← l62 sK1 sK0 sK1]
  have l68 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l64 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l69 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l68 sK1 X0 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l70 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l62 sK1 sK1 X0]
    conv => enter [1]; rw [← l69 sK1 X0 sK1]
  have l71 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l70 sK1 X0]
  have l72 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l67 sK0 sK1 sK2]
    conv => enter [1]; rw [← l71 sK1 X0]
  have l73 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l72 sK0 sK1 sK2 (sK1 ◇ X0)]
    conv => enter [1]; rw [← h54222 X0 sK1 (sK1 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l73 x y z x]

theorem Equation4512_54222_implies_Equation54208 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54208 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l1 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l4 sK1 X0]
    conv => enter [1]; rw [← h54222 X0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK0)]
  have l7 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 1]; rw [l5 sK1 X0]
  have l8 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l7 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l8 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l12 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l10 X0 sK1 X1]
    conv => enter [1]; rw [l5 sK1 (X0 ◇ X1)]
  have l13 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l12 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l11 sK0 sK1]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l21 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54222 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1 X0]
    conv => enter [1, 2, 2]; rw [← l11 sK0 sK1]
  have l22 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X0) ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 X1 X2]
    conv => enter [1]; rw [← h54222 (X1 ◇ X0) X2 X1]
  have l23 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54222 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l24 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X1 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54222 X0 X1 X2]
  have l25 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l24 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l26 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l22 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ X2)]
  have l27 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l21 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1)]
  have l28 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l25 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l29 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l27 sK1 X0 sK0]
    conv => enter [1]; rw [l26 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ sK0)) sK1]
  have l30 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h54222 (sK0 ◇ sK0) sK1 X0]
  have l31 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l28 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ X0) X3]
  have l32 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l29 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l3 sK1 sK0 (sK1 ◇ sK1)]
  have l33 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l31 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l34 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l32 sK1 X0 sK0]
  have l35 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l33 X0 X1 X3 X0]
    conv => enter [1]; rw [← h54222 (X0 ◇ X3) X1 X0]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l34 sK1 sK0 X0]
  have l37 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X3 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l35 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 X3 (X1 ◇ X1)]
  have l38 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 sK1 X0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l40 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 sK0 X1
    conv => enter [1, 2, 2]; rw [l30 sK0 sK1 X1]
    conv => enter [1]; rw [← h54222 (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1 X0]
  have l41 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [l40 sK1 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X1 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1)]
  have l42 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [l41 sK1 X0 sK0 X1]
    conv => enter [1]; rw [← l37 X1 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l43 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [l42 sK1 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l44 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [l43 sK1 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l39 sK0 sK1]
  have l45 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l38 sK0 sK1 sK0]
    conv => enter [1]; rw [l44 sK1 sK0 sK0 X1]
  have l46 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 2, 2]; rw [l45 sK0 sK1 X0]
    conv => enter [1]; rw [← h54222 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 X1]
  have l47 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l45 sK0 sK1 X0]
    conv => enter [1]; rw [l46 X0 X0 sK0 sK1]
  have l48 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l45 sK0 sK1 X0]
    conv => enter [1]; rw [l47 X0 sK0 sK1]
  have l49 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l48 sK0 sK1 X0]
    conv => enter [1]; rw [← h54222 X0 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l50 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l45 sK0 sK1 X0]
    conv => enter [1]; rw [l49 X0 sK0 sK1]
  have l51 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l50 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l52 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [l23 X1 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← l51 sK0 sK1 X0 X1]
  intro x y
  conv => enter [1]; rw [l52 x y y x]

theorem Equation4512_54222_implies_Equation54171 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54171 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l10 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l9 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l11 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l10 X0 sK0 X1]
    conv => enter [1]; rw [l7 sK0 (X0 ◇ X1)]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l11 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l4 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l13 sK1 X0]
    conv => enter [1]; rw [← h54222 X0 sK1 (sK1 ◇ sK1)]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK1 (sK0 ◇ sK0)]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l18 sK1 sK0 X0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1)]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK1 ◇ sK1) X0]
  have l23 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l14 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l25 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 1]; rw [l14 sK1 X0]
  have l26 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l25 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0 (sK1 ◇ sK1)]
  have l28 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ sK1)]
  have l29 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l26 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l30 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l29 X0 sK1 X1]
    conv => enter [1]; rw [l14 sK1 (X0 ◇ X1)]
  have l31 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l30 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l34 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54222 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l35 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54222 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0 X0]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54222 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK0)]
  have l37 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X0) ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 X1 X2]
    conv => enter [1]; rw [← h54222 (X1 ◇ X0) X2 X1]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← h54222 (sK0 ◇ (sK1 ◇ sK1)) sK0 sK1]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← h54222 (sK1 ◇ sK1) (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ sK0))]
  have l41 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ (sK1 ◇ X0))]
  have l42 : ∀ X1 sK0 X0 : G, ((X1 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l7 sK0 (X1 ◇ ((sK0 ◇ sK0) ◇ X0))]
    conv => enter [1, 2]; rw [← h54222 X0 (sK0 ◇ sK0) X1]
  have l43 : ∀ X1 sK1 X0 : G, ((X1 ◇ ((sK1 ◇ sK1) ◇ X0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [← l14 sK1 (X1 ◇ ((sK1 ◇ sK1) ◇ X0))]
    conv => enter [1, 2]; rw [← h54222 X0 (sK1 ◇ sK1) X1]
  have l44 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((X1 ◇ ((sK1 ◇ sK1) ◇ X0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h54222 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l43 X1 sK1 X0]
  have l45 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((X1 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l42 X1 sK0 X0]
  have l46 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h54222 sK1 sK1 X0]
    conv => enter [1]; rw [l41 sK1 X0 X1]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l40 sK1 sK0]
  have l48 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l37 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ X2)]
  have l49 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l36 sK0 sK1 X0]
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ sK1)]
  have l50 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l35 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l12 X0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l51 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l34 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ sK0)]
  have l52 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l44 sK1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 ((sK1 ◇ sK1) ◇ X0) (sK1 ◇ sK1)]
  have l53 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l45 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ sK0)]
  have l54 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l46 sK1 X1 X0]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0 (sK1 ◇ sK1)]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l39 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1)]
  have l57 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l49 sK1 X0 sK0]
    conv => enter [1]; rw [← l31 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l58 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l50 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l59 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [← l51 sK0 X1 X0]
  have l60 : ∀ X1 sK1 X0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l31 X1 sK1 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [← l52 sK1 X1 X0]
  have l61 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l53 sK0 X1 X0]
    conv => enter [1]; rw [← l12 X1 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l62 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l54 sK1 X1 X0]
  have l63 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← l55 sK1 sK0]
  have l64 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l57 sK1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l65 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l58 sK0 X0 sK1]
    conv => enter [1]; rw [l48 sK1 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l66 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l59 sK0 X1 X0]
  have l67 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l14 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l60 X1 sK1 X0]
  have l68 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l61 sK0 X1 X0]
    conv => enter [1, 2]; rw [l7 sK0 X0]
  have l69 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l64 sK1 sK1 sK0]
  have l70 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l65 sK0 X0 sK1]
  have l71 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l66 sK0 X1 X0]
  have l72 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l67 sK1 X1 X0]
    conv => enter [1, 2]; rw [l14 sK1 X0]
  have l73 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l68 sK0 X1 X0]
  have l74 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l63 sK1 sK0]
    conv => enter [1]; rw [l72 sK1 X1 X0]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l70 sK0 sK1 sK0]
  have l76 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l38 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0]
  have l77 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2]; rw [← l56 sK0 sK1]
    conv => enter [1]; rw [← h54222 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l78 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l56 sK0 sK1]
  have l79 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l78 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK1 ◇ sK1) X0]
  have l80 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l69 sK1 sK0]
    conv => enter [1]; rw [← l77 sK0 sK1 X0]
  have l81 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l74 sK1 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l82 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1 (sK1 ◇ sK1)]
  have l83 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l84 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [← l83 sK0 sK1]
  have l85 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l84 sK0 sK1]
    conv => enter [1]; rw [← l74 sK1 sK0 (sK0 ◇ sK0) sK1]
  have l86 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK1 ◇ sK1) X0]
  have l87 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l86 sK0 X0 sK1]
  have l88 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l38 sK0 X0]
    conv => enter [1]; rw [l87 sK0 X0 sK1]
  have l89 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l63 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l90 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l63 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l91 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l90 sK1 sK0 X0]
    conv => enter [1]; rw [l14 sK1 X0]
  have l92 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l89 sK0 sK1]
  have l93 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l91 sK1 sK0 X0]
  have l94 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [l92 sK0 sK1]
  have l95 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l85 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1) X0]
  have l96 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l95 sK0 X0 sK1]
    conv => enter [1]; rw [l93 sK1 sK0 X0]
  have l97 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l96 sK0 X0 sK1]
  have l98 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l38 sK0 X0]
    conv => enter [1]; rw [l97 sK0 X0 sK1]
  have l99 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54222 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l94 sK0 sK1]
  have l100 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l73 sK0 sK0 sK0]
    conv => enter [1]; rw [← l99 sK1 sK0 sK0]
  have l101 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l69 sK1 sK0]
    conv => enter [1]; rw [← l100 sK0 sK1]
  have l102 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l101 sK1 sK0]
    conv => enter [1]; rw [l79 sK0 sK1 (sK0 ◇ sK0)]
  have l103 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l102 sK1 sK0]
  have l104 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l103 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ sK1)]
  have l105 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [← l104 sK0 sK1]
  have l106 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l76 sK0]
    conv => enter [1]; rw [← l105 sK1 sK0]
  have l107 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l98 sK1 sK0 sK1]
    conv => enter [1]; rw [l106 sK1 sK0]
  have l108 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l107 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l109 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l108 sK0 sK1]
    conv => enter [1]; rw [← l76 sK0]
  have l110 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l107 sK1 sK0]
    conv => enter [1]; rw [← l109 sK0 sK1]
  have l111 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l107 sK1 sK0]
    conv => enter [1]; rw [l98 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l111 x y]
  conv => enter [1]; rw [l110 y x]

theorem Equation4512_54222_implies_Equation54174 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54174 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l4 sK1 X0]
    conv => enter [1]; rw [← h54222 X0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l5 sK1 X0]
  have l8 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 1]; rw [l5 sK1 X0]
  have l9 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l8 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l10 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l9 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l11 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l10 X0 sK1 X1]
    conv => enter [1]; rw [l5 sK1 (X0 ◇ X1)]
  have l12 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l11 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [← h54222 X0 sK1 sK1]
  have l14 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54222 X0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ X0)]
  have l15 : ∀ X1 sK1 X0 : G, ((X1 ◇ ((sK1 ◇ sK1) ◇ X0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [← l5 sK1 (X1 ◇ ((sK1 ◇ sK1) ◇ X0))]
    conv => enter [1, 2]; rw [← h54222 X0 (sK1 ◇ sK1) X1]
  have l16 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((X1 ◇ ((sK1 ◇ sK1) ◇ X0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h54222 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l15 X1 sK1 X0]
  have l17 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l16 sK1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 ((sK1 ◇ sK1) ◇ X0) (sK1 ◇ sK1)]
  have l18 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h54222 (sK1 ◇ sK0) sK1 X0]
  have l19 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l17 sK1 X1 X0]
    conv => enter [1]; rw [← l12 X1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l20 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l19 sK1 X1 X0]
    conv => enter [1, 2]; rw [l5 sK1 X0]
  have l21 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l5 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l20 sK1 X1 X0]
  have l22 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l13 sK1 sK1]
    conv => enter [1]; rw [← l0 sK1 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54222 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l24 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h54222 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ sK0))]
  have l25 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((X0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l24 sK1 sK0 X0]
    conv => enter [1]; rw [l13 sK1 (X0 ◇ (sK1 ◇ sK0))]
  have l26 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l25 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK0) (sK1 ◇ sK1)]
  have l27 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l26 sK1 sK0 X0]
    conv => enter [1]; rw [← l12 X0 sK1 (sK1 ◇ sK0)]
  have l28 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l27 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK0)]
  have l29 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l28 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h54222 sK0 sK1 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h54222 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  have l31 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54222 (sK1 ◇ (sK1 ◇ sK0)) sK1 X0]
    conv => enter [1, 2, 2]; rw [← h54222 sK0 sK1 sK1]
  have l32 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l14 sK1 sK1 sK0]
    conv => enter [1]; rw [l31 sK1 sK0 X0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l30 sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l35 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54222 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l23 sK0 sK1]
  have l36 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l2 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l35 sK1 sK0 X0]
  have l37 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l18 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l36 sK1 sK0 X0]
  have l38 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l37 sK1 sK0 X0]
  have l39 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1, 2, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← h54222 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK1 sK0]
    conv => enter [1]; rw [l39 sK1 sK1 sK0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54222 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l34 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l29 sK1 sK0 (sK1 ◇ sK0)]
  have l44 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [l29 sK1 sK0 X0]
  have l45 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l38 sK0 sK1 X0]
    conv => enter [1]; rw [← h54222 (sK0 ◇ (sK1 ◇ sK1)) X0 (sK1 ◇ (sK1 ◇ sK0))]
  have l46 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l44 sK0 sK1 X0]
    conv => enter [1]; rw [l45 X0 sK0 sK1]
  have l47 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l48 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l47 sK1 X0 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l49 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l48 sK1 X0 sK1]
    conv => enter [1]; rw [← l21 sK1 sK1 X0]
  have l50 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [← l49 sK1 X0]
  have l51 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l50 sK1 X0]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0]
  have l53 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l54 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l53 sK0 sK1 X0]
    conv => enter [1]; rw [l51 sK1 X0]
  have l55 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l54 sK0 sK1 X0]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l56 x y]

theorem Equation4512_54222_implies_Equation54201 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation54201 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54222 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation4512_54222_implies_Equation53827 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation53827 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l11 sK0 X0]
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ X0)]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← l6 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [l18 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l24 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l24 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l27 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54222 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l25 sK0]
    conv => enter [1]; rw [h54222 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l25 sK0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l30 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54222 X0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ X0)]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l23 sK0 sK0]
    conv => enter [1]; rw [l28 sK0 X0]
  have l35 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [← h54222 sK2 sK1 X0]
    conv => enter [1]; rw [l30 sK2 sK1 sK0 sK2]
  have l36 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l27 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ sK0)]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1, 2]; rw [← l26 sK0]
  have l38 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 sK0]
    conv => enter [1]; rw [l33 sK0 X0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l34 sK0 X0]
  have l40 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [← l36 sK0 X1 X0]
  have l41 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l37 sK0 X0]
    conv => enter [1]; rw [l19 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l42 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 X0]
    conv => enter [1, 2]; rw [← l38 X0 sK0]
  have l43 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l40 sK0 X1 X0]
  have l44 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l41 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l45 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l43 sK0 X1 X0]
  have l46 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l38 X0 sK0]
    conv => enter [1]; rw [l44 X0 sK0]
    conv => enter [1, 2]; rw [← l38 X0 sK0]
  have l47 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0 X0]
    conv => enter [1]; rw [← l46 X0 sK0]
  have l48 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l49 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l48 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l50 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l45 sK0 sK0 X1]
    conv => enter [1]; rw [← l49 sK0 X1 sK0]
  have l51 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l50 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54222 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l52 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l38 X0 sK0]
    conv => enter [1]; rw [l51 X0 sK0 X1]
  have l53 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l47 sK0 X0]
    conv => enter [1]; rw [l52 X0 sK0 X1]
  have l54 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l55 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l54 sK0 sK1 sK2]
  have l56 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l55 sK1 sK0 sK2]
    conv => enter [1]; rw [← l38 sK1 sK0]
  have l57 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l56 sK1 sK0 sK2]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1]; rw [← l35 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l58 x y z]

theorem Equation4512_54222_implies_Equation53814 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation53814 G := by
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
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l10 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l12 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l10 sK0 sK2]
    conv => enter [1, 2]; rw [l8 sK0 sK2]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X1]
    conv => enter [1, 1]; rw [l10 sK0 X0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l15 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l12 sK2 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK2)]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l14 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l18 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l17 X0 sK0 X1]
    conv => enter [1]; rw [l10 sK0 (X0 ◇ X1)]
  have l19 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l18 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l16 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l21 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← l15 sK2 sK0]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l19 sK0 sK0 sK2]
    conv => enter [1]; rw [← l21 sK0 sK2]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK2)]
  have l24 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [l23 sK0 sK2]
  have l25 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l24 sK0 sK2]
    conv => enter [1]; rw [l20 sK0 sK2]
    conv => enter [1, 2]; rw [l24 sK0 sK2]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l20 sK0 X0]
    conv => enter [1]; rw [l10 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l10 sK0 X0]
    conv => enter [1]; rw [l27 sK0 X0]
  have l29 : ∀ sK0 sK2 X0 : G, (((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h54222 ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l25 sK0 sK2]
  have l30 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)))) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1, 2, 2]; rw [← l24 sK0 sK2]
    conv => enter [1]; rw [← h54222 sK2 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l10 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l32 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54222 X0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ X0)]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1, 2]; rw [← l16 sK0]
  have l34 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l30 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← l16 sK0]
  have l35 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l29 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l36 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l28 X0 sK0]
    conv => enter [1]; rw [l33 sK0 X0]
  have l37 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l35 sK0 X0 sK2]
    conv => enter [1, 2]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l38 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l37 sK0 X0 sK2]
    conv => enter [1]; rw [← l19 (sK0 ◇ sK2) sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [l36 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l38 sK0 X0 sK2]
  have l40 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l39 sK0 sK2 sK0]
    conv => enter [1]; rw [l34 sK0 sK0 sK2]
  have l41 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l36 sK2 sK0]
    conv => enter [1]; rw [← l40 sK0 sK2]
  have l42 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l41 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l43 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l32 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK2]
    conv => enter [1]; rw [← l42 sK2 sK0]
  have l44 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l7 sK0]
    conv => enter [1]; rw [l43 sK0 sK2]
  have l45 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l36 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l44 sK0 sK2]
  have l46 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l45 sK0 sK2]
  have l47 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l36 sK0 sK0]
    conv => enter [1]; rw [l46 sK0 sK2]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54222 sK2 sK0 sK1]
    conv => enter [1]; rw [← l47 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l48 x y z]

theorem Equation4512_54222_implies_Equation53824 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation53824 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l6 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l8 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l9 sK0 X0]
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l6 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54222 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l14 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l13 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [← l14 sK0 X1 X0]
  have l16 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 X1 X0]
  have l17 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 X1 X0]
  have l18 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l19 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l18 sK0 X1 X0]
  have l20 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l17 sK0 sK0 X1]
    conv => enter [1]; rw [l19 sK0 sK0 X1]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l12 X0 sK0]
  have l22 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l21 sK0 X0]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l20 sK0 X1]
    conv => enter [1]; rw [← l22 X0 sK0 X1]
  have l24 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l23 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

theorem Equation4512_54222_implies_Equation53817 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation53817 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l11 sK0 X0]
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ X0)]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← l6 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [l18 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l24 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l24 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l27 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54222 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l25 sK0]
    conv => enter [1]; rw [h54222 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l25 sK0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l23 sK0 sK0]
    conv => enter [1]; rw [l28 sK0 X0]
  have l34 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l27 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ sK0)]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1, 2]; rw [← l26 sK0]
  have l36 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 sK0]
    conv => enter [1]; rw [l32 sK0 X0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l33 sK0 X0]
  have l38 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [← l34 sK0 X1 X0]
  have l39 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l35 sK0 X0]
    conv => enter [1]; rw [l19 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l40 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 X0]
    conv => enter [1, 2]; rw [← l36 X0 sK0]
  have l41 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l38 sK0 X1 X0]
  have l42 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l39 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l43 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l41 sK0 X1 X0]
  have l44 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l36 X0 sK0]
    conv => enter [1]; rw [l42 X0 sK0]
    conv => enter [1, 2]; rw [← l36 X0 sK0]
  have l45 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l40 sK0 X0]
    conv => enter [1]; rw [← l44 X0 sK0]
  have l46 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l47 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l46 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l48 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l43 sK0 sK0 X1]
    conv => enter [1]; rw [← l47 sK0 X1 sK0]
  have l49 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l48 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54222 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l50 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l36 X0 sK0]
    conv => enter [1]; rw [l49 X0 sK0 X1]
  have l51 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l45 sK0 X0]
    conv => enter [1]; rw [l50 X0 sK0 X1]
  have l52 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l51 sK0 X0 X1]
  have l53 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l48 sK0 X2]
    conv => enter [1]; rw [← l52 X0 X1 X2 sK0]
  have l54 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [← l53 sK0 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [← l54 x y z x]

theorem Equation4512_54222_implies_Equation53848 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation53848 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [l8 sK0 X0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l11 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l12 sK0 X0]
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ X0)]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54222 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54222 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ sK0) sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l19 sK0 X0]
  have l27 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 sK0 X0 X1]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l10 sK0 X0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l29 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l17 sK0 X0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l30 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l15 X0 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l32 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [l27 sK0 X0 X1]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l28 sK0 X0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1, 2]; rw [← l29 X0 sK0]
  have l35 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 X1 X0]
  have l36 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l30 X0 sK0]
    conv => enter [1]; rw [← l33 sK0 X0]
  have l37 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l35 sK0 X1 X0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← l36 X0 sK0]
  have l39 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l40 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l39 sK0 X1 X0]
  have l41 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l37 sK0 sK0 X1]
    conv => enter [1]; rw [l40 sK0 sK0 X1]
  have l42 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l41 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54222 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l43 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l30 X0 sK0]
    conv => enter [1]; rw [l42 X0 sK0 X1]
  have l44 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l38 sK0 X0]
    conv => enter [1]; rw [l43 X0 sK0 X1]
  have l45 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l44 sK0 sK2 sK1]
    conv => enter [1]; rw [h54222 sK2 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l45 x y z z]

theorem Equation4512_54222_implies_Equation53813 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54222 : Equation54222 G) : Equation53813 G := by
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
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l10 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l13 sK0 X0]
    conv => enter [1]; rw [l10 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l10 sK0 X0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l17 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54222 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l10 sK0 X0]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l19 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h54222 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h54222 X0 (sK0 ◇ sK0) sK0]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l13 sK0 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
    conv => enter [1, 2]; rw [← h54222 X0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54222 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l21 X0 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54222 sK0 sK0 X0]
    conv => enter [1]; rw [l19 sK0 X0 X1]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1, 2]; rw [← l12 sK0]
  have l26 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l17 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1, 2]; rw [← l12 sK0]
  have l28 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 X1 X0]
  have l29 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l16 X0 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l30 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l26 sK0 X0 sK1]
    conv => enter [1]; rw [← l23 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l27 sK0 X0]
  have l32 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l28 sK0 X1 X0]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l8 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l30 sK0 X0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l33 sK0 sK1 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l31 sK0 (sK0 ◇ sK1)]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← l36 sK1 sK0]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l29 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l38 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h54222 sK1 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l42 x y]

end Semigroup5
