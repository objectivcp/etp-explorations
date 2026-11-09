import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54354_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54354 : Equation54354 G) : Equation4271 G := by
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
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54354 sK0 X0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54354 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l6 sK0]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54354 X0 X1 X2]
    conv => enter [1]; rw [← h54354 X0 X3 X2]
  have l14 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X2 ◇ X3))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← h54354 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54354 sK0 X0 sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1, 2]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l11 sK0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54354 (sK0 ◇ sK0) X0 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [l3 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l21 sK0 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l27 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0 (sK0 ◇ sK0)]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l28 sK0]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [← l27 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l32 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 sK0]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l33 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l35 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
  have l36 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l35 sK0 X0 sK1 sK2]
  have l37 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [l36 sK0 X0 sK1 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l39 sK0 sK1 sK2]
  have l41 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54354 (sK0 ◇ sK0) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l40 sK0 sK1 sK2]
  have l42 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l41 sK0 X0 sK1 sK2]
  have l43 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l42 sK0 X0 sK1 sK2]
  have l44 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h54354 (sK1 ◇ sK2) X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l45 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l37 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
    conv => enter [1]; rw [← l44 sK0 sK1 sK2 X0]
  have l46 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l45 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ sK0)]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l48 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l47 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l49 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l46 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l50 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((X0 ◇ sK0) ◇ X1)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l46 sK0 sK1 sK2 X0]
  have l51 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l50 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2)) X1]
  have l52 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
    conv => enter [1]; rw [l49 sK0 sK1 sK2 X0 X1]
  have l53 : ∀ sK0 X1 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 sK1 sK2 X0
    conv => enter [1]; rw [l48 sK0 X1 sK1 sK2]
    conv => enter [1]; rw [← l51 sK0 sK1 sK2 X0 X1]
  have l54 : ∀ sK0 X1 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 sK1 sK2 X0
    conv => enter [1]; rw [l53 sK0 X1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l55 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l52 sK0 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [h54354 X0 sK0 sK0]
  have l56 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l55 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [← l54 sK0 (sK0 ◇ X0) sK0 sK0 X0]
  have l57 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l56 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l58 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l56 sK0 X0]
  have l59 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l58 sK0 X0 X1]
  have l60 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l59 sK0 X0 X1]
  have l61 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l34 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l60 sK0 X0 X1]
  have l62 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l57 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l63 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l61 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l62 sK0 X0]
  have l64 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l63 sK0 X0]
    conv => enter [1]; rw [← l30 sK0]
  have l65 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [← l64 sK0 X0]
  have l66 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l13 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l65 sK0 X2]
  have l67 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l66 X0 X0 sK2 sK0]
    conv => enter [1]; rw [l13 X0 X0 sK2 sK1]
  have l68 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l67 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l33 sK0]
  intro x y z
  conv => enter [1]; rw [← l68 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54378 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54378 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← h4271 X0 sK2 sK1]
    conv => enter [1]; rw [h4271 X0 sK2 (sK2 ◇ sK1)]
  have l1 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK1]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 x w y z]

theorem Equation4512_54378_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54378 : Equation54378 G) : Equation4271 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54378 sK0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l4 sK0 X0 X1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 (sK1 ◇ sK2)]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l8 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54381 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54381 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [← h4271 X0 sK2 sK2]
    conv => enter [1]; rw [h4271 X0 sK2 (sK2 ◇ sK2)]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK2]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 x w y z]

theorem Equation4512_54381_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54381 : Equation54381 G) : Equation4271 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54381 sK0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l4 sK0 X0 X1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 (sK1 ◇ sK2)]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l8 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54379 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54379 G := by
  have l0 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK2 (sK2 ◇ sK3)]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l0 sK1 sK2 sK3]
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 x w y z]

theorem Equation4512_54379_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54379 : Equation54379 G) : Equation4271 G := by
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
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54379 sK0 X0 X1 sK0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 sK0 X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l4 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 (sK1 ◇ sK2)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l17 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54357 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54357 G := by
  have l0 : ∀ X0 sK0 sK2 sK3 : G, (X0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK0 sK2 sK3
    conv => enter [1]; rw [← h4271 X0 sK0 sK2]
    conv => enter [1]; rw [h4271 X0 sK2 (sK2 ◇ sK3)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_54357_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54357 : Equation54357 G) : Equation4271 G := by
  have l0 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← h54357 X2 (X0 ◇ X1) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l1 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [l0 X2 sK0 X0 X2]
    conv => enter [1, 2]; rw [h54357 X0 X2 sK0 sK0]
  have l2 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [l1 X2 sK0 X0]
    conv => enter [1, 2]; rw [← h54357 X0 sK0 sK0 sK0]
  have l3 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [h54357 X2 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 X2 sK0 X0]
  have l4 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54357 X1 X2 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 X0 sK0 X0]
  have l5 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [l3 X1 sK0 X0]
    conv => enter [1]; rw [← l4 X1 X2 X0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l7 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l5 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 X0 sK0 sK0 (sK1 ◇ sK2)]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l9 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54382 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54382 G := by
  have l0 : ∀ X0 sK1 sK0 sK3 sK4 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK1 sK0 sK3 sK4
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK3 (sK3 ◇ sK4)]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation54382_implies_Equation4271 (G : Type*) [Magma G] (h54382 : Equation54382 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54382 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54382 X0 X5 X6 X0 X0]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x x y z]

@[equational_result]
theorem Equation4272_implies_Equation4351 (G : Type*) [Magma G] (h4272 : Equation4272 G) : Equation4351 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4272 sK1 sK0]
    conv => enter [1]; rw [h4272 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4351_implies_Equation4272 (G : Type*) [Magma G] (h4351 : Equation4351 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4351 x x y]

theorem Equation4272_4512_implies_Equation54257 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation54257 G := by
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
  have l2 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h4272 sK1 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 sK2]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4272 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4272 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1, 2]; rw [h4272 sK1 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_54257_implies_Equation4272 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54257 : Equation54257 G) : Equation4272 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54257 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54257 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation4272_4512_implies_Equation54292 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation54292 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4272 sK2 sK1]
    conv => enter [1]; rw [h4272 sK2 sK0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4272 sK2 sK1]
    conv => enter [1]; rw [h4272 sK2 X0]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [l1 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4272 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK2) sK2 sK1]
  have l3 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [← l2 sK2 sK1 sK3]
  have l4 : ∀ sK3 sK0 sK2 X0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [l2 sK2 sK1 X0]
  have l5 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4272 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l6 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l5 sK2 X0 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l7 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l4 sK3 sK0 sK2 sK3 sK3]
    conv => enter [1]; rw [← l6 sK2 sK3 sK3]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK2]
    conv => enter [1]; rw [← l7 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_54292_implies_Equation4272 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54292 : Equation54292 G) : Equation4272 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54292 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation4272_4512_implies_Equation54212 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation54212 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4272 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4272 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [h4272 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h4272 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54212_implies_Equation4272 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54212 : Equation54212 G) : Equation4272 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54212 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54212 X0 sK0]
  have l3 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation4272_4512_implies_Equation54274 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation54274 G := by
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
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 X0]
  have l4 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4272 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l4 sK1 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK2]
  have l6 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l5 sK1 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK1 sK0 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l8 z y x]

theorem Equation4512_54274_implies_Equation4272 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54274 : Equation54274 G) : Equation4272 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54274 X0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 X0]
  intro x y
  conv => enter [1]; rw [l2 x x y]

theorem Equation4272_4512_implies_Equation54223 (G : Type*) [Magma G] (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation54223 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4272 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4272 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h4272 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [← h4272 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [h4272 sK0 sK2]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4272 sK0 sK1]
    conv => enter [1]; rw [h4272 sK0 X0]
  have l3 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4272 sK0 sK1]
    conv => enter [1]; rw [h4272 sK0 sK2]
  have l4 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [← l1 sK0 sK2 X0]
    conv => enter [1]; rw [l1 sK0 sK2 X1]
  have l5 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1, 2]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [l4 X0 X0 sK0 X1]
    conv => enter [1, 2]; rw [l3 X0 sK0 sK1]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4272 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l6 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l9 z y]

theorem Equation4512_54223_implies_Equation4272 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54223 : Equation54223 G) : Equation4272 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54223 X0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54223 X0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  intro x y
  conv => enter [1]; rw [l3 x x y]

@[equational_result]
theorem Equation4273_implies_Equation4332 (G : Type*) [Magma G] (h4273 : Equation4273 G) : Equation4332 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4273 sK1 sK2]
    conv => enter [1]; rw [h4273 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4332_implies_Equation4273 (G : Type*) [Magma G] (h4332 : Equation4332 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [h4332 x x y]

@[equational_result]
theorem Equation4274_implies_Equation4281 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4281 G := by
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
  intro x y z w
  conv => enter [1]; rw [← l2 y z w x]

@[equational_result]
theorem Equation4281_implies_Equation4274 (G : Type*) [Magma G] (h4281 : Equation4281 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [h4281 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation4292 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4292 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 sK2]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4274 sK0 sK1 sK2]
  have l2 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
    conv => enter [1]; rw [h4274 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x x y y z]

@[equational_result]
theorem Equation4292_implies_Equation4274 (G : Type*) [Magma G] (h4292 : Equation4292 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4292 sK0 sK0 X0]
    conv => enter [1]; rw [h4292 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4295 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4295 G := by
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
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l7 y z x x y]

theorem Equation4295_4512_implies_Equation4274 (G : Type*) [Magma G] (h4295 : Equation4295 G) (h4512 : Equation4512 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4295 X2 X0 X1]
    conv => enter [1]; rw [h4295 X2 X0 X0]
  have l1 : ∀ X0 sK0 : G, ((X0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4295 sK0 (X0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4295 sK0 sK0 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h4295 sK0 X0 sK0]
    conv => enter [1]; rw [h4295 sK0 X0 X1]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h4512 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [← l3 X1 sK0]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h4295 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [h4295 (sK0 ◇ sK0) X0 X1]
  have l6 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h4295 sK0 sK2 sK0]
    conv => enter [1]; rw [h4295 sK2 (sK0 ◇ sK0) sK0]
  have l7 : ∀ X1 X0 sK0 sK2 : G, ((X1 ◇ X0) ◇ (sK0 ◇ sK2)) = (sK2 ◇ (X0 ◇ (X0 ◇ sK2))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [← h4295 sK2 (X1 ◇ X0) sK0]
    conv => enter [1, 2]; rw [← h4295 X0 sK2 X1]
  have l8 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4295 sK2 X0 sK0]
    conv => enter [1]; rw [h4295 sK2 X0 X1]
  have l9 : ∀ sK2 X0 sK0 X1 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))) = ((X1 ◇ X0) ◇ (sK0 ◇ sK2)) := by
    intro sK2 X0 sK0 X1
    conv => enter [1, 2]; rw [l8 X0 sK0 sK2 X0]
    conv => enter [1]; rw [← l7 X1 X0 sK0 sK2]
  have l10 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4295 (sK0 ◇ sK2) sK2 sK0]
    conv => enter [1]; rw [l6 sK2 sK0]
  have l11 : ∀ sK2 X0 sK0 X1 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 X0 sK0 X1
    conv => enter [1]; rw [l9 sK2 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 (sK0 ◇ sK2)]
  have l12 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l10 sK0 sK2]
    conv => enter [1]; rw [l8 (sK0 ◇ sK2) (sK0 ◇ sK2) sK2 sK0]
  have l13 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [h4295 (sK0 ◇ sK2) sK2 X0]
    conv => enter [1]; rw [l11 sK2 X0 sK0 X1]
  have l14 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [← l13 sK0 sK2 X1 X0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK2) (sK0 ◇ sK2) sK2 sK0]
  have l15 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [l12 sK0 sK2]
    conv => enter [1]; rw [← l14 X1 X0 sK0 sK2]
  have l16 : ∀ X1 X0 sK1 sK0 sK2 : G, ((X1 ◇ X0) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK2)))) := by
    intro X1 X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h4295 (sK0 ◇ sK2) (X1 ◇ X0) sK1]
    conv => enter [1, 2]; rw [← h4295 X0 (sK0 ◇ sK2) X1]
  have l17 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h4295 (sK0 ◇ sK2) X0 sK1]
    conv => enter [1]; rw [h4295 (sK0 ◇ sK2) X0 X0]
  have l18 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l17 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l15 sK0 sK2 X0 X0]
  have l19 : ∀ sK0 sK2 X1 X0 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) = ((X1 ◇ X0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1 X0 sK1
    conv => enter [1, 2]; rw [l15 sK0 sK2 X0 X0]
    conv => enter [1]; rw [← l16 X1 X0 sK1 sK0 sK2]
  have l20 : ∀ sK0 sK2 X1 X0 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X1 X0 sK1
    conv => enter [1]; rw [l19 sK0 sK2 X1 X0 sK1]
    conv => enter [1]; rw [← h4512 X1 X0 (sK1 ◇ (sK0 ◇ sK2))]
  have l21 : ∀ sK0 sK2 X1 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X1 X0 sK1
    conv => enter [1]; rw [l15 sK0 sK2 (sK0 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l20 sK0 sK2 X1 X0 sK1]
  have l22 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [← h4295 (sK0 ◇ sK0) (sK0 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [← l18 X0 sK1 sK0 sK2]
  have l23 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK2 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← l22 sK0 sK2 sK0 sK0]
  have l24 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l3 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l23 sK0 sK2]
  have l25 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l18 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l24 sK0 sK2]
  have l26 : ∀ X0 sK1 sK0 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1]; rw [l25 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l4 sK0 sK0 X1]
  have l27 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l26 X0 X0 sK0 sK2 X0]
    conv => enter [1]; rw [l18 X0 X0 sK0 sK2]
  have l28 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X0]
    conv => enter [1]; rw [h4295 X0 sK0 X1]
  have l29 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l5 X0 sK0 X0]
    conv => enter [1]; rw [h4295 X0 (sK0 ◇ sK0) X1]
  have l30 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4295 sK2 X0 sK0]
  have l31 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4295 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l32 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l31 sK0 sK0 X1]
    conv => enter [1]; rw [← l28 (X1 ◇ sK0) sK0 sK0]
  have l33 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [l30 sK2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK2) X1]
  have l34 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l28 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l35 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l32 sK0 X1]
    conv => enter [1]; rw [← h4512 X1 sK0 (sK0 ◇ sK0)]
  have l36 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← l33 sK2 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ X0) X1]
  have l37 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (sK0 ◇ sK2)) = (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [← h4295 sK2 X1 sK0]
    conv => enter [1]; rw [← l36 X0 sK0 sK2 X1]
  have l38 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l35 sK0 sK0]
    conv => enter [1]; rw [l27 sK0 sK0 sK2]
  have l39 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l38 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l40 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l29 X0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l39 sK0 X0 X0]
  have l41 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [l40 X0 sK0]
  have l42 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4295 sK2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l34 sK2 sK0]
  have l43 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0 sK2]
    conv => enter [1]; rw [l8 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK2 sK0]
  have l44 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l24 sK0 sK2]
    conv => enter [1]; rw [l43 sK0 sK2]
  have l45 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l35 sK0 sK0]
    conv => enter [1]; rw [l44 sK0 sK2]
  have l46 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK2 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l45 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK2) X0]
  have l47 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l37 X0 sK0 sK2 sK2]
    conv => enter [1]; rw [← l46 sK0 X0 sK2]
  have l48 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l41 sK0 X0]
    conv => enter [1]; rw [← l47 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l48 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4298 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4298 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 sK2]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK2]
  have l2 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 X0]
  have l3 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 X2 X0]
  have l4 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK1 sK2 X1 X2]
  have l5 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK2) sK1]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l7 y z w x y]

@[equational_result]
theorem Equation4298_implies_Equation4274 (G : Type*) [Magma G] (h4298 : Equation4298 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← h4298 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4298 sK0 sK0 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l0 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation4302 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4302 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4274 sK1 sK1 sK2]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation4302_implies_Equation4274 (G : Type*) [Magma G] (h4302 : Equation4302 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [h4302 x x y z]

@[equational_result]
theorem Equation4274_implies_Equation4303 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4303 G := by
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
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l7 z y x x y]

theorem Equation4303_4512_implies_Equation4274 (G : Type*) [Magma G] (h4303 : Equation4303 G) (h4512 : Equation4512 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4303 sK0 sK2 sK2]
    conv => enter [1]; rw [h4303 sK2 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4303 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4303 (sK0 ◇ sK0) sK0 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4303 sK0 sK0 X0]
    conv => enter [1]; rw [h4303 X0 (sK0 ◇ sK0) X1]
  have l3 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [h4303 (sK0 ◇ sK2) sK0 X1]
    conv => enter [1, 2]; rw [l0 sK0 sK2 X0]
  have l4 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [← l3 sK0 sK2 X1 X0]
    conv => enter [1]; rw [h4303 (sK0 ◇ sK2) sK0 sK0]
  have l5 : ∀ X1 X0 sK0 sK2 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X1 X0 sK0 sK2 sK1
    conv => enter [1]; rw [l4 X1 X0 sK0 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK0 sK2 X0]
  have l7 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l6 sK1 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK2) sK0 X0]
  have l8 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l7 X0 sK1 sK0 sK2]
  have l9 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h4303 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK0)]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4303 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
  have l12 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4303 sK0 sK2 sK0]
  have l13 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l12 sK0 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK0 sK2 sK1]
  have l14 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l8 sK0 sK0 sK0 sK2]
    conv => enter [1]; rw [← l13 sK0 sK2 sK0]
  have l15 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l14 sK0 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4306 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4306 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 sK2]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK2]
  have l2 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 X0]
  have l3 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 X2 X0]
  have l4 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK1 sK2 X1 X2]
  have l5 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK2) sK1]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l7 z y w x y]

@[equational_result]
theorem Equation4306_implies_Equation4274 (G : Type*) [Magma G] (h4306 : Equation4306 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [h4306 x x y z]

@[equational_result]
theorem Equation4274_implies_Equation4309 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4309 G := by
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
  have l4 : ∀ sK3 sK0 sK1 X1 X2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK3 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK1 X1 X2]
  have l5 : ∀ sK3 sK0 sK1 X1 X0 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK1 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK3]
  have l6 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK3 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x x y z w x]

@[equational_result]
theorem Equation4309_implies_Equation4274 (G : Type*) [Magma G] (h4309 : Equation4309 G) : Equation4274 G := by
  have l0 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h4309 sK0 sK0 X0 X0]
    conv => enter [1]; rw [h4309 X0 sK0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation4313 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4313 G := by
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
  conv => enter [1]; rw [l7 x x y z w u]

@[equational_result]
theorem Equation4313_implies_Equation4274 (G : Type*) [Magma G] (h4313 : Equation4313 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [h4313 x x y x z]

@[equational_result]
theorem Equation4274_implies_Equation4322 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4322 G := by
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
  have l6 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y x y x z]

@[equational_result]
theorem Equation4322_implies_Equation4274 (G : Type*) [Magma G] (h4322 : Equation4322 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4322 X0 X1 X1]
    conv => enter [1]; rw [h4322 X1 X0 X2]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4322 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4322 sK0 X0 X1]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h4322 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4326 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4326 G := by
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
  have l4 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ ((sK2 ◇ sK1) ◇ X2)) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK2 sK1 X1 X2]
  have l5 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK1) sK1]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l7 y z w x y]

@[equational_result]
theorem Equation4326_implies_Equation4274 (G : Type*) [Magma G] (h4326 : Equation4326 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← h4326 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4326 sK0 sK0 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation4328 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4328 G := by
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
  conv => enter [1]; rw [l7 x y x z x y]

theorem Equation4328_4512_implies_Equation4274 (G : Type*) [Magma G] (h4328 : Equation4328 G) (h4512 : Equation4512 G) : Equation4274 G := by
  have l0 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1, 2]; rw [h4328 sK0 sK0 X0]
    conv => enter [1]; rw [h4328 (sK0 ◇ sK0) X0 X1]
  have l1 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4328 sK2 sK0 sK0]
    conv => enter [1]; rw [h4328 sK0 sK2 X0]
  have l2 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← l1 sK2 sK0 X0]
    conv => enter [1]; rw [l1 sK2 sK0 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4328 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l2 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4329 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4329 G := by
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
  conv => enter [1]; rw [l7 x y x z x w]

@[equational_result]
theorem Equation4329_implies_Equation4274 (G : Type*) [Magma G] (h4329 : Equation4329 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [h4329 x x y z]

@[equational_result]
theorem Equation4274_implies_Equation4333 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4333 G := by
  have l0 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK1]
    conv => enter [1]; rw [h4274 sK2 X1 sK1]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4274 sK2 sK1 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation4333_implies_Equation4274 (G : Type*) [Magma G] (h4333 : Equation4333 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [h4333 x x y z]

@[equational_result]
theorem Equation4274_implies_Equation4335 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4335 G := by
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
  conv => enter [1]; rw [l7 x y x z w y]

@[equational_result]
theorem Equation4335_implies_Equation4274 (G : Type*) [Magma G] (h4335 : Equation4335 G) : Equation4274 G := by
  have l0 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h4335 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [h4335 sK0 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation4338 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4338 G := by
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
  conv => enter [1]; rw [l7 x y x z w u]

@[equational_result]
theorem Equation4338_implies_Equation4274 (G : Type*) [Magma G] (h4338 : Equation4338 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [h4338 x x y x z]

@[equational_result]
theorem Equation4274_implies_Equation4344 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4344 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK0 sK1]
  have l3 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l3 y x z x y]

@[equational_result]
theorem Equation4344_implies_Equation4274 (G : Type*) [Magma G] (h4344 : Equation4344 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4344 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4344 X0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4344 X0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h4344 X0 sK0 X0]
    conv => enter [1]; rw [h4344 sK0 X0 sK2]
  have l3 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l2 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4345 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4345 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK0 sK1]
  have l3 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l3 y z x x y]

theorem Equation4345_4512_implies_Equation4274 (G : Type*) [Magma G] (h4345 : Equation4345 G) (h4512 : Equation4512 G) : Equation4274 G := by
  have l0 : ∀ X1 X0 sK0 : G, ((X1 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h4345 (X1 ◇ X0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4345 X0 sK0 X1]
  have l1 : ∀ X1 X0 X2 sK0 : G, ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h4345 (X1 ◇ X0) X2 sK0]
    conv => enter [1, 2]; rw [← h4345 X0 sK0 X1]
  have l2 : ∀ X2 X0 sK0 X1 : G, (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X2 X0 sK0 X1
    conv => enter [1]; rw [← l1 X1 X0 X2 sK0]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ X2)]
  have l3 : ∀ X1 X0 sK0 : G, ((X1 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l0 X1 X0 sK0]
    conv => enter [1]; rw [← h4345 (sK0 ◇ sK0) sK0 X0]
  have l4 : ∀ X1 X0 sK0 : G, ((X1 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l3 X1 X0 sK0]
    conv => enter [1]; rw [h4345 (sK0 ◇ sK0) sK0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l4 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 X1 X0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4345 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [h4345 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4345 (X0 ◇ X0) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4345 (sK0 ◇ sK0) X0 sK0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l7 X0 X1 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1]; rw [← l5 sK0 X0 (sK0 ◇ sK0)]
  have l10 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l2 X1 X0 sK0 X0]
    conv => enter [1]; rw [l8 X0 X1 sK0]
  have l11 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l5 sK0 X1 X0]
    conv => enter [1]; rw [l10 X1 X0 sK0]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [← l9 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h4345 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l13 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l11 sK0 X0 sK0]
    conv => enter [1]; rw [l12 X0 sK0 X1]
  have l14 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4345 sK2 X0 sK0]
    conv => enter [1]; rw [h4345 sK2 X0 X1]
  have l15 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l14 X0 sK0 sK2 sK2]
    conv => enter [1]; rw [h4345 X0 sK2 X1]
  have l16 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [h4345 sK2 sK0 sK0]
  have l17 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l16 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h4345 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l19 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h4345 X0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l17 sK2 sK0 X0]
  have l20 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l19 X0 sK0 sK2]
    conv => enter [1]; rw [l15 sK2 (sK0 ◇ sK0) X0 sK0]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4345 sK2 sK0 sK0]
    conv => enter [1]; rw [l18 sK2 sK0]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l20 sK0 sK0 sK2]
    conv => enter [1]; rw [l21 sK0 sK2]
  have l23 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [l14 X0 (sK0 ◇ (sK0 ◇ sK0)) sK2 sK0]
  have l24 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 sK0 X0]
    conv => enter [1]; rw [← l24 sK0 X0 sK0]
  have l26 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 sK0 X0]
    conv => enter [1]; rw [← l23 X0 sK0 X0]
  have l27 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l20 sK1 sK0 sK2]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l28 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l27 sK1 sK0 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK0]
    conv => enter [1]; rw [← l28 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l29 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4347 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4347 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4274 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h4274 sK2 X0 (sK2 ◇ sK2)]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 sK1 sK2]
  have l3 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l3 y z w x y]

@[equational_result]
theorem Equation4347_implies_Equation4274 (G : Type*) [Magma G] (h4347 : Equation4347 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h4347 X0 sK0 X0 X0]
    conv => enter [1]; rw [← h4347 X3 sK0 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4347 sK0 sK0 X0 X1]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← h4347 sK0 X0 X1 X2]
    conv => enter [1]; rw [← l1 sK0 X0 X0]
  intro x y z
  conv => enter [1]; rw [← l2 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation4349 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4349 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 X1 sK2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4274 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK1 sK2 X0 X0]
  have l6 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l6 z x w x y]

@[equational_result]
theorem Equation4349_implies_Equation4274 (G : Type*) [Magma G] (h4349 : Equation4349 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [h4349 x x y z]

@[equational_result]
theorem Equation4274_implies_Equation4350 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4350 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK0 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4274 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4350_implies_Equation4274 (G : Type*) [Magma G] (h4350 : Equation4350 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4350 sK0 sK0 sK2]
    conv => enter [1]; rw [h4350 sK2 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4352 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4352 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4274 sK2 sK1 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4274 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

@[equational_result]
theorem Equation4352_implies_Equation4274 (G : Type*) [Magma G] (h4352 : Equation4352 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4352 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4353 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4353 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 X1 sK2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4274 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK1 sK2 X0 X0]
  have l6 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l6 z w x x y]

@[equational_result]
theorem Equation4353_implies_Equation4274 (G : Type*) [Magma G] (h4353 : Equation4353 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4353 sK0 sK0 sK2 sK0]
    conv => enter [1]; rw [h4353 sK2 sK0 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4356 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4356 G := by
  have l0 : ∀ X0 X1 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro X0 X1 sK3
    conv => enter [1]; rw [h4274 X0 X1 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 sK3 X0 sK3]
  have l1 : ∀ X0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3
    conv => enter [1]; rw [l0 X0 X0 sK3]
    conv => enter [1]; rw [← h4274 sK3 X0 (sK3 ◇ sK3)]
  have l2 : ∀ X0 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l1 X0 sK3]
    conv => enter [1]; rw [h4274 sK3 sK2 sK3]
  have l3 : ∀ X1 X0 X2 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK3 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK2 sK3]
  intro x y z w u
  conv => enter [1]; rw [← l3 z w u x y]

@[equational_result]
theorem Equation4356_implies_Equation4274 (G : Type*) [Magma G] (h4356 : Equation4356 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4356 sK0 sK0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4356 X0 sK0 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4356 sK0 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4363 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4363 G := by
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
  have l4 : ∀ sK1 sK2 sK3 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK2 sK3 X1 X2]
  have l5 : ∀ sK1 sK2 sK3 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK3) sK1]
  have l6 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 X2 sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z y x w]

@[equational_result]
theorem Equation4363_implies_Equation4274 (G : Type*) [Magma G] (h4363 : Equation4363 G) : Equation4274 G := by
  have l0 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h4363 X1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [h4363 X1 X0 X1 X2]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h4363 X0 sK0 sK2 (X1 ◇ X0)]
    conv => enter [1]; rw [← l0 X1 sK0 X0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 sK0 X0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4365 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4365 G := by
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
  have l4 : ∀ sK1 sK2 sK3 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK2 sK3 X1 X2]
  have l5 : ∀ sK1 sK2 sK3 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK3) sK1]
  have l6 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 X2 sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z y z w]

@[equational_result]
theorem Equation4365_implies_Equation4274 (G : Type*) [Magma G] (h4365 : Equation4365 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h4365 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h4365 X2 sK0 sK0 X0]
  have l1 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X2 ◇ sK0)) = (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h4365 X1 X2 sK0 (sK0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4365 X0 sK0 sK0 X1]
  have l2 : ∀ X2 X0 sK0 sK2 : G, (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro X2 X0 sK0 sK2
    conv => enter [1]; rw [← l1 X2 X2 sK0 X0]
    conv => enter [1]; rw [h4365 X2 X2 sK0 sK2]
  have l3 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [h4365 X1 X2 X3 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 X3 sK0 X0]
  have l4 : ∀ X1 X2 X3 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro X1 X2 X3 sK0 sK2
    conv => enter [1]; rw [l3 X1 X2 X3 X1 sK0]
    conv => enter [1]; rw [l2 X2 X1 sK0 sK2]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4365 sK0 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4365 sK0 sK0 sK0 sK2]
  have l7 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 sK0 X1 X2
    conv => enter [1, 2]; rw [l0 sK0 sK0 X1]
    conv => enter [1]; rw [h4365 X0 X1 (sK0 ◇ sK0) X2]
  have l8 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l7 X0 sK0 X0 X0]
    conv => enter [1]; rw [l4 X0 (sK0 ◇ sK0) X0 sK0 sK2]
  have l9 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1, 2]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [h4365 X0 sK0 (sK0 ◇ sK2) X1]
  have l10 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l9 X0 sK0 sK2 X0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK2) X0 sK0 sK2]
  have l11 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l8 X0 sK0 X0]
    conv => enter [1]; rw [← l8 X1 sK0 X0]
  have l12 : ∀ sK0 sK2 X2 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X2)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X2 X1 X0
    conv => enter [1]; rw [← h4365 X1 (sK0 ◇ sK0) (sK0 ◇ sK2) X2]
    conv => enter [1, 2]; rw [← l8 X0 sK0 sK2]
  have l13 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [← l4 X0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK2]
    conv => enter [1]; rw [← l12 sK0 sK2 X2 X0 X0]
  have l14 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l13 X0 sK0 sK2 X0]
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) (sK0 ◇ sK2) X0 sK0 sK2]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 X0]
  have l16 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0 sK2]
  have l17 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l16 sK0 sK2]
    conv => enter [1]; rw [← l14 X0 sK0 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ sK2) sK2]
    conv => enter [1]; rw [← l14 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4366 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4366 G := by
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
  conv => enter [1]; rw [l7 x y z y w x]

theorem Equation4366_4512_implies_Equation4274 (G : Type*) [Magma G] (h4366 : Equation4366 G) (h4512 : Equation4512 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 X2 X3 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X3) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1, 2]; rw [← h4366 X2 X0 X3 X1]
    conv => enter [1]; rw [← h4366 (X0 ◇ X3) sK0 sK0 X2]
  have l1 : ∀ sK0 X3 X1 X0 : G, (sK0 ◇ (X3 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X3 X1 X0
    conv => enter [1]; rw [← h4366 X1 sK0 (sK0 ◇ X0) X3]
    conv => enter [1, 2]; rw [← h4366 X0 sK0 sK0 sK0]
  have l2 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [h4366 X1 sK0 sK2 X1]
    conv => enter [1]; rw [l1 sK0 X1 X1 X0]
  have l3 : ∀ sK0 X0 X1 X2 X3 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1]; rw [l0 sK0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X3 (sK0 ◇ sK0)]
  have l4 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l2 X0 sK0 sK2 X0]
    conv => enter [1]; rw [← l3 sK0 X0 X1 X2 X0]
  have l5 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h4366 sK0 X0 (X0 ◇ X0) sK0]
    conv => enter [1]; rw [← l4 X0 sK0 sK2 X0 X0]
  have l6 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [l5 X0 sK0 sK2]
    conv => enter [1]; rw [← h4366 (sK0 ◇ sK2) sK0 sK0 X0]
  have l7 : ∀ X1 X0 sK0 sK2 X2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro X1 X0 sK0 sK2 X2
    conv => enter [1, 2]; rw [l5 X0 sK0 sK2]
    conv => enter [1]; rw [← h4366 (sK0 ◇ sK2) X1 X2 X0]
  have l8 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4366 (sK0 ◇ sK2) X1 X1 sK1]
    conv => enter [1]; rw [← l7 X1 X0 sK0 sK2 X1]
  have l9 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 X0 sK2]
    conv => enter [1]; rw [h4366 (sK0 ◇ sK2) sK0 sK0 sK1]
  have l10 : ∀ X1 sK1 sK0 sK2 : G, (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X1 sK1 sK0 sK2
    conv => enter [1]; rw [l8 X1 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 X1]
  have l11 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4366 sK0 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l9 sK0 X0 sK1 sK2]
  have l12 : ∀ X1 sK1 sK0 sK2 : G, (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK1 sK0 sK2
    conv => enter [1]; rw [l10 X1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l5 X1 sK0 sK2]
  have l13 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l5 sK1 sK0 sK2]
    conv => enter [1]; rw [l11 sK1 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l12 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l13 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4368 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4368 G := by
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
  conv => enter [1]; rw [l7 x y z y w u]

@[equational_result]
theorem Equation4368_implies_Equation4274 (G : Type*) [Magma G] (h4368 : Equation4368 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [h4368 X0 sK0 sK2 X1 X0]
    conv => enter [1]; rw [h4368 sK0 X1 X0 sK1 (sK0 ◇ sK2)]
  have l1 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [h4368 X0 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4368 sK0 X1 X0 sK1 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK1 sK0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4370 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4370 G := by
  have l0 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 sK3]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 sK2 sK1 sK3]
  have l2 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK3]
    conv => enter [1]; rw [h4274 sK2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z z w]

@[equational_result]
theorem Equation4370_implies_Equation4274 (G : Type*) [Magma G] (h4370 : Equation4370 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h4370 X0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4370 X1 sK0 sK2 X0]
  have l1 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [h4370 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h4370 sK0 sK0 X1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4371 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4371 G := by
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
  have l4 : ∀ sK3 sK0 sK1 X1 X2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK3 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK1 X1 X2]
  have l5 : ∀ sK3 sK0 sK1 X1 X0 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK1 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK3]
  have l6 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK3 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z w x]

theorem Equation4371_4512_implies_Equation4274 (G : Type*) [Magma G] (h4371 : Equation4371 G) (h4512 : Equation4512 G) : Equation4274 G := by
  have l0 : ∀ X1 X0 sK0 : G, ((X1 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h4371 (X1 ◇ X0) sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4371 sK0 X1 X0 sK0]
  have l1 : ∀ X1 X0 sK0 : G, ((X1 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l0 X1 X0 sK0]
    conv => enter [1]; rw [h4371 sK0 X0 (sK0 ◇ sK0) sK0]
  have l2 : ∀ X1 X0 sK0 : G, ((X1 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l1 X1 X0 sK0]
    conv => enter [1]; rw [h4371 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l2 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 X1 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4371 (sK0 ◇ sK0) sK0 sK0 sK2]
    conv => enter [1, 2]; rw [h4371 sK2 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [h4371 sK0 sK0 (sK0 ◇ sK2) sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h4371 (sK0 ◇ sK2) sK0 sK0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4371 sK0 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4371 (sK0 ◇ sK0) X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4371 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h4371 X0 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l8 sK0 X0 X0]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4371 (sK0 ◇ sK0) sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [h4371 (sK0 ◇ sK2) sK0 sK0 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [h4371 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4371 sK0 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
  have l13 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [h4371 X0 sK0 (sK1 ◇ (sK0 ◇ sK2)) X1]
  have l14 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [l13 X0 sK0 sK1 sK2 X1]
  have l15 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [h4371 sK2 sK0 sK0 sK0]
  have l16 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK0) X0]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 sK0 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l16 sK0 X0 X0 X0]
  have l18 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l15 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h4371 X0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l17 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l21 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h4371 X0 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l18 sK2 sK0 X0]
  have l22 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h4371 X0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l20 X0 sK0]
  have l23 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l21 X0 sK0 sK2]
    conv => enter [1]; rw [h4371 sK2 (sK0 ◇ sK0) X0 sK0]
  have l24 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4371 sK0 sK0 sK2 sK0]
    conv => enter [1]; rw [l19 sK2 sK0]
  have l25 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4371 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l19 X0 sK0]
  have l26 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l25 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l3 sK0 X2 X0]
  have l27 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l23 sK0 sK0 sK2]
    conv => enter [1]; rw [l24 sK0 sK2]
  have l28 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l26 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l22 sK0 sK0]
  have l29 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (X0 ◇ X1)) := by
    intro X1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l27 sK0 sK2]
    conv => enter [1]; rw [h4371 X1 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
  have l30 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l28 sK0 sK0 X1 sK0]
    conv => enter [1]; rw [← l29 X1 sK0 sK0 sK0]
  have l31 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l30 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l32 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← l28 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1 sK0]
    conv => enter [1]; rw [← l31 sK0 X1 sK0]
  have l33 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h4371 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l32 sK0 X0]
  have l34 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l33 X0 sK0 sK2]
    conv => enter [1]; rw [← l22 sK2 sK0]
  have l35 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l34 X0 sK0 sK2]
    conv => enter [1]; rw [l19 sK2 sK0]
  have l36 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l32 sK0 sK2]
    conv => enter [1]; rw [← l35 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l36 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4372 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4372 G := by
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
  conv => enter [1]; rw [l7 x y z z w y]

@[equational_result]
theorem Equation4372_implies_Equation4274 (G : Type*) [Magma G] (h4372 : Equation4372 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h4372 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h4372 X2 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4372 sK0 sK0 sK0 X0]
  have l2 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [h4372 sK0 X0 sK0 X1]
  have l3 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1]; rw [h4372 sK0 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l3 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation4373 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4373 G := by
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
  conv => enter [1]; rw [l7 x y z z w u]

@[equational_result]
theorem Equation4373_implies_Equation4274 (G : Type*) [Magma G] (h4373 : Equation4373 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 sK2 X2 sK1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X2 sK1
    conv => enter [1]; rw [h4373 X0 sK0 sK2 X0 X2]
    conv => enter [1]; rw [h4373 sK2 X0 X2 sK1 (sK0 ◇ sK2)]
  have l1 : ∀ X0 sK0 X2 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 X2 sK1 sK2
    conv => enter [1]; rw [h4373 X0 sK0 sK0 X0 X2]
    conv => enter [1]; rw [h4373 sK0 X0 X2 sK1 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK1 sK0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4375 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4375 G := by
  have l0 : ∀ X0 sK3 sK4 X1 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK3 X0 sK4]
    conv => enter [1]; rw [h4274 sK3 X1 sK4]
  have l1 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h4274 sK3 sK2 sK4]
  have l2 : ∀ sK2 sK3 sK4 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK3 ◇ X1)) := by
    intro sK2 sK3 sK4 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 sK4]
    conv => enter [1]; rw [h4274 sK3 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

@[equational_result]
theorem Equation4375_implies_Equation4274 (G : Type*) [Magma G] (h4375 : Equation4375 G) : Equation4274 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h4375 sK0 sK0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4375 sK0 sK0 (sK0 ◇ sK0) X1 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4375 sK0 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4376 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4376 G := by
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
  have l4 : ∀ sK1 sK2 sK3 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK2 sK3 X1 X2]
  have l5 : ∀ sK1 sK2 sK3 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK3) sK1]
  have l6 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 X2 sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w z y]

theorem Equation4376_4512_implies_Equation4274 (G : Type*) [Magma G] (h4376 : Equation4376 G) (h4512 : Equation4512 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 2]; rw [h4376 sK0 sK0 sK0 X1]
    conv => enter [1]; rw [h4376 X0 X1 (sK0 ◇ sK0) X2]
  have l1 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h4376 X0 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h4376 X0 (sK0 ◇ sK0) sK0 X2]
  have l2 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [h4376 X0 sK0 sK2 X0]
    conv => enter [1]; rw [h4376 X0 sK2 sK0 X2]
  have l3 : ∀ X1 X0 sK0 sK2 X3 X2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) = (X3 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X1 X0 sK0 sK2 X3 X2
    conv => enter [1, 2]; rw [l2 X0 sK0 sK2 X2]
    conv => enter [1]; rw [h4376 X1 X2 (sK0 ◇ sK2) X3]
  have l4 : ∀ X1 sK1 sK0 sK2 X3 X2 : G, (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X3 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X1 sK1 sK0 sK2 X3 X2
    conv => enter [1, 2]; rw [l2 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [l3 X1 X1 sK0 sK2 X3 X2]
  have l5 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [l0 X1 sK0 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK0) sK0 X0]
  have l6 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK0 X1 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK0) sK0 sK2 sK1]
  have l7 : ∀ X1 sK1 sK0 sK2 X2 X0 : G, (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK1 sK0 sK2 X2 X0
    conv => enter [1]; rw [l4 X1 sK1 sK0 sK2 X2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← l6 X0 sK0 (sK0 ◇ sK2) sK1 sK2]
  have l8 : ∀ X0 sK0 X3 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X3 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 X3 X2
    conv => enter [1]; rw [l5 X0 sK0 X0 X2]
    conv => enter [1]; rw [h4376 X0 X2 (sK0 ◇ (sK0 ◇ sK0)) X3]
  have l9 : ∀ X0 sK1 sK0 sK2 X3 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X3 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 sK1 sK0 sK2 X3 X2
    conv => enter [1]; rw [l7 X0 sK1 sK0 sK2 X0 X2]
    conv => enter [1]; rw [h4376 X0 X2 (sK0 ◇ (sK0 ◇ sK0)) X3]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4376 sK0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l12 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l11 sK1 sK0 sK2 X0 sK1]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
  have l14 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l13 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 X1 X2]
  have l15 : ∀ sK1 sK0 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK1 sK0 sK2 X1 X2
    conv => enter [1]; rw [l12 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l9 sK1 sK1 sK0 sK2 X1 X2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK0 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4377 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4377 G := by
  have l0 : ∀ X0 sK3 sK4 X1 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK3 X0 sK4]
    conv => enter [1]; rw [h4274 sK3 X1 sK4]
  have l1 : ∀ X0 sK3 sK4 X1 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK3 X0 sK4]
    conv => enter [1]; rw [h4274 sK3 X1 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [h4274 sK3 X0 sK4]
  have l2 : ∀ X1 sK3 sK4 X2 X0 : G, (X1 ◇ ((sK3 ◇ sK4) ◇ X2)) = ((sK3 ◇ sK4) ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro X1 sK3 sK4 X2 X0
    conv => enter [1]; rw [← h4274 (sK3 ◇ sK4) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK3 ◇ sK4) sK3 sK4 X0]
  have l3 : ∀ X0 sK3 sK4 X1 X2 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ ((sK3 ◇ sK4) ◇ X2)) := by
    intro X0 sK3 sK4 X1 X2
    conv => enter [1]; rw [l1 X0 sK3 sK4 (sK3 ◇ sK4)]
    conv => enter [1]; rw [← l2 X1 sK3 sK4 X2 X0]
  have l4 : ∀ sK2 sK3 sK4 X1 X2 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X1 ◇ ((sK3 ◇ sK4) ◇ X2)) := by
    intro sK2 sK3 sK4 X1 X2
    conv => enter [1]; rw [l3 sK2 sK3 sK4 X1 X2]
  have l5 : ∀ sK2 sK3 sK4 X1 X0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK3 sK4 X1 X0
    conv => enter [1]; rw [l4 sK2 sK3 sK4 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK3 ◇ sK4) sK2]
  have l6 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK3 sK4 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK3 sK4 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK3 ◇ sK4)) := by
    intro X1 X0 X2 sK2 sK3 sK4
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w z u]

@[equational_result]
theorem Equation4377_implies_Equation4274 (G : Type*) [Magma G] (h4377 : Equation4377 G) : Equation4274 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h4377 sK0 sK0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4377 X1 sK0 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4377 sK0 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4379 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4379 G := by
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
  conv => enter [1]; rw [l7 x y z w u v]

@[equational_result]
theorem Equation4379_implies_Equation4274 (G : Type*) [Magma G] (h4379 : Equation4379 G) : Equation4274 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h4379 sK0 sK0 sK0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4379 sK0 sK0 (sK0 ◇ sK0) X1 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4379 sK0 sK0 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54400 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54400 G := by
  have l0 : ∀ X0 sK1 sK3 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK1 sK3 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK3 ◇ sK0)]
  have l1 : ∀ X0 sK1 sK3 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK1 sK3 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK3 ◇ sK0)]
  have l2 : ∀ X1 sK1 sK3 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X2)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X1 sK1 sK3 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK3 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK3 ◇ sK0)) sK1 sK3 sK0 X0]
  have l3 : ∀ X0 sK1 sK3 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro X0 sK1 sK3 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK1 sK3 sK0 X2 X0]
  have l4 : ∀ sK2 sK1 sK3 sK0 X1 X2 : G, (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro sK2 sK1 sK3 sK0 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK3 sK0 X1 X2]
  have l5 : ∀ sK2 sK1 sK3 sK0 X1 X0 : G, (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 sK3 sK0 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 sK0 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK3 ◇ sK0)) sK2]
  have l6 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 sK3 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK1 sK3 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro X1 X0 X2 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l7 x y z y x z w]

theorem Equation4512_54400_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54400 : Equation54400 G) : Equation4274 G := by
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
  have l5 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l6 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54400 sK0 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l6 sK0 X0 X1]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l9 sK0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l11 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l4 sK0]
    conv => enter [1]; rw [l11 sK0]
  have l13 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 sK2]
  have l14 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← h54400 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l14 sK0]
  have l17 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [l15 sK0 X0 X1]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l13 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1, 2]; rw [← l17 sK0 X0 sK0]
  have l20 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l17 sK0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l20 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← h54400 X1 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l23 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [l21 sK0 X0 X1]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l12 sK0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l16 sK0]
  have l26 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l18 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l27 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l26 sK0 X0 X1]
    conv => enter [1]; rw [← h54400 X1 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [l27 sK0 X0 X1]
  have l29 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l25 sK0 X0]
    conv => enter [1]; rw [l28 sK0 X0 X1]
  have l30 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l23 sK0 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l31 : ∀ sK0 X0 X2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [l30 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h54400 X2 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [← l25 sK0 X0]
    conv => enter [1]; rw [l31 sK0 X0 X2 X1]
  have l33 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l29 sK0 sK0 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l33 sK0]
  have l35 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [l32 sK0 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l35 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54401 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54401 G := by
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
  have l4 : ∀ sK1 sK0 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK1 X1 X2]
  have l5 : ∀ sK1 sK0 X1 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK1]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK1]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z x w]
  conv => enter [1]; rw [l6 x w y]

theorem Equation4512_54401_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54401 : Equation54401 G) : Equation4274 G := by
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
  have l3 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X1 sK0 X0 X2
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [h54401 X1 (sK0 ◇ sK0) (sK0 ◇ X0) X2]
  have l4 : ∀ sK0 X0 X1 X2 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ X2)) = (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h54401 ((sK0 ◇ sK0) ◇ X0) X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54401 sK0 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54401 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54401 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54401 sK0 (sK0 ◇ sK0) X1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 X0 X1 X2 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l4 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l3 X1 sK0 X0 X1]
    conv => enter [1]; rw [h54401 (sK0 ◇ sK0) X1 (X1 ◇ X1) sK0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l12 sK0 X0 X0]
    conv => enter [1]; rw [l11 sK0 X0 X0]
  have l16 : ∀ sK0 X0 X1 X2 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l13 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [h54401 (sK0 ◇ sK0) X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) sK0]
  have l17 : ∀ sK0 X0 X1 X2 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l16 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [l15 X0 sK0]
  have l18 : ∀ X1 X0 sK0 X2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 sK0 X2
    conv => enter [1]; rw [← l17 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X1 ◇ X2)]
  have l19 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54401 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l18 X1 X0 sK0 X0]
  have l20 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l15 X0 sK0]
    conv => enter [1]; rw [l19 X0 sK0 X1]
  have l21 : ∀ X1 sK0 X2 X3 X0 : G, ((X1 ◇ sK0) ◇ (X2 ◇ X3)) = (X2 ◇ ((X1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 sK0 X2 X3 X0
    conv => enter [1]; rw [h54401 (X1 ◇ sK0) X2 X3 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l9 sK0 X1 X0]
  have l22 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ X3)) = (X2 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h54401 X1 X2 X3 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l9 sK0 X0 X1]
  have l23 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l22 X1 X2 X3 sK0 X1]
    conv => enter [1, 2]; rw [l14 X1 sK0 (X1 ◇ sK0)]
  have l24 : ∀ X1 sK0 X2 X3 X0 : G, ((X1 ◇ sK0) ◇ (X2 ◇ X3)) = (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro X1 sK0 X2 X3 X0
    conv => enter [1]; rw [l21 X1 sK0 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l25 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X2 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l23 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [l15 X1 sK0]
  have l26 : ∀ X1 sK0 X2 X3 : G, ((X1 ◇ sK0) ◇ (X2 ◇ X3)) = (X2 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l24 X1 sK0 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l27 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l25 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l20 X1 sK0 X2]
  have l28 : ∀ X1 sK0 X2 X3 : G, ((X1 ◇ sK0) ◇ (X2 ◇ X3)) = (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l26 X1 sK0 X2 X3]
    conv => enter [1, 2]; rw [l14 X1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ X2 sK0 X1 X3 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X1 ◇ sK0) ◇ (X2 ◇ X3)) := by
    intro X2 sK0 X1 X3
    conv => enter [1]; rw [← l27 X2 X1 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [← l28 X1 sK0 X2 X3]
  have l30 : ∀ X2 sK0 X1 X3 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (X2 ◇ X3))) := by
    intro X2 sK0 X1 X3
    conv => enter [1]; rw [l29 X2 sK0 X1 X3]
    conv => enter [1]; rw [← h4512 X1 sK0 (X2 ◇ X3)]
  have l31 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X2
    conv => enter [1]; rw [l30 X1 sK0 X2 X1]
    conv => enter [1]; rw [l27 X2 sK0 (X1 ◇ X1) sK0]
  have l32 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l10 sK0 sK0 X0]
    conv => enter [1]; rw [l10 sK0 sK0 X2]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 sK0 X0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l31 (sK0 ◇ sK0) sK0 X0]
  have l35 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← l27 X0 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l35 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54402 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54402 G := by
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
  intro x y z w
  conv => enter [1]; rw [l8 x y z x w y]
  conv => enter [1]; rw [l6 x w y y]

theorem Equation4512_54402_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54402 : Equation54402 G) : Equation4274 G := by
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
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54402 X0 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54402 sK0 sK0 X1 X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54402 sK0 (sK0 ◇ sK0) X1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l10 : ∀ sK0 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l8 sK0 sK0 X0]
    conv => enter [1]; rw [l8 sK0 sK0 X2]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1]; rw [← l9 sK0 X1 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK0 X0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l13 sK0]
  have l19 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l17 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← h54402 X0 (sK0 ◇ sK0) X1 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l16 sK0 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1, 2]; rw [← l18 sK0]
  have l22 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h54402 X1 sK0 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l23 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54402 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [h54402 X0 sK0 X1 sK0]
  have l24 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l23 X0 X1 X2 sK0]
    conv => enter [1]; rw [l5 X1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ X1 sK0 X0 sK2 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X1 sK0 X0 sK2
    conv => enter [1]; rw [l22 X1 sK0 X0]
    conv => enter [1]; rw [← h54402 X1 sK0 sK2 sK0]
  have l26 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l24 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l21 sK0 X1]
  have l27 : ∀ X1 sK0 sK2 : G, (X1 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 sK2
    conv => enter [1]; rw [← l25 X1 sK0 X1 sK2]
    conv => enter [1, 2]; rw [l12 sK0 X1]
  have l28 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l26 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l18 sK0]
  have l29 : ∀ X1 sK0 sK2 : G, (X1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 sK2
    conv => enter [1]; rw [l27 X1 sK0 sK2]
    conv => enter [1, 2]; rw [← l13 sK0]
  have l30 : ∀ sK0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [← l28 X1 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l29 X1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l30 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54404 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54404 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [h4274 sK0 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK1 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4274 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 sK1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0 sK1]
  have l6 : ∀ X1 X0 X2 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z x w]
  conv => enter [1]; rw [l5 x w y]

theorem Equation4512_54404_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54404 : Equation54404 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54404 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54404 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l5 sK0 sK0 X0]
    conv => enter [1]; rw [l5 sK0 sK0 X2]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK0 X0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54404 X0 (sK0 ◇ sK0) X1 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l15 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l6 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54404 X0 sK0 sK2 sK0]
  have l16 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [l15 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54405 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54405 G := by
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
  have l4 : ∀ sK2 sK1 sK0 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK2 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK0 X1 X2]
  have l5 : ∀ sK2 sK1 sK0 X1 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK0 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK2]
  have l6 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 sK2]
  have l7 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK2 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z x w u]
  conv => enter [1]; rw [l6 x w u y]

theorem Equation4512_54405_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54405 : Equation54405 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l2 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h54405 sK0 sK0 X2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l3 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 sK0 X0 X1 X2]
  have l4 : ∀ sK0 X0 X3 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X3) := by
    intro sK0 X0 X3
    conv => enter [1]; rw [← l3 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK0 sK0 X3]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l5 sK0 (sK2 ◇ X0)]
    conv => enter [1]; rw [l1 sK0 sK2 X0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54405 X0 (sK0 ◇ sK0) X1 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2]; rw [← l8 sK0]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54405 sK0 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l7 sK0 sK0 sK0]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 X0 X1]
  have l14 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l13 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54405 X0 sK0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54426 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54426 G := by
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
  have l6 : ∀ sK3 sK1 sK0 X0 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 sK3]
  have l7 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK3 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK3 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z z x w]
  conv => enter [1]; rw [l6 z x w y]

theorem Equation4512_54426_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54426 : Equation54426 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l3 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← h54426 X0 (sK0 ◇ sK0) sK0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [l6 sK0 X0 sK0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l6 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 X0 sK0]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l11 sK0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [h54426 X2 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK0 X0 X1 X2]
  have l14 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l13 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l13 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l14 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54435 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54435 G := by
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
  have l4 : ∀ sK3 sK0 sK1 X1 X2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK3 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK1 X1 X2]
  have l5 : ∀ sK3 sK0 sK1 X1 X0 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK1 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK3]
  have l6 : ∀ sK3 sK0 sK1 X0 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK3]
  have l7 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK3 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK3 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l8 x y z z w x]
  conv => enter [1]; rw [l6 z w x y]

theorem Equation4512_54435_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54435 : Equation54435 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l3 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← h54435 X1 (sK0 ◇ sK0) sK0 X0]
  have l5 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ X1 X0 sK0 : G, ((X1 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0)) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l6 sK0 X1 X0]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X1 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l6 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l9 X1 X0 sK0]
  have l11 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [l7 X2 sK0 X0 X2]
    conv => enter [1]; rw [← h54435 X2 (sK0 ◇ (sK0 ◇ sK0)) X0 X2]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l12 sK0 X1 X0]
  have l14 : ∀ X0 X1 sK0 X2 : G, ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l11 X1 sK0 X2]
  have l15 : ∀ X0 X1 sK0 X2 : G, ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l14 X0 X1 sK0 X2]
    conv => enter [1]; rw [← h54435 X2 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l15 X0 X1 sK0 X2]
  have l17 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ X1)) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [l16 X0 X1 sK0 X2]
  have l18 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l17 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l17 sK0 X0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l18 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54436 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54436 G := by
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
  have l6 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK2 X0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 sK3]
  have l7 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 X0 X0]
  have l8 : ∀ X1 X0 X2 sK3 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK3 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l8 x y z z w y]
  conv => enter [1]; rw [l6 z w y y]

end Semigroup5
