import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54241_implies_Equation54266 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation54266 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l2 : ∀ sK2 sK0 sK3 X0 : G, ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK3) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ X0) := by
    intro sK2 sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK0 ◇ sK3) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 (sK0 ◇ sK3)]
  have l3 : ∀ sK2 sK0 sK3 X0 : G, ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK3) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK3)) ◇ X0)) := by
    intro sK2 sK0 sK3 X0
    conv => enter [1]; rw [l2 sK2 sK0 sK3 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK3)) X0]
  have l4 : ∀ X1 sK2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ X0) ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [h54241 X1 (sK2 ◇ sK2) (sK2 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 sK2 X0]
  have l5 : ∀ X1 sK2 sK0 sK3 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (((sK0 ◇ sK3) ◇ X0) ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK3)) ◇ X0)))) := by
    intro X1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [h54241 X1 (sK2 ◇ sK2) ((sK0 ◇ sK3) ◇ X0)]
    conv => enter [1, 2, 2]; rw [l3 sK2 sK0 sK3 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54241 X1 X2 X0]
    conv => enter [1]; rw [h54241 X1 X2 X2]
    conv => enter [1, 2]; rw [h54241 X1 X2 X0]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54241 X2 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h54241 X0 X1 X2]
  have l8 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54241 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l1 sK1 sK2]
  have l9 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54241 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l10 : ∀ sK3 sK2 sK0 X0 : G, (sK3 ◇ ((sK2 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ (sK0 ◇ sK3)))) = (X0 ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ X0)) := by
    intro sK3 sK2 sK0 X0
    conv => enter [1]; rw [h54241 sK3 (sK2 ◇ (sK0 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h4512 sK3 (sK2 ◇ (sK0 ◇ sK3)) X0]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54241 (X1 ◇ X2) X3 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X3)]
  have l12 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ sK2)) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (X0 ◇ sK2)]
    conv => enter [1]; rw [← h54241 sK2 X0 sK2]
  have l13 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l11 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l14 : ∀ sK3 sK2 sK0 X0 : G, ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ (sK0 ◇ sK3))) = (X0 ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ X0)) := by
    intro sK3 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK2 ◇ (sK0 ◇ sK3)) (sK2 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [l10 sK3 sK2 sK0 X0]
  have l15 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l9 sK2 X0]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1]; rw [l12 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l17 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l7 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l18 : ∀ X1 sK2 sK0 sK3 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK3) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK3)) ◇ X0))))) := by
    intro X1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [l5 X1 sK2 sK0 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK3) X0 (X1 ◇ (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK3)) ◇ X0)))]
  have l19 : ∀ X1 sK2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l4 X1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 X0 (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)))]
  have l20 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l15 sK2 X0]
  have l21 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l13 X2 X0 X1 X1]
    conv => enter [1]; rw [← l17 X2 X0 X1]
  have l22 : ∀ X1 sK2 sK0 sK3 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK3) ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ (sK0 ◇ sK3)))))) := by
    intro X1 sK2 sK0 sK3
    conv => enter [1]; rw [l18 X1 sK2 sK0 sK3 X1]
    conv => enter [1, 2]; rw [← l13 X1 sK2 (sK2 ◇ (sK0 ◇ sK3)) X1]
  have l23 : ∀ X1 sK2 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))))) := by
    intro X1 sK2
    conv => enter [1]; rw [l19 X1 sK2 X1]
    conv => enter [1, 2]; rw [← l13 X1 sK2 (sK2 ◇ sK2) X1]
  have l24 : ∀ X1 sK2 sK0 sK3 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK3) ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK2 sK0 sK3
    conv => enter [1]; rw [l22 X1 sK2 sK0 sK3]
    conv => enter [1, 2]; rw [l21 X1 sK2 (sK2 ◇ (sK0 ◇ sK3))]
  have l25 : ∀ X1 sK2 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK2
    conv => enter [1]; rw [l23 X1 sK2]
    conv => enter [1, 2]; rw [l21 X1 sK2 (sK2 ◇ sK2)]
  have l26 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l20 sK2 sK2]
    conv => enter [1]; rw [← l0 sK2 sK2]
  have l27 : ∀ X1 sK2 : G, (X1 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 sK2
    conv => enter [1]; rw [h54241 X1 sK2 sK2]
    conv => enter [1]; rw [← l25 X1 sK2]
  have l28 : ∀ sK0 sK3 X1 sK2 : G, ((sK0 ◇ sK3) ◇ (X1 ◇ (sK2 ◇ sK2))) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK3 X1 sK2
    conv => enter [1]; rw [← l24 X1 sK2 sK0 sK3]
    conv => enter [1, 2]; rw [← l26 sK2]
  have l29 : ∀ X1 sK2 : G, (X1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK2
    conv => enter [1]; rw [l27 X1 sK2]
    conv => enter [1, 2]; rw [← l26 sK2]
  have l30 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l0 sK2 ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l16 sK1 sK2]
  have l31 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l16 sK1 sK2]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [h54241 sK2 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l16 sK1 sK2]
  have l33 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [l31 sK2 sK1]
  have l34 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l21 sK2 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l30 sK2 sK1]
  have l35 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l34 sK2 sK1]
    conv => enter [1]; rw [l33 sK2 sK1]
  have l36 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h54241 (sK2 ◇ sK2) sK2 sK2]
    conv => enter [1]; rw [l35 sK2 sK1]
  have l37 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l26 sK2]
    conv => enter [1]; rw [l36 sK2 sK1]
  have l38 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1, 2]; rw [← l32 sK1 sK2]
  have l39 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [h54241 X0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l32 sK1 sK2]
  have l40 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54241 X0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l38 sK1 sK2]
  have l41 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l40 X0 sK2 sK1]
    conv => enter [1]; rw [← l39 X0 sK1 sK2]
  have l42 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l33 sK2 sK1]
  have l43 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l37 sK2 sK1]
    conv => enter [1]; rw [← l42 sK1 sK2]
  have l44 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [← l43 sK1 sK2]
  have l45 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l44 sK1 sK2]
    conv => enter [1]; rw [← l28 sK0 sK3 sK1 sK2]
  have l46 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK3) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l45 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [← l41 (sK0 ◇ sK3) sK2 sK1]
  have l47 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l38 sK1 sK2]
    conv => enter [1]; rw [← l37 sK2 sK1]
  have l48 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54241 X0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l37 sK2 sK1]
  have l49 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l48 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← l29 X0 sK2]
  have l50 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54241 X0 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l47 sK1 sK2]
  have l51 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [l50 X0 sK2 X0]
    conv => enter [1, 2]; rw [← l41 X0 sK2 X0]
  have l52 : ∀ sK2 sK0 sK3 : G, ((sK2 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK3) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK3) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54241 (sK0 ◇ sK3) sK2 sK2]
  have l53 : ∀ sK2 X0 : G, (sK2 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h54241 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h54241 X0 sK2 sK2]
  have l54 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK2)))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [h54241 X1 sK2 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← h54241 X0 sK2 sK2]
  have l55 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK2))))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l54 X1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) (X1 ◇ (X0 ◇ (sK2 ◇ sK2)))]
  have l56 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ X0)) := by
    intro X0 sK2
    conv => enter [1]; rw [l51 X0 sK2]
    conv => enter [1]; rw [← l53 sK2 X0]
  have l57 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l46 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [← l52 sK2 sK0 sK3]
  have l58 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK2)))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l55 X1 sK2 X0]
    conv => enter [1]; rw [← l6 (sK2 ◇ sK2) X1 X0]
  have l59 : ∀ sK3 sK1 sK2 sK0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l57 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [h4512 sK3 (sK2 ◇ (sK0 ◇ sK3)) (sK2 ◇ sK2)]
  have l60 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [l41 sK3 sK2 sK3]
    conv => enter [1]; rw [l59 sK3 sK3 sK2 sK0]
  have l61 : ∀ X0 sK3 sK2 sK0 : G, (X0 ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK3 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK3 sK2 sK0
    conv => enter [1]; rw [h54241 X0 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l60 sK3 sK2 sK0]
  have l62 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l58 X0 sK2 sK3]
    conv => enter [1]; rw [← l61 X0 sK3 sK2 sK0]
  have l63 : ∀ X0 sK3 sK2 sK0 : G, (X0 ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))))) = (X0 ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK3 sK2 sK0
    conv => enter [1]; rw [h54241 X0 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) X0]
    conv => enter [1, 2]; rw [← l14 sK3 sK2 sK0 X0]
  have l64 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l14 sK3 sK2 sK0 (sK2 ◇ sK2)]
  have l65 : ∀ sK3 sK2 sK0 sK1 : G, ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ sK2)) = (sK1 ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1]; rw [l49 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) sK2 sK1]
    conv => enter [1]; rw [l64 sK1 sK2 sK3 sK0]
  have l66 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l62 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [l63 X0 sK3 sK2 sK0]
  have l67 : ∀ sK3 sK2 sK1 sK0 : G, (sK3 ◇ (sK2 ◇ sK2)) = (sK1 ◇ ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [l60 sK3 sK2 sK0]
    conv => enter [1]; rw [l65 sK3 sK2 sK0 sK1]
  have l68 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l66 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l67 sK3 sK2 sK1 sK1]
  have l69 : ∀ sK0 sK3 sK2 sK1 : G, ((sK0 ◇ sK3) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK3 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK3 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l68 sK3 sK2 sK1]
  have l70 : ∀ sK0 sK3 sK2 : G, ((sK0 ◇ sK3) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l69 sK0 sK3 sK2 sK0]
    conv => enter [1]; rw [← l41 sK0 sK2 sK0]
  have l71 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l46 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l70 sK0 sK1 sK2]
  have l72 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h54241 sK2 sK0 sK3]
    conv => enter [1]; rw [l56 sK2 sK0]
  have l73 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l71 sK1 sK2 sK0]
    conv => enter [1]; rw [← l72 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l73 x y z w]

theorem Equation4512_54266_implies_Equation54241 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54266 : Equation54266 G) : Equation54241 G := by
  have l0 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h54266 X0 sK1 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ sK1)]
  have l1 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l0 X0 sK1 X0]
    conv => enter [1]; rw [← l0 X1 sK1 X0]
  have l2 : ∀ X0 sK1 X1 X2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l3 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l2 X0 sK1 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK1 sK0]
  have l4 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l3 sK0 sK1 X1 sK0]
  have l5 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54266 X0 X1 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 X0]
  have l6 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l5 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 X1]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l6 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l7 sK0 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X0)]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h54266 (sK0 ◇ (sK1 ◇ sK2)) X0 sK2 sK1]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l10 x y z x]

theorem Equation4512_54241_implies_Equation54288 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation54288 G := by
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
  have l53 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l52 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [h54241 X0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l53 x y z w]

@[equational_result]
theorem Equation54288_implies_Equation54241 (G : Type*) [Magma G] (h54288 : Equation54288 G) : Equation54241 G := by
  have l0 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [h54288 X0 X1 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [h54288 sK0 (X0 ◇ sK0) (sK1 ◇ sK2) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h54288 sK1 sK2 sK2 sK0]
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK2 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54288 sK0 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4512_54241_implies_Equation54293 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation54293 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l2 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK2) ◇ (sK3 ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) sK3 X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 sK3]
  have l3 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK2) ◇ (sK3 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l2 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK3) (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← h4512 sK2 sK3 (sK0 ◇ (sK2 ◇ sK3))]
  have l5 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ sK3) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) (sK0 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK3 (sK0 ◇ (sK2 ◇ sK3))]
  have l6 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ sK3) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)) = (sK2 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l5 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) X0]
  have l7 : ∀ X1 sK2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ X0) ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [h54241 X1 (sK2 ◇ sK2) (sK2 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 sK2 X0]
  have l8 : ∀ X1 sK2 sK3 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK3 ◇ X0) ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK3) ◇ X0)))) := by
    intro X1 sK2 sK3 X0
    conv => enter [1]; rw [h54241 X1 (sK2 ◇ sK2) (sK3 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l3 sK2 sK3 X0]
  have l9 : ∀ X1 sK2 sK3 sK0 X0 : G, (X1 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = (((sK0 ◇ (sK2 ◇ sK3)) ◇ X0) ◇ (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0)))) := by
    intro X1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h54241 X1 (sK2 ◇ sK3) ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [l6 sK2 sK3 sK0 X0]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54241 X1 X2 X0]
    conv => enter [1]; rw [h54241 X1 X2 X2]
    conv => enter [1, 2]; rw [h54241 X1 X2 X0]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54241 X2 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h54241 X0 X1 X2]
  have l12 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [h54241 sK0 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK3) X0]
  have l13 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54241 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l1 sK1 sK2]
  have l14 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54241 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l15 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h54241 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK3 X0]
  have l16 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3)))) = (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [h54241 sK3 (sK0 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h4512 sK3 (sK0 ◇ (sK2 ◇ sK3)) X0]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54241 (X1 ◇ X2) X3 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X3)]
  have l18 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ sK2)) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (X0 ◇ sK2)]
    conv => enter [1]; rw [← h54241 sK2 X0 sK2]
  have l19 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l17 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l20 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK2 ◇ sK3)) (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [l16 sK3 sK0 sK2 X0]
  have l21 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ sK3) = (X0 ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 sK3]
    conv => enter [1]; rw [l15 sK2 sK3 X0]
  have l22 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l14 sK2 X0]
  have l23 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l13 sK1 sK2]
    conv => enter [1]; rw [l18 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l24 : ∀ sK0 sK2 sK3 X0 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK3) (sK2 ◇ sK3)]
    conv => enter [1]; rw [l12 sK0 sK2 sK3 X0]
  have l25 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l11 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l26 : ∀ X1 sK2 sK3 sK0 X0 : G, (X1 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0))))) := by
    intro X1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l9 X1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK3)) X0 (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0)))]
  have l27 : ∀ X1 sK2 sK3 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK3 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK3) ◇ X0))))) := by
    intro X1 sK2 sK3 X0
    conv => enter [1]; rw [l8 X1 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 sK3 X0 (X1 ◇ (sK2 ◇ ((sK2 ◇ sK3) ◇ X0)))]
  have l28 : ∀ X1 sK2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l7 X1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 X0 (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)))]
  have l29 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l22 sK2 X0]
  have l30 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l19 X2 X0 X1 X1]
    conv => enter [1]; rw [← l25 X2 X0 X1]
  have l31 : ∀ X1 sK2 sK3 sK0 : G, (X1 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))))) := by
    intro X1 sK2 sK3 sK0
    conv => enter [1]; rw [l26 X1 sK2 sK3 sK0 X1]
    conv => enter [1, 2]; rw [← l19 X1 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) X1]
  have l32 : ∀ X1 sK2 sK3 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK3 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))))) := by
    intro X1 sK2 sK3
    conv => enter [1]; rw [l27 X1 sK2 sK3 X1]
    conv => enter [1, 2]; rw [← l19 X1 sK2 (sK2 ◇ sK3) X1]
  have l33 : ∀ X1 sK2 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))))) := by
    intro X1 sK2
    conv => enter [1]; rw [l28 X1 sK2 X1]
    conv => enter [1, 2]; rw [← l19 X1 sK2 (sK2 ◇ sK2) X1]
  have l34 : ∀ X1 sK2 sK3 sK0 : G, (X1 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK2 sK3 sK0
    conv => enter [1]; rw [l31 X1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l30 X1 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))]
  have l35 : ∀ X1 sK2 sK3 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK3 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK2 sK3
    conv => enter [1]; rw [l32 X1 sK2 sK3]
    conv => enter [1, 2]; rw [l30 X1 sK2 (sK2 ◇ sK3)]
  have l36 : ∀ X1 sK2 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK2
    conv => enter [1]; rw [l33 X1 sK2]
    conv => enter [1, 2]; rw [l30 X1 sK2 (sK2 ◇ sK2)]
  have l37 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l29 sK2 sK2]
    conv => enter [1]; rw [← l0 sK2 sK2]
  have l38 : ∀ X1 sK2 : G, (X1 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 sK2
    conv => enter [1]; rw [h54241 X1 sK2 sK2]
    conv => enter [1]; rw [← l36 X1 sK2]
  have l39 : ∀ sK3 X1 sK2 : G, (sK3 ◇ (X1 ◇ (sK2 ◇ sK2))) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK3 X1 sK2
    conv => enter [1]; rw [← l35 X1 sK2 sK3]
    conv => enter [1, 2]; rw [← l37 sK2]
  have l40 : ∀ X1 sK2 : G, (X1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK2
    conv => enter [1]; rw [l38 X1 sK2]
    conv => enter [1, 2]; rw [← l37 sK2]
  have l41 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l0 sK2 ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l23 sK1 sK2]
  have l42 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l23 sK1 sK2]
  have l43 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l23 sK1 sK2]
    conv => enter [1]; rw [h54241 sK2 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l23 sK1 sK2]
  have l44 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [l42 sK2 sK1]
  have l45 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l30 sK2 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l41 sK2 sK1]
  have l46 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l45 sK2 sK1]
    conv => enter [1]; rw [l44 sK2 sK1]
  have l47 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h54241 (sK2 ◇ sK2) sK2 sK2]
    conv => enter [1]; rw [l46 sK2 sK1]
  have l48 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l37 sK2]
    conv => enter [1]; rw [l47 sK2 sK1]
  have l49 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l23 sK1 sK2]
    conv => enter [1, 2]; rw [← l43 sK1 sK2]
  have l50 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [h54241 X0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l43 sK1 sK2]
  have l51 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54241 X0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l49 sK1 sK2]
  have l52 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l49 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l53 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l51 X0 sK2 sK1]
    conv => enter [1]; rw [← l50 X0 sK1 sK2]
  have l54 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l44 sK2 sK1]
  have l55 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l48 sK2 sK1]
    conv => enter [1]; rw [← l54 sK1 sK2]
  have l56 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [← l55 sK1 sK2]
  have l57 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l56 sK1 sK2]
    conv => enter [1]; rw [← l39 sK3 sK1 sK2]
  have l58 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l57 sK1 sK2 sK3]
    conv => enter [1]; rw [← l53 sK3 sK2 sK1]
  have l59 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 sK3
    conv => enter [1, 2]; rw [l58 sK1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK2 sK3 (sK2 ◇ sK2)]
  have l60 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l48 sK2 sK2]
    conv => enter [1]; rw [l59 sK2 sK2 sK3]
  have l61 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l49 sK1 sK2]
    conv => enter [1]; rw [← l48 sK2 sK1]
  have l62 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54241 X0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l48 sK2 sK1]
  have l63 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1, 1]; rw [l48 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l64 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l52 sK1 sK2 X0]
    conv => enter [1]; rw [← l63 sK2 X0 sK1]
  have l65 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l62 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← l40 X0 sK2]
  have l66 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l64 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l67 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK2)))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [h54241 X1 sK2 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← h54241 X0 sK2 sK2]
  have l68 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK2))))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l67 X1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) (X1 ◇ (X0 ◇ (sK2 ◇ sK2)))]
  have l69 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK2)))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l68 X1 sK2 X0]
    conv => enter [1]; rw [← l10 (sK2 ◇ sK2) X1 X0]
  have l70 : ∀ X0 sK2 sK3 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [h54241 X0 (sK2 ◇ sK3) (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l60 sK2 sK3]
  have l71 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l69 X0 sK2 sK2]
    conv => enter [1]; rw [← l70 X0 sK2 sK3]
  have l72 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [h54241 (sK0 ◇ (sK2 ◇ sK3)) sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK2 ◇ sK3)) (sK2 ◇ sK3)]
  have l73 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h54241 sK0 sK2 sK3]
    conv => enter [1]; rw [h54241 sK0 sK2 sK2]
    conv => enter [1, 2]; rw [h54241 sK0 sK2 sK3]
  have l74 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l4 sK0 sK2 sK3]
    conv => enter [1, 2]; rw [← l73 sK3 sK0 sK2]
  have l75 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [l73 sK3 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))]
  have l76 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [l73 sK3 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))]
  have l77 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK2 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1, 1]; rw [l73 sK3 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) X0]
  have l78 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l73 sK3 sK0 sK2]
    conv => enter [1]; rw [l76 sK2 sK3 sK0]
  have l79 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l75 sK2 sK3 sK0]
    conv => enter [1]; rw [← l66 sK1 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))]
  have l80 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l78 sK3 sK0 sK2]
    conv => enter [1]; rw [l79 sK2 sK3 sK0 sK1]
  have l81 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1, 1]; rw [l78 sK3 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) X0]
  have l82 : ∀ sK3 sK0 sK2 X0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l80 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) X0]
  have l83 : ∀ sK0 sK2 sK3 X0 : G, (((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1, 1]; rw [l74 sK0 sK2 sK3]
    conv => enter [1]; rw [← h4512 sK0 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) X0]
  have l84 : ∀ sK0 sK2 sK3 X0 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)) = (sK0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK3)) (sK0 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [l83 sK0 sK2 sK3 X0]
  have l85 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK3 sK0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l53 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) sK2 sK1]
  have l86 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l0 sK2 ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK2)]
    conv => enter [1, 2]; rw [← l20 sK3 sK0 sK2 sK2]
  have l87 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3))) = (sK0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK3) ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← l20 sK3 sK0 sK2 (sK2 ◇ sK3)]
  have l88 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l87 sK0 sK2 sK3]
    conv => enter [1]; rw [← l84 sK0 sK2 sK3 (sK0 ◇ (sK2 ◇ sK3))]
  have l89 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK2))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l81 sK3 sK0 sK2 (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l86 sK2 sK3 sK0]
  have l90 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l85 sK3 sK0 sK2 sK3]
    conv => enter [1]; rw [← l65 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) sK2 sK3]
  have l91 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l24 sK0 sK2 sK3 (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l88 sK0 sK2 sK3]
  have l92 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l89 sK3 sK0 sK2]
    conv => enter [1]; rw [← l66 sK1 sK2 ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK2)]
  have l93 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l91 sK0 sK2 sK3]
    conv => enter [1, 2]; rw [← l72 sK0 sK2 sK3]
  have l94 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l92 sK3 sK0 sK2 sK3]
    conv => enter [1]; rw [← l82 sK3 sK0 sK2 sK2 sK3]
  have l95 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l93 sK0 sK2 sK3]
    conv => enter [1]; rw [← l34 (sK0 ◇ (sK2 ◇ sK3)) sK2 sK3 sK0]
  have l96 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l95 sK0 sK2 sK3]
    conv => enter [1]; rw [← l71 (sK0 ◇ (sK2 ◇ sK3)) sK2 sK3]
  have l97 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK2)) = (sK3 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [h54241 (sK0 ◇ (sK2 ◇ sK3)) sK2 sK3]
    conv => enter [1, 2]; rw [l96 sK0 sK2 sK3]
  have l98 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l97 sK0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK2 ◇ sK3)) (sK2 ◇ sK2)]
  have l99 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) = ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h54241 X0 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l98 sK0 sK2 sK3]
  have l100 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l69 X0 sK2 (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l99 X0 sK3 sK0 sK2]
  have l101 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK3) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l21 sK2 sK3 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l53 (sK2 ◇ sK3) sK2 sK1]
  have l102 : ∀ X0 sK2 sK3 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = (X0 ◇ ((sK2 ◇ sK3) ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [h54241 X0 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [← l21 sK2 sK3 X0]
  have l103 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ sK3) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK3) sK0]
  have l104 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK3) ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l71 X0 sK2 sK3]
    conv => enter [1]; rw [l102 X0 sK2 sK3]
  have l105 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ sK3) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l101 sK2 sK3 sK2]
    conv => enter [1]; rw [← l65 (sK2 ◇ sK3) sK2 sK2]
  have l106 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK3) ◇ sK3) := by
    intro sK2 sK3
    conv => enter [1]; rw [l60 sK2 sK3]
    conv => enter [1]; rw [← l105 sK2 sK3]
  have l107 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK3) ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l61 sK1 sK2]
    conv => enter [1]; rw [l106 sK2 sK3]
  have l108 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ sK3)) = (sK2 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [l103 sK2 sK3 sK0]
    conv => enter [1]; rw [l6 sK2 sK3 sK0 sK0]
  have l109 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ ((sK2 ◇ sK3) ◇ sK3)) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK0) := by
    intro sK3 sK2 sK0
    conv => enter [1, 2]; rw [l103 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK2 ◇ sK3)) sK0]
  have l110 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ sK3) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK2 sK3 sK3]
    conv => enter [1]; rw [l109 sK3 sK2 sK0]
  have l111 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ sK3)) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l108 sK2 sK3 sK0]
    conv => enter [1]; rw [← l77 sK3 sK0 sK2 sK0]
  have l112 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l107 sK1 sK2 sK3]
    conv => enter [1]; rw [l110 sK2 sK3 sK0]
  have l113 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l104 (sK2 ◇ sK3) sK2 sK3]
    conv => enter [1]; rw [l111 sK2 sK3 sK0]
  have l114 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l112 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l113 sK2 sK3 sK1]
  have l115 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK3 sK0 sK2 sK0]
    conv => enter [1, 2]; rw [← l112 sK1 sK2 sK3 sK0]
  have l116 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l115 sK3 sK0 sK2 sK3]
    conv => enter [1]; rw [← l53 sK0 sK2 sK3]
  have l117 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h54241 sK0 sK2 sK3]
    conv => enter [1]; rw [← l116 sK3 sK0 sK2]
  have l118 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1, 2]; rw [l114 sK1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK3) (sK2 ◇ sK2)]
  have l119 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l53 sK0 sK2 sK0]
    conv => enter [1]; rw [l118 sK0 sK0 sK2 sK3]
  have l120 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h54241 sK0 sK2 sK3]
    conv => enter [1]; rw [l119 sK0 sK2 sK3]
  have l121 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l117 sK3 sK0 sK2]
    conv => enter [1]; rw [l90 sK3 sK0 sK2]
  have l122 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l117 sK3 sK0 sK2]
    conv => enter [1]; rw [l94 sK3 sK0 sK2]
  have l123 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK2 ◇ sK3)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l120 sK3 sK0 sK2]
  have l124 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l121 sK3 sK0 sK2]
    conv => enter [1]; rw [l123 sK3 sK0 sK2]
  have l125 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) = (sK2 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h54241 X0 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) sK2]
    conv => enter [1, 2, 2]; rw [← l122 sK3 sK0 sK2]
  have l126 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l100 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [l125 X0 sK3 sK0 sK2]
  have l127 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [l124 sK3 sK0 sK2]
    conv => enter [1]; rw [l3 sK2 sK3 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))]
  have l128 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l127 sK2 sK3 sK0]
    conv => enter [1]; rw [← l126 (sK2 ◇ sK3) sK2 sK3 sK0]
  have l129 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l60 sK2 sK3]
    conv => enter [1]; rw [← l128 sK2 sK3 sK0]
  have l130 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l78 sK3 sK0 sK2]
    conv => enter [1]; rw [← l129 sK2 sK3 sK0]
  have l131 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l61 sK1 sK2]
    conv => enter [1]; rw [← l130 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l131 x y z w]

@[equational_result]
theorem Equation54293_implies_Equation54241 (G : Type*) [Magma G] (h54293 : Equation54293 G) : Equation54241 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54293 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← h54293 X0 sK1 sK1 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54293 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_54241_implies_Equation54308 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation54308 G := by
  have l0 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ X0)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l1 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK3) sK3]
    conv => enter [1, 2]; rw [← h4512 sK3 sK3 sK3]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54241 X2 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h54241 X0 X1 X2]
  have l3 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = (X0 ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h54241 sK2 (sK3 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK3 ◇ sK3) X0]
  have l4 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [h54241 sK2 sK3 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [← l1 sK2 sK3]
  have l5 : ∀ sK3 X0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [h54241 sK3 sK3 X0]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54241 (X1 ◇ X2) X3 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X3)]
  have l7 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
    conv => enter [1, 1]; rw [← h54241 X0 X1 X2]
  have l8 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (X0 ◇ sK3)) = (sK3 ◇ (X0 ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 (X0 ◇ sK3)]
    conv => enter [1]; rw [← h54241 sK3 X0 sK3]
  have l9 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l7 X2 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l10 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l6 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l11 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ sK3) = (X0 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 sK3]
    conv => enter [1]; rw [l5 sK3 X0]
  have l12 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l4 sK2 sK3]
    conv => enter [1]; rw [l8 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l13 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = (X0 ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK3) (sK3 ◇ sK3)]
    conv => enter [1]; rw [l3 sK2 sK3 X0]
  have l14 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l15 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l9 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l16 : ∀ sK3 X0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [h4512 sK3 sK3 sK3]
    conv => enter [1]; rw [l11 sK3 X0]
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
  have l20 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3
    conv => enter [1]; rw [l16 sK3 sK3]
    conv => enter [1]; rw [← l0 sK3 sK3]
  have l21 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1, 2]; rw [l20 sK3]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK3) (sK3 ◇ sK3)]
  have l22 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l1 sK2 sK3]
    conv => enter [1]; rw [l21 sK2 sK3]
  have l23 : ∀ sK3 sK2 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK2 ◇ (sK3 ◇ sK3))))) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [← l0 sK3 ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK2 ◇ (sK3 ◇ sK3)))]
    conv => enter [1, 2]; rw [← l12 sK2 sK3]
  have l24 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK2 ◇ (sK3 ◇ sK3)))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [← h4512 sK3 sK3 ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK2 ◇ (sK3 ◇ sK3)))]
    conv => enter [1, 2]; rw [← l12 sK2 sK3]
  have l25 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l12 sK2 sK3]
    conv => enter [1]; rw [h54241 sK3 (sK2 ◇ (sK3 ◇ sK3)) (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1, 2]; rw [← l12 sK2 sK3]
  have l26 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l25 sK2 sK3]
    conv => enter [1]; rw [l24 sK3 sK2]
  have l27 : ∀ sK3 sK2 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [← l17 sK3 (sK3 ◇ sK3) (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [l23 sK3 sK2]
  have l28 : ∀ sK3 sK2 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l27 sK3 sK2]
    conv => enter [1]; rw [l26 sK3 sK2]
  have l29 : ∀ sK3 sK2 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [h54241 (sK3 ◇ sK3) sK3 sK3]
    conv => enter [1]; rw [l28 sK3 sK2]
  have l30 : ∀ sK3 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l20 sK3]
    conv => enter [1]; rw [l29 sK3 sK2]
  have l31 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l12 sK2 sK3]
    conv => enter [1, 2]; rw [← l25 sK2 sK3]
  have l32 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro X0 sK2 sK3
    conv => enter [1, 2]; rw [l25 sK2 sK3]
    conv => enter [1]; rw [h54241 X0 (sK2 ◇ (sK3 ◇ sK3)) (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1, 2, 2]; rw [← l25 sK2 sK3]
  have l33 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1, 1]; rw [l25 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK3)) (sK2 ◇ (sK3 ◇ sK3)) X0]
  have l34 : ∀ X0 sK3 sK2 : G, (X0 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro X0 sK3 sK2
    conv => enter [1]; rw [h54241 X0 sK3 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1, 2, 2]; rw [← l31 sK2 sK3]
  have l35 : ∀ X0 sK3 sK2 : G, (X0 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3 sK2
    conv => enter [1]; rw [l34 X0 sK3 sK2]
    conv => enter [1]; rw [← l32 X0 sK2 sK3]
  have l36 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l31 sK2 sK3]
    conv => enter [1]; rw [← l30 sK3 sK2]
  have l37 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l1 sK2 sK3]
    conv => enter [1, 2]; rw [← l36 sK2 sK3]
  have l38 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) := by
    intro sK2 sK3
    conv => enter [1]; rw [l35 sK2 sK3 sK2]
    conv => enter [1]; rw [← l37 sK2 sK3]
  have l39 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = ((X0 ◇ (X1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l13 sK2 sK3 (X0 ◇ (X1 ◇ (sK2 ◇ (sK3 ◇ sK3))))]
    conv => enter [1, 2]; rw [← h54241 X0 X1 (sK2 ◇ (sK3 ◇ sK3))]
  have l40 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = (X0 ◇ ((X1 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l39 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK2 ◇ (sK3 ◇ sK3))) (X0 ◇ (X1 ◇ X1))]
  have l41 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l40 sK2 sK3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK2 ◇ (sK3 ◇ sK3)) (X0 ◇ (X1 ◇ X1))]
  have l42 : ∀ sK2 sK3 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = (X1 ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X1 ◇ X1)))) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l41 sK2 sK3 sK2 X1]
    conv => enter [1]; rw [← l19 X1 (sK2 ◇ (sK3 ◇ sK3)) (X1 ◇ X1) sK2]
  have l43 : ∀ sK2 sK3 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X1 ◇ X1))) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l42 sK2 sK3 X1]
    conv => enter [1]; rw [← l10 (sK2 ◇ (sK3 ◇ sK3)) (sK2 ◇ (sK3 ◇ sK3)) X1 X1]
  have l44 : ∀ sK2 sK3 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l43 sK2 sK3 X1]
    conv => enter [1]; rw [← l33 sK2 sK3 (X1 ◇ X1)]
  have l45 : ∀ sK2 sK3 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ sK3) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l22 sK2 sK3]
    conv => enter [1]; rw [l44 sK2 sK3 X1]
  have l46 : ∀ sK2 sK3 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l38 sK2 sK3]
    conv => enter [1]; rw [l45 sK2 sK3 X1]
  have l47 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l46 sK2 sK3 X0]
    conv => enter [1]; rw [h54241 (sK2 ◇ (sK3 ◇ sK3)) X0 X0]
    conv => enter [1, 2]; rw [← l46 sK2 sK3 X0]
  have l48 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l47 sK2 sK3 X0]
    conv => enter [1]; rw [← l35 X0 sK3 sK2]
  have l49 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [h54241 X0 X1 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1, 2, 2]; rw [← l47 sK2 sK3 X1]
  have l50 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l49 X0 X1 sK2 sK3]
    conv => enter [1]; rw [← l32 X0 sK2 sK3]
  have l51 : ∀ X0 X1 sK3 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro X0 X1 sK3
    conv => enter [1]; rw [l50 X0 X1 X0 sK3]
    conv => enter [1]; rw [← l35 X0 sK3 X0]
  have l52 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X1)) = (sK2 ◇ (sK3 ◇ sK3)) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l51 X0 X1 sK3]
    conv => enter [1]; rw [l48 X0 sK3 sK2]
  have l53 : ∀ sK2 sK3 sK4 X0 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK4 ◇ (X0 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK4 X0 sK0
    conv => enter [1]; rw [l52 sK2 sK3 X0 sK0]
    conv => enter [1]; rw [h54241 X0 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l53 x y z w u]

@[equational_result]
theorem Equation54308_implies_Equation54241 (G : Type*) [Magma G] (h54308 : Equation54308 G) : Equation54241 G := by
  have l0 : ∀ X0 sK1 X4 : G, (X0 ◇ (sK1 ◇ sK1)) = (X4 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X4
    conv => enter [1]; rw [h54308 X0 sK1 X0 X0 X0]
    conv => enter [1]; rw [← h54308 X4 sK1 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54308 sK0 sK1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_54287_implies_Equation54248 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54287 : Equation54287 G) : Equation54248 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h54287 X2 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h54287 X0 X1 X2 X2]
  have l1 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h54287 sK2 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l2 : ∀ sK0 sK2 X0 X1 sK1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X0)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0 X1 sK1
    conv => enter [1]; rw [h54287 (sK0 ◇ sK2) X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) X0]
  have l3 : ∀ sK1 sK0 sK2 X0 X1 sK3 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X0)) = (X1 ◇ ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0 X1 sK3
    conv => enter [1]; rw [h54287 (sK1 ◇ (sK0 ◇ sK2)) X0 X1 sK3]
    conv => enter [1, 2]; rw [h4512 sK3 (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l4 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 sK1 (sK0 ◇ sK2)]
  have l5 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 sK2 sK2]
  have l6 : ∀ X1 sK3 sK1 sK0 sK2 X0 : G, (X1 ◇ ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro X1 sK3 sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l3 sK1 sK0 sK2 X0 X1 sK3]
    conv => enter [1]; rw [← l5 sK2 (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l7 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l2 sK0 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← l5 sK2 (sK0 ◇ sK2) X0]
  have l8 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54287 X0 X1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X0 X1 X3]
  have l9 : ∀ sK3 sK1 sK0 sK2 X0 X1 : G, ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK3 sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h54287 sK3 (sK1 ◇ (sK0 ◇ sK2)) X0 X1]
  have l10 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1]; rw [h54287 sK1 (sK0 ◇ sK2) X0 X1]
  have l11 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ sK2) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK2 sK2]
    conv => enter [1]; rw [h54287 sK0 sK2 X0 X1]
  have l12 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h54287 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l13 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l12 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l14 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l13 sK2 X0]
  have l15 : ∀ sK3 sK1 sK0 sK2 : G, ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l9 sK3 sK1 sK0 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l16 : ∀ sK3 sK1 sK0 sK2 : G, ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l9 sK3 sK1 sK0 sK2 sK3 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK3 (sK1 ◇ (sK0 ◇ sK2)) (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l17 : ∀ sK3 sK1 sK0 sK2 X0 : G, ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (sK3 ◇ ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ (sK0 ◇ sK2)) (X0 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
    conv => enter [1, 2]; rw [← l9 sK3 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l18 : ∀ sK1 sK0 sK2 sK3 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l10 sK1 sK0 sK2 sK3 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [← l17 sK3 sK1 sK0 sK2 X0]
  have l19 : ∀ sK1 sK0 sK2 sK3 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l18 sK1 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l9 sK3 sK1 sK0 sK2 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK1]
  have l20 : ∀ sK1 sK0 sK2 sK3 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l19 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l15 sK3 sK1 sK0 sK2]
  have l21 : ∀ X0 X1 sK2 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK2 sK3 sK1 sK0
    conv => enter [1, 2, 2]; rw [← l20 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [← h54287 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) X0 X1]
  have l22 : ∀ X0 X1 sK2 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l21 X0 X1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK0 sK2 (sK0 ◇ sK2) (sK0 ◇ sK2)]
  have l23 : ∀ X0 X1 sK2 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l22 X0 X1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [← l5 sK2 (sK0 ◇ sK2) (sK0 ◇ sK2)]
  have l24 : ∀ X0 X1 sK2 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l23 X0 X1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [← l5 sK2 (sK2 ◇ sK2) (sK0 ◇ sK2)]
  have l25 : ∀ X0 X1 sK2 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l24 X0 X1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [← l14 sK2 (sK0 ◇ sK2)]
  have l26 : ∀ sK0 sK2 X0 X1 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ sK2) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK2 X0 X1 sK3 sK1
    conv => enter [1]; rw [l11 sK0 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l25 X0 X1 sK2 sK3 sK1 sK0]
  have l27 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l26 sK0 sK2 sK0 sK0 sK3 sK1]
    conv => enter [1]; rw [← h54287 (sK2 ◇ sK2) (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK0 sK0]
  have l28 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l27 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l5 sK2 (sK2 ◇ sK2) (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l29 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l28 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l14 sK2 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l30 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ sK2) = ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l29 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l9 sK3 sK1 sK0 sK2 sK2 (sK2 ◇ sK2)]
  have l31 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l30 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [l15 sK3 sK1 sK0 sK2]
  have l32 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l10 sK1 sK0 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK1 ◇ (sK0 ◇ sK2))]
  have l33 : ∀ X0 sK3 sK1 sK0 sK2 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← l10 sK1 sK0 sK2 X0 sK3]
    conv => enter [1]; rw [l32 sK1 sK0 sK2]
  have l34 : ∀ sK2 sK3 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← l20 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l32 sK1 sK0 sK2]
  have l35 : ∀ sK0 sK2 X0 X1 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK2 X0 X1 sK3 sK1
    conv => enter [1]; rw [h54287 (sK0 ◇ sK2) sK2 X0 X1]
    conv => enter [1, 2, 2]; rw [l31 sK0 sK2 sK3 sK1]
  have l36 : ∀ sK0 sK2 X0 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ X0)) = (((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK2 X0 sK3 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK2) sK2 X0]
    conv => enter [1, 1]; rw [l31 sK0 sK2 sK3 sK1]
  have l37 : ∀ sK0 sK2 X0 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 X0 sK3 sK1
    conv => enter [1]; rw [l36 sK0 sK2 X0 sK3 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
  have l38 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l35 sK0 sK2 sK0 sK0 sK3 sK1]
    conv => enter [1]; rw [← h54287 (sK2 ◇ sK2) (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK0 sK0]
  have l39 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l37 sK0 sK2 X0 sK0 sK1]
    conv => enter [1]; rw [l6 (sK2 ◇ sK2) sK0 sK1 sK0 sK2 X0]
  have l40 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l38 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l5 sK2 (sK2 ◇ sK2) (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l41 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l39 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [l7 (sK2 ◇ sK2) sK0 sK0 sK2 X0]
  have l42 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l40 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l14 sK2 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l43 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l42 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l9 sK3 sK1 sK0 sK2 sK2 (sK2 ◇ sK2)]
  have l44 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l43 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [l15 sK3 sK1 sK0 sK2]
  have l45 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l44 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [l34 sK2 sK0 sK1 sK0]
  have l46 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l45 sK0 sK2 sK1]
    conv => enter [1]; rw [l41 sK0 sK2 sK2]
  have l47 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK2 (sK2 ◇ sK2) sK0]
    conv => enter [1]; rw [← l46 sK2 sK1 sK0]
  have l48 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l47 sK2 sK1 sK0]
  have l49 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l48 sK2 sK1 sK0]
  have l50 : ∀ sK2 X0 sK3 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 X0 sK3 sK1 sK0
    conv => enter [1]; rw [l49 sK2 sK1 sK0]
    conv => enter [1]; rw [← l33 X0 sK3 sK1 sK0 sK2]
  have l51 : ∀ X1 sK1 sK2 X0 sK3 sK0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X1 sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [← h54287 sK2 sK2 X1 sK1]
    conv => enter [1]; rw [l50 sK2 X0 sK3 sK1 sK0]
  have l52 : ∀ sK3 sK1 sK0 sK2 X0 : G, ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l16 sK3 sK1 sK0 sK2]
    conv => enter [1]; rw [← l51 X0 sK1 sK2 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK3 sK0]
  have l53 : ∀ sK3 sK1 sK0 sK2 X0 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l11 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [l11 sK0 sK2 X0 sK1]
  have l54 : ∀ sK3 sK1 sK0 sK2 X0 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l53 sK3 sK1 sK0 sK2 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [l52 sK3 sK1 sK0 sK2 X0]
  have l55 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1]; rw [← l54 sK3 sK1 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l55 x y z w]

theorem Equation4512_54248_implies_Equation54287 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54248 : Equation54248 G) : Equation54287 G := by
  have l0 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ sK2)]
  have l2 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2))) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h54248 X0 (sK2 ◇ sK2) X1 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK2]
  have l3 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [h54248 X0 sK2 X0 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l2 X0 sK2 X0 X0]
  have l4 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54248 (sK2 ◇ sK2) sK2 X0 sK2]
    conv => enter [1]; rw [← l3 X0 sK2]
  have l5 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [← l4 sK2 X1]
    conv => enter [1]; rw [l4 sK2 X0]
  have l6 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0]
    conv => enter [1]; rw [h54248 sK0 sK2 X0 sK1]
  have l7 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l5 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l6 sK2 X0 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

theorem Equation4512_54287_implies_Equation54307 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54287 : Equation54287 G) : Equation54307 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h54287 X2 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h54287 X0 X1 X2 X2]
  have l1 : ∀ sK3 X0 X1 sK0 : G, (sK3 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X0)) := by
    intro sK3 X0 X1 sK0
    conv => enter [1]; rw [h54287 sK3 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK3 X0]
  have l2 : ∀ sK0 sK3 X0 X1 sK1 : G, ((sK0 ◇ sK3) ◇ (X0 ◇ X0)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ X0)) := by
    intro sK0 sK3 X0 X1 sK1
    conv => enter [1]; rw [h54287 (sK0 ◇ sK3) X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK3) X0]
  have l3 : ∀ sK1 sK0 sK3 X0 X1 sK4 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ X0)) = (X1 ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK0 sK3 X0 X1 sK4
    conv => enter [1]; rw [h54287 (sK1 ◇ (sK0 ◇ sK3)) X0 X1 sK4]
    conv => enter [1, 2]; rw [h4512 sK4 (sK1 ◇ (sK0 ◇ sK3)) X0]
  have l4 : ∀ sK1 sK0 sK3 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK3) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 sK1 (sK0 ◇ sK3)]
  have l5 : ∀ sK3 X0 X1 : G, ((sK3 ◇ sK3) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK3 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 sK3 sK3]
  have l6 : ∀ sK4 sK1 sK0 sK3 X0 X1 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK4 sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK0 ◇ sK3)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 sK4 (sK1 ◇ (sK0 ◇ sK3))]
  have l7 : ∀ X1 sK4 sK1 sK0 sK3 X0 : G, (X1 ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ X0)) = ((sK3 ◇ sK3) ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ X0)) := by
    intro X1 sK4 sK1 sK0 sK3 X0
    conv => enter [1]; rw [← l3 sK1 sK0 sK3 X0 X1 sK4]
    conv => enter [1]; rw [← l5 sK3 (sK1 ◇ (sK0 ◇ sK3)) X0]
  have l8 : ∀ X1 sK1 sK0 sK3 X0 : G, (X1 ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ X0)) = ((sK3 ◇ sK3) ◇ ((sK0 ◇ sK3) ◇ X0)) := by
    intro X1 sK1 sK0 sK3 X0
    conv => enter [1]; rw [← l2 sK0 sK3 X0 X1 sK1]
    conv => enter [1]; rw [← l5 sK3 (sK0 ◇ sK3) X0]
  have l9 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54287 X0 X1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X0 X1 X3]
  have l10 : ∀ sK4 sK1 sK0 sK3 X0 X1 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))))) := by
    intro sK4 sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK0 ◇ sK3)) (sK1 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [h54287 sK4 (sK1 ◇ (sK0 ◇ sK3)) X0 X1]
  have l11 : ∀ sK1 sK0 sK3 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK3) (sK0 ◇ sK3)]
    conv => enter [1]; rw [h54287 sK1 (sK0 ◇ sK3) X0 X1]
  have l12 : ∀ sK0 sK3 X0 X1 : G, ((sK0 ◇ sK3) ◇ sK3) = (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK3 sK3]
    conv => enter [1]; rw [h54287 sK0 sK3 X0 X1]
  have l13 : ∀ sK3 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3
    conv => enter [1]; rw [h54287 sK3 sK3 sK3 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK3 ◇ sK3)]
  have l14 : ∀ sK3 X0 : G, ((sK3 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1, 1]; rw [l13 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK3 ◇ sK3) X0]
  have l15 : ∀ sK3 X0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ sK3) X0]
    conv => enter [1]; rw [l14 sK3 X0]
  have l16 : ∀ sK4 sK1 sK0 sK3 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK0 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [l10 sK4 sK1 sK0 sK3 sK3 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))]
  have l17 : ∀ sK4 sK1 sK0 sK3 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK0 ◇ sK3))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [l10 sK4 sK1 sK0 sK3 sK4 (sK1 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ (sK0 ◇ sK3)) (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))]
  have l18 : ∀ sK4 sK1 sK0 sK3 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))))) = (sK4 ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK4 sK1 sK0 sK3 X0
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK0 ◇ sK3)) (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))))]
    conv => enter [1, 2]; rw [← l10 sK4 sK1 sK0 sK3 (sK1 ◇ (sK0 ◇ sK3)) X0]
  have l19 : ∀ sK1 sK0 sK3 sK4 X0 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))))) := by
    intro sK1 sK0 sK3 sK4 X0
    conv => enter [1]; rw [l11 sK1 sK0 sK3 sK4 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))]
    conv => enter [1]; rw [← l18 sK4 sK1 sK0 sK3 X0]
  have l20 : ∀ sK1 sK0 sK3 sK4 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l19 sK1 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [← l10 sK4 sK1 sK0 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) sK1]
  have l21 : ∀ sK1 sK0 sK3 sK4 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l20 sK1 sK0 sK3 sK4]
    conv => enter [1]; rw [l16 sK4 sK1 sK0 sK3]
  have l22 : ∀ X0 X1 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))))) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK3 sK4 sK1 sK0
    conv => enter [1, 2, 2]; rw [← l21 sK1 sK0 sK3 sK4]
    conv => enter [1]; rw [← h54287 (sK1 ◇ (sK0 ◇ sK3)) (sK0 ◇ sK3) X0 X1]
  have l23 : ∀ X0 X1 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))))) = ((sK0 ◇ sK3) ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l22 X0 X1 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK0 sK3 (sK0 ◇ sK3) (sK0 ◇ sK3)]
  have l24 : ∀ X0 X1 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))))) = ((sK3 ◇ sK3) ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l23 X0 X1 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l5 sK3 (sK0 ◇ sK3) (sK0 ◇ sK3)]
  have l25 : ∀ X0 X1 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l24 X0 X1 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l5 sK3 (sK3 ◇ sK3) (sK0 ◇ sK3)]
  have l26 : ∀ X0 X1 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l25 X0 X1 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l15 sK3 (sK0 ◇ sK3)]
  have l27 : ∀ sK0 sK3 X0 X1 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ sK3) = (X0 ◇ (X1 ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))))) := by
    intro sK0 sK3 X0 X1 sK4 sK1
    conv => enter [1]; rw [l12 sK0 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l26 X0 X1 sK3 sK4 sK1 sK0]
  have l28 : ∀ sK0 sK3 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ sK3) = ((sK3 ◇ sK3) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))))) := by
    intro sK0 sK3 sK4 sK1
    conv => enter [1]; rw [l27 sK0 sK3 sK0 sK0 sK4 sK1]
    conv => enter [1]; rw [← h54287 (sK3 ◇ sK3) (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) sK0 sK0]
  have l29 : ∀ sK0 sK3 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ sK3) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))))) := by
    intro sK0 sK3 sK4 sK1
    conv => enter [1]; rw [l28 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [← l5 sK3 (sK3 ◇ sK3) (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))]
  have l30 : ∀ sK0 sK3 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ sK3) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))))) := by
    intro sK0 sK3 sK4 sK1
    conv => enter [1]; rw [l29 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [← l15 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))]
  have l31 : ∀ sK0 sK3 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ sK3) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3 sK4 sK1
    conv => enter [1]; rw [l30 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [← l10 sK4 sK1 sK0 sK3 sK3 (sK3 ◇ sK3)]
  have l32 : ∀ sK0 sK3 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ sK3) = ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK0 sK3 sK4 sK1
    conv => enter [1]; rw [l31 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [l16 sK4 sK1 sK0 sK3]
  have l33 : ∀ sK0 sK3 X0 X1 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))))) := by
    intro sK0 sK3 X0 X1 sK4 sK1
    conv => enter [1]; rw [h54287 (sK0 ◇ sK3) sK3 X0 X1]
    conv => enter [1, 2, 2]; rw [l32 sK0 sK3 sK4 sK1]
  have l34 : ∀ sK0 sK3 X0 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ (sK3 ◇ X0)) = (((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) ◇ X0) := by
    intro sK0 sK3 X0 sK4 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK3) sK3 X0]
    conv => enter [1, 1]; rw [l32 sK0 sK3 sK4 sK1]
  have l35 : ∀ sK0 sK3 X0 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ (sK3 ◇ X0)) = ((sK3 ◇ sK3) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ X0)) := by
    intro sK0 sK3 X0 sK4 sK1
    conv => enter [1]; rw [l34 sK0 sK3 X0 sK4 sK1]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) X0]
  have l36 : ∀ sK0 sK3 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))))) := by
    intro sK0 sK3 sK4 sK1
    conv => enter [1]; rw [l33 sK0 sK3 sK0 sK0 sK4 sK1]
    conv => enter [1]; rw [← h54287 (sK3 ◇ sK3) (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) sK0 sK0]
  have l37 : ∀ sK0 sK3 X0 sK1 : G, ((sK0 ◇ sK3) ◇ (sK3 ◇ X0)) = ((sK3 ◇ sK3) ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ X0)) := by
    intro sK0 sK3 X0 sK1
    conv => enter [1]; rw [l35 sK0 sK3 X0 sK0 sK1]
    conv => enter [1]; rw [l7 (sK3 ◇ sK3) sK0 sK1 sK0 sK3 X0]
  have l38 : ∀ sK0 sK3 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))))) := by
    intro sK0 sK3 sK4 sK1
    conv => enter [1]; rw [l36 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [← l5 sK3 (sK3 ◇ sK3) (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))]
  have l39 : ∀ sK0 sK3 X0 : G, ((sK0 ◇ sK3) ◇ (sK3 ◇ X0)) = ((sK3 ◇ sK3) ◇ ((sK0 ◇ sK3) ◇ X0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l37 sK0 sK3 X0 sK0]
    conv => enter [1]; rw [l8 (sK3 ◇ sK3) sK0 sK0 sK3 X0]
  have l40 : ∀ sK0 sK3 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))))) := by
    intro sK0 sK3 sK4 sK1
    conv => enter [1]; rw [l38 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [← l15 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))]
  have l41 : ∀ sK0 sK3 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3 sK4 sK1
    conv => enter [1]; rw [l40 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [← l10 sK4 sK1 sK0 sK3 sK3 (sK3 ◇ sK3)]
  have l42 : ∀ sK0 sK3 sK4 sK1 : G, ((sK0 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK0 sK3 sK4 sK1
    conv => enter [1]; rw [l41 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [l16 sK4 sK1 sK0 sK3]
  have l43 : ∀ sK3 sK4 sK1 sK0 : G, ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) = ((sK3 ◇ sK3) ◇ ((sK0 ◇ sK3) ◇ sK3)) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l42 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [l39 sK0 sK3 sK3]
  have l44 : ∀ sK3 sK4 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK3 sK3 (sK3 ◇ sK3) sK0]
    conv => enter [1]; rw [← l43 sK3 sK4 sK1 sK0]
  have l45 : ∀ sK3 sK4 sK1 sK0 : G, ((sK3 ◇ sK3) ◇ sK3) = ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK3 sK3 sK3]
    conv => enter [1]; rw [l44 sK3 sK4 sK1 sK0]
  have l46 : ∀ sK3 sK4 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h4512 sK3 sK3 sK3]
    conv => enter [1]; rw [l45 sK3 sK4 sK1 sK0]
  have l47 : ∀ sK4 sK1 sK0 sK3 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK3 X0
    conv => enter [1]; rw [l10 sK4 sK1 sK0 sK3 X0 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [← l46 sK3 sK4 sK1 sK0]
  have l48 : ∀ sK3 sK4 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h54287 sK3 sK3 sK3 sK3]
    conv => enter [1]; rw [← l47 sK4 sK1 sK0 sK3 sK3]
  have l49 : ∀ X0 X1 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ sK3)))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro X0 X1 sK3 sK4 sK1 sK0
    conv => enter [1, 2, 2]; rw [l48 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← h54287 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) (sK1 ◇ (sK0 ◇ sK3)) X0 X1]
  have l50 : ∀ X0 X1 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ sK3)))) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro X0 X1 sK3 sK1 sK0
    conv => enter [1]; rw [l49 X0 X1 sK3 X0 sK1 sK0]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK3 (sK1 ◇ (sK0 ◇ sK3)) (sK1 ◇ (sK0 ◇ sK3))]
  have l51 : ∀ X0 X1 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ sK3)))) = ((sK3 ◇ sK3) ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro X0 X1 sK3 sK1 sK0
    conv => enter [1]; rw [l50 X0 X1 sK3 sK1 sK0]
    conv => enter [1]; rw [← l5 sK3 (sK1 ◇ (sK0 ◇ sK3)) (sK1 ◇ (sK0 ◇ sK3))]
  have l52 : ∀ X0 X1 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ sK3)))) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro X0 X1 sK3 sK1 sK0
    conv => enter [1]; rw [l51 X0 X1 sK3 sK1 sK0]
    conv => enter [1]; rw [← l5 sK3 (sK3 ◇ sK3) (sK1 ◇ (sK0 ◇ sK3))]
  have l53 : ∀ X0 X1 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ sK3)))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro X0 X1 sK3 sK1 sK0
    conv => enter [1]; rw [l52 X0 X1 sK3 sK1 sK0]
    conv => enter [1]; rw [← l15 sK3 (sK1 ◇ (sK0 ◇ sK3))]
  have l54 : ∀ sK1 sK0 sK3 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ sK3)))) := by
    intro sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [l11 sK1 sK0 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l53 X0 X1 sK3 sK1 sK0]
  have l55 : ∀ sK1 sK0 sK3 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l54 sK1 sK0 sK3 sK1 sK1]
    conv => enter [1]; rw [← h54287 sK3 (sK3 ◇ sK3) sK1 sK1]
  have l56 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [h54287 sK3 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l55 sK1 sK0 sK3]
  have l57 : ∀ sK3 X0 sK4 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l56 sK3 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 sK3 X0 sK4]
  have l58 : ∀ X1 sK2 sK3 X0 sK4 sK1 sK0 : G, (X1 ◇ (sK2 ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro X1 sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [← h54287 sK3 sK3 X1 sK2]
    conv => enter [1]; rw [l57 sK3 X0 sK4 sK1 sK0]
  have l59 : ∀ sK4 sK1 sK0 sK3 X0 sK2 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK3 X0 sK2
    conv => enter [1]; rw [l17 sK4 sK1 sK0 sK3]
    conv => enter [1]; rw [← l58 X0 sK2 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) sK4 sK1 sK0]
  have l60 : ∀ sK4 sK1 sK0 sK3 X0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK3 X0
    conv => enter [1]; rw [← l12 sK0 sK3 sK4 sK1]
    conv => enter [1]; rw [l12 sK0 sK3 X0 sK1]
  have l61 : ∀ sK4 sK1 sK0 sK3 X0 sK2 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK3 X0 sK2
    conv => enter [1]; rw [l60 sK4 sK1 sK0 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))]
    conv => enter [1]; rw [l59 sK4 sK1 sK0 sK3 X0 sK2]
  have l62 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK3 sK2]
    conv => enter [1]; rw [← l61 sK4 sK1 sK0 sK3 sK2 sK2]
  intro x y z w u
  conv => enter [1]; rw [l62 x y z w u]

@[equational_result]
theorem Equation54307_implies_Equation54287 (G : Type*) [Magma G] (h54307 : Equation54307 G) : Equation54287 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54307 sK1 sK2 sK1 sK1 sK2]
    conv => enter [1]; rw [← h54307 X0 sK2 sK1 sK1 sK2]
  have l1 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [h54307 sK1 sK2 X1 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_54253_implies_Equation54265 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54253 : Equation54253 G) : Equation54265 G := by
  have l0 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK0 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 (sK0 ◇ sK2)]
  have l1 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l0 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l2 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h54253 X2 (X1 ◇ (X0 ◇ X1)) X3]
    conv => enter [1, 2, 2]; rw [← h54253 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54253 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h54253 (sK0 ◇ sK2) sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK2) sK2]
  have l5 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h4512 X2 (X1 ◇ (X0 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h54253 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54253 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ X1))]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54253 X0 X1 X0]
  have l8 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l5 X2 X1 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l9 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l3 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l10 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l2 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X0 ◇ (X1 ◇ X1))]
  have l11 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l8 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l12 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ sK2) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 sK2]
    conv => enter [1]; rw [h54253 sK0 sK2 X0]
  have l13 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l7 X1 X2 X0]
    conv => enter [1]; rw [← l9 X3 X2 X0 X1]
  have l14 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l10 X2 X1 X0 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l15 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l11 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l16 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l14 X2 X1 X0 X3]
    conv => enter [1, 2, 2]; rw [← l13 X1 X1 X0 X0]
  have l17 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l15 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l18 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l16 X2 X1 X0 X2]
    conv => enter [1]; rw [← l13 X1 X1 X2 X1]
  have l19 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l18 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X1 X0]
    conv => enter [1]; rw [← l17 (X0 ◇ X1) X1 (X0 ◇ X1) X1]
  have l21 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1]; rw [← l17 X1 X1 (X0 ◇ X1) X0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1 X1 X1]
    conv => enter [1]; rw [← l22 X1 X0]
  have l24 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l1 sK2 sK0 sK2]
    conv => enter [1, 2]; rw [l12 sK0 sK2 X0]
  have l25 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ sK2) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l12 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK0 ◇ sK2))]
  have l26 : ∀ sK3 sK2 sK0 X0 X1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK2 sK0 X0 X1
    conv => enter [1]; rw [← l12 sK0 sK2 sK3]
    conv => enter [1]; rw [l25 sK0 sK2 X0 X1]
  have l27 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 sK2]
    conv => enter [1]; rw [l24 sK2 sK0 X0]
  have l28 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [l26 sK3 sK2 sK0 (sK2 ◇ sK2) sK3]
    conv => enter [1]; rw [← l27 sK0 sK2 sK3]
  have l29 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h54253 sK2 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK2 ◇ sK2)]
  have l30 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [l28 sK3 sK2 sK0]
    conv => enter [1]; rw [← l29 sK2 sK0]
  have l31 : ∀ sK3 sK2 sK0 X0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK2 sK0 X0
    conv => enter [1]; rw [l30 sK3 sK2 sK0]
    conv => enter [1]; rw [← l23 X0 sK2]
  intro x y z w
  conv => enter [1]; rw [← l31 z y w x]

theorem Equation4512_54265_implies_Equation54253 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54265 : Equation54265 G) : Equation54253 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [← h54265 (X1 ◇ X2) sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l3 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h54265 (sK1 ◇ sK1) sK1 X0 sK0]
  have l6 : ∀ X0 sK1 X1 X2 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 X1 X2 sK0
    conv => enter [1]; rw [h54265 X0 sK1 (X1 ◇ X2) sK0]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK2 sK1 sK0 X1 X2 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0 X1 X2
    conv => enter [1]; rw [← h54265 sK2 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 sK2 sK1 X1 X2 sK0]
  have l8 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h54265 sK1 sK1 sK2 sK0]
  have l9 : ∀ X0 sK1 sK0 X1 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0 X1 sK2
    conv => enter [1]; rw [l4 X0 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [h54265 X0 sK1 sK2 sK0]
  have l10 : ∀ sK2 sK1 sK0 X1 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0 X1
    conv => enter [1]; rw [l7 sK2 sK1 sK0 X1 sK2]
    conv => enter [1, 2]; rw [← h54265 sK0 sK1 sK2 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h54265 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK1 sK0 sK2]
  have l12 : ∀ sK0 sK1 X1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1 sK2
    conv => enter [1]; rw [h54265 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK1 sK0 X1 sK2]
  have l13 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1]; rw [← l13 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_54350_implies_Equation54321 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54350 : Equation54350 G) : Equation54321 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54350 X0 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54350 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X0]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK1 sK2]
    conv => enter [1]; rw [h54350 X0 (sK2 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l1 X0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK2 sK1]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l4 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 X0]
    conv => enter [1, 1]; rw [l5 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 sK2 sK1]
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l10 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l12 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h54350 (sK0 ◇ (sK1 ◇ sK2)) sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h54350 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2, 2]; rw [l2 sK0 sK1 sK2]
    conv => enter [1, 1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 X0]
  have l15 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ X0)]
  have l17 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [h54350 (sK0 ◇ (sK1 ◇ sK2)) X1 X0]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2 X0 X1]
  have l18 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l16 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l8 sK0 sK2 sK1 X0]
  have l19 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2 X1 X0]
  have l20 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l18 sK0 sK1 sK2 X0]
  have l21 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK0 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [h54350 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l20 sK0 sK2 sK1 X0]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK0 sK2 sK1]
  have l24 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK0 sK2 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l23 sK0 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [← l24 sK0 sK2 sK1]
  have l26 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l25 sK0 sK1 sK2]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l19 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54350 (sK0 ◇ (sK1 ◇ sK2)) sK0 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l22 sK0 sK2 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l31 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [l30 sK0 sK2 sK1]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l31 sK0 sK2 sK1]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l34 x y z]
  conv => enter [1]; rw [l2 x z y]

theorem Equation4512_54321_implies_Equation54350 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54321 : Equation54321 G) : Equation54350 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK2)]
  have l4 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l3 sK2 sK1 sK0]
  have l5 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [← l3 sK2 sK1 sK0]
  have l6 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l5 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK2) X0]
  have l7 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK2 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← l6 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l8 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h54321 X3 X2 (X0 ◇ X1)]
  have l9 : ∀ X1 sK1 sK2 X0 sK0 : G, (X1 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0)) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro X1 sK1 sK2 X0 sK0
    conv => enter [1]; rw [h54321 X1 ((sK1 ◇ sK2) ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l10 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2)) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54321 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK2]
    conv => enter [1, 2, 2]; rw [← l3 sK2 sK1 sK0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h54321 X0 X1 X2]
    conv => enter [1]; rw [← h54321 X0 (X2 ◇ X1) X0]
  have l12 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54321 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l13 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h54321 sK0 X0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l14 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h54321 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK2]
  have l15 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h54321 sK1 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l16 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ (X0 ◇ X1))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [h54321 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ (X1 ◇ X0))]
  have l17 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (X1 ◇ X0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [h54321 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ (X1 ◇ X0))]
  have l18 : ∀ sK0 sK2 sK1 X0 X1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ X0))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1, 2]; rw [h54321 (sK2 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ X0))]
  have l19 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ X0))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1]; rw [l18 sK0 sK2 sK1 X0 X1]
  have l20 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (X1 ◇ X0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [l17 sK0 sK1 sK2 X0 X1]
  have l21 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [l16 sK1 sK2 X0 X1]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK1]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X2 X1 X0]
  have l24 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l10 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← h54321 X0 (sK1 ◇ sK2) (sK2 ◇ (sK1 ◇ sK0))]
  have l25 : ∀ X1 sK1 sK2 X0 sK0 : G, (X1 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK1 sK2 X0 sK0
    conv => enter [1]; rw [l9 X1 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h54321 X1 X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l26 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l8 X3 X0 X1 X2]
    conv => enter [1]; rw [← h54321 X3 (X1 ◇ X2) X0]
  have l27 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54321 X0 X2 X1]
    conv => enter [1]; rw [l23 X0 X1 X2]
  have l28 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l24 X0 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) sK2]
  have l29 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ sK0))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l25 X1 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 sK0]
  have l30 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l26 X3 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l31 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l28 X0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l15 sK1 (sK0 ◇ (sK1 ◇ sK2)) sK2]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54321 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l22 sK0 sK1 sK2]
  have l33 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54321 X0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [l22 sK0 sK1 sK2]
  have l34 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54321 X0 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l33 X0 sK0 sK1 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2]
  have l36 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l34 X0 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK0) sK0]
  have l37 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
  have l38 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l36 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l30 X0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK0) sK0]
  have l39 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK1)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l38 X0 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l22 sK0 sK1 sK2]
  have l40 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)))) = (X0 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 X0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0]
  have l41 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l40 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l42 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l41 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l30 X0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l43 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← l42 X0 sK0 sK1 sK2]
  have l44 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l43 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 X0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
  have l45 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [h54321 sK0 (sK1 ◇ sK2) sK0]
  have l46 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [h54321 X0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← h54321 X0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l47 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54321 X0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l46 X0 sK1 sK2 sK0]
  have l48 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54321 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1, 2, 2]; rw [← l45 sK0 sK1 sK2]
  have l49 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [← l45 sK0 sK1 sK2]
  have l50 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l49 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
  have l51 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l48 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 X0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l52 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l50 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l53 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l51 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l54 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l52 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h54321 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l55 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l30 X0 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [← l53 X0 sK0 sK1 sK2]
  have l56 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l45 sK0 sK1 sK2]
    conv => enter [1]; rw [l55 X0 sK0 sK1 sK2]
  have l57 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h54321 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) sK0]
  have l58 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54321 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l47 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
  have l59 : ∀ X0 sK0 sK1 sK2 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = (X0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1, 1]; rw [l47 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) X1]
  have l60 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)]
    conv => enter [1, 2]; rw [← l47 sK0 sK0 sK1 sK2]
  have l61 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)]
    conv => enter [1, 2]; rw [← l47 sK2 sK0 sK1 sK2]
  have l62 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l47 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l63 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l47 (sK1 ◇ sK0) sK0 sK1 sK2]
  have l64 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l63 sK2 sK1 sK0]
  have l65 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l62 sK0 sK1 sK2]
  have l66 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l61 sK1 sK2 sK0]
  have l67 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l60 sK1 sK0 sK2]
  have l68 : ∀ X0 sK0 sK1 sK2 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [l59 X0 sK0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
  have l69 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0))]
  have l70 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l65 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 (sK0 ◇ (sK1 ◇ sK2)) sK2 sK1]
  have l71 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l67 sK1 sK0 sK2]
    conv => enter [1]; rw [l56 (sK1 ◇ sK0) sK0 sK1 sK2]
  have l72 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK1 ◇ sK2)) X1]
    conv => enter [1]; rw [l68 X0 sK0 sK1 sK2 X1]
  have l73 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l69 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 (sK0 ◇ (sK1 ◇ sK2)) ((sK1 ◇ sK2) ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
  have l74 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l73 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l75 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 sK1 sK2]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l76 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
    conv => enter [1]; rw [l56 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
  have l77 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l76 sK0 sK1 sK2]
    conv => enter [1]; rw [l54 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l78 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
    conv => enter [1]; rw [← l77 sK0 sK1 sK2]
  have l79 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l78 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
  have l80 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54321 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l79 sK0 sK1 sK2]
  have l81 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l80 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 (sK1 ◇ sK2) sK1 sK2]
  have l82 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l81 sK0 sK1 sK2]
  have l83 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) ((sK1 ◇ sK2) ◇ sK0) X0]
    conv => enter [1, 1]; rw [l58 sK0 sK1 sK2]
  have l84 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l83 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l85 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l84 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) sK0 X0]
  have l86 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l85 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2 X0 sK0]
  have l87 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l64 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))]
  have l88 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l87 sK0 sK2 sK1]
  have l89 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54321 X0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l66 sK1 sK2 sK0]
  have l90 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l89 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 X0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l91 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l90 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 (sK1 ◇ sK2)]
  have l92 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l30 X0 (sK0 ◇ (sK1 ◇ sK2)) sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l91 X0 sK0 sK1 sK2]
  have l93 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l92 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l30 X0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) sK2]
  have l94 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [h54321 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
  have l95 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1, 2]; rw [h54321 X0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← h54321 X0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l96 : ∀ X0 sK2 sK1 sK0 X1 : G, ((X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) ◇ X1) = (X0 ◇ ((X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X1)) := by
    intro X0 sK2 sK1 sK0 X1
    conv => enter [1, 1]; rw [h54321 X0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) X1]
  have l97 : ∀ X0 sK2 sK1 sK0 X1 : G, ((X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) ◇ X1) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X1))) := by
    intro X0 sK2 sK1 sK0 X1
    conv => enter [1]; rw [l96 X0 sK2 sK1 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X1]
  have l98 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [h54321 X0 sK0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l95 X0 sK2 sK1 sK0]
  have l99 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1]; rw [h54321 X0 X1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l97 X0 sK2 sK1 sK0 X1]
  have l100 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1]; rw [l99 X0 X1 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 X0 ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) X1]
  have l101 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X1))) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1]; rw [l100 X0 X1 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) sK0 X1]
  have l102 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK0 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1]; rw [l101 X0 X1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l30 X0 sK0 X1 (sK2 ◇ (sK1 ◇ sK0))]
  have l103 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) = (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l94 sK0 sK2 sK1]
  have l104 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l103 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l105 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l104 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l106 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l105 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h54321 sK0 X0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l107 : ∀ sK0 sK2 sK1 : G, (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK2) ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l98 ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← h54321 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK2) sK0]
  have l108 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h54321 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l98 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 sK2 sK1]
  have l109 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l98 (sK2 ◇ (sK1 ◇ sK0)) sK0 sK2 sK1]
  have l110 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l109 sK0 sK2 sK1]
  have l111 : ∀ sK0 sK2 sK1 : G, (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK2) ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l107 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK2) ◇ sK0))]
  have l112 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l110 sK0 sK2 sK1]
    conv => enter [1]; rw [← h54321 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) sK2]
  have l113 : ∀ sK0 sK2 sK1 : G, (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l111 sK0 sK2 sK1]
    conv => enter [1]; rw [← l72 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 sK1 sK2 ((sK1 ◇ sK2) ◇ sK0)]
  have l114 : ∀ sK0 sK2 sK1 : G, (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l113 sK0 sK2 sK1]
    conv => enter [1]; rw [l30 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) sK0]
  have l115 : ∀ sK0 sK2 sK1 : G, (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l114 sK0 sK2 sK1]
    conv => enter [1]; rw [l106 sK0 sK2 sK1 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
  have l116 : ∀ sK0 sK2 sK1 : G, (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l115 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l117 : ∀ sK0 sK2 sK1 : G, (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l116 sK0 sK2 sK1]
    conv => enter [1]; rw [← l30 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK2))]
  have l118 : ∀ sK0 sK2 sK1 : G, (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l117 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l119 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l98 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK2 sK1]
    conv => enter [1]; rw [← l118 sK0 sK2 sK1]
  have l120 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l119 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l121 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l47 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 sK1 sK2]
    conv => enter [1]; rw [← l120 sK0 sK1 sK2]
  have l122 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l121 sK0 sK2 sK1]
  have l123 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l122 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l124 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l47 (sK2 ◇ sK1) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l70 sK0 sK1 sK2]
  have l125 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l70 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l126 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l70 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 X0 (sK2 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2))]
  have l127 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l126 X0 sK0 sK1 sK2]
  have l128 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l124 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l129 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l127 X0 sK2 sK1 sK0]
    conv => enter [1]; rw [← h54321 X0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
  have l130 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l125 sK0 sK1 sK2]
    conv => enter [1]; rw [l86 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l131 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l128 sK2 sK1 sK0]
    conv => enter [1]; rw [← l7 sK2 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l132 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l30 X0 sK1 (sK0 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1]; rw [l129 X0 sK2 sK1 sK0]
  have l133 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l130 sK0 sK1 sK2]
    conv => enter [1]; rw [l86 sK0 sK1 sK2 sK0]
  have l134 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l131 sK2 sK1 sK0]
  have l135 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l15 sK1 (sK0 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1]; rw [l132 X0 sK1 sK0 sK2]
  have l136 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l133 sK0 sK1 sK2]
    conv => enter [1]; rw [l54 sK0 sK1 sK2 sK0]
  have l137 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK1 sK0]
    conv => enter [1]; rw [l134 sK2 sK1 sK0]
  have l138 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l31 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l135 X0 sK1 sK2 sK0]
  have l139 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l136 sK0 sK1 sK2]
    conv => enter [1]; rw [← l45 sK0 sK1 sK2]
  have l140 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l47 (sK1 ◇ sK2) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l139 sK0 sK1 sK2]
  have l141 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [← l139 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 X0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l142 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [← l139 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
  have l143 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
    conv => enter [1]; rw [l142 sK0 sK1 sK2 X0]
  have l144 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54321 X0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l141 X0 sK0 sK1 sK2]
  have l145 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l140 sK1 sK2 sK0]
    conv => enter [1]; rw [l56 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l146 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l54 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l143 sK0 sK1 sK2 X0]
  have l147 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l71 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l148 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54321 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l71 sK1 sK0 sK2]
  have l149 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54321 X0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l148 X0 sK0 sK1 sK2]
  have l150 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l147 sK2 sK1 sK0]
  have l151 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l149 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK0)]
  have l152 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK1)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l151 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l22 sK0 sK1 sK2]
  have l153 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l152 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l39 X0 sK1 sK0 sK2]
  have l154 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l82 sK0 sK1 sK2]
    conv => enter [1]; rw [l58 sK0 sK1 sK2]
  have l155 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l139 sK0 sK1 sK2]
    conv => enter [1]; rw [l154 sK0 sK1 sK2]
  have l156 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l155 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l157 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
    conv => enter [1]; rw [l156 sK0 sK1 sK2 X0]
  have l158 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l54 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l157 sK0 sK1 sK2 X0]
  have l159 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0)) = (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) X0]
    conv => enter [1, 1]; rw [l108 sK0 sK2 sK1]
  have l160 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l159 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l161 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l160 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l162 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l161 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l19 sK0 sK2 sK1 X0 sK0]
  have l163 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l112 sK0 sK2 sK1]
    conv => enter [1]; rw [← h54321 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2 (sK1 ◇ sK0)]
  have l164 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l163 sK0 sK2 sK1]
    conv => enter [1]; rw [l162 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l165 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l164 sK0 sK2 sK1]
    conv => enter [1]; rw [l162 sK0 sK2 sK1 sK0]
  have l166 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l165 sK0 sK2 sK1]
    conv => enter [1]; rw [l106 sK0 sK2 sK1 sK0]
  have l167 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l166 sK0 sK2 sK1]
    conv => enter [1]; rw [← l94 sK0 sK2 sK1]
  have l168 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l88 sK0 sK2 sK1]
    conv => enter [1]; rw [← h54321 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
  have l169 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l168 sK0 sK2 sK1]
    conv => enter [1]; rw [← l44 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 sK1 sK2]
  have l170 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l88 sK0 sK2 sK1]
    conv => enter [1]; rw [← l169 sK0 sK2 sK1]
  have l171 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l170 sK0 sK2 sK1]
    conv => enter [1]; rw [l162 sK0 sK2 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l172 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l171 sK0 sK2 sK1]
    conv => enter [1]; rw [l123 sK0 sK2 sK1 sK0]
  have l173 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l172 sK0 sK2 sK1]
    conv => enter [1]; rw [← l86 sK0 sK1 sK2 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l174 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l173 sK0 sK2 sK1]
    conv => enter [1]; rw [← l158 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1 sK2]
  have l175 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l174 sK0 sK2 sK1]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK2 sK1]
  have l176 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l121 sK0 sK2 sK1]
    conv => enter [1]; rw [l175 sK0 sK2 sK1]
  have l177 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l137 sK2 sK1 sK0]
  have l178 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h54321 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l137 sK2 sK1 sK0]
  have l179 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)))) = (X0 ◇ (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1, 2, 2]; rw [l137 sK2 sK1 sK0]
    conv => enter [1]; rw [← h54321 X0 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK2 ◇ (sK1 ◇ sK0))]
  have l180 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l179 X0 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK1 ◇ sK0))]
  have l181 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l178 sK2 sK1 sK0]
    conv => enter [1]; rw [← h54321 (sK2 ◇ (sK1 ◇ sK0)) sK2 sK1]
  have l182 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l177 sK0 sK2 sK1]
  have l183 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h54321 X0 (sK1 ◇ sK2) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l180 X0 sK2 sK1 sK0]
  have l184 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l181 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l139 sK0 sK1 sK2]
  have l185 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l182 sK0 sK2 sK1]
    conv => enter [1]; rw [← l144 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 sK1 sK2]
  have l186 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l56 (sK2 ◇ (sK1 ◇ sK0)) sK0 sK1 sK2]
    conv => enter [1]; rw [← l184 sK2 sK1 sK0]
  have l187 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l185 sK0 sK2 sK1]
    conv => enter [1]; rw [l106 sK0 sK2 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l188 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l150 sK2 sK1 sK0]
    conv => enter [1]; rw [l186 sK2 sK1 sK0]
  have l189 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1, 2, 2]; rw [l150 sK2 sK1 sK0]
    conv => enter [1]; rw [← h54321 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK2 ◇ (sK1 ◇ sK0))]
  have l190 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l189 X0 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK1 ◇ sK0))]
  have l191 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l102 X0 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK2 sK1]
    conv => enter [1]; rw [← l190 X0 sK2 sK1 sK0]
  have l192 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l191 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 X0 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK1 ◇ sK0))]
  have l193 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l145 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l194 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l193 sK1 sK0 sK2]
    conv => enter [1]; rw [← l30 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
  have l195 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l194 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l196 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l195 sK1 sK0 sK2]
    conv => enter [1]; rw [← l138 (sK1 ◇ sK0) sK1 sK2 sK0]
  have l197 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l196 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 (sK2 ◇ (sK1 ◇ sK0))]
  have l198 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l197 sK1 sK0 sK2]
  have l199 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l198 sK1 sK0 sK2]
    conv => enter [1]; rw [← l138 sK1 sK1 sK2 sK0]
  have l200 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l187 sK0 sK2 sK1]
    conv => enter [1]; rw [← h54321 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK2))]
  have l201 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l200 sK0 sK2 sK1]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK2 sK1]
  have l202 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l201 sK0 sK2 sK1]
    conv => enter [1]; rw [← l176 sK0 sK1 sK2]
  have l203 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l202 sK0 sK2 sK1]
    conv => enter [1]; rw [← l13 sK0 (sK1 ◇ sK2) sK2 sK1]
  have l204 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l203 sK0 sK1 sK2]
  have l205 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [h54321 sK1 sK2 sK1]
  have l206 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1, 2]; rw [h54321 X0 sK2 sK1]
    conv => enter [1]; rw [← h54321 X0 (sK1 ◇ sK2) X0]
  have l207 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h54321 (sK1 ◇ sK0) sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2))]
  have l208 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [h54321 (sK2 ◇ (sK1 ◇ sK0)) sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK0 sK2 ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2))]
  have l209 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l208 sK1 sK0 sK2]
    conv => enter [1]; rw [l30 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK2)]
  have l210 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l207 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK2)]
  have l211 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54321 X0 sK1 sK2]
    conv => enter [1]; rw [l206 X0 sK2 sK1]
  have l212 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l209 sK1 sK0 sK2]
    conv => enter [1, 2, 2]; rw [l167 sK0 sK2 sK1]
  have l213 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK2 ◇ sK1)]
    conv => enter [1]; rw [l210 sK2 sK1 sK0]
  have l214 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l29 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 sK1 sK2]
    conv => enter [1]; rw [← l212 sK1 sK0 sK2]
  have l215 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l188 sK2 sK1 sK0]
    conv => enter [1]; rw [l213 sK2 sK1 sK0]
  have l216 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l214 sK1 sK0 sK2]
    conv => enter [1]; rw [l2 sK1 sK0 sK2 (sK2 ◇ sK1)]
  have l217 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l27 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2]
    conv => enter [1]; rw [← l216 sK1 sK0 sK2]
  have l218 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l217 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l121 sK0 sK2 sK1]
  have l219 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l218 sK1 sK0 sK2]
    conv => enter [1]; rw [l192 sK1 sK0 sK1 sK2]
  have l220 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l219 sK1 sK0 sK2]
    conv => enter [1]; rw [l199 sK1 sK0 sK2]
  have l221 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l15 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2]
    conv => enter [1]; rw [l220 sK1 sK0 sK2]
  have l222 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54321 X0 (sK1 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1, 2, 2]; rw [← l205 sK1 sK2]
  have l223 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK1 ◇ sK2) ◇ sK1) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l205 sK1 sK2]
  have l224 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l223 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK1 X0]
  have l225 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l222 X0 sK1 sK2]
    conv => enter [1]; rw [← h54321 X0 sK1 (sK1 ◇ sK2)]
  have l226 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l224 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
  have l227 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l225 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK2) sK1]
  have l228 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l226 sK1 sK2 X0]
    conv => enter [1]; rw [← h54321 sK1 X0 (sK1 ◇ sK2)]
  have l229 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l30 X0 sK1 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l227 X0 sK1 sK2]
  have l230 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l205 sK1 sK2]
    conv => enter [1]; rw [l229 X0 sK1 sK2]
  have l231 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l211 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1 sK2]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0]
  have l232 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ (sK1 ◇ sK2)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l211 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) sK1 sK2]
    conv => enter [1, 2]; rw [← l66 sK1 sK2 sK0]
  have l233 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l211 ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) sK1 sK2]
    conv => enter [1, 2]; rw [← h54321 (sK1 ◇ sK2) sK2 sK1]
  have l234 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l211 sK0 sK1 sK2]
    conv => enter [1]; rw [h54321 sK0 (sK1 ◇ sK2) sK0]
  have l235 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l211 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [← h54321 (sK1 ◇ sK2) sK2 sK1]
  have l236 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l211 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l237 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l211 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK2) ◇ sK0)]
  have l238 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l211 (sK1 ◇ sK0) sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 (sK1 ◇ sK0)]
  have l239 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l238 sK1 sK0 sK2]
    conv => enter [1]; rw [l153 sK1 sK0 sK1 sK2]
  have l240 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l237 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK0]
  have l241 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l233 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))]
  have l242 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l232 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l243 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l231 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)))]
  have l244 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l239 sK1 sK0 sK2]
  have l245 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l240 sK1 sK0 sK2]
    conv => enter [1]; rw [l56 sK1 sK0 sK1 sK2]
  have l246 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l241 sK1 sK2]
    conv => enter [1]; rw [← h54321 (sK1 ◇ sK2) (sK2 ◇ sK1) (sK1 ◇ sK2)]
  have l247 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l93 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
    conv => enter [1]; rw [← l242 sK0 sK1 sK2]
  have l248 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l243 sK1 sK0 sK2]
    conv => enter [1]; rw [← l72 sK1 sK0 sK1 sK2 ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2))]
  have l249 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l245 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l250 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l246 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK1 ◇ sK2)]
  have l251 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l247 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 (sK1 ◇ sK2)]
  have l252 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l248 sK1 sK0 sK2]
    conv => enter [1]; rw [l30 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK2)]
  have l253 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l249 sK1 sK0 sK2]
  have l254 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l250 sK1 sK2]
    conv => enter [1]; rw [← l21 sK1 sK2 (sK1 ◇ sK2) sK1]
  have l255 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l86 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l251 sK0 sK1 sK2]
  have l256 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l252 sK1 sK0 sK2]
    conv => enter [1]; rw [← l183 sK1 sK1 sK2 sK0]
  have l257 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l253 sK1 sK0 sK2]
  have l258 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l254 sK1 sK2]
    conv => enter [1]; rw [l230 (sK1 ◇ sK2) sK1 sK2]
  have l259 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l58 sK0 sK1 sK2]
    conv => enter [1]; rw [l255 sK0 sK1 sK2]
  have l260 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l256 sK1 sK0 sK2]
  have l261 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l258 sK1 sK2]
    conv => enter [1]; rw [l228 sK1 sK2 (sK1 ◇ sK2)]
  have l262 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l155 sK0 sK1 sK2]
    conv => enter [1]; rw [l259 sK0 sK1 sK2]
  have l263 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [← l139 sK0 sK1 sK2]
    conv => enter [1]; rw [l260 sK1 sK0 sK2]
  have l264 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l261 sK1 sK2]
    conv => enter [1]; rw [← l15 sK1 (sK1 ◇ sK2) sK2]
  have l265 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l236 sK0 sK1 sK2]
    conv => enter [1]; rw [l262 sK0 sK1 sK2]
  have l266 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l56 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [l263 sK1 sK0 sK2]
  have l267 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l264 sK1 sK2]
    conv => enter [1]; rw [← l15 sK1 sK2 sK2]
  have l268 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l266 sK1 sK0 sK2]
  have l269 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l267 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l270 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l257 sK1 sK0 sK2]
    conv => enter [1]; rw [l268 sK1 sK0 sK2]
  have l271 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l269 sK1 sK2]
  have l272 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54321 (sK1 ◇ sK2) sK2 sK1]
    conv => enter [1]; rw [l271 sK1 sK2]
  have l273 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l234 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l274 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l273 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l275 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l274 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h54321 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l276 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l265 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54321 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) sK2]
  have l277 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l276 sK0 sK1 sK2]
    conv => enter [1]; rw [← l146 sK0 sK2 sK1 sK2]
  have l278 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l275 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [← l277 sK0 sK1 sK2]
  have l279 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l278 sK0 sK1 sK2]
    conv => enter [1]; rw [← l155 sK0 sK1 sK2]
  have l280 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l236 sK0 sK1 sK2]
    conv => enter [1]; rw [← l279 sK0 sK1 sK2]
  have l281 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l280 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
  have l282 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l215 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l283 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l282 sK0 sK2 sK1]
  have l284 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l121 sK0 sK2 sK1]
    conv => enter [1]; rw [l283 sK0 sK2 sK1]
  have l285 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l204 sK0 sK1 sK2]
    conv => enter [1]; rw [l284 sK0 sK1 sK2]
  have l286 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l235 sK1 sK2]
  have l287 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l286 sK0 sK1 sK2]
  have l288 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l281 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l287 sK0 sK1 sK2]
  have l289 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l288 sK0 sK1 sK2]
    conv => enter [1]; rw [l139 sK0 sK1 sK2]
  have l290 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l236 sK0 sK1 sK2]
    conv => enter [1]; rw [← l289 sK0 sK1 sK2]
  have l291 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l244 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) X0]
  have l292 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l291 sK1 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l293 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l292 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h54321 sK1 X0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l294 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l293 sK1 sK0 sK2 X0]
  have l295 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l235 sK1 sK2]
    conv => enter [1]; rw [l272 sK1 sK2]
  have l296 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l295 sK1 sK2]
  have l297 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 sK2]
    conv => enter [1]; rw [← l296 sK1 sK0 sK2]
  have l298 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l297 sK1 sK0 sK2]
    conv => enter [1]; rw [l294 sK1 sK0 sK2 (sK1 ◇ sK2)]
  have l299 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l298 sK1 sK0 sK2]
    conv => enter [1]; rw [l221 sK1 sK2 sK0]
  have l300 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l270 sK1 sK0 sK2]
    conv => enter [1]; rw [← l299 sK1 sK0 sK2]
  have l301 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l300 sK1 sK0 sK2]
    conv => enter [1]; rw [l294 sK1 sK0 sK2 sK2]
  have l302 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l301 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l303 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l302 sK1 sK0 sK2]
  have l304 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l275 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l303 sK0 sK1 sK2]
  have l305 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l290 sK0 sK1 sK2]
    conv => enter [1]; rw [l304 sK0 sK1 sK2]
  have l306 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l305 sK0 sK1 sK2]
    conv => enter [1]; rw [← l204 sK0 sK1 sK2]
  have l307 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [h54321 X0 sK0 sK1]
    conv => enter [1]; rw [← h54321 X0 (sK1 ◇ sK0) X0]
  have l308 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54321 X0 sK1 sK0]
    conv => enter [1]; rw [l307 X0 sK0 sK1]
  have l309 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h54321 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [h54321 sK2 sK0 sK1]
  have l310 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l270 sK1 sK0 sK2]
    conv => enter [1]; rw [← l263 sK1 sK0 sK2]
  have l311 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l310 sK1 sK0 sK2]
    conv => enter [1]; rw [l294 sK1 sK0 sK2 sK0]
  have l312 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l311 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l313 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l308 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1 sK0]
    conv => enter [1, 2]; rw [← l312 sK1 sK0 sK2]
  have l314 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l308 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) sK2]
  have l315 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l285 sK0 sK1 sK2]
    conv => enter [1]; rw [← l313 sK0 sK2 sK1]
  have l316 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l306 sK0 sK1 sK2]
    conv => enter [1]; rw [l315 sK0 sK1 sK2]
  have l317 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l314 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK2]
  have l318 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1, 1]; rw [l314 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) sK2 X0]
  have l319 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l317 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2 X0]
  have l320 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l316 sK0 sK1 sK2]
    conv => enter [1]; rw [l319 sK0 sK2 sK1 (sK1 ◇ sK0)]
  have l321 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l309 sK2 sK1 sK0]
    conv => enter [1]; rw [← l27 (sK2 ◇ (sK1 ◇ sK0)) sK2 sK2]
  have l322 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l321 sK2 sK1 sK0]
    conv => enter [1]; rw [← l318 sK2 sK1 sK0 sK2]
  have l323 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l314 sK2 sK1 sK0]
    conv => enter [1]; rw [← l322 sK2 sK1 sK0]
  have l324 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l323 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK0))]
  have l325 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l320 sK0 sK1 sK2]
    conv => enter [1]; rw [← l324 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l325 x y z]

theorem Equation4512_54350_implies_Equation54347 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54350 : Equation54350 G) : Equation54347 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h54350 X1 X2 X0]
    conv => enter [1, 2]; rw [h54350 X0 X2 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54350 X0 X1 X2]
    conv => enter [1]; rw [h54350 X0 X2 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h54350 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X2 ◇ (X1 ◇ X0)) X3]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ X0) X3]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 (X2 ◇ X0)]
  have l5 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l6 X0 X1 X2 X3]
  have l8 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54350 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X2 (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h54350 X0 X1 X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 (X0 ◇ (X1 ◇ X2))]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1, 2]; rw [← l7 X1 X0 X0 X2]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← l4 X0 X0 X1]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l4 X0 X1 X2]
  have l14 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [← h54350 (X1 ◇ (X0 ◇ (X2 ◇ X0))) X0 X3]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X0))) X3]
  have l16 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
  have l17 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l14 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X0)) (X0 ◇ X3)]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) (X0 ◇ (X1 ◇ X2))]
  have l19 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l20 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l17 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) (X0 ◇ X3)]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1]; rw [← l7 X0 (X2 ◇ X0) X0 (X1 ◇ X2)]
  have l22 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l19 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X0 X3]
  have l23 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l20 X1 X0 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 (X0 ◇ X3)]
  have l24 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l21 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X0 ◇ (X1 ◇ X2))]
  have l25 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l22 X0 X1 X2 X3]
  have l26 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [l11 X0 X2 X3]
    conv => enter [1]; rw [← l23 X1 X0 X2 X3]
  have l27 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l24 X0 X1 X2]
    conv => enter [1]; rw [← l8 X0 X0 X1 X2]
  have l28 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l25 X0 X1 X2 X3]
  have l29 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l26 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X0)) (X3 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l30 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l29 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) (X3 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l31 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l30 X1 X0 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 (X3 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l32 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l31 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← l28 X0 X2 X3 (X1 ◇ X2)]
  have l33 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l12 X2 (X0 ◇ X1)]
  have l34 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l27 X2 X0 X1]
    conv => enter [1]; rw [← l33 X2 X0 X1]
  have l35 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l32 X1 X0 X2 X3]
    conv => enter [1, 2, 2]; rw [← l34 X2 X3 X1]
  have l36 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [← l35 X0 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [h54350 x y z]
  conv => enter [1]; rw [← l34 x z y]
  conv => enter [1]; rw [l36 x z y]

end Semigroup5
