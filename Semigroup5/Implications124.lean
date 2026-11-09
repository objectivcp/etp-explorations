import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41547_implies_Equation54168 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41547 : Equation41547 G) : Equation54168 G := by
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
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h41547 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41547 X0 X1]
  have l6 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41547 (sK2 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 sK2]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41547 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l8 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h41547 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41547 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l10 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41547 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X2]
    conv => enter [1, 1]; rw [← h41547 X0 X1]
  have l12 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41547 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))]
  have l13 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41547 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK0 ◇ ((sK2 ◇ sK2) ◇ sK0))]
  have l14 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (X0 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [h41547 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (sK2 ◇ (X0 ◇ sK2)))]
  have l15 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (X0 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l14 sK2 X0]
  have l16 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l13 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK2) sK0]
  have l17 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l19 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l7 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l20 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [h41547 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l21 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l6 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)))]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)))]
  have l23 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (X0 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l15 sK2 X0]
  have l24 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l17 X0 X1 X2]
  have l25 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l18 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l26 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l20 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l27 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l21 sK2 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK2 (sK2 ◇ sK2) ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)]
  have l28 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)))]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X1 X0]
    conv => enter [1, 2]; rw [← l19 X1 X0 X0]
  have l30 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l25 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l31 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l27 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK2 ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)]
  have l32 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)))]
  have l33 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l30 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l34 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1, 2]; rw [l23 sK2 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l31 sK2 sK2]
  have l35 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l32 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ X0)]
  have l36 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [l34 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) (sK2 ◇ (sK2 ◇ sK2))]
  have l37 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l35 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ X0)]
  have l38 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l36 sK2]
    conv => enter [1]; rw [l29 sK2 (sK2 ◇ sK2)]
  have l39 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ X0)]
  have l40 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l26 sK2]
    conv => enter [1]; rw [← l38 sK2]
  have l41 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l39 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l33 X0 (X0 ◇ X0) X1]
  have l42 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l40 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l43 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l41 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h41547 X0 X0]
  have l44 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l43 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l45 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l44 X1 X0]
    conv => enter [1]; rw [l29 X1 (X0 ◇ (X1 ◇ X0))]
  have l46 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l45 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l47 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l46 X1 X0]
    conv => enter [1, 2]; rw [l29 X0 (X1 ◇ X0)]
  have l48 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l47 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l49 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l48 X1 X0]
    conv => enter [1]; rw [← l33 X1 X0 X0]
  have l50 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l42 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l51 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l26 sK2]
    conv => enter [1, 2]; rw [← l42 sK2]
  have l52 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l26 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l53 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l52 sK1 sK2]
    conv => enter [1, 2]; rw [← l42 sK2]
  have l54 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l53 sK1 sK2]
  have l55 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l51 sK2]
    conv => enter [1]; rw [← l1 sK0 sK2]
  have l56 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41547 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [← l55 sK0 sK2]
  have l57 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l56 sK2 sK0]
    conv => enter [1]; rw [l29 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l58 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))]
  have l59 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l51 sK2]
    conv => enter [1]; rw [l58 sK2 sK1]
  have l60 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l54 sK1 sK2]
  have l61 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l60 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK2]
  have l62 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l61 sK0 sK1 sK2]
  have l63 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l61 sK0 sK1 sK2]
  have l64 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l63 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
  have l65 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l62 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK2]
  have l66 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l57 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l67 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l51 sK2]
    conv => enter [1]; rw [l66 sK2 sK0]
  have l68 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l67 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l69 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41547 (sK0 ◇ (sK2 ◇ sK2)) (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l68 sK0 sK2]
  have l70 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l68 sK0 sK2]
    conv => enter [1]; rw [← l69 sK0 sK2]
  have l71 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l70 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) (sK0 ◇ (sK2 ◇ sK2)) X0]
  have l72 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h41547 X1 X0]
    conv => enter [1, 2]; rw [l29 X0 X1]
  have l73 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [h41547 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2, 2]; rw [l29 X0 X1]
  have l74 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l29 sK0 (sK1 ◇ sK2)]
  have l75 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l29 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l76 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l29 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l77 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))]
    conv => enter [1, 2]; rw [l29 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l78 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l77 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X0)]
  have l79 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
  have l80 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l81 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l73 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X1) (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))]
  have l82 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l76 sK1 sK2]
  have l83 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l81 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))]
  have l84 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l83 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) (X0 ◇ (X1 ◇ X1))]
  have l85 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l84 X1 X0]
    conv => enter [1]; rw [← l33 X1 ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) X0]
  have l86 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l85 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l87 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l86 X1 X0]
    conv => enter [1, 2]; rw [← l33 X1 X1 X0]
  have l88 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l87 X1 X0]
    conv => enter [1]; rw [l29 X1 X1]
  have l89 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l88 X1 X0]
  have l90 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l29 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l89 X1 X0]
  have l91 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l90 X1 X0]
  have l92 : ∀ X1 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1
    conv => enter [1]; rw [h41547 X1 X1]
    conv => enter [1]; rw [l91 X1 X1]
  have l93 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l59 sK2 sK1]
    conv => enter [1, 2]; rw [← l82 sK1 sK2]
  have l94 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l10 sK2 sK1]
    conv => enter [1, 2]; rw [← l82 sK1 sK2]
  have l95 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l82 sK1 sK2]
  have l96 : ∀ sK1 sK2 X0 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l82 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l97 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) sK2 X0]
    conv => enter [1]; rw [l96 sK1 sK2 X0]
  have l98 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l95 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK2]
  have l99 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [l79 sK0 sK1 sK2]
  have l100 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l99 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l101 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l80 sK0 sK1 sK2]
  have l102 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l80 sK0 sK1 sK2]
  have l103 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l102 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
  have l104 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l101 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l105 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (((sK1 ◇ sK2) ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1, 1]; rw [l94 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 ((sK1 ◇ sK2) ◇ sK2) X0]
  have l106 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ X0))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l105 sK2 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) sK2 X0]
  have l107 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l98 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l108 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [← l98 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
  have l109 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
    conv => enter [1]; rw [l108 sK0 sK1 sK2 X0]
  have l110 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1]; rw [l107 sK0 sK1 sK2]
  have l111 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l104 sK0 sK1 sK2]
  have l112 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l111 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2) X0]
  have l113 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l110 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2) X0]
  have l114 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK2 X0]
    conv => enter [1]; rw [l113 sK0 sK1 sK2 X0]
  have l115 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK2)) ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l16 sK0 sK2]
  have l116 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l115 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l117 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l116 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) sK0 X0]
  have l118 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l117 sK0 X0 sK2]
    conv => enter [1]; rw [← l71 sK0 sK2 (sK0 ◇ X0)]
  have l119 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41547 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK0 sK1 sK2]
  have l120 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l119 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l121 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l120 sK0 sK1 sK2]
    conv => enter [1]; rw [l100 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l122 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l121 sK0 sK1 sK2]
    conv => enter [1]; rw [l112 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l123 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l122 sK0 sK1 sK2]
    conv => enter [1]; rw [← l114 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l124 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l123 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l72 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l125 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l124 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l80 sK0 sK1 sK2]
  have l126 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l125 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l98 sK0 sK1 sK2]
  have l127 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l78 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [← l126 sK0 sK1 sK2]
  have l128 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l127 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l129 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l128 sK0 sK1 sK2]
    conv => enter [1]; rw [l100 sK0 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l130 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l129 sK0 sK1 sK2]
    conv => enter [1]; rw [l112 sK0 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l131 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l130 sK0 sK1 sK2]
    conv => enter [1]; rw [← l114 sK0 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l132 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l72 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK2]
    conv => enter [1]; rw [← l131 sK0 sK1 sK2]
  have l133 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l132 sK0 sK1 sK2]
    conv => enter [1]; rw [l65 sK0 sK1 sK2]
  have l134 : ∀ sK1 sK2 X0 sK0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l135 : ∀ sK1 sK2 X0 sK0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l134 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l136 : ∀ sK1 sK2 X0 sK0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l135 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [l103 sK0 sK1 sK2 X0]
  have l137 : ∀ sK1 sK2 X0 sK0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l136 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l109 sK0 sK1 sK2 X0]
  have l138 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l137 sK1 sK2 X0 sK0]
  have l139 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l97 sK1 sK2 X0]
    conv => enter [1]; rw [l138 sK1 sK2 X0 sK0]
  have l140 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l92 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))]
  have l141 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l140 sK0 sK1 sK2]
    conv => enter [1]; rw [← l109 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l142 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l141 sK0 sK1 sK2]
  have l143 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l98 sK0 sK1 sK2]
    conv => enter [1]; rw [l142 sK0 sK1 sK2]
  have l144 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2, 2]; rw [l59 sK2 sK1]
    conv => enter [1]; rw [l49 (sK2 ◇ sK2) (sK1 ◇ sK2)]
  have l145 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l49 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))]
  have l146 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [l49 (sK1 ◇ sK2) X0]
  have l147 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [l49 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l148 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1]; rw [← l147 sK0 sK1 sK2 X0]
  have l149 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1]; rw [← l146 sK0 sK1 sK2 X0]
  have l150 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l145 sK0 sK1 sK2]
  have l151 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l144 sK2 sK1]
    conv => enter [1]; rw [← l50 sK2 (sK1 ◇ sK2)]
  have l152 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l72 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l148 sK0 sK1 sK2 X0]
  have l153 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l72 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l149 sK0 sK1 sK2 X0]
  have l154 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l54 sK1 sK2]
    conv => enter [1]; rw [l151 sK2 sK1]
  have l155 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l150 sK0 sK1 sK2]
    conv => enter [1]; rw [l103 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l156 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l93 sK2 sK1]
    conv => enter [1]; rw [l154 sK2 sK1]
  have l157 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l155 sK0 sK1 sK2]
    conv => enter [1]; rw [← l109 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l158 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1, 1]; rw [l156 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK1 ◇ sK2) X0]
  have l159 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l157 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK1 ◇ sK2))]
  have l160 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l29 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l157 sK0 sK1 sK2]
  have l161 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41547 (sK2 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [← l157 sK0 sK1 sK2]
  have l162 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l157 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK1 ◇ sK2)) X0]
  have l163 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l162 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK1 ◇ sK2) X0]
  have l164 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l161 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK2) ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l165 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l160 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l166 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l164 sK2 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK2 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l167 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l163 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l165 sK0 sK1 sK2]
  have l168 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l166 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l139 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) sK0]
  have l169 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l167 sK0 sK1 sK2]
    conv => enter [1]; rw [l153 sK0 sK1 sK2 (sK2 ◇ (sK1 ◇ sK2))]
  have l170 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l168 sK2 sK1 sK0]
    conv => enter [1]; rw [← l106 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) sK1]
  have l171 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l169 sK0 sK1 sK2]
    conv => enter [1]; rw [← l109 sK0 sK1 sK2 (sK2 ◇ (sK1 ◇ sK2))]
  have l172 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l170 sK2 sK1 sK0]
    conv => enter [1]; rw [← l158 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1]
  have l173 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l171 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (sK1 ◇ sK2)]
  have l174 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l172 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK2) (sK2 ◇ (sK1 ◇ sK2))]
  have l175 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l173 sK0 sK1 sK2]
    conv => enter [1]; rw [l64 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l176 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l106 sK2 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l174 sK2 sK0 sK1]
  have l177 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l175 sK0 sK1 sK2]
    conv => enter [1]; rw [← l143 sK0 sK1 sK2]
  have l178 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l156 sK2 sK1]
    conv => enter [1]; rw [l176 sK2 sK1 sK0]
  have l179 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1, 1]; rw [l178 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l180 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l177 sK0 sK1 sK2]
    conv => enter [1]; rw [l133 sK0 sK1 sK2]
  have l181 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l79 sK0 sK1 sK2]
    conv => enter [1]; rw [l177 sK0 sK1 sK2]
  have l182 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [← l177 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l183 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l177 sK0 sK1 sK2]
    conv => enter [1]; rw [l92 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l177 sK0 sK1 sK2]
  have l184 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l183 sK0 sK1 sK2]
    conv => enter [1]; rw [l112 sK0 sK1 sK2 sK2]
  have l185 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l182 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l100 sK0 sK1 sK2 X0]
  have l186 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l184 sK0 sK1 sK2]
    conv => enter [1]; rw [← l114 sK0 sK1 sK2 sK2]
  have l187 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l185 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l112 sK0 sK1 sK2 X0]
  have l188 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l187 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l114 sK0 sK1 sK2 X0]
  have l189 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
    conv => enter [1]; rw [l188 sK0 sK1 sK2 X0]
  have l190 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l181 sK0 sK1 sK2]
    conv => enter [1]; rw [l104 sK0 sK1 sK2]
  have l191 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h41547 (sK2 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2, 2]; rw [← l186 sK0 sK1 sK2]
  have l192 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l191 sK2 sK0 sK1]
    conv => enter [1]; rw [← l179 sK2 ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) sK0 sK1]
  have l193 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l192 sK2 sK0 sK1]
    conv => enter [1]; rw [← l50 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)]
  have l194 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l42 sK2]
    conv => enter [1]; rw [l193 sK2 sK0 sK1]
  have l195 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l29 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l190 sK0 sK1 sK2]
  have l196 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l195 sK0 sK1 sK2]
    conv => enter [1]; rw [← l114 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)]
  have l197 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l78 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [← l196 sK0 sK1 sK2]
  have l198 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l197 sK0 sK1 sK2]
    conv => enter [1]; rw [← l114 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l199 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l198 sK0 sK1 sK2]
    conv => enter [1]; rw [← l159 sK0 sK1 sK2]
  have l200 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l189 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [l199 sK0 sK1 sK2]
  have l201 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1, 1]; rw [l194 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) X0]
  have l202 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l201 sK2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
  have l203 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l61 sK0 sK1 sK2]
    conv => enter [1]; rw [l200 sK0 sK1 sK2]
  have l204 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l200 sK0 sK1 sK2]
  have l205 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h41547 (sK2 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [l200 sK0 sK1 sK2]
  have l206 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l205 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [l64 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l207 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l65 sK0 sK1 sK2]
    conv => enter [1]; rw [l204 sK0 sK1 sK2]
  have l208 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l206 sK2 sK0 sK1]
    conv => enter [1]; rw [← l202 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) sK0 sK1]
  have l209 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l180 sK0 sK1 sK2]
    conv => enter [1]; rw [l207 sK0 sK1 sK2]
  have l210 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l42 sK2]
    conv => enter [1]; rw [l208 sK2 sK0 sK1]
  have l211 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l203 sK0 sK1 sK2]
    conv => enter [1]; rw [l209 sK0 sK1 sK2]
  have l212 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
    conv => enter [1, 1]; rw [l203 sK0 sK1 sK2]
  have l213 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l212 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l214 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l210 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l215 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l214 sK0 sK2 sK1]
    conv => enter [1]; rw [← l118 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK2]
  have l216 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l215 sK0 sK2 sK1]
    conv => enter [1]; rw [← l211 sK0 sK1 sK2]
  have l217 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41547 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l216 sK0 sK2 sK1]
  have l218 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l216 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l219 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l217 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l218 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2)) sK1]
  have l220 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l219 sK0 sK1 sK2]
    conv => enter [1]; rw [l152 sK0 sK1 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l221 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l220 sK0 sK1 sK2]
    conv => enter [1]; rw [l112 sK0 sK1 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l222 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l221 sK0 sK1 sK2]
    conv => enter [1]; rw [← l114 sK0 sK1 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l223 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l222 sK0 sK1 sK2]
    conv => enter [1]; rw [← l189 sK0 sK1 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l224 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l223 sK0 sK1 sK2]
    conv => enter [1]; rw [l213 sK0 sK1 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l225 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l218 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l224 sK0 sK1 sK2]
  have l226 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l79 sK0 sK1 sK2]
    conv => enter [1]; rw [← l225 sK0 sK2 sK1]
  have l227 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l70 sK0 sK2]
    conv => enter [1]; rw [← l226 sK0 sK1 sK2]
  have l228 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l227 sK0 sK2 sK1]
    conv => enter [1]; rw [l181 sK0 sK1 sK2]
  have l229 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l157 sK0 sK1 sK2]
    conv => enter [1]; rw [← l143 sK0 sK1 sK2]
  have l230 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l229 sK0 sK1 sK2]
    conv => enter [1]; rw [← l228 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l230 x z y]

theorem Equation4512_41547_implies_Equation53870 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41547 : Equation41547 G) : Equation53870 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h41547 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41547 X0 X1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41547 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41547 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41547 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41547 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l5 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X2]
    conv => enter [1, 1]; rw [← h41547 X0 X1]
  have l12 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41547 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))]
  have l13 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l17 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l8 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l19 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)))]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l13 X0 X1 X2]
  have l21 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l14 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l24 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)))]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1 X0]
    conv => enter [1, 2]; rw [← l17 X1 X0 X0]
  have l26 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l21 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l28 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l24 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)))]
  have l29 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l26 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l31 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ X0)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l33 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l31 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ X0)]
  have l34 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l33 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ X0)]
  have l35 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l34 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l29 X0 (X0 ◇ X0) X1]
  have l36 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l35 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h41547 X0 X0]
  have l37 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l36 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l38 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1]; rw [l25 X1 (X0 ◇ (X1 ◇ X0))]
  have l39 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l38 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l40 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l39 X1 X0]
    conv => enter [1, 2]; rw [l25 X0 (X1 ◇ X0)]
  have l41 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l40 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l42 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l41 X1 X0]
    conv => enter [1]; rw [← l29 X1 X0 X0]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l45 sK0 sK1]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2]; rw [← l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41547 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [l44 sK0 sK1]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← l48 sK0 sK1 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l48 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l48 sK0 sK1 sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l54 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l42 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK1]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← l55 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l59 x y]

theorem Equation4512_41547_implies_Equation54172 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41547 : Equation41547 G) : Equation54172 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l3 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 X0]
    conv => enter [1, 1]; rw [l5 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l9 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41547 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41547 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41547 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l16 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2]; rw [l8 sK1 sK0 (sK1 ◇ sK1)]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41547 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l19 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1))]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l36 x y]

theorem Equation4512_41534_implies_Equation307 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41534 : Equation41534 G) : Equation307 G := by
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
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41534 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h41534 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1, 2]; rw [← l12 sK0]
  intro x
  conv => enter [1]; rw [l14 x]

theorem Equation4512_41534_implies_Equation41529 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41534 : Equation41534 G) : Equation41529 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41534 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l6 x]

theorem Equation4512_41534_implies_Equation54175 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41534 : Equation41534 G) : Equation54175 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l4 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l6 sK1]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l11 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41534 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK1]
  have l12 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [h41534 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l10 sK1 (sK1 ◇ sK1)]
  have l13 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41534 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h41534 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l14 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l17 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l12 sK1]
    conv => enter [1]; rw [l3 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))]
  have l18 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)]
  have l19 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1]
    conv => enter [1]; rw [← l8 sK1 sK1]
  have l20 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l17 sK1]
    conv => enter [1, 2]; rw [l10 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))]
  have l21 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1]
    conv => enter [1, 2]; rw [← l4 sK1]
  have l22 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1, 2]; rw [← l4 sK1]
  have l23 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))]
  have l24 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l25 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1, 2]; rw [← l15 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l26 sK1]
  have l28 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1]; rw [← l27 sK1]
  have l29 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l25 sK1]
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l30 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l24 sK1]
    conv => enter [1]; rw [← l29 sK1]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l30 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l32 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [← l31 sK1]
  intro x y
  conv => enter [1, 2]; rw [l32 y]

theorem Equation4512_41534_implies_Equation53860 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41534 : Equation41534 G) : Equation53860 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41534 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41534 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK0) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ X0) sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation4512_41529_53807_implies_Equation307 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41529 : Equation41529 G) (h53807 : Equation53807 G) : Equation307 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h41529 X0]
    conv => enter [1, 2]; rw [← h53807 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l5 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1, 2]; rw [l4 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l10 sK0]
    conv => enter [1]; rw [h53807 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l10 sK0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l13 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l14 sK0]
  intro x
  conv => enter [1]; rw [l15 x]

theorem Equation4512_41529_53807_implies_Equation54175 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41529 : Equation41529 G) (h53807 : Equation53807 G) : Equation54175 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h41529 X0]
    conv => enter [1, 2]; rw [← h53807 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l5 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l8 sK1 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l7 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l16 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK1 (sK1 ◇ sK1)]
  have l19 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ sK1)]
  have l20 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [← l9 sK1 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2]; rw [l7 sK1]
  have l24 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1, 2]; rw [← l5 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l28 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l26 sK1]
  have l29 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l28 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l31 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [l0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l20 sK1]
  have l32 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l31 sK1]
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ sK1)]
  have l33 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l32 sK1]
    conv => enter [1, 2]; rw [l7 sK1]
  have l34 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l33 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l29 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l34 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [← h53807 (sK1 ◇ (sK1 ◇ sK1))]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l41 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l44 x y]

theorem Equation4512_41529_53807_implies_Equation53860 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41529 : Equation41529 G) (h53807 : Equation53807 G) : Equation53860 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h41529 X0]
    conv => enter [1, 2]; rw [← h53807 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h53807 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_41628_41733_implies_Equation42223 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41628 : Equation41628 G) (h41733 : Equation41733 G) : Equation42223 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X0 ◇ X0))) X2]
    conv => enter [1, 1]; rw [← h41628 X0 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X0)) X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 X2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41733 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41733 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_41538_41783_implies_Equation41799 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41538 : Equation41538 G) (h41783 : Equation41783 G) : Equation41799 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [h41538 X0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X2]
    conv => enter [1, 1]; rw [← h41538 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l3 : ∀ X0 sK2 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h41783 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X1))) X2]
  have l8 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X1)) X2]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l10 X0 X1 X2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l6 X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l13 sK0 sK1 sK2]
  have l15 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l6 X0 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← l14 X0 sK1 sK2 X0]
  have l16 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ sK1)))))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l6 X1 (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l15 X0 sK1 sK2]
  have l17 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))))) = (X1 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l16 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← l6 X1 (X0 ◇ sK1) X0]
  have l18 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l11 X0 sK1 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l17 sK1 sK1 sK1 sK2]
  have l19 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X0 ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l18 X0 sK1 sK2]
    conv => enter [1]; rw [← h41783 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l19 x y z]

theorem Equation4512_41628_41783_implies_Equation41849 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41628 : Equation41628 G) (h41783 : Equation41783 G) : Equation41849 G := by
  have l0 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41628 sK1 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK1 sK1]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ sK1) sK1]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK1)) sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK1]
  have l4 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK1 X0]
    conv => enter [1, 1]; rw [← l2 sK1 sK2]
  have l5 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ sK1) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) sK1 X0]
    conv => enter [1, 1]; rw [← l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l9 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h41628 X0 sK1]
    conv => enter [1]; rw [← l5 sK2 sK1 (sK1 ◇ (sK1 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41628 X0 sK1]
  have l10 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [h41628 X0 sK1]
    conv => enter [1]; rw [l8 sK0 sK2 sK1 (sK1 ◇ (sK1 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41628 X0 sK1]
  have l11 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 sK1 (X0 ◇ X1) sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l12 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((X0 ◇ X0) ◇ X1)) = (((sK0 ◇ sK1) ◇ (X0 ◇ X0)) ◇ X1) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [l10 sK0 sK2 sK1 X0]
  have l13 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (X0 ◇ X0) X1]
  have l14 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l13 sK0 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41783 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41783 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41783 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))))]
  have l18 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [h41783 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) X0]
  have l19 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l18 sK2 sK1 X0]
    conv => enter [1]; rw [← l11 sK1 X0 X0 sK2]
  have l20 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l17 sK0 sK2 sK1]
    conv => enter [1]; rw [l14 sK0 sK2 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l21 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h41783 sK1 X0]
    conv => enter [1]; rw [← l19 sK2 sK1 X0]
  have l22 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2]
  have l23 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l16 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l21 sK1 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l25 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l22 sK0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← l24 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2]
  have l26 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l23 sK2 sK1]
    conv => enter [1]; rw [← l21 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK2]
  have l27 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (X0 ◇ sK1) := by
    intro X0 sK2 sK1
    conv => enter [1, 2]; rw [l26 sK2 sK1]
    conv => enter [1]; rw [← h41783 X0 sK1]
  have l28 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l25 sK0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [l27 sK1 sK2 sK1]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l29 x y z]

theorem Equation4512_41538_41733_implies_Equation41799 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41538 : Equation41538 G) (h41733 : Equation41733 G) : Equation41799 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ X0)]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l0 sK2 X0]
  have l2 : ∀ X0 sK2 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [h41538 X0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 sK2]
  have l3 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [h41538 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l4 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [l3 sK2 X0]
    conv => enter [1]; rw [← l1 sK2 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 sK2 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2
    conv => enter [1]; rw [l2 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l6 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l4 sK2 X0]
  have l7 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l6 sK2 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h41538 X0 X1]
    conv => enter [1]; rw [← h41733 X0 (X1 ◇ (X1 ◇ X1))]
  have l9 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1, 2, 2]; rw [l5 X0 sK2]
    conv => enter [1]; rw [← h41733 X0 (sK2 ◇ (sK2 ◇ sK2))]
  have l10 : ∀ X0 X1 sK2 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X1)) := by
    intro X0 X1 sK2
    conv => enter [1, 1]; rw [l5 X0 sK2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) X1]
  have l11 : ∀ X0 X1 sK2 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l10 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ (sK2 ◇ sK2)) X1]
  have l12 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l11 X0 X1 sK2]
  have l13 : ∀ sK2 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1, 1]; rw [l7 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) (X0 ◇ (X0 ◇ X0)) X1]
  have l14 : ∀ sK2 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l13 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l15 : ∀ sK2 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l14 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l16 : ∀ X0 X1 X2 sK2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 X2 sK2
    conv => enter [1, 2]; rw [← l8 X1 X2]
    conv => enter [1, 2]; rw [l9 X1 sK2]
  have l17 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1, 1]; rw [← l9 X0 sK2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l18 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l17 X0 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l19 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l18 X0 sK2 X1]
  have l20 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l19 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (sK2 ◇ sK2)) X1]
  have l21 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h41733 X0 X1]
    conv => enter [1]; rw [l20 X0 X1 sK2]
  have l22 : ∀ sK2 X0 X1 : G, (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X0))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l8 ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← l21 ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) X0 sK2]
  have l23 : ∀ sK2 X0 X1 : G, (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X0)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l22 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) X0 (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X0))]
  have l24 : ∀ sK2 X0 X1 : G, (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X0))))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l23 sK2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) X0 (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X0)]
  have l25 : ∀ sK2 X0 X1 : G, (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X0)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l24 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l21 X0 (X0 ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X0)) sK2]
  have l26 : ∀ sK2 X0 X1 : G, (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0))))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l25 sK2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) X0 X0]
  have l27 : ∀ sK2 X0 X1 : G, (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l26 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l12 X0 (X0 ◇ X0) sK2]
  have l28 : ∀ sK2 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l15 sK2 X0 X0]
    conv => enter [1]; rw [← l27 sK2 X0 X1]
  have l29 : ∀ sK2 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l28 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) X0 (X1 ◇ (X1 ◇ X1))]
  have l30 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [l29 sK2 X0 sK2]
  have l31 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l21 X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) sK2]
    conv => enter [1, 2]; rw [← l30 sK2 sK1]
  have l32 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X0 ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l31 X0 sK1 sK2]
    conv => enter [1]; rw [← l21 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l32 x y z]

theorem Equation4512_41538_41733_implies_Equation41849 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41538 : Equation41538 G) (h41733 : Equation41733 G) : Equation41849 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h41538 X0 X1]
    conv => enter [1]; rw [← h41733 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h41733 X0 X2]
    conv => enter [1]; rw [← l4 X0 X1 X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_41557_41733_implies_Equation41849 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41557 : Equation41557 G) (h41733 : Equation41733 G) : Equation41849 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X0))) X2]
    conv => enter [1, 1]; rw [← h41557 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X0)) X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [h41557 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l6 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 sK1]
    conv => enter [1]; rw [l5 sK2 sK1]
  have l7 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l6 sK2 sK1]
  have l8 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l7 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) sK1]
  have l9 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l8 sK2 sK1]
  have l10 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK1)) sK1]
  have l11 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l10 sK2 sK1]
  have l12 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l11 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK1]
  have l13 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h41557 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l14 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 sK1]
    conv => enter [1]; rw [l13 sK2 sK1 sK0]
  have l15 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))))))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [h41557 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))))))]
  have l16 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l15 sK0 sK2 sK1]
  have l17 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l12 sK0 sK2 sK1]
    conv => enter [1]; rw [l16 sK0 sK2 sK1]
  have l18 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l14 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l19 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l18 sK2 sK1 sK0]
  have l20 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l19 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l21 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1]; rw [l20 sK2 sK1 sK0]
  have l22 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1)) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l21 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l23 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK1]
    conv => enter [1]; rw [l22 sK0 sK2 sK1]
  have l24 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))))))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))))) (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))))]
    conv => enter [1, 2, 2, 2]; rw [← l17 sK0 sK2 sK1]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))))]
    conv => enter [1, 2, 2, 2]; rw [← l23 sK0 sK2 sK1]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41733 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
  have l27 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41733 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l24 sK0 sK2 sK1]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [← l27 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l28 x y z]

theorem Equation4512_41557_41783_implies_Equation41849 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41557 : Equation41557 G) (h41783 : Equation41783 G) : Equation41849 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X0))) X2]
    conv => enter [1, 1]; rw [← h41557 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X0)) X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41557 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK1]
    conv => enter [1, 2, 2, 2]; rw [← h41557 sK1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h41557 sK1 sK2]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l8 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l5 sK2 sK1]
    conv => enter [1]; rw [← h41783 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK1]
  have l9 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l8 sK2 sK1]
  have l10 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK1]
  have l11 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ sK1) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l10 sK0 sK2 sK1]
  have l12 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) sK1 X0]
  have l13 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h41557 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l14 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 sK1]
    conv => enter [1]; rw [l13 sK2 sK1 sK0]
  have l15 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l14 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l15 sK2 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41783 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l18 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41783 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))))]
  have l19 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
    conv => enter [1]; rw [l12 sK0 sK2 sK1 ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))))]
  have l20 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l19 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [l7 sK1 sK2 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l21 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← h41557 sK1 sK2]
  have l22 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l16 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l23 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1]; rw [l22 sK2 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [h41557 sK1 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [← l23 sK2 sK1 sK0]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1))]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK2 sK1 ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1)]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l30 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1 sK2]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK2 sK1]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← l21 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l32 x y z]

theorem Equation4512_41849_41931_implies_Equation42223 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41849 : Equation41849 G) (h41931 : Equation41931 G) : Equation42223 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h41931 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1))) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41931 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← h41849 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2) sK0]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41849 X0 X1 X2]
    conv => enter [1]; rw [l4 X0 X2 (X2 ◇ (X2 ◇ X1))]
    conv => enter [1, 2, 2, 2]; rw [← h41849 X0 X1 X2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41931 sK1 sK2]
    conv => enter [1]; rw [l5 sK2 (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41931 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h41849 X0 (sK1 ◇ sK2) sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [l8 sK1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_41769_41849_implies_Equation41799 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41769 : Equation41769 G) (h41849 : Equation41849 G) : Equation41799 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ X0) = (sK2 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h41769 sK2 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 sK2]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [l0 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41849 X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) sK2]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK2 sK1]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41849 X0 sK1 sK2]
    conv => enter [1]; rw [← l2 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_41621_41849_42223_implies_Equation42197 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41621 : Equation41621 G) (h41849 : Equation41849 G) (h42223 : Equation42223 G) : Equation42197 G := by
  have l0 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41621 sK1 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 sK1]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41621 sK0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK2 sK0]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41621 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l3 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41621 sK2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l4 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41621 (sK0 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
  have l5 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h41621 (sK1 ◇ (sK0 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41621 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l7 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l5 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l8 : ∀ sK2 sK1 : G, ((sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41621 (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) sK2]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK1 sK2]
  have l9 : ∀ sK2 sK1 : G, ((sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l8 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 ((sK1 ◇ sK2) ◇ sK1) (sK1 ◇ sK1)]
  have l10 : ∀ sK2 sK1 : G, ((sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1))) = (((sK1 ◇ sK2) ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [← h42223 ((sK1 ◇ sK2) ◇ sK1) (sK1 ◇ sK1) sK2]
  have l11 : ∀ sK2 sK1 : G, ((sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK1 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l11 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 ((sK1 ◇ sK2) ◇ sK1) (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1))]
  have l13 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) sK1 (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1))]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l13 sK1 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 ((sK1 ◇ sK2) ◇ sK1)]
  have l15 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41849 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l14 sK1 sK2]
  have l16 : ∀ sK2 sK0 : G, ((sK2 ◇ ((sK0 ◇ sK2) ◇ sK0)) ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ ((sK0 ◇ sK2) ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41621 (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0)) sK2]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 sK2]
  have l17 : ∀ sK2 sK0 : G, ((sK2 ◇ ((sK0 ◇ sK2) ◇ sK0)) ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (((sK0 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l16 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 ((sK0 ◇ sK2) ◇ sK0) (sK0 ◇ sK0)]
  have l18 : ∀ sK2 sK0 : G, ((sK2 ◇ ((sK0 ◇ sK2) ◇ sK0)) ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))) = (((sK0 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l17 sK2 sK0]
    conv => enter [1]; rw [← h42223 ((sK0 ◇ sK2) ◇ sK0) (sK0 ◇ sK0) sK2]
  have l19 : ∀ sK2 sK0 : G, ((sK2 ◇ ((sK0 ◇ sK2) ◇ sK0)) ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l18 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (((sK0 ◇ sK2) ◇ sK0) ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l19 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK2 ((sK0 ◇ sK2) ◇ sK0) (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))]
  have l21 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l20 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) sK0 (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))]
  have l22 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK2 ((sK0 ◇ sK2) ◇ sK0)]
  have l23 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41849 sK2 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l22 sK0 sK2]
  have l24 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK2 ◇ sK1) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l15 sK2 sK1]
  have l25 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK2 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l24 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
  have l26 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l25 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l27 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l26 sK2 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 X0]
  have l28 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41849 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1]; rw [← l27 sK2 sK1 X0]
  have l29 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l28 sK1 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l30 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l28 sK1 sK2 ((sK0 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) X0]
  have l31 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l2 sK2 sK1]
    conv => enter [1]; rw [← l28 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))]
  have l32 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2 ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l4 sK0 sK2 sK1]
  have l33 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l23 sK2 sK0]
  have l34 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK2 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l33 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 sK0 X0]
  have l35 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l34 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l36 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l35 sK2 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
  have l37 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (sK2 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h41849 (sK0 ◇ sK2) X0 sK0]
    conv => enter [1]; rw [← l36 sK2 sK0 X0]
  have l38 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l37 sK0 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l39 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK2 ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l40 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l37 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ X0)]
  have l41 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [l40 sK1 sK0 sK2 X0]
  have l42 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [l37 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2))]
  have l43 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l42 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l44 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [l37 sK0 sK2 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l45 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l44 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l46 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)))) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1]; rw [h41849 X1 ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l47 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41849 X0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 sK1 sK2]
  have l48 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41849 X1 (X0 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 2, 2]; rw [← h41621 X0 X2]
  have l49 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h41621 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h41849 (X0 ◇ (X0 ◇ X1)) X1 X0]
  have l50 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ X0))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h41849 sK1 X0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ (sK2 ◇ X0))]
  have l51 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ X0))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l50 sK1 X0 sK2]
    conv => enter [1]; rw [l29 sK1 sK2 (sK2 ◇ X0)]
  have l52 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l49 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X1]
  have l53 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l47 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l54 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0))) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l46 X1 sK1 sK0 sK2 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
  have l55 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (sK2 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l51 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l29 sK1 sK2 X0]
  have l56 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l52 X0 X1]
    conv => enter [1]; rw [← h42223 (X0 ◇ X1) X1 X0]
  have l57 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l53 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK0 sK2]
  have l58 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l56 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 X1]
  have l59 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l57 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2))]
  have l60 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l58 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ (X0 ◇ X1))]
  have l61 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l60 X0 X1]
    conv => enter [1]; rw [l48 X0 (X0 ◇ X1) X0]
  have l62 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l61 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l63 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h42223 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l62 X0 X1]
  have l64 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [l43 sK1 sK0 sK2]
  have l65 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l43 sK1 sK0 sK2]
  have l66 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l65 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
  have l67 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [l45 sK1 sK0 sK2]
  have l68 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41849 sK2 (sK1 ◇ (sK0 ◇ sK2)) sK0]
    conv => enter [1]; rw [← l37 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l69 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41621 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) sK0]
    conv => enter [1, 2, 2]; rw [← h41849 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l70 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41621 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41849 X0 (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l71 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (X0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l70 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l72 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l69 sK0 sK1 sK2]
    conv => enter [1]; rw [← l54 sK0 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2))]
  have l73 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l71 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l54 X0 sK1 sK0 sK2 (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l74 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l72 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2))]
  have l75 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h41621 (sK1 ◇ (sK0 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l73 sK0 sK1 sK2 sK1]
  have l76 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l75 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))]
  have l77 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l76 sK1 sK0 sK2]
    conv => enter [1]; rw [l48 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) sK0]
  have l78 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l77 sK1 sK0 sK2]
    conv => enter [1]; rw [← l54 sK0 sK1 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l79 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l78 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l80 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l79 sK1 sK0 sK2]
    conv => enter [1]; rw [l43 sK1 sK0 sK2]
  have l81 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [← l80 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) X0]
  have l82 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
    conv => enter [1]; rw [l81 sK1 sK2 sK0 X0]
  have l83 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
    conv => enter [1, 2]; rw [← l68 sK2 sK1 sK0]
  have l84 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l83 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK0 ◇ sK2))]
  have l85 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
    conv => enter [1, 2]; rw [l84 sK1 sK0 sK2]
  have l86 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41849 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [l84 sK1 sK0 sK2]
  have l87 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41621 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [l84 sK1 sK0 sK2]
  have l88 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l87 sK0 sK1 sK2]
    conv => enter [1]; rw [l66 sK1 sK0 sK2 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l89 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l86 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l66 sK1 sK0 sK2 ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l90 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l80 sK0 sK1 sK2]
    conv => enter [1]; rw [l85 sK0 sK1 sK2]
  have l91 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l88 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l82 sK1 sK2 sK0 ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l92 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l91 sK0 sK1 sK2]
    conv => enter [1]; rw [← l89 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l93 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l92 sK0 sK1 sK2]
    conv => enter [1]; rw [l74 sK0 sK1 sK2]
  have l94 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l41 sK1 sK0 sK2 ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← l3 sK2 sK0]
  have l95 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h41621 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2, 2]; rw [← l41 sK1 sK0 sK2 (sK1 ◇ sK2)]
  have l96 : ∀ X1 sK0 X0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ X0)) = (X1 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)))) := by
    intro X1 sK0 X0 sK1 sK2
    conv => enter [1]; rw [h41849 X1 (sK0 ◇ X0) (sK1 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [← l41 sK1 sK0 sK2 X0]
  have l97 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l95 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ sK2)]
  have l98 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l94 sK1 sK0 sK2]
    conv => enter [1]; rw [l29 sK1 sK2 sK2]
  have l99 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l97 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK1 ◇ sK2)]
  have l100 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l98 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l28 sK1 sK2 sK2]
  have l101 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l100 sK1 sK0 sK2]
    conv => enter [1]; rw [← l63 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
  have l102 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l101 sK2 sK1 sK0]
    conv => enter [1]; rw [l39 sK0 sK2 sK1 (sK0 ◇ sK2)]
  have l103 : ∀ sK1 sK2 X0 sK0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l99 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (sK1 ◇ sK2) X0]
  have l104 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l103 sK1 sK2 X0 sK0]
  have l105 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l41 sK1 sK0 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
    conv => enter [1, 2]; rw [← l64 sK0 sK1 sK2]
  have l106 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l105 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l93 sK1 sK2 sK0]
  have l107 : ∀ sK1 sK2 sK0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h41621 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l67 sK0 sK1 sK2]
  have l108 : ∀ sK1 sK2 sK0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l107 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l48 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))]
  have l109 : ∀ sK1 sK2 sK0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l108 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l110 : ∀ sK1 sK2 sK0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l109 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l111 : ∀ sK1 sK2 sK0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l110 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l104 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) sK0]
  have l112 : ∀ sK1 sK2 sK0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l111 sK1 sK2 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK1 sK0 sK2]
  have l113 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l96 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2)) sK1 sK2]
    conv => enter [1]; rw [← l112 sK1 sK2 sK0]
  have l114 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l113 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))]
  have l115 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l114 sK0 sK1 sK2]
    conv => enter [1]; rw [l48 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (sK1 ◇ sK2)]
  have l116 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l115 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l59 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l117 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l116 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l93 sK1 sK2 sK0]
  have l118 : ∀ sK1 sK2 sK0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h41621 ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l90 sK1 sK2 sK0]
  have l119 : ∀ sK1 sK2 sK0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l118 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2)) ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l120 : ∀ sK1 sK2 sK0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l119 sK1 sK2 sK0]
    conv => enter [1, 2, 2, 2]; rw [l106 sK1 sK0 sK2]
  have l121 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h41849 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l120 sK1 sK2 sK0]
  have l122 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l121 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2)) ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l123 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l122 sK0 sK1 sK2]
    conv => enter [1]; rw [l48 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ sK2)]
  have l124 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l123 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l32 sK1 sK2 sK0]
  have l125 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l124 sK0 sK1 sK2]
    conv => enter [1]; rw [l29 sK1 sK2 ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))]
  have l126 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (sK2 ◇ (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l125 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l30 sK1 sK2 sK0 (sK0 ◇ sK2)]
  have l127 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41849 sK0 (sK1 ◇ (sK0 ◇ sK2)) sK0]
    conv => enter [1]; rw [l126 sK0 sK1 sK2]
  have l128 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l127 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))]
  have l129 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l128 sK0 sK1 sK2]
    conv => enter [1]; rw [l38 sK0 sK2 ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))]
  have l130 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l129 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l39 sK0 sK2 sK1 (sK0 ◇ sK2)]
  have l131 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l130 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l102 sK2 sK1 sK0]
  have l132 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l131 sK0 sK1 sK2]
    conv => enter [1]; rw [← h41849 X0 (sK1 ◇ sK2) sK2]
  have l133 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l117 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l132 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l134 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l133 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l31 sK2 sK1]
  have l135 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l134 sK0 sK1 sK2]
    conv => enter [1]; rw [l29 sK1 sK2 (sK2 ◇ sK2)]
  have l136 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l135 sK0 sK1 sK2]
    conv => enter [1]; rw [← l48 sK2 sK2 (sK1 ◇ sK2)]
  have l137 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l55 sK1 sK2 sK2]
    conv => enter [1]; rw [← l136 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l137 x y z]

theorem Equation4512_41548_41799_41849_implies_Equation41833 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41548 : Equation41548 G) (h41799 : Equation41799 G) (h41849 : Equation41849 G) : Equation41833 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l2 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [h41548 sK2 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 sK2]
  have l3 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ sK2)]
  have l4 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l3 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l5 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l4 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l6 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1, 2]; rw [l5 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l6 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l9 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK2)) ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l8 sK1 sK2]
  have l10 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l11 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41799 X0 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l12 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h41799 sK2 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK2 ◇ sK2)) (X0 ◇ (X0 ◇ X0))]
  have l13 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l11 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l8 sK1 sK2]
  have l14 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l12 sK2 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l6 sK2]
  have l15 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l14 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l16 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l15 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l17 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l13 sK2 sK1 sK2]
  have l18 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41548 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l10 sK2 sK1]
  have l19 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l18 sK2 sK1]
    conv => enter [1, 2, 2]; rw [l17 sK2 sK1]
  have l20 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l19 sK2 sK1]
    conv => enter [1, 2]; rw [l0 sK2 sK1]
  have l21 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l20 sK2 sK1]
    conv => enter [1]; rw [← l16 sK2 sK1 sK1]
  have l22 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l12 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [l21 sK2 sK1]
  have l23 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41849 X0 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l22 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l23 x y z]

theorem Equation4512_41538_41628_implies_Equation41592 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41538 : Equation41538 G) (h41628 : Equation41628 G) : Equation41592 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
    conv => enter [1, 2]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41538 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41538 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41538 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41538 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ X0))]
  have l20 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h41538 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l21 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0 X0]
    conv => enter [1]; rw [← l7 sK1 sK0 (X0 ◇ (X0 ◇ X0))]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0]
  have l24 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l21 sK1 sK0 X0]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK1 sK0 (sK0 ◇ sK1)]
  have l26 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l27 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [l24 sK1 sK0 X0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))]
  have l29 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l31 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41628 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41628 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)))]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l34 sK0 sK1 X0]
    conv => enter [1]; rw [← l9 sK0 sK1 ((sK0 ◇ sK1) ◇ (X0 ◇ X0))]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK0]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l35 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l13 sK1 sK0 (X0 ◇ X0)]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X0))]
  have l40 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l31 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l31 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l42 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l41 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) X0]
  have l44 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l43 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1, 2]; rw [l15 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l47 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 (sK0 ◇ sK1)]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l54 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l40 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l55 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l54 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l56 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l55 sK0 X0]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
  have l58 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41538 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [← l44 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [l57 sK0 sK1]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41628 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l58 sK1 sK0]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1 sK1]
    conv => enter [1]; rw [← l60 sK1 sK0]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [l61 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [l63 sK0 sK1]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [l64 sK0 sK1]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2, 2]; rw [← l65 sK0 sK1]
  have l67 : ∀ sK0 X0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
  have l68 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l67 sK0 X0 sK1]
  have l69 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l66 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) X0]
  have l70 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l69 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l71 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l70 sK1 sK0 X0]
    conv => enter [1]; rw [← l68 sK0 (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) sK1]
  have l72 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l71 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l73 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l72 sK1 sK0 X0]
    conv => enter [1]; rw [← l56 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l74 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l42 sK0 X0]
    conv => enter [1]; rw [← l73 sK1 sK0 X0]
  have l75 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l27 sK1 sK0 X0]
    conv => enter [1]; rw [← l74 sK0 (X0 ◇ (X0 ◇ X0)) sK1]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK0]
    conv => enter [1]; rw [← l75 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l76 x y]

theorem Equation4512_5099_implies_Equation4695 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5099 : Equation5099 G) : Equation4695 G := by
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
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h5099 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l7 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l5 sK0]
  intro x
  conv => enter [1]; rw [l9 x]

theorem Equation4512_4798_implies_Equation4695 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4798 : Equation4798 G) : Equation4695 G := by
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
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l7 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4798 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l8 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0]
  have l11 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l6 sK0]
  intro x
  conv => enter [1]; rw [l11 x]

theorem Equation4512_4949_implies_Equation4798 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4949 : Equation4949 G) : Equation4798 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l5 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l8 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l4 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l10 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l12 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l6 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [l8 sK1]
  have l14 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l15 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [l12 sK1]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l10 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1 X0]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l11 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) X0]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1]; rw [l17 sK1 X0]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l14 sK1]
  have l20 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l21 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l15 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l22 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1]; rw [l21 sK1 X0]
  have l23 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [l10 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  have l24 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l11 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
  have l25 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l15 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [l25 sK1]
  have l27 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [l24 sK1]
  have l28 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l23 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) sK1 X0]
  have l29 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1]; rw [l28 sK1 X0]
  have l30 : ∀ sK1 X0 : G, (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l26 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l31 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1]; rw [l30 sK1 X0]
  have l32 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4949 X0 sK1]
  have l33 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h4949 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l34 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h4949 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l35 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h4949 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))))]
  have l36 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [h4949 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l37 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [l36 sK1]
    conv => enter [1]; rw [← l22 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l38 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l35 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l3 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l39 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l34 sK1]
    conv => enter [1]; rw [← l16 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l40 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l33 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l41 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [l1 sK1 sK1]
    conv => enter [1]; rw [l32 sK1 X0]
  have l42 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [l37 sK1]
    conv => enter [1, 2]; rw [← l31 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l43 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l38 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l18 sK1 (sK1 ◇ sK1)]
  have l44 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l39 sK1]
    conv => enter [1]; rw [← l29 sK1 (sK1 ◇ sK1)]
  have l45 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l40 sK1]
    conv => enter [1]; rw [← l9 sK1 (sK1 ◇ sK1)]
  have l46 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [l4 sK1]
    conv => enter [1]; rw [l41 sK1 X0]
  have l47 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l42 sK1]
    conv => enter [1]; rw [← l2 sK1 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l48 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l43 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l27 sK1]
  have l49 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l44 sK1]
    conv => enter [1, 2]; rw [← l29 sK1 sK1]
  have l50 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l45 sK1]
    conv => enter [1]; rw [← l16 sK1 sK1]
  have l51 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l47 sK1]
    conv => enter [1, 2]; rw [← l31 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l52 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l48 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l53 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l49 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)]
  have l54 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l51 sK1]
    conv => enter [1]; rw [← l31 sK1 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l55 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [l53 sK1]
    conv => enter [1, 2]; rw [← l23 sK1]
  have l56 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))))) := by
    intro sK1
    conv => enter [1]; rw [l54 sK1]
    conv => enter [1, 2, 2]; rw [← l26 sK1]
  have l57 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l55 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l58 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l56 sK1]
    conv => enter [1]; rw [← l52 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ sK1) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) sK1]
    conv => enter [1, 2]; rw [← l50 sK1]
  have l60 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l57 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l61 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← l46 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l62 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [l61 sK1]
    conv => enter [1]; rw [← h4949 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l63 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [← l20 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l62 sK1 X0]
  have l64 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [l60 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l63 sK1 X0]
  have l65 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [l6 sK1]
    conv => enter [1]; rw [l64 sK1 X0]
  have l66 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ sK1)) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [l58 sK1]
    conv => enter [1]; rw [l65 sK1 X0]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l66 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
    conv => enter [1, 2]; rw [l59 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l66 sK1 sK0]
    conv => enter [1]; rw [← l67 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l68 x y]

end Semigroup5
