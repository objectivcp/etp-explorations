import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53808_53810_53816_53818_53870_implies_Equation53811 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53810 : Equation53810 G) (h53816 : Equation53816 G) (h53818 : Equation53818 G) (h53870 : Equation53870 G) : Equation53811 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))]
    conv => enter [1, 2]; rw [← h53808 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h53816 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53808 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l3 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l9 sK0 X0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53810 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53816 X2 X0]
    conv => enter [1, 2]; rw [h53816 X0 X1]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53816 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l10 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53816 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h53816 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l14 X0 X1 X2]
  have l18 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [l12 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l13 X1 sK0]
  have l19 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l17 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [l13 X2 sK0]
  have l20 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [← l18 X2 X0 X1 sK0]
    conv => enter [1]; rw [l13 X2 sK0]
  have l21 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1, 2]; rw [h53818 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l19 X0 X1 X2 sK0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l21 X0 X1 X0 sK0]
    conv => enter [1]; rw [l20 X0 X1 X0 sK0]
  have l23 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l22 X0 sK0 X1]
    conv => enter [1, 2]; rw [l13 X1 sK0]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 (sK0 ◇ (sK1 ◇ sK2)) sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l25 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [← l11 sK2 sK0]
    conv => enter [1]; rw [h53818 sK2 X0 sK1]
  have l26 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l23 sK2 sK0 sK2]
    conv => enter [1]; rw [l25 sK2 sK0 X0 sK1]
  have l27 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l26 sK2 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l28 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l27 sK1 sK2 sK0]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l28 sK1 sK2 sK0]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [← l30 sK0 sK1 sK2]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53870 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l33 x y z]

theorem Equation4512_53818_53822_53835_53870_implies_Equation53838 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53818 : Equation53818 G) (h53822 : Equation53822 G) (h53835 : Equation53835 G) (h53870 : Equation53870 G) : Equation53838 G := by
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
  have l7 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h53818 (sK0 ◇ sK0) X0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK0 sK0]
  have l8 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h53818 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53818 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ sK0))]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53818 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53818 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53822 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53870 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l15 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l16 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0 sK2]
  have l17 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53818 sK0 X0 sK2]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h53818 (sK0 ◇ sK0) X0 sK0]
  have l19 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l22 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l15 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l23 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l16 sK0 X0 sK2]
  have l24 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X0 sK2]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l26 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53818 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l19 sK0 X0 X1]
  have l27 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53818 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l20 sK0 X0 X1]
  have l28 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l21 sK0 X0 X1]
  have l29 : ∀ X0 X3 X1 X2 : G, (X0 ◇ ((X0 ◇ X0) ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [l22 X0 X3 X1 X2]
  have l30 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l23 sK0 X0 sK2]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l25 sK0 X0]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l26 sK0 sK0 sK0]
  have l33 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l29 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X3]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l30 sK0 sK0 sK0]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [l34 sK0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l32 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53818 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l38 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53818 (X0 ◇ (sK0 ◇ sK0)) X1 sK0]
    conv => enter [1, 2, 2]; rw [← h53818 sK0 X0 sK0]
  have l39 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l38 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l40 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l31 sK0 X0]
    conv => enter [1]; rw [← l39 X0 sK0 X0]
  have l41 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l40 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l42 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l41 X0 sK0]
    conv => enter [1]; rw [l33 X0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l43 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53835 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l42 X0 sK0]
  have l44 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l43 sK0 X0]
    conv => enter [1, 2]; rw [← l35 sK0]
  have l45 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l44 sK0 X0]
  have l46 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l45 sK0 X0]
  have l47 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [l46 sK0 X0]
  have l48 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l47 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l49 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  have l50 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l49 sK2 sK0 sK1]
  have l51 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l48 sK0 sK2]
    conv => enter [1]; rw [l50 sK2 sK0 sK1]
  have l52 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l51 sK0 sK2 sK1]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l52 sK1 sK2 sK0]
  have l54 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53870 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) (sK1 ◇ (sK2 ◇ sK0))]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [← l54 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l55 x y z]

theorem Equation4512_53808_53818_54172_implies_Equation53820 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53818 : Equation53818 G) (h54172 : Equation54172 G) : Equation53820 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54172 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h53818 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ ((X0 ◇ X0) ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l6 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X3]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53808 X0 X3]
    conv => enter [1]; rw [← l7 X0 X1 X2 X3]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2 (X1 ◇ X2)]
    conv => enter [1]; rw [← l2 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_53818_53850_54057_implies_Equation53828 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53818 : Equation53818 G) (h53850 : Equation53850 G) (h54057 : Equation54057 G) : Equation53828 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53818 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53818 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53850 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54057 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53818 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53818 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l10 sK0 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l16 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h53850 (sK0 ◇ sK0) X0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK0 sK0]
  have l17 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0 X0 sK2]
  have l18 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0 X0 sK2]
  have l19 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1]; rw [l18 sK0 X0 sK2]
  have l20 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l19 sK0 X0 sK2]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54057 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 sK0]
  have l22 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l20 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← l21 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l22 x y z]

theorem Equation4512_53850_54057_implies_Equation53846 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53850 : Equation53850 G) (h54057 : Equation54057 G) : Equation53846 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [h54057 X1 X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53850 X2 X0 X1]
    conv => enter [1]; rw [h53850 X2 X3 X2]
    conv => enter [1, 2]; rw [h53850 X2 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2 X0]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53850 X2 X1 X0]
    conv => enter [1]; rw [l6 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_53817_54014_implies_Equation53814 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53817 : Equation53817 G) (h54014 : Equation54014 G) : Equation53814 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54014 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h53817 X3 X0 X0]
    conv => enter [1, 2]; rw [h53817 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X0 X1 X2]
    conv => enter [1]; rw [← l4 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation53817_54014_implies_Equation53819 (G : Type*) [Magma G] (h53817 : Equation53817 G) (h54014 : Equation54014 G) : Equation53819 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53817 X2 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h54014 X0 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation53832_54057_implies_Equation54118 (G : Type*) [Magma G] (h53832 : Equation53832 G) (h54057 : Equation54057 G) : Equation54118 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53832 X0 X1]
    conv => enter [1]; rw [← h54057 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [h53832 x z]

theorem Equation53810_53813_53816_54014_implies_Equation54018 (G : Type*) [Magma G] (h53810 : Equation53810 G) (h53813 : Equation53813 G) (h53816 : Equation53816 G) (h54014 : Equation54014 G) : Equation54018 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53816 X0 sK0]
    conv => enter [1, 2]; rw [h53810 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53810 sK0 sK1]
    conv => enter [1]; rw [h53813 sK0 sK0]
    conv => enter [1, 2]; rw [h53810 sK0 sK1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53810 X0 X1]
    conv => enter [1]; rw [← h54014 X0 X1]
  have l3 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l0 X0 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l4 x z y]

theorem Equation4512_53808_53822_implies_Equation53836 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53822 : Equation53822 G) : Equation53836 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l3 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l2 sK1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l0 sK1 X0]
    conv => enter [1]; rw [← h53808 (sK1 ◇ sK1) X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h53808 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53808 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53808 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [← l6 sK1 X0]
  have l12 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 sK1]
  have l13 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l15 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l12 sK1]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l15 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l20 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1 X0]
    conv => enter [1]; rw [← l11 sK1 X0]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [← l20 sK1 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [h53822 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l18 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l21 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l23 x y]
  conv => enter [1]; rw [l13 y]

@[equational_result]
theorem Equation42197_implies_Equation41849 (G : Type*) [Magma G] (h42197 : Equation42197 G) : Equation41849 G := by
  have l0 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ (X0 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 X0 sK1
    conv => enter [1, 2, 2, 2]; rw [h42197 sK2 sK1 sK2]
    conv => enter [1]; rw [← h42197 X0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h42197 X0 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42197_implies_Equation41897 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42197 : Equation42197 G) : Equation41897 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h42197 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [h42197 X0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h42197 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation42197_implies_Equation42223 (G : Type*) [Magma G] (h42197 : Equation42197 G) : Equation42223 G := by
  have l0 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [h42197 X0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [← h42197 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) sK0]
  have l1 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h42197 X0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h42197 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2, 2]; rw [← l1 X0 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h42197 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_42197_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42197 : Equation42197 G) : Equation41621 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42197 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation42197_implies_Equation41557 (G : Type*) [Magma G] (h42197 : Equation42197 G) : Equation41557 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1, 2, 2, 2]; rw [h42197 sK1 sK0 sK1]
    conv => enter [1]; rw [← h42197 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h42197 X0 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 X0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x x y]

theorem Equation4512_42197_implies_Equation4362 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42197 : Equation42197 G) : Equation4362 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X2 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42197 X2 (X0 ◇ (X2 ◇ X1)) X2]
    conv => enter [1, 2, 2]; rw [← h42197 X0 X1 X2]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (sK2 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h42197 sK0 X0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK2 X0]
  have l2 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h42197 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (sK2 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h42197 sK1 X0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ X0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 (sK2 ◇ X0) sK2]
    conv => enter [1, 2]; rw [l0 sK2 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 ((sK1 ◇ sK2) ◇ X0) sK1 sK2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l2 sK0 X0 sK1 sK2]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ X0)) = (sK2 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l3 sK1 X0 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [l7 sK1 sK2 X0]
  have l10 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l3 sK1 (sK0 ◇ sK2) sK2]
    conv => enter [1, 2, 2]; rw [l9 sK1 sK2 (sK0 ◇ sK2)]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [l9 sK1 sK2 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK1 ◇ sK2)]
  have l13 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l9 sK1 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2, 2]; rw [← l14 sK2 sK1 sK0]
  have l16 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l10 sK1 sK0 sK2]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation4512_41833_implies_Equation41799 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41833 : Equation41833 G) : Equation41799 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ X0)]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l0 sK2 X0]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h41833 sK2 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l3 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l2 sK2 sK2]
    conv => enter [1]; rw [← l1 sK2 (sK2 ◇ sK2)]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l3 sK2]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41833 X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) sK2]
    conv => enter [1, 2, 2]; rw [l4 sK1 sK2]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41833 X0 sK1 sK2]
    conv => enter [1]; rw [← l5 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_41833_implies_Equation41849 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41833 : Equation41833 G) : Equation41849 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h41833 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41833 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK2)]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h41833 X0 (X1 ◇ X1) X1]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ (X1 ◇ X1))]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1 X0 X1]
  have l5 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (sK2 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [l4 sK2 sK1 X0]
  have l6 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [← l5 sK2 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) sK2 X0]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l6 sK2 sK1 sK2]
  have l8 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l7 X0 sK1 sK2]
    conv => enter [1]; rw [l4 X0 (sK2 ◇ (sK2 ◇ sK1)) sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_41833_implies_Equation41735 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41833 : Equation41833 G) : Equation41735 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
    conv => enter [1, 1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41833 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 sK1]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41833 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41833 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l6 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK0]
  have l13 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l8 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y x]

theorem Equation4512_41833_implies_Equation41548 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41833 : Equation41833 G) : Equation41548 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41833 X0 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK0 (sK1 ◇ sK1)]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l3 X0 sK0 sK1]
    conv => enter [1]; rw [← h41833 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  intro x y
  conv => enter [1]; rw [l4 x x y]

theorem Equation4512_41833_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41833 : Equation41833 G) : Equation41557 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41833 X0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h41833 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41833 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h41833 sK1 X0 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41833 X0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l5 sK1 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l7 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l9 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41833 X0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41833 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l10 sK0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK0 sK1]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK1]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l17 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [l12 sK0 sK1]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l20 : ∀ X0 X1 X2 sK0 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1, 1]; rw [h41833 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) X2]
  have l21 : ∀ X0 X1 X2 sK0 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l20 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l22 : ∀ X0 X1 X2 sK0 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l21 X0 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l23 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l22 X0 X1 X2 sK0]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41833 X0 X1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l11 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) sK0]
  have l25 : ∀ X0 sK0 X1 : G, (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) = ((X0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [← l11 X0 sK0]
  have l26 : ∀ X0 sK0 X1 : G, (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l25 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l24 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (X1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0))]
  have l28 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l26 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X1]
  have l29 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l27 X0 X1 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l30 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l29 X0 X1 sK0]
    conv => enter [1]; rw [← l28 X0 sK0 (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)))]
  have l31 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l30 X0 X1 sK0]
    conv => enter [1]; rw [← l23 X0 X1 ((sK0 ◇ sK0) ◇ sK0) sK0]
  have l32 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l31 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l33 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41833 X0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l15 sK1 sK0 sK1]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 sK1]
    conv => enter [1]; rw [← l15 sK1 sK0 (sK0 ◇ sK0)]
  have l35 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l33 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l36 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l35 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l15 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l38 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l37 sK1 sK0]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l38 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0 (sK1 ◇ sK0)]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l34 sK1 sK0]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [l39 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 (sK1 ◇ (sK1 ◇ sK0)) sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l43 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l36 (sK0 ◇ sK0) sK1 sK0]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0]
    conv => enter [1, 2]; rw [l19 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l42 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0 (sK1 ◇ sK0)]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l48 sK1 sK0]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK1 sK0]
    conv => enter [1]; rw [l49 sK1 sK0]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l45 sK1 sK0]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l41 sK0 sK1]
  have l53 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l50 sK1 sK0]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [← l53 sK1 sK0]
  have l55 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l54 sK1 sK0]
  have l56 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l55 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK0) X0]
  have l57 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l3 X1 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h41833 X0 (sK0 ◇ sK0) sK0]
  have l58 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l57 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l59 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l52 sK0 sK1]
  have l60 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l59 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l56 sK1 sK0 sK0]
  have l61 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l60 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l58 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK0) sK0]
  have l62 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l61 X0 sK0 sK1]
    conv => enter [1]; rw [← l32 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
  intro x y
  conv => enter [1]; rw [l62 x x y]

theorem Equation4512_41833_implies_Equation4358 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41833 : Equation41833 G) : Equation4358 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h41833 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h41833 sK1 X0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41833 X0 (sK1 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l1 sK1 (sK2 ◇ sK2) sK2]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l3 X0 sK1 sK2]
    conv => enter [1]; rw [← l0 X0 sK2 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_41999_implies_Equation41883 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41999 : Equation41999 G) : Equation41883 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41999 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_41999_implies_Equation41833 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41999 : Equation41999 G) : Equation41833 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41999 (sK1 ◇ (sK2 ◇ sK2)) X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l0 sK1 sK2 sK1]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h41999 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h41999 sK1 X0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l2 sK2 sK1 X0]
  have l4 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l3 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X1))) sK2]
    conv => enter [1]; rw [← h41999 X1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l5 : ∀ X1 sK2 sK1 : G, (X1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X1 ◇ sK1) := by
    intro X1 sK2 sK1
    conv => enter [1]; rw [← l4 sK1 X1 X1 sK2]
    conv => enter [1]; rw [← h41999 X1 sK1 X1]
  intro x y z
  conv => enter [1]; rw [← l5 x z y]

theorem Equation4512_41999_implies_Equation42197 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41999 : Equation41999 G) : Equation42197 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41999 (X1 ◇ X0) X2 X1]
    conv => enter [1, 2]; rw [← h41999 X0 X1 X1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41999 X1 X2 X0]
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X1)) X0 X2]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X2 X0]
    conv => enter [1]; rw [← h4512 (X0 ◇ (X0 ◇ X1)) X0 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ X2)]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l3 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X2)]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_41999_implies_Equation43 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41999 : Equation41999 G) : Equation43 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41999 (X1 ◇ (X1 ◇ X0)) X2 X1]
    conv => enter [1, 2, 2]; rw [← h41999 X0 X1 X1]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ (X2 ◇ X0))) X3]
    conv => enter [1, 1]; rw [← h41999 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41999 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ (X3 ◇ X0)))]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ X0))]
    conv => enter [1]; rw [← h41999 X0 sK0 sK1]
  have l4 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 sK1 X1]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41999 X0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l4 sK0 sK1 X0 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h41999 X0 X2 X0]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l8 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l9 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l7 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ (X2 ◇ X0)) X3]
  have l10 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l8 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l11 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l9 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X2 ◇ X0) X3]
  have l12 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l11 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X0 X3]
  have l13 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X3)) = ((X0 ◇ X3) ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l12 X0 X1 X3 X0]
    conv => enter [1]; rw [← h41999 (X0 ◇ X3) X1 X0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ sK0) sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41999 (sK0 ◇ sK1) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l15 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← l17 sK1 sK0 X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l10 (sK0 ◇ sK1) (sK1 ◇ sK0) (sK0 ◇ sK1)]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [l6 (sK1 ◇ sK0) (sK0 ◇ sK1) (sK1 ◇ sK0)]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l20 sK0 sK1 (sK1 ◇ sK0)]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← h41999 (sK1 ◇ sK0) X0 (sK0 ◇ sK1)]
  have l24 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l23 sK0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h41999 X1 (sK1 ◇ sK0) X0]
  have l25 : ∀ X1 sK0 sK1 : G, (X1 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [h41999 X1 (sK0 ◇ sK1) X1]
    conv => enter [1]; rw [l24 sK0 sK1 X1 X1]
  have l26 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41999 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [l25 sK1 sK1 sK0]
  have l27 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← l13 X0 X2 X1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← h41999 sK1 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l10 (sK0 ◇ sK1) sK1 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h41999 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l33 x y]

theorem Equation4512_41999_implies_Equation41585 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41999 : Equation41999 G) : Equation41585 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41999 (sK0 ◇ X0) X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41999 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l10 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h41999 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l11 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l0 sK0 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 sK0 X1]
  have l12 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 (sK1 ◇ sK1) X1]
  have l13 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1]
  have l14 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l13 sK1 sK0 sK1 X0]
    conv => enter [1]; rw [← h41999 X0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l12 sK0 sK1 sK0 X0]
    conv => enter [1]; rw [← h41999 X0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l11 sK0 sK0 X0]
    conv => enter [1, 2]; rw [← h41999 X0 (sK0 ◇ sK0) sK0]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1, 2, 2]; rw [l4 sK1 (sK1 ◇ sK1)]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41999 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l19 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41999 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41999 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l22 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l17 sK1 X0]
    conv => enter [1, 2]; rw [l4 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l21 sK0 X0 X1]
  have l24 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l22 sK1 X0]
    conv => enter [1]; rw [← l10 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) X0 sK1]
  have l25 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l24 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [← l18 sK0 sK1 (sK0 ◇ sK0)]
  have l27 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41999 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [l26 sK0 sK1]
  have l28 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41999 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l27 sK1 sK0 X0]
  have l29 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41999 X0 X1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l28 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) sK1]
  have l30 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l28 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X1))) sK1]
    conv => enter [1]; rw [← h41999 X1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l31 : ∀ X1 sK1 sK0 : G, (X1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK1 sK0
    conv => enter [1]; rw [← l30 sK0 X1 X1 sK1]
    conv => enter [1]; rw [← h41999 X1 (sK0 ◇ sK0) X1]
  have l32 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l29 X0 X1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l28 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) sK1]
  have l33 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l32 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) X1]
  have l34 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l33 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1]
  have l35 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l34 X0 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l28 sK0 (X0 ◇ X1) X0]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK1 sK0]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l19 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 (sK1 ◇ sK1) (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [l38 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l36 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← l41 sK0 sK1]
  have l43 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l43 sK1 sK0]
    conv => enter [1]; rw [l6 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l43 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1))]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l45 sK1 sK0]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1, 2]; rw [← l28 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK1]
    conv => enter [1]; rw [← l46 sK0 sK1]
  have l49 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [l14 sK1 sK0 sK0]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l31 sK0 sK1 sK0]
    conv => enter [1]; rw [← l51 sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 (sK1 ◇ sK1)]
  have l54 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41999 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l50 sK1 sK0]
  have l55 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l54 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l56 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l55 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [l53 sK1 sK0]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK0]
    conv => enter [1]; rw [← l58 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [l56 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l60 x y]

theorem Equation4512_41999_implies_Equation41592 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41999 : Equation41999 G) : Equation41592 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)]
    conv => enter [1, 2]; rw [l7 sK0 sK1 X0]
  have l18 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41999 ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41999 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l20 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41999 ((sK0 ◇ sK1) ◇ X0) X1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 sK1 X0]
  have l21 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41999 ((sK0 ◇ sK1) ◇ X0) X1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [← l12 sK0 sK1 X0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41999 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l23 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41999 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l24 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41999 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ (X3 ◇ X0)))]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))]
    conv => enter [1]; rw [← h41999 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l26 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l12 sK0 sK1 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 (sK0 ◇ sK1) X1]
  have l27 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l5 sK0 sK1 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 (sK0 ◇ sK1) X1]
  have l28 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 (sK1 ◇ (sK0 ◇ sK1)) X1]
  have l29 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41999 X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l28 sK0 sK1 X0 X0]
  have l30 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41999 X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l27 sK0 sK1 X0 X0]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l26 sK0 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h41999 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) sK0]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK1) ◇ X0))) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [l25 sK0 sK1 X0]
  have l33 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l24 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h41999 X0 X2 X0]
  have l34 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l23 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 X0]
  have l35 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l21 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l17 sK0 sK1 X0]
  have l36 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l20 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l38 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41999 (sK1 ◇ (sK0 ◇ sK1)) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l39 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h41999 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l40 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41999 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l41 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l18 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)]
  have l42 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← l16 sK1 sK0 X0]
    conv => enter [1]; rw [l32 sK0 sK1 X0]
  have l43 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l35 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← l17 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)]
  have l44 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l36 sK0 sK1 X0 X1]
  have l45 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l46 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l41 sK1 sK0 X0 X1]
  have l47 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)]
    conv => enter [1]; rw [l42 sK0 sK1 X0]
  have l48 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l43 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l34 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) X1 sK0 sK1]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0 X0]
    conv => enter [1]; rw [← l22 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0 sK0]
  have l50 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l48 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) X1]
  have l51 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l49 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l52 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l50 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0 X1]
  have l53 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l52 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l47 sK0 sK1 (X0 ◇ X1)]
  have l54 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l53 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l55 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l54 sK0 sK1 X0 X1]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l38 sK1 sK0 sK0]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l57 sK0 sK1]
  have l59 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41999 sK0 X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [← l58 sK0 sK1]
  have l60 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l59 sK0 X0 sK1]
    conv => enter [1]; rw [← l44 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
  have l61 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l60 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l62 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l61 sK0 X0 sK1]
    conv => enter [1]; rw [l55 sK0 sK1 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)]
  have l63 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l62 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0 (sK0 ◇ sK1)]
  have l64 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l63 sK0 X0 sK1]
    conv => enter [1, 2]; rw [l31 sK0 sK1 X0]
  have l65 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l64 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l39 sK1 sK1 sK0]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l39 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1]; rw [← l68 sK0 sK1]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [l69 sK0 sK1]
  have l72 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1, 2]; rw [l31 sK0 sK1 (sK0 ◇ sK0)]
  have l73 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l73 sK0 sK1]
  have l75 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h41999 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l71 sK0 sK1]
  have l76 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l75 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l77 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l76 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l33 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l78 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l77 sK1 X0 sK0]
    conv => enter [1]; rw [← l46 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l79 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l16 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l74 sK0 sK1]
  have l80 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l81 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l80 sK0 X0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l82 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l79 sK1 sK0]
    conv => enter [1]; rw [l33 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) sK0 (sK0 ◇ sK0)]
  have l83 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l81 sK0 X0 sK1]
  have l84 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l78 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l82 sK1 sK0]
  have l85 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [← l83 sK0 (sK0 ◇ sK0) sK1]
  have l86 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK0]
    conv => enter [1]; rw [← l85 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l86 x y]

theorem Equation4512_41999_implies_Equation4276 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41999 : Equation41999 G) : Equation4276 G := by
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
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h41999 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l3 sK1 X0]
  have l5 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h41999 X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l6 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 (sK1 ◇ sK1) X1]
  have l7 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41999 X0 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l6 sK1 X0 X0]
  have l8 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l5 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 X0]
  have l9 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l4 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41999 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41999 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l9 X0 X1 sK1]
    conv => enter [1]; rw [← l8 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) X1 sK1]
  have l13 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l12 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) X0 X1]
  have l14 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l14 sK1]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l17 sK1 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l7 (sK0 ◇ sK0) sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h41999 (sK1 ◇ (sK1 ◇ sK1)) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l20 sK0 sK1]
  have l23 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41999 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l22 sK1 X0 sK0]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [l23 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l26 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l27 x y]

theorem Equation4512_41883_41933_implies_Equation41897 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41883 : Equation41883 G) (h41933 : Equation41933 G) : Equation41897 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l6 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l6 sK1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1 X0]
    conv => enter [1, 1]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h41883 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h41883 sK1 (sK0 ◇ sK1)]
  have l15 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41883 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 sK1]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 sK1]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 sK1]
  have l19 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l18 sK1 X0]
    conv => enter [1]; rw [← h41883 X0 (sK1 ◇ sK1)]
  have l20 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l17 sK1 X0]
    conv => enter [1]; rw [← h41883 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l16 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h41883 X0 (sK1 ◇ sK1)]
  have l22 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [← l8 sK1 (sK1 ◇ sK1)]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 (sK1 ◇ sK1)]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l13 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ sK1)]
  have l25 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 sK1]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK1]
    conv => enter [1]; rw [← l24 sK1 sK0]
  have l28 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l25 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 sK1]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [l20 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l21 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l29 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l31 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41883 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2, 2]; rw [← l31 sK1]
  have l36 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l31 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l37 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l35 sK1 X0]
    conv => enter [1, 2]; rw [← l36 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l38 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l37 sK1 X0]
    conv => enter [1, 2]; rw [← l31 sK1]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1))]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← l38 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 sK0 sK1]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [l30 sK0 sK1]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l38 sK1 sK0]
    conv => enter [1]; rw [← l43 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l19 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l33 sK0 sK1]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l46 sK1 sK0]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l47 sK1 sK0]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK0 ◇ sK1)]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [l38 sK1 (sK0 ◇ sK1)]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [l41 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41933 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l51 sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l55 x y]

theorem Equation4512_41883_41933_implies_Equation41735 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41883 : Equation41883 G) (h41933 : Equation41933 G) : Equation41735 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
    conv => enter [1, 1]; rw [l5 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l7 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41883 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 sK0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41883 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 sK1]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 (sK1 ◇ sK0)]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41883 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l15 sK0 sK1 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 (sK0 ◇ (sK1 ◇ sK0))]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l26 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l25 sK0 sK1 X0]
    conv => enter [1]; rw [← h41883 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l27 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l24 sK0 sK1 X0]
    conv => enter [1]; rw [← h41883 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 2]; rw [l15 sK0 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l29 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l22 sK0 sK1 X0]
    conv => enter [1]; rw [← h41883 X0 (sK0 ◇ (sK1 ◇ sK0))]
  have l30 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l21 sK0 sK1 X0]
    conv => enter [1]; rw [← h41883 X0 (sK0 ◇ sK1)]
  have l31 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l19 sK1 sK0 X0]
    conv => enter [1]; rw [← h41883 X0 (sK1 ◇ sK0)]
  have l32 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l18 sK0 sK1 X0]
    conv => enter [1]; rw [← h41883 X0 (sK0 ◇ (sK1 ◇ sK0))]
  have l33 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l17 X0 X1 X2]
    conv => enter [1, 2]; rw [← h41883 X0 X2]
  have l34 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l15 sK0 sK1 (sK1 ◇ sK0)]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l7 sK0 sK1]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← h41933 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l36 sK1 sK0]
  have l38 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1) X0]
  have l39 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l38 sK1 sK0 X0]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1) X0]
  have l40 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l39 sK1 sK0 X0]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l26 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l16 sK0 sK1]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l26 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l26 sK0 (sK1 ◇ sK0) sK1]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l11 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l47 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [l44 sK0 sK1]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l47 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l49 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l50 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1]; rw [l49 sK0 sK1 X0]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l29 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l52 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK0) X0]
  have l53 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l52 sK1 sK0 X0]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [l30 sK0 (sK1 ◇ sK0) sK1]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [l54 sK0 sK1]
  have l56 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
  have l57 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l56 sK0 sK1 X0]
    conv => enter [1]; rw [l33 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
  have l58 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l53 sK1 sK0 X0]
    conv => enter [1]; rw [← l57 sK0 sK1 X0]
  have l59 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l58 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1, 2]; rw [l33 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 (sK0 ◇ sK0)]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0))]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0 (sK0 ◇ sK0)]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1, 2]; rw [l33 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK0 sK0]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0)]
  have l67 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l50 sK0 sK1 sK0]
  have l68 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l32 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [← l67 sK0 sK1]
  have l69 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l68 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l69 sK1 sK0]
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK1]
  have l71 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l69 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l72 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l71 sK1 sK0 X0]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l73 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [l45 sK0 sK1]
  have l74 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l72 sK1 sK0 X0]
  have l75 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l73 sK0 sK1]
  have l76 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1]; rw [l75 sK0 sK1]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l76 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l78 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l76 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l79 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1]; rw [l78 sK1 sK0 X0]
  have l80 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [l77 sK0 sK1]
  have l81 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l82 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1]; rw [l81 sK0 sK1 X0]
  have l83 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l84 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l85 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l84 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l86 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h41933 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X1]
    conv => enter [1, 2, 2, 2]; rw [← h41883 X0 X1]
  have l87 : ∀ X0 sK0 sK1 : G, ((X0 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41933 (X0 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2]; rw [l31 sK1 X0 sK0]
  have l88 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41933 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l51 sK1 sK0]
  have l89 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h41933 (sK1 ◇ X0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l1 sK1 sK0 X0]
  have l90 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41933 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l91 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41933 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← l85 sK0 sK1]
  have l92 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h41933 X0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ X0)))]
  have l93 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41933 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l2 sK1 sK0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l94 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l93 X0 sK1 sK0]
    conv => enter [1, 2]; rw [l15 sK0 sK1 ((sK1 ◇ sK0) ◇ X0)]
  have l95 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l92 sK0 X0 sK1]
    conv => enter [1]; rw [l33 (sK0 ◇ sK1) sK1 (sK1 ◇ (sK1 ◇ X0))]
  have l96 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [l48 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l97 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l90 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l98 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l89 sK1 X0 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l99 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l88 sK1 sK0]
    conv => enter [1]; rw [← l59 sK1 sK0 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l100 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l87 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 sK0 sK1]
  have l101 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [l86 X0 X1]
  have l102 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l94 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l40 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l103 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l95 sK0 X0 sK1]
    conv => enter [1, 2]; rw [l33 (sK0 ◇ sK1) sK1 (sK1 ◇ X0)]
  have l104 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l96 sK0 sK1]
    conv => enter [1]; rw [← l74 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l105 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l97 sK1 sK0]
    conv => enter [1, 2]; rw [l15 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l106 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l98 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l15 sK0 sK1 (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l107 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l99 sK1 sK0]
    conv => enter [1, 2]; rw [l33 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l108 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l101 X0 X1]
  have l109 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l102 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l33 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) X0]
  have l110 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l103 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [l33 (sK0 ◇ sK1) sK1 X0]
  have l111 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l104 sK0 sK1]
    conv => enter [1, 2]; rw [l48 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l112 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l105 sK1 sK0]
    conv => enter [1, 2]; rw [← l40 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l113 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l106 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l40 sK1 sK0 (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l114 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l107 sK1 sK0]
    conv => enter [1, 2]; rw [← l40 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l115 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l108 X0 X1]
  have l116 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l109 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l3 sK1 sK0 X0]
  have l117 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l30 X0 sK0 sK1]
    conv => enter [1]; rw [l110 sK0 X0 sK1]
  have l118 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l111 sK0 sK1]
    conv => enter [1, 2]; rw [← l74 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l119 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l112 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l33 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l120 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l113 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [l33 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l121 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l114 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l33 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l122 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h41933 X1 X0]
    conv => enter [1]; rw [l115 X0 X1]
  have l123 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l118 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l76 sK1 sK0]
  have l124 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l119 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l41 sK0 sK1]
  have l125 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l120 sK1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [l33 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK1) X0]
  have l126 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l121 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l41 sK0 sK1]
  have l127 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l124 sK1 sK0]
    conv => enter [1]; rw [← l117 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK0 sK1]
  have l128 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l125 sK1 X0 sK0]
    conv => enter [1]; rw [← l117 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) sK0 sK1]
  have l129 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l117 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK0 sK1]
    conv => enter [1]; rw [← l126 sK1 sK0]
  have l130 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l128 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 (sK0 ◇ sK1)]
  have l131 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [← l129 sK0 sK1]
  have l132 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l130 sK1 X0 sK0]
  have l133 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l127 sK1 sK0]
    conv => enter [1]; rw [← l131 sK0 sK1]
  have l134 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l127 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK0 ◇ sK1) X0]
  have l135 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l134 sK1 sK0 X0]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK0 ◇ sK1) X0]
  have l136 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l135 sK1 sK0 X0]
  have l137 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41883 (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l133 sK1 sK0]
  have l138 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l137 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l59 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l139 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l138 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [l13 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l140 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l139 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l59 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l141 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l140 sK0 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [l9 sK0 sK1]
  have l142 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l141 sK0 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l42 sK1 sK0]
  have l143 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l142 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l123 sK0 sK1]
  have l144 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41933 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1, 2, 2, 2]; rw [← l143 sK0 sK1 X0]
  have l145 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l144 sK0 sK1 X0]
    conv => enter [1]; rw [← l122 X0 (sK0 ◇ sK1)]
  have l146 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41933 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2, 2, 2]; rw [l145 sK0 sK1 X0]
  have l147 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l146 X0 sK0 sK1]
    conv => enter [1]; rw [← l82 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ sK1)))]
  have l148 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l147 X0 sK0 sK1]
    conv => enter [1]; rw [← l136 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ sK1)))]
  have l149 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l148 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l74 sK1 sK0 (X0 ◇ (sK0 ◇ sK1))]
  have l150 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l149 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l132 sK1 X0 sK0]
  have l151 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l150 X0 sK0 sK1]
    conv => enter [1]; rw [l100 sK1 X0 sK0]
  have l152 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41933 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1, 2, 2, 2]; rw [l151 X0 sK0 sK1]
  have l153 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41933 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← l152 sK0 sK1 X0]
  have l154 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41933 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [← l153 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))]
  have l155 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l154 X0 sK0 sK1]
    conv => enter [1]; rw [← l136 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0))]
  have l156 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l155 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l74 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)]
  have l157 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l156 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l79 sK1 sK0 X0]
  have l158 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l116 X0 sK1 sK0]
    conv => enter [1]; rw [← l157 X0 sK0 sK1]
  have l159 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l158 X0 sK1 sK0]
    conv => enter [1]; rw [l151 X0 sK0 sK1]
  have l160 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41933 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [l159 X0 sK1 sK0]
  have l161 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41933 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← l160 sK1 sK0 X0]
  have l162 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l161 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l163 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l162 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ sK0)]
  have l164 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l163 sK0 sK1]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK0]
  have l165 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l164 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l166 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l165 sK0 sK1]
    conv => enter [1]; rw [← l85 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l166 x y]

theorem Equation4512_41883_41933_implies_Equation43 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41883 : Equation41883 G) (h41933 : Equation41933 G) : Equation43 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41883 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41883 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 sK1]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h41883 X0 (sK0 ◇ sK1)]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h41883 X0 X2]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 X0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ sK1) sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2]; rw [l4 (sK0 ◇ sK1) sK1 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h41883 X0 (sK1 ◇ sK0)]
  have l12 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41883 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41933 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l12 sK1 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation4512_41849_implies_Equation41783 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41849 : Equation41849 G) : Equation41783 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l3 sK1]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41849 X0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK1]
  have l7 : ∀ X1 X0 sK1 : G, (X1 ◇ X0) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h41849 X1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK1 X0]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l6 X0 sK1]
    conv => enter [1, 2]; rw [l5 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l8 X0 sK1]
    conv => enter [1]; rw [← l7 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation41849_implies_Equation41733 (G : Type*) [Magma G] (h41849 : Equation41849 G) : Equation41733 G := by
  intro x y
  conv => enter [1]; rw [h41849 x y x]

@[equational_result]
theorem Equation41849_implies_Equation41557 (G : Type*) [Magma G] (h41849 : Equation41849 G) : Equation41557 G := by
  intro x y
  conv => enter [1]; rw [h41849 x x y]

theorem Equation4512_41790_implies_Equation3316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41790 : Equation41790 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41790 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41790 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l4 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l5 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_41790_implies_Equation54335 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41790 : Equation41790 G) : Equation54335 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ X1))) X3]
    conv => enter [1, 1]; rw [← h41790 X0 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41790 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (sK1 ◇ sK2))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X1)) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ X1) X3]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X0 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1, 2, 2]; rw [l7 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l5 X0 sK1 (sK1 ◇ sK2) X1]
    conv => enter [1, 2, 2]; rw [l8 X1 X0 sK1 sK2]
  have l10 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK1 sK2 X0]
    conv => enter [1]; rw [← l9 X0 sK1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_41790_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41790 : Equation41790 G) : Equation41534 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41790 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_41790_implies_Equation41529 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41790 : Equation41790 G) : Equation41529 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41790 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation41726_implies_Equation41613 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41613 G := by
  intro x y z w
  conv => enter [1]; rw [h41726 x y x z w]

@[equational_result]
theorem Equation41726_implies_Equation41667 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41667 G := by
  intro x y z w
  conv => enter [1]; rw [h41726 x y z x w]

@[equational_result]
theorem Equation41726_implies_Equation41684 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41684 G := by
  intro x y z w
  conv => enter [1]; rw [h41726 x y z y w]

@[equational_result]
theorem Equation41726_implies_Equation41711 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41711 G := by
  intro x y z w
  conv => enter [1]; rw [h41726 x y z w y]

@[equational_result]
theorem Equation41726_implies_Equation41716 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41716 G := by
  intro x y z w
  conv => enter [1]; rw [h41726 x y z w z]

@[equational_result]
theorem Equation41726_implies_Equation41576 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41576 G := by
  intro x y z w
  conv => enter [1]; rw [h41726 x x y z w]

@[equational_result]
theorem Equation41726_implies_Equation41597 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41597 G := by
  intro x y z
  conv => enter [1]; rw [h41726 x y x y z]

@[equational_result]
theorem Equation41726_implies_Equation41605 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41605 G := by
  intro x y z
  conv => enter [1]; rw [h41726 x y x z y]

@[equational_result]
theorem Equation41726_implies_Equation41659 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41659 G := by
  intro x y z
  conv => enter [1]; rw [h41726 x y z x y]

theorem Equation4512_41726_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41726 : Equation41726 G) : Equation315 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 X1 X2 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h41726 sK0 X0 X1 X2 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 sK0]
  have l2 : ∀ X1 X2 X0 X3 X4 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X4 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h41726 (X1 ◇ (X2 ◇ X0)) X3 X4 X1 X1]
    conv => enter [1, 2, 2]; rw [← h41726 X0 X1 X1 X1 X2]
  have l3 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l2 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41726 (sK0 ◇ sK0) sK0 sK0 sK0 sK0]
  have l5 : ∀ X0 X3 X4 : G, (X0 ◇ X0) = (X3 ◇ (X4 ◇ (X0 ◇ X0))) := by
    intro X0 X3 X4
    conv => enter [1]; rw [h41726 X0 X0 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← l3 X3 X4 X0 X0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41726 (sK0 ◇ sK0) X0 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41726 sK0 sK0 sK0 sK0 sK0]
  have l7 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h41726 sK0 (sK1 ◇ sK0) X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l8 : ∀ sK0 X3 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ (sK0 ◇ sK0))) ◇ X3)) := by
    intro sK0 X3 X0 X1 X2
    conv => enter [1, 1]; rw [h41726 sK0 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) X3]
  have l9 : ∀ sK0 X3 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (sK0 ◇ sK0)) ◇ X3))) := by
    intro sK0 X3 X0 X1 X2
    conv => enter [1]; rw [l8 sK0 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (sK0 ◇ sK0)) X3]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41726 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 sK1 sK0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l12 : ∀ sK0 X3 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X3)))) := by
    intro sK0 X3 X0 X1 X2
    conv => enter [1]; rw [l9 sK0 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (sK0 ◇ sK0) X3]
  have l13 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l15 : ∀ sK0 X0 X1 X2 X3 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 X2 X3 sK1
    conv => enter [1]; rw [h41726 sK0 (X0 ◇ X1) X2 X3 sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (sK1 ◇ sK0)))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← h41726 (sK1 ◇ sK0) sK0 sK0 sK0 sK0]
  have l17 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l18 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h41726 X0 (X0 ◇ X0) X0 X0 X0]
    conv => enter [1]; rw [l13 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK1]
    conv => enter [1, 2]; rw [← h41726 X0 (X0 ◇ X0) X0 X0 X0]
  have l19 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ X0) sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0 X0]
  have l20 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l19 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l14 sK0 X0 sK1]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l20 sK0 X0 sK0]
  have l22 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (sK1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l18 (X0 ◇ X1) sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1 X0]
    conv => enter [1]; rw [← h41726 X1 X0 X0 X1 X0]
  have l24 : ∀ sK0 X0 X1 X2 X3 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1]; rw [h41726 (sK0 ◇ X0) X1 X2 X3 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l21 sK0 X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ X0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l24 sK0 X0 sK0 sK0 sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ X0)]
  have l27 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [← l23 sK0 X0]
    conv => enter [1]; rw [← l26 sK0 X0]
  have l28 : ∀ sK0 X0 X1 X2 X3 X4 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) := by
    intro sK0 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l27 X0 sK0]
    conv => enter [1]; rw [h41726 X0 X1 X2 X3 X4]
  have l29 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← l5 X0 X1 X2]
  have l30 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l29 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l31 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l30 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ X0) X3]
  have l32 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l31 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X3]
  have l33 : ∀ sK0 X3 X0 : G, ((sK0 ◇ sK0) ◇ X3) = (X0 ◇ (X0 ◇ X3)) := by
    intro sK0 X3 X0
    conv => enter [1]; rw [l28 sK0 X3 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← l32 X0 X3 sK0 sK0]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l33 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l34 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l35 x y]

@[equational_result]
theorem Equation41726_implies_Equation41550 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41550 G := by
  intro x y z
  conv => enter [1]; rw [h41726 x x y x z]

@[equational_result]
theorem Equation41726_implies_Equation41568 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41568 G := by
  intro x y z
  conv => enter [1]; rw [h41726 x x y z y]

theorem Equation4512_41726_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41726 : Equation41726 G) : Equation41621 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l5 : ∀ sK1 sK0 X0 X1 X2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h41726 (sK1 ◇ sK0) X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l6 : ∀ sK1 sK0 X0 X1 X2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (X2 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h41726 (sK1 ◇ sK0) X0 X1 X2 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [l2 sK1 sK0]
  have l7 : ∀ sK1 sK0 X1 X2 X3 X0 : G, ((sK1 ◇ sK0) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X1 X2 X3 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X1 ◇ (X2 ◇ (X3 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41726 X0 sK0 X1 X2 X3]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41726 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK1 sK1 (sK1 ◇ sK0)]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41726 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK1 sK1 sK0]
  have l10 : ∀ sK1 sK0 X0 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41726 (sK1 ◇ sK0) X0 X1 X2 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l9 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [l10 sK1 sK0 (sK1 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l4 sK1 sK0 (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 sK0]
  have l19 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h41726 sK0 X0 X1 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]
  conv => enter [1]; rw [l18 y x]

theorem Equation4512_41726_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41726 : Equation41726 G) : Equation41547 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK1 sK0 X0 X1 X2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h41726 (sK1 ◇ sK0) X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l6 : ∀ sK1 sK0 X0 X1 X2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h41726 (sK1 ◇ sK0) X0 X1 X2 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41726 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK1 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41726 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK1 sK1 sK0]
  have l9 : ∀ sK1 sK0 X0 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41726 (sK1 ◇ sK0) X0 X1 X2 sK0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l7 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41726 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l9 sK1 sK0 sK0 sK0 sK0]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 X0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l16 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h41726 sK0 X0 X1 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l17 x y]
  conv => enter [1]; rw [l15 y x]

@[equational_result]
theorem Equation41726_implies_Equation41557 (G : Type*) [Magma G] (h41726 : Equation41726 G) : Equation41557 G := by
  intro x y
  conv => enter [1]; rw [h41726 x x y y y]

theorem Equation4512_41726_implies_Equation41628 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41726 : Equation41726 G) : Equation41628 G := by
  have l0 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41726 (sK0 ◇ sK0) X0 X1 X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41726 sK0 sK0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK0 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41726 (sK0 ◇ sK0) X0 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41726 sK0 sK0 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_41726_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41726 : Equation41726 G) : Equation41534 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l1 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41726 sK0 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41726 (sK0 ◇ sK0) sK0 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41726 (sK0 ◇ sK0) X0 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41726 sK0 sK0 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_41726_implies_Equation53938 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41726 : Equation41726 G) : Equation53938 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
  have l4 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l5 : ∀ sK1 X0 X1 X2 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1 X2 sK0
    conv => enter [1]; rw [h41726 sK1 X0 X1 X2 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [l1 sK0 sK1]
  have l6 : ∀ X1 X2 X0 X3 X4 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X4 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h41726 (X1 ◇ (X2 ◇ X0)) X3 X4 X1 X1]
    conv => enter [1, 2, 2]; rw [← h41726 X0 X1 X1 X1 X2]
  have l7 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l6 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41726 (sK1 ◇ sK1) sK1 sK1 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ X0 X3 X4 : G, (X0 ◇ X0) = (X3 ◇ (X4 ◇ (X0 ◇ X0))) := by
    intro X0 X3 X4
    conv => enter [1]; rw [h41726 X0 X0 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← l7 X3 X4 X0 X0 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l11 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h41726 (sK1 ◇ sK1) X0 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← h41726 sK1 sK1 sK1 sK1 sK1]
  have l13 : ∀ sK1 X3 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ (sK1 ◇ sK1))) ◇ X3)) := by
    intro sK1 X3 X0 X1 X2
    conv => enter [1, 1]; rw [h41726 sK1 X0 X1 X2 sK1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) X3]
  have l14 : ∀ sK1 X3 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (sK1 ◇ sK1)) ◇ X3))) := by
    intro sK1 X3 X0 X1 X2
    conv => enter [1]; rw [l13 sK1 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (sK1 ◇ sK1)) X3]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l12 sK1 X0]
  have l16 : ∀ sK1 X3 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((sK1 ◇ sK1) ◇ X3)))) := by
    intro sK1 X3 X0 X1 X2
    conv => enter [1]; rw [l14 sK1 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (sK1 ◇ sK1) X3]
  have l17 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l15 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l18 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l15 sK1 (sK0 ◇ sK1)]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l11 sK2 sK0 sK1]
  have l21 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [← l18 sK2 sK0 sK1]
  have l22 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1 sK1 sK1]
    conv => enter [1, 1]; rw [← l20 sK1 sK1 sK1]
  have l23 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l24 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l17 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l23 sK1 X0 sK1]
  have l25 : ∀ X0 X4 : G, (X0 ◇ X0) = (X4 ◇ (X0 ◇ X0)) := by
    intro X0 X4
    conv => enter [1]; rw [h41726 X0 (X0 ◇ X0) X0 X0 X0]
    conv => enter [1]; rw [l17 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X4]
    conv => enter [1, 2]; rw [← h41726 X0 (X0 ◇ X0) X0 X0 X0]
  have l26 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l25 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l27 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h41726 X1 X1 X0 X1 X0]
    conv => enter [1]; rw [← l26 X0 X1 X1]
  have l28 : ∀ sK1 X0 X1 X2 X3 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 X1 X2 X3
    conv => enter [1]; rw [h41726 (sK1 ◇ X0) X1 X2 X3 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK1 X0]
  have l29 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ X0) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l16 sK1 X0 sK1 sK1 sK1]
    conv => enter [1]; rw [← l28 sK1 X0 sK1 sK1 sK1]
  have l30 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l29 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK1 ◇ X0)]
  have l31 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l30 sK1 X0]
    conv => enter [1]; rw [← l27 X0 sK1]
  have l32 : ∀ sK1 X0 X1 X2 X3 X4 : G, ((sK1 ◇ sK1) ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) := by
    intro sK1 X0 X1 X2 X3 X4
    conv => enter [1]; rw [l31 sK1 X0]
    conv => enter [1]; rw [h41726 X0 X1 X2 X3 X4]
  have l33 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← l9 X0 X1 X2]
  have l34 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l33 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l35 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l34 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ X0) X3]
  have l36 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l35 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X3]
  have l37 : ∀ sK1 X3 X0 : G, ((sK1 ◇ sK1) ◇ X3) = (X0 ◇ (X0 ◇ X3)) := by
    intro sK1 X3 X0
    conv => enter [1]; rw [l32 sK1 X3 sK1 sK1 X0 X0]
    conv => enter [1]; rw [← l36 X0 X3 sK1 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l37 sK1 sK1 sK0]
    conv => enter [1]; rw [← l22 sK1]
  intro x y z
  conv => enter [1]; rw [l38 x y]
  conv => enter [1]; rw [l20 y z x]

theorem Equation4512_41726_implies_Equation53959 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41726 : Equation41726 G) : Equation53959 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X4 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h41726 (X1 ◇ (X2 ◇ X0)) X3 X4 X1 X1]
    conv => enter [1, 2, 2]; rw [← h41726 X0 X1 X1 X1 X2]
  have l1 : ∀ X1 X2 X3 X4 X0 X5 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5)) = ((X0 ◇ X0) ◇ X5) := by
    intro X1 X2 X3 X4 X0 X5
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X0))) X5]
    conv => enter [1, 1]; rw [← h41726 X0 X1 X2 X3 X4]
  have l2 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h41726 X0 (X1 ◇ X2) X3 X4 X5]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X5 ◇ X0)))]
  have l3 : ∀ X1 X2 X3 X4 X0 X5 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5)) = (X0 ◇ (X0 ◇ X5)) := by
    intro X1 X2 X3 X4 X0 X5
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X0 X5]
    conv => enter [1]; rw [← h4512 X0 X0 X5]
  have l4 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l5 : ∀ X0 X5 X1 X2 X3 X4 : G, (X0 ◇ (X0 ◇ X5)) = (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X5))) := by
    intro X0 X5 X1 X2 X3 X4
    conv => enter [1]; rw [← l3 X1 X2 X3 X4 X0 X5]
    conv => enter [1, 2]; rw [← h4512 X2 (X3 ◇ (X4 ◇ X0)) X5]
  have l6 : ∀ X0 X3 X4 : G, (X0 ◇ X0) = (X3 ◇ (X4 ◇ (X0 ◇ X0))) := by
    intro X0 X3 X4
    conv => enter [1]; rw [h41726 X0 X0 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← l4 X3 X4 X0 X0 X0]
  have l7 : ∀ X0 X5 X1 X2 X3 X4 : G, (X0 ◇ (X0 ◇ X5)) = (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X0) ◇ X5)))) := by
    intro X0 X5 X1 X2 X3 X4
    conv => enter [1]; rw [l5 X0 X5 X1 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X3 (X4 ◇ X0) X5]
  have l8 : ∀ X0 X5 X1 X2 X3 X4 : G, (X0 ◇ (X0 ◇ X5)) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X5))))) := by
    intro X0 X5 X1 X2 X3 X4
    conv => enter [1]; rw [l7 X0 X5 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X4 X0 X5]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0 X0]
    conv => enter [1]; rw [← h41726 X1 X0 X0 (X0 ◇ X1) X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5))))) = (X6 ◇ (X7 ◇ (X8 ◇ (X9 ◇ X5)))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8 X9
    conv => enter [1]; rw [← l2 X5 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [h41726 X5 X6 X7 X8 X9]
  intro x y z
  conv => enter [1]; rw [l8 x y x x x x]
  conv => enter [1]; rw [l11 x x x x x y x x x x]
  conv => enter [1]; rw [← h41726 y x x x x]
  conv => enter [1]; rw [← l10 z y]

end Semigroup5
