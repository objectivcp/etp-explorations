import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4284_4512_53808_implies_Equation53810 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53808 : Equation53808 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4284 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation4284_4512_53808_implies_Equation53816 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53808 : Equation53808 G) : Equation53816 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4284 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4284 sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 X0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4284 (sK0 ◇ sK0) X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4284 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (X0 ◇ X0)]
    conv => enter [1]; rw [← l13 sK0 sK1 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l18 sK0 sK1 X0]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53808 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← h53808 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l23 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l20 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l24 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53808 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l26 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [← l23 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l28 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l26 sK1 X0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l3 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l32 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l24 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l33 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l28 sK1 X0]
    conv => enter [1]; rw [← l32 sK1 X0]
  have l34 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l33 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l35 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l36 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l34 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [← l35 sK0 X0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [← l36 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l37 x y]

theorem Equation4284_4512_53822_53825_implies_Equation53850 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53825 : Equation53825 G) : Equation53850 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4284 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l4 X2 X0 X1]
    conv => enter [1, 2]; rw [h4284 X0 X1]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h53825 X0 X2]
    conv => enter [1]; rw [← l0 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [h53822 x y]
  conv => enter [1]; rw [l6 y x z]
  conv => enter [1]; rw [l5 y z x]
  conv => enter [1, 2]; rw [← h4284 z x]

theorem Equation4284_4512_53822_53825_implies_Equation53838 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53825 : Equation53825 G) : Equation53838 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4284 sK0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4284 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) (sK2 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h53825 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l5 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l4 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK2 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l7 sK1 sK2 sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4284_4512_53822_53825_implies_Equation53842 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53825 : Equation53825 G) : Equation53842 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4284 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l4 X2 X0 X1]
    conv => enter [1, 2]; rw [h4284 X0 X1]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h53825 X0 X2]
    conv => enter [1]; rw [← l0 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [h53822 x y]
  conv => enter [1]; rw [l6 y x z]
  conv => enter [1]; rw [l5 y z x]

theorem Equation4284_4512_53813_53816_implies_Equation53817 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53813 : Equation53813 G) (h53816 : Equation53816 G) : Equation53817 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4284 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [← l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← h53813 X0 X1]
    conv => enter [1]; rw [← h53816 X2 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]
  conv => enter [1]; rw [← l4 x y z]

theorem Equation4284_4512_53813_53816_implies_Equation53820 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53813 : Equation53813 G) (h53816 : Equation53816 G) : Equation53820 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4284 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← h53813 X0 X1]
    conv => enter [1]; rw [← h53816 X2 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]
  conv => enter [1]; rw [← l4 x y z]
  conv => enter [1, 2]; rw [h4284 y z]

theorem Equation4284_4512_53808_53810_53813_implies_Equation53811 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53810 : Equation53810 G) (h53813 : Equation53813 G) : Equation53811 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4284 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4284 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4284 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53810 sK0 X0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK2) X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4284 (sK0 ◇ sK0) X0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h4284 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l7 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l15 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [l15 sK0 X0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4284 (sK1 ◇ sK2) X0]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4284 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l17 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ sK2) X0]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2 X0]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l22 sK0 sK1 sK2 X0]
  have l24 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4284 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l21 sK0 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l24 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l25 sK0 sK1 sK2]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53808 X0 sK0]
    conv => enter [1, 2]; rw [h4284 X0 sK0]
  have l29 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l28 X0 sK0]
    conv => enter [1]; rw [l11 X0 sK0]
  have l30 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53808 sK1 sK2]
    conv => enter [1]; rw [h4284 sK1 (sK1 ◇ sK2)]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l30 sK1 sK2]
    conv => enter [1]; rw [l29 sK1 sK0]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
  have l35 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [l35 sK0 X0 sK1 sK2]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l27 sK0 sK1 sK2]
  have l38 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4284 sK2 X0]
  have l39 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4284 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l40 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l38 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ X0)]
  have l41 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (((sK1 ◇ sK2) ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l39 sK1 sK2]
  have l42 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4284 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l39 sK1 sK2]
  have l43 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l31 sK1 sK2 sK0]
    conv => enter [1]; rw [l42 sK1 sK2]
  have l44 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) sK2 X0]
    conv => enter [1]; rw [← l41 sK1 sK2 X0]
  have l45 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK1 ◇ (((sK1 ◇ sK2) ◇ sK2) ◇ X0)) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1, 1]; rw [l43 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK2) ◇ sK2) X0]
  have l46 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ X0))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l45 sK1 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) sK2 X0]
  have l47 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ X0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l44 sK1 sK2 (sK2 ◇ X0)]
    conv => enter [1]; rw [← l46 sK1 sK0 X0 sK2]
  have l48 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ X0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l47 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l49 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← l48 sK1 sK2 X0 sK0]
  have l50 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ X0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l49 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l3 (sK1 ◇ sK2) sK2 X0]
  have l51 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53810 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l40 sK1 sK2 X0]
  have l52 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l51 sK1 sK2 sK1]
    conv => enter [1]; rw [← l50 sK1 sK0 sK2 sK1]
  have l53 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l52 sK1 sK2 sK0]
    conv => enter [1]; rw [l29 (sK1 ◇ sK2) sK0]
  have l54 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53813 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l55 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l54 sK1 sK2]
    conv => enter [1]; rw [l29 sK1 sK0]
  have l56 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l55 sK1 sK2 sK0]
    conv => enter [1]; rw [l53 sK1 sK0 sK2]
  have l57 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l56 sK1 sK2 sK0]
  have l58 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0))]
  have l59 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← l58 sK0 sK1 sK2]
  have l60 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l60 x y z]

theorem Equation4284_4512_53815_implies_Equation53809 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53815 : Equation53815 G) : Equation53809 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h53815 X0 X1]
    conv => enter [1]; rw [l3 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4284_4512_53815_implies_Equation53812 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53815 : Equation53815 G) : Equation53812 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53815 sK0 X0]
    conv => enter [1, 2]; rw [h4284 X0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation4284_4512_53812_implies_Equation53809 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53812 : Equation53812 G) : Equation53809 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h53812 X1 X0]
    conv => enter [1, 2]; rw [← h4284 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4284_4512_53812_implies_Equation53815 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53812 : Equation53812 G) : Equation53815 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4284 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53812 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4284_4512_53809_implies_Equation53812 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53809 : Equation53809 G) : Equation53812 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l3 X2 X0 X1]
    conv => enter [1, 2]; rw [h4284 X0 X1]
  intro x y
  conv => enter [1]; rw [h53809 x y]
  conv => enter [1]; rw [l4 x y x]

theorem Equation4284_4512_53866_53888_implies_Equation53884 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53866 : Equation53866 G) (h53888 : Equation53888 G) : Equation53884 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4284 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h53888 sK0 X0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4284 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 sK1]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4284 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4284 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ X0)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53888 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4284 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
    conv => enter [1]; rw [h4284 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4284 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4284 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l19 X0 sK0 sK1]
  have l21 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4284 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l22 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [h4284 sK0 sK1]
    conv => enter [1]; rw [← h53866 X0 (sK1 ◇ sK1) sK0]
  have l23 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← h4284 X0 sK1]
    conv => enter [1]; rw [h53866 X0 sK1 X0]
    conv => enter [1, 2]; rw [h4284 X0 sK1]
  have l24 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l23 X0 sK1]
    conv => enter [1]; rw [h53866 X0 (sK1 ◇ sK1) sK2]
  have l25 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l23 X0 sK1]
    conv => enter [1]; rw [← l22 X0 sK0 sK1]
  have l26 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l25 X0 sK1 sK0]
    conv => enter [1]; rw [← l20 X0 sK0 sK1]
  have l27 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l26 sK2 sK1 sK0]
    conv => enter [1]; rw [h4284 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l28 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l27 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  have l29 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l28 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 sK1]
  have l30 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l26 sK2 sK1 sK2]
    conv => enter [1]; rw [← l29 sK2 sK1 sK2]
  have l31 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l30 sK2 sK1]
    conv => enter [1]; rw [l21 sK2 sK1]
  have l32 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l31 sK2 sK1]
    conv => enter [1]; rw [l26 (sK2 ◇ (sK1 ◇ sK1)) sK1 sK0]
  have l33 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l32 sK2 sK1 sK0]
    conv => enter [1]; rw [h4284 (sK2 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l34 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l33 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  have l35 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l34 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 sK1]
  have l36 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l32 sK2 sK1 sK2]
    conv => enter [1]; rw [← l35 sK2 sK1 sK2]
  have l37 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1, 2]; rw [l36 sK2 sK1]
    conv => enter [1]; rw [← h4284 X0 (sK2 ◇ (sK1 ◇ sK1))]
  have l38 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l24 X0 sK1 sK2]
    conv => enter [1]; rw [← l37 X0 sK2 sK1]
  have l39 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l26 X0 sK1 sK0]
    conv => enter [1]; rw [l38 X0 sK1 sK2]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l39 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l40 x y z]

theorem Equation4284_4512_53866_53888_54186_implies_Equation54168 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53866 : Equation53866 G) (h53888 : Equation53888 G) (h54186 : Equation54186 G) : Equation54168 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4284 (sK1 ◇ sK2) X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4284 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h54186 sK0 X0 (sK1 ◇ sK2)]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4284 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4284 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2]; rw [h4284 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h4284 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X0)]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4284 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h53888 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0]
  have l12 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54186 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 X0]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4284 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4284 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [h4284 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l19 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h4284 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2]
  have l20 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l19 X0 sK0 sK1 sK2]
  have l21 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h53866 X0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l22 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l20 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 X0 sK0 sK1 sK2]
  have l23 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← h4284 X0 sK2]
    conv => enter [1]; rw [h53866 X0 sK2 sK1]
  have l24 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l23 X0 sK2 sK1]
    conv => enter [1]; rw [← l22 X0 sK0 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l24 sK0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l25 x z y]

theorem Equation4284_54182_implies_Equation53880 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h54182 : Equation54182 G) : Equation53880 G := by
  intro x y z
  conv => enter [1]; rw [h4284 x y]
  conv => enter [1]; rw [h54182 x y z]

theorem Equation4284_53876_implies_Equation54178 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h53876 : Equation53876 G) : Equation54178 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4284 X0 sK1]
    conv => enter [1]; rw [h53876 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4284_54178_implies_Equation53876 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h54178 : Equation54178 G) : Equation53876 G := by
  intro x y z
  conv => enter [1]; rw [h4284 x y]
  conv => enter [1]; rw [h54178 x y z]

theorem Equation4284_53880_implies_Equation54182 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h53880 : Equation53880 G) : Equation54182 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4284 sK0 sK2]
    conv => enter [1]; rw [h53880 sK0 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4284_4512_53850_implies_Equation53838 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53850 : Equation53850 G) : Equation53838 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53850 X2 X0 X1]
    conv => enter [1]; rw [l3 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4284_53850_implies_Equation53842 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h53850 : Equation53850 G) : Equation53842 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h53850 X1 X2 X0]
    conv => enter [1, 2]; rw [h4284 X0 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4284_53817_implies_Equation53820 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h53817 : Equation53817 G) : Equation53820 G := by
  intro x y z
  conv => enter [1]; rw [h53817 x y z]
  conv => enter [1, 2]; rw [h4284 y z]

theorem Equation4284_4512_53817_implies_Equation53811 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53817 : Equation53817 G) : Equation53811 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4284 sK0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ X0) X1]
  have l2 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53817 sK0 X0 X1]
    conv => enter [1]; rw [← l2 sK0 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4284_53842_implies_Equation53850 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h53842 : Equation53842 G) : Equation53850 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h53842 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← h4284 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4284_4512_53811_implies_Equation53817 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53811 : Equation53811 G) : Equation53817 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4284 sK0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53811 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ X0) X1]
  have l5 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4284_4512_53838_implies_Equation53850 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53838 : Equation53838 G) : Equation53850 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1, 2]; rw [h4284 X0 X1]
  intro x y z
  conv => enter [1]; rw [h53838 x y z]
  conv => enter [1]; rw [l4 y z x]
  conv => enter [1, 2]; rw [← h4284 z x]

theorem Equation4284_4512_53820_implies_Equation53817 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53820 : Equation53820 G) : Equation53817 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53820 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4284 X0 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]
  conv => enter [1]; rw [← l3 x y z]

theorem Equation4284_54194_implies_Equation53892 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h54194 : Equation54194 G) : Equation53892 G := by
  intro x y z w
  conv => enter [1]; rw [h4284 x y]
  conv => enter [1]; rw [h54194 x y z w]

theorem Equation4284_53892_implies_Equation54194 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h53892 : Equation53892 G) : Equation54194 G := by
  have l0 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [← h4284 X0 sK2]
    conv => enter [1]; rw [h53892 X0 sK2 X1 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4284_4512_41529_implies_Equation307 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation307 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4284 X0 X1]
    conv => enter [1]; rw [h4284 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X1 ◇ X1)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4284 sK0 X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4284 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4284 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l7 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h4284 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l9 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l9 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l15 sK0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l18 sK0]
    conv => enter [1]; rw [← h4284 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4284 (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l23 : ∀ X0 sK0 X1 : G, ((X0 ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 1]; rw [l10 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
  have l24 : ∀ X0 sK0 X1 : G, ((X0 ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ X1) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l23 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l25 : ∀ X0 sK0 X1 : G, ((X0 ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l24 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l22 sK0 X1]
  have l26 : ∀ X0 sK0 X1 : G, (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [l25 X0 sK0 X1]
  have l27 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l26 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0]
    conv => enter [1]; rw [l19 X0 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [h41529 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) sK0]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [← l27 (sK0 ◇ sK0) sK0 sK0]
  have l32 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41529 sK0]
    conv => enter [1]; rw [← l28 sK0 sK0]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [← l14 sK0 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [← l22 sK0 sK0]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [← l8 sK0]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1]; rw [← l9 sK0]
  have l38 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l39 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [← l37 sK0]
  intro x
  conv => enter [1]; rw [l39 x]

theorem Equation4284_4512_41529_implies_Equation53873 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation53873 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4284 sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ X0)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l4 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4284 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l5 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4284 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 sK1]
    conv => enter [1]; rw [l5 sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l4 sK1]
  have l8 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4284 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l6 sK1]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [l6 sK1]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l11 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1, 2]; rw [← l7 sK1]
  have l12 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l12 sK1]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l13 sK1]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l7 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l15 sK1 X0]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l14 sK1]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l17 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4284 (sK1 ◇ sK1) X0]
  have l20 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h4284 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l21 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l20 sK1]
  have l22 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
  have l23 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l21 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l24 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [h41529 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l25 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41529 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l25 sK1]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK1)]
  have l28 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l26 sK1]
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ sK1)]
  have l29 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1]; rw [← l16 sK1 (sK1 ◇ sK1)]
  have l30 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l29 sK1]
    conv => enter [1, 2]; rw [l10 sK1 sK1]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l30 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)]
  have l32 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l31 sK1]
    conv => enter [1]; rw [l18 sK1 sK1]
  have l33 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l32 sK1]
    conv => enter [1]; rw [← l22 sK1 sK1]
  have l34 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l33 sK1]
    conv => enter [1]; rw [l10 sK1 sK1]
  have l35 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l34 sK1]
    conv => enter [1]; rw [← l16 sK1 sK1]
  have l36 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l35 sK1]
    conv => enter [1, 2]; rw [l6 sK1]
  have l37 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l36 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l38 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l37 sK1]
    conv => enter [1]; rw [l14 sK1]
  have l39 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l38 sK1]
    conv => enter [1]; rw [l23 sK1]
  have l40 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l39 sK1]
  have l41 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l40 sK1]
  have l42 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [l23 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l41 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l42 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← l44 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 sK1]
    conv => enter [1]; rw [← l45 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l46 x y]

theorem Equation4284_4512_41529_implies_Equation53870 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation53870 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4284 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4284 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← l7 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4284 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l13 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4284 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4284 (sK0 ◇ sK1) X0]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ X0)]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l17 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [l18 sK0 sK1]
  have l26 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l25 sK0 sK1 X0]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4284 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (X0 ◇ X0)]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l27 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l30 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l29 sK0 sK1 X0]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l32 sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l31 sK1 sK0]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l36 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ sK1)]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l38 sK0 sK1]
  have l41 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (X0 ◇ X0) X1]
  have l42 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l41 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 sK0 sK1]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l45 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l42 sK0 sK1 X0 X1]
  have l46 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 X0]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l44 sK0 sK1]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [h4284 (sK0 ◇ sK1) X0]
  have l49 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← l48 sK0 sK1 X0]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l51 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1]; rw [l46 sK0 sK1 X0]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l38 sK0 sK1]
    conv => enter [1]; rw [l50 sK0 sK1]
  have l53 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l49 sK0 sK1 X0]
    conv => enter [1]; rw [l51 sK0 sK1 X0]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1 sK1]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l55 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l49 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)]
    conv => enter [1]; rw [h4284 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l49 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l53 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l58 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1]; rw [← l55 sK0 sK1 X0]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l18 sK0 sK1]
    conv => enter [1]; rw [l54 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 sK0 sK1]
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1, 2]; rw [l22 sK0 sK1]
  have l61 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l49 sK0 sK1 X0]
    conv => enter [1]; rw [l58 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l49 sK0 sK1 X0]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1, 2]; rw [← l52 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l59 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41529 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l8 sK0 sK1]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h41529 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l67 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [← l45 sK0 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1 (sK1 ◇ sK1)]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1, 2]; rw [← l21 sK0 sK1 sK1]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1, 2]; rw [← l28 sK0 sK1]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1, 2]; rw [l24 sK0 sK1 sK1]
  have l73 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0 sK1]
    conv => enter [1]; rw [← l62 sK0 sK1]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l35 sK0 sK1]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l73 sK0 sK1]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l76 sK0 sK1]
    conv => enter [1]; rw [← h4284 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l78 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [← l63 sK0 sK1]
  have l79 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l78 sK0 sK1]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l79 sK0 sK1]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [h41529 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l80 sK0 sK1]
  have l82 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [← h4284 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l83 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [← l61 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l84 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l85 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l84 sK0 sK1]
    conv => enter [1, 2]; rw [← h4284 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l86 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l85 sK0 sK1]
    conv => enter [1, 2]; rw [← l63 sK0 sK1]
  have l87 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0 sK1]
    conv => enter [1]; rw [← h4284 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l88 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l87 sK0 sK1]
    conv => enter [1]; rw [← l82 sK0 sK0 sK1]
  have l89 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK0 sK1]
  have l90 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l89 sK0 sK1]
    conv => enter [1]; rw [← l75 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l90 x y]

theorem Equation4284_4512_4695_implies_Equation3 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4284 X0 X1]
    conv => enter [1]; rw [h4284 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ ((X0 ◇ sK0) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [h4284 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ ((X0 ◇ sK0) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l3 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l5 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l4 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 X1 X2]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4284 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4284 (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X0) X1]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l15 sK0 X0 X1]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [h4695 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l19 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4695 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))]
  have l21 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1, 2]; rw [l9 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l23 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [← l16 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l25 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ sK0)]
  have l26 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l27 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← h4284 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ sK0)]
  have l31 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [← h4284 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l33 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [← l32 sK0]
  intro x
  conv => enter [1]; rw [l33 x]

theorem Equation4284_4512_4695_implies_Equation41773 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation41773 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 sK1 X1 : G, (X0 ◇ ((X0 ◇ sK1) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK1) X1]
    conv => enter [1, 1]; rw [h4284 X0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [h4284 sK0 sK1]
  have l3 : ∀ X0 sK1 X1 : G, (X0 ◇ ((X0 ◇ sK1) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l1 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l5 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l3 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4284 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h4284 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ X0)]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4284 sK1 X0]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 sK1 X0]
    conv => enter [1]; rw [l14 sK1 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h4284 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ sK1)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 (sK1 ◇ sK1)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l18 sK0 sK1]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK1 ◇ sK1) X0]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l24 sK0 sK1 X0]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l29 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1, 2]; rw [h4695 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4695 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))]
  have l32 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l29 sK1]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l33 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h4695 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))]
  have l35 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l32 sK1]
    conv => enter [1, 2]; rw [l13 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l36 : ∀ sK1 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l33 sK1]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))]
  have l38 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l35 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l39 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l36 sK1]
    conv => enter [1, 2]; rw [l13 sK1 (sK1 ◇ sK1)]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))]
  have l41 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l38 sK1]
    conv => enter [1]; rw [l7 (sK1 ◇ sK1) sK1 (sK1 ◇ sK1)]
  have l42 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l39 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l44 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l41 sK1]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l45 : ∀ sK1 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l42 sK1]
    conv => enter [1]; rw [← l16 sK1 (sK1 ◇ sK1)]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l47 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l44 sK1]
    conv => enter [1, 2]; rw [l13 sK1 (sK1 ◇ sK1)]
  have l48 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l45 sK1]
    conv => enter [1]; rw [← l15 sK1 (sK1 ◇ sK1)]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1 (sK1 ◇ sK1)]
  have l50 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l47 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1 (sK1 ◇ sK1)]
  have l52 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l50 sK1]
    conv => enter [1]; rw [l7 (sK1 ◇ sK1) sK1 sK1]
  have l53 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l52 sK1]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ sK1)]
  have l54 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l53 sK1]
    conv => enter [1, 2]; rw [l13 sK1 sK1]
  have l55 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l54 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ sK1)]
  have l56 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l55 sK1]
    conv => enter [1]; rw [h4284 (sK1 ◇ sK1) sK1]
  have l57 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l56 sK1]
    conv => enter [1]; rw [l13 sK1 sK1]
  have l58 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l57 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l59 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l58 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l60 : ∀ sK1 : G, sK1 = (sK1 ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l48 sK1]
    conv => enter [1]; rw [← l59 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l60 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2]; rw [← l60 sK1]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1, 2]; rw [← l60 sK1]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [l64 sK0 sK1]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l63 sK0 sK1]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l66 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l67 x y]

theorem Equation4362_54339_implies_Equation54485 (G : Type*) [Magma G] (h4362 : Equation4362 G) (h54339 : Equation54339 G) : Equation54485 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54339 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h4362 sK1 sK2 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [h4362 sK0 sK2 (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4362 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4284_4314_4358_4512_54318_54331_54335_54337_54338_54351_54352_implies_Equation54350 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4314 : Equation4314 G) (h4358 : Equation4358 G) (h4512 : Equation4512 G) (h54318 : Equation54318 G) (h54331 : Equation54331 G) (h54335 : Equation54335 G) (h54337 : Equation54337 G) (h54338 : Equation54338 G) (h54351 : Equation54351 G) (h54352 : Equation54352 G) : Equation54350 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4314 (sK0 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4314 (sK1 ◇ sK2) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54318 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54351 sK0 (sK1 ◇ sK2) sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4358 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4314 (sK0 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4314 (sK2 ◇ (sK1 ◇ sK0)) sK0]
  have l7 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l6 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
  have l8 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
    conv => enter [1]; rw [← h54318 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l8 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l10 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
    conv => enter [1]; rw [← h54351 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
  have l11 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h4358 sK0 sK0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK0 sK2 sK1]
  have l12 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4314 (sK1 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4314 sK2 sK1]
  have l13 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK1 ◇ sK2))]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l13 sK1 sK2]
    conv => enter [1]; rw [← h54318 sK1 sK2 (sK1 ◇ sK2)]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l14 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ sK2)]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [← h54351 sK1 sK2 sK1]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4358 sK1 sK1 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2]
  have l18 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4314 (sK2 ◇ sK2) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4314 (sK1 ◇ sK0) sK2]
  have l19 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l18 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l20 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l19 sK2 sK1 sK0]
    conv => enter [1]; rw [← h54318 sK2 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
  have l21 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l20 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l22 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l21 sK2 sK1 sK0]
    conv => enter [1]; rw [← h54351 sK2 (sK1 ◇ sK0) sK2]
  have l23 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h4358 sK2 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l22 sK2 sK1 sK0]
  have l24 : ∀ X3 X2 X1 X0 : G, (X3 ◇ ((X2 ◇ X1) ◇ X0)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X1 X0
    conv => enter [1]; rw [h4358 X3 (X2 ◇ X1) X0]
    conv => enter [1, 2]; rw [h4358 X0 X2 X1]
  have l25 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l24 X3 X0 X1 X2]
  have l26 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4284 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4358 X0 sK0 sK1]
  have l27 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l26 X0 sK0 sK1]
    conv => enter [1]; rw [l25 X0 (sK0 ◇ sK1) sK0 sK1]
  have l28 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l27 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← h54335 sK1 sK0 sK1]
  have l29 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54352 X0 sK0 sK1]
    conv => enter [1]; rw [← l28 X0 sK1 sK0]
  have l30 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h4358 X0 sK1 sK0]
    conv => enter [1]; rw [l29 X0 sK0 sK1]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4284 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l32 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4358 sK0 (sK1 ◇ sK2) X0]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2 sK0]
  have l34 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h4358 X0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l33 sK0 sK1 sK2]
  have l35 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l34 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4358 X0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l36 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [h4314 (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ X0)]
  have l37 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l11 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l38 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h4284 sK0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK0))]
  have l39 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [h4358 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l40 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l38 sK0 sK2 sK1]
    conv => enter [1]; rw [← l39 sK0 sK2 sK1 sK0]
  have l41 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l36 sK0 sK2 sK1 X0]
  have l42 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l40 sK0 sK2 sK1]
  have l43 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h4358 X0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l40 sK0 sK2 sK1]
  have l44 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l43 X0 sK2 sK1 sK0]
    conv => enter [1]; rw [h4358 X0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0]
  have l45 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l46 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l17 sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ sK0)]
  have l48 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
    conv => enter [1]; rw [← l39 sK0 sK2 sK1 sK1]
  have l49 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54337 (sK0 ◇ sK0) X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← h4314 (sK1 ◇ sK2) sK0]
  have l50 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54337 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l51 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h54337 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ sK0)]
  have l52 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l51 sK0 sK2 sK1 X0]
  have l53 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l10 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
  have l54 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l22 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) sK2]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l56 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
  have l57 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l58 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l11 sK0 sK2 sK1]
    conv => enter [1]; rw [l53 sK0 sK2 sK1]
  have l59 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l23 sK2 sK1 sK0]
    conv => enter [1]; rw [l54 sK2 sK1 sK0]
  have l60 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
  have l61 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [l56 sK1 sK2]
  have l62 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h54318 sK0 X0 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l63 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l30 sK2 sK1 sK0]
    conv => enter [1]; rw [l59 sK2 sK1 sK0]
  have l64 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l62 sK0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [l35 X0 sK1 sK2 sK0]
  have l65 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l64 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h54331 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l66 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l65 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK1 ◇ sK2))]
  have l67 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54318 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l66 sK0 X0 sK1 sK2]
  have l68 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l32 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l67 sK0 X0 sK1 sK2]
  have l69 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l63 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK2]
  have l70 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l69 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2 X0]
  have l71 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4284 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2]
    conv => enter [1, 2]; rw [← l69 sK0 sK2 sK1]
  have l72 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l37 sK0 sK2 sK1]
    conv => enter [1]; rw [← l71 sK0 sK2 sK1]
  have l73 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l72 sK0 sK2 sK1]
    conv => enter [1]; rw [← l70 sK0 sK2 sK1 sK2]
  have l74 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l69 sK0 sK2 sK1]
    conv => enter [1]; rw [← l73 sK0 sK2 sK1]
  have l75 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l61 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK1 X0]
  have l76 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l75 sK1 sK2 X0]
  have l77 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l46 sK1 sK2]
  have l78 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l77 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2 sK1]
  have l79 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l33 sK0 sK1 sK2]
    conv => enter [1]; rw [l78 sK0 sK1 sK2]
  have l80 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l60 sK0 sK1 sK2]
    conv => enter [1]; rw [l79 sK0 sK1 sK2]
  have l81 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1 X0]
    conv => enter [1, 1]; rw [← l48 sK0 sK1 sK2]
  have l82 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l48 sK0 sK1 sK2]
    conv => enter [1]; rw [h4358 X0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1]
  have l83 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4284 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [← l48 sK0 sK1 sK2]
  have l84 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l81 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK0) X0]
  have l85 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l80 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK1 X0]
  have l86 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l85 sK0 sK1 sK2 X0]
  have l87 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [h4358 sK1 sK0 X0]
  have l88 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l76 sK1 sK2 sK0]
    conv => enter [1]; rw [← l87 sK1 sK0 (sK1 ◇ sK2)]
  have l89 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l88 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK2)]
  have l90 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l23 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
  have l91 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l30 sK2 sK1 sK0]
    conv => enter [1]; rw [l90 sK2 sK1 sK0]
  have l92 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l91 sK2 sK1 sK0]
    conv => enter [1]; rw [← h54337 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2 sK1]
  have l93 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l92 sK0 sK2 sK1]
    conv => enter [1]; rw [← l70 sK0 sK2 sK1 sK1]
  have l94 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l93 sK0 sK2 sK1]
    conv => enter [1]; rw [← l48 sK0 sK1 sK2]
  have l95 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l89 sK1 sK2 sK0]
  have l96 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l95 sK0 sK1 sK2]
    conv => enter [1]; rw [← l68 sK0 sK1 sK2 sK1]
  have l97 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l80 sK0 sK1 sK2]
    conv => enter [1]; rw [← l96 sK0 sK1 sK2]
  have l98 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l94 sK0 sK2 sK1]
    conv => enter [1]; rw [l40 sK0 sK2 sK1]
  have l99 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h4358 X0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l94 sK0 sK2 sK1]
  have l100 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4284 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l94 sK0 sK2 sK1]
  have l101 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l100 sK0 sK2 sK1]
    conv => enter [1]; rw [← l83 sK0 sK2 sK1]
  have l102 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l99 X0 sK2 sK1 sK0]
    conv => enter [1]; rw [l82 X0 sK0 sK1 sK2]
  have l103 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l58 sK0 sK2 sK1]
    conv => enter [1]; rw [← l98 sK0 sK1 sK2]
  have l104 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l101 sK0 sK2 sK1]
    conv => enter [1]; rw [l84 sK0 sK2 sK1 sK1]
  have l105 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [← l44 X0 sK2 sK1 sK0]
    conv => enter [1]; rw [l102 X0 sK2 sK1 sK0]
  have l106 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l97 sK0 sK1 sK2]
    conv => enter [1]; rw [← l103 sK0 sK2 sK1]
  have l107 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l104 sK0 sK2 sK1]
    conv => enter [1]; rw [h4358 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK0) sK1]
  have l108 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1, 2]; rw [l74 sK0 sK2 sK1]
    conv => enter [1]; rw [l105 X0 sK0 sK2 sK1]
  have l109 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l74 sK0 sK2 sK1]
    conv => enter [1]; rw [← l106 sK0 sK1 sK2]
  have l110 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l86 sK0 sK1 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l107 sK0 sK2 sK1]
  have l111 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l110 sK0 sK1 sK2]
    conv => enter [1]; rw [l45 sK0 sK2 sK1 (sK2 ◇ (sK1 ◇ sK0))]
  have l112 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l41 sK0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l111 sK0 sK1 sK2]
  have l113 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l112 sK0 sK2 sK1]
    conv => enter [1]; rw [← h54337 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l114 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l113 sK0 sK2 sK1]
    conv => enter [1]; rw [h4358 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l115 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l114 sK0 sK2 sK1]
    conv => enter [1]; rw [← l68 sK0 sK1 sK2 sK1]
  have l116 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l80 sK0 sK1 sK2]
    conv => enter [1]; rw [← l115 sK0 sK2 sK1]
  have l117 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l116 sK0 sK1 sK2]
    conv => enter [1]; rw [← l52 sK0 sK2 sK1 sK0]
  have l118 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l109 sK0 sK2 sK1]
    conv => enter [1]; rw [l117 sK0 sK1 sK2]
  have l119 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54338 X0 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l120 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l119 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [h4358 X0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l121 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54338 X0 (sK1 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
  have l122 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l120 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l109 sK0 sK2 sK1]
  have l123 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l121 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l108 X0 sK0 sK2 sK1]
  have l124 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h4358 X0 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l123 X0 sK1 sK0 sK2]
  have l125 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l124 X0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l122 X0 sK0 sK1 sK2]
  have l126 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l39 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [l125 X0 sK2 sK1 sK0]
  have l127 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l68 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l126 sK0 sK2 sK1 X0]
  have l128 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l118 sK0 sK2 sK1]
    conv => enter [1]; rw [← l127 sK0 sK1 sK2 sK0]
  have l129 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l130 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l129 sK0 sK1 sK2]
    conv => enter [1]; rw [← l128 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l130 x y z]

theorem Equation4284_4369_4512_53862_54199_implies_Equation53899 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) (h53862 : Equation53862 G) (h54199 : Equation54199 G) : Equation53899 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h4284 X2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [h4369 (X1 ◇ X0) X1 X0]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [h54199 X1 X0]
    conv => enter [1]; rw [← l0 X2 X1 X0]
  have l2 : ∀ sK0 X0 sK1 X1 : G, ((sK0 ◇ X0) ◇ (sK1 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [h4369 (sK0 ◇ X0) sK1 X1]
    conv => enter [1, 2]; rw [h4369 sK1 sK0 X0]
  have l3 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← l2 sK0 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK1 ◇ X1)]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ X0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h4369 X0 sK0 sK1]
    conv => enter [1]; rw [h4369 sK0 sK1 (sK0 ◇ X0)]
  have l5 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4369 (sK1 ◇ X0) sK1 sK0]
    conv => enter [1, 2]; rw [h4284 sK1 X0]
  have l6 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l5 sK1 X0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK1 ◇ sK0)]
  have l8 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ X0) ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l3 X0 sK0 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 X0 sK0]
  have l9 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l8 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK1 ◇ sK0)]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4369 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4369 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53862 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l11 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation4291_4314_4358_4362_4512_54351_54395_implies_Equation54398 (G : Type*) [Magma G] (h4291 : Equation4291 G) (h4314 : Equation4314 G) (h4358 : Equation4358 G) (h4362 : Equation4362 G) (h4512 : Equation4512 G) (h54351 : Equation54351 G) (h54395 : Equation54395 G) : Equation54398 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h4362 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4291 sK1 sK2]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h4362 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l0 sK2 sK0 sK1]
  have l2 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [h4358 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  have l3 : ∀ X0 sK2 sK1 : G, ((X0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) = ((X0 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1, 2]; rw [h4362 X0 sK1 sK2]
    conv => enter [1]; rw [h4314 (X0 ◇ sK2) sK1]
  have l4 : ∀ X0 sK2 sK1 : G, ((X0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l3 X0 sK2 sK1]
    conv => enter [1]; rw [← h4512 X0 sK2 (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = ((X0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54351 X0 sK1 sK2]
    conv => enter [1]; rw [← l4 X0 sK2 sK1]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 sK2 (X0 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l6 X0 sK1 sK2]
    conv => enter [1]; rw [← h54395 sK2 X0 (sK1 ◇ sK2)]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4276_4512_53807_implies_Equation53836 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation53836 G := by
  have l0 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l3 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l0 sK0 X0 sK1]
    conv => enter [1]; rw [l1 sK1 X0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK0 sK1 sK1]
  have l5 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53807 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1]; rw [← l6 sK1 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l7 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4276_53832_implies_Equation53840 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53832 : Equation53832 G) : Equation53840 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [h53832 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4276_53810_implies_Equation53840 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53810 : Equation53810 G) : Equation53840 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h4276 sK2 X0]
    conv => enter [1]; rw [h53810 X0 sK2]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4276_4512_53825_implies_Equation53848 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h53825 : Equation53825 G) : Equation53848 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h53825 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4276_4512_53813_implies_Equation53848 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h53813 : Equation53813 G) : Equation53848 G := by
  have l0 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53813 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4276_53815_implies_Equation53823 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53815 : Equation53815 G) : Equation53823 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [h53815 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4276_53850_implies_Equation53824 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53850 : Equation53850 G) : Equation53824 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [h53850 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4276_53817_implies_Equation53824 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53817 : Equation53817 G) : Equation53824 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4276 sK0 X0]
    conv => enter [1]; rw [h53817 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4276_53812_implies_Equation53826 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53812 : Equation53812 G) : Equation53826 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [h53812 sK1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y x]

theorem Equation4276_53809_implies_Equation53833 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53809 : Equation53809 G) : Equation53833 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [h53809 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4276_53846_implies_Equation53827 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53846 : Equation53846 G) : Equation53827 G := by
  have l0 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [h53846 sK2 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

theorem Equation4276_53819_implies_Equation53844 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53819 : Equation53819 G) : Equation53844 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4276 sK0 X0]
    conv => enter [1]; rw [h53819 X0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4276_53814_implies_Equation53827 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53814 : Equation53814 G) : Equation53827 G := by
  have l0 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [h53814 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

theorem Equation4276_53828_implies_Equation53844 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53828 : Equation53828 G) : Equation53844 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [h53828 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4276_53842_implies_Equation53830 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53842 : Equation53842 G) : Equation53830 G := by
  have l0 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [h53842 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

theorem Equation4276_53811_implies_Equation53834 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53811 : Equation53811 G) : Equation53834 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4276 sK0 X0]
    conv => enter [1]; rw [h53811 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4276_53820_implies_Equation53830 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53820 : Equation53820 G) : Equation53830 G := by
  have l0 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4276 sK2 X0]
    conv => enter [1]; rw [h53820 X0 X1 sK2]
  have l1 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y x z]

theorem Equation4276_53838_implies_Equation53834 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53838 : Equation53838 G) : Equation53834 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [h53838 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4276_4512_53815_54164_54201_implies_Equation53830 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h53815 : Equation53815 G) (h54164 : Equation54164 G) (h54201 : Equation54201 G) : Equation53830 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h53815 X0 X1]
    conv => enter [1]; rw [h4276 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54164 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54164 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l7 X0 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54201 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l11 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1]; rw [l11 X0 X1 X2]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l12 X0 X1 X2]
  have l14 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
    conv => enter [1]; rw [l0 X2 (X0 ◇ X1) X3]
  have l15 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l14 X2 X0 X1 X3]
  have l16 : ∀ X3 X2 X1 X0 : G, (X3 ◇ (X3 ◇ X3)) = (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X3 X2 X1 X0
    conv => enter [1]; rw [← l15 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← l13 X1 X0 X2]
  have l17 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l16 X3 X2 X0 X1]
    conv => enter [1, 2]; rw [l8 X0 X1 X2]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [← l13 X1 X0 (X2 ◇ (X0 ◇ X1))]
  have l19 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1]; rw [← l17 X3 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l19 y x z x]

theorem Equation4276_4512_53808_53899_53900_implies_Equation53834 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53899 : Equation53899 G) (h53900 : Equation53900 G) : Equation53834 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4276 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (X1 ◇ X2))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h53899 X2 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h53808 X2 X1]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1, 2]; rw [h4276 X0 sK0]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 X1 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53900 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l6 sK0]
  have l8 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h53900 sK1 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK2)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l7 X0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ X0) ◇ ((sK2 ◇ X0) ◇ sK0)) = (sK0 ◇ ((sK2 ◇ X0) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h53899 (sK2 ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK2 X0]
  have l12 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h53899 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l13 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ X0) ◇ ((sK2 ◇ X0) ◇ sK0)) = (sK0 ◇ (sK2 ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l11 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 ((sK0 ◇ sK2) ◇ X0)]
  have l14 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l12 sK2 sK0]
    conv => enter [1]; rw [h53900 sK2 sK0]
  have l15 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ X0) ◇ ((sK2 ◇ X0) ◇ sK0)) = ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l13 sK2 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (X0 ◇ ((sK0 ◇ sK2) ◇ X0))]
  have l16 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK0)]
  have l17 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ X0) ◇ ((sK2 ◇ X0) ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h53899 X0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l15 sK2 X0 sK0]
  have l18 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK2 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l17 X0 sK0 sK2]
    conv => enter [1]; rw [h53900 (sK2 ◇ X0) sK0]
  have l19 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l18 X0 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 (sK0 ◇ sK0)]
  have l20 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l19 X0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (X0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← l8 sK1 sK0 sK2]
  have l22 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l21 sK1 sK0 sK2]
    conv => enter [1]; rw [l20 (sK1 ◇ (sK0 ◇ sK2)) sK0 sK2]
  have l23 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l16 sK0 sK2]
  have l24 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l23 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK0)]
  have l25 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l8 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l24 sK1 sK0 sK2]
  have l26 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l26 sK1 sK0 sK2]
  have l28 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [← l22 sK1 sK0 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← l28 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l29 x y z]

theorem Equation53813_53848_54201_implies_Equation54243 (G : Type*) [Magma G] (h53813 : Equation53813 G) (h53848 : Equation53848 G) (h54201 : Equation54201 G) : Equation54243 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53848 X0 X2 X1]
    conv => enter [1]; rw [← h54201 X1 X2]
  intro x y z
  conv => enter [1]; rw [← l0 z x y]
  conv => enter [1]; rw [h53813 z x]

theorem Equation53813_53848_53899_implies_Equation53922 (G : Type*) [Magma G] (h53813 : Equation53813 G) (h53848 : Equation53848 G) (h53899 : Equation53899 G) : Equation53922 G := by
  intro x y z
  conv => enter [1]; rw [h53899 x y]
  conv => enter [1]; rw [← h53848 y y x]
  conv => enter [1]; rw [h53813 y z]

theorem Equation4276_53818_implies_Equation53855 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53818 : Equation53818 G) : Equation53855 G := by
  have l0 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h4276 sK1 sK2]
    conv => enter [1]; rw [h53818 sK2 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_53818_53855_54201_implies_Equation53830 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53818 : Equation53818 G) (h53855 : Equation53855 G) (h54201 : Equation54201 G) : Equation53830 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54201 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X2))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53855 X3 X0 X1 X2]
    conv => enter [1]; rw [h54201 X3 X3]
    conv => enter [1, 2]; rw [h53855 X3 X0 X1 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X2 X0]
    conv => enter [1, 2]; rw [← l2 X2 X0 X1 X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1 X0]
    conv => enter [1]; rw [← l3 X1 X2 X0]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h53818 X1 X2 X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_53808_53835_53855_53899_implies_Equation53834 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53835 : Equation53835 G) (h53855 : Equation53855 G) (h53899 : Equation53899 G) : Equation53834 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l2 : ∀ X0 X1 X2 X4 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X4 ◇ (X4 ◇ (X4 ◇ X3))) := by
    intro X0 X1 X2 X4 X3
    conv => enter [1]; rw [← h53855 X3 X0 X1 X2]
    conv => enter [1]; rw [h53835 X3 X4]
  have l3 : ∀ X3 X4 X5 X0 X1 X2 : G, (X3 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5)) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X5) := by
    intro X3 X4 X5 X0 X1 X2
    conv => enter [1]; rw [h4512 X3 (X3 ◇ (X3 ◇ X4)) X5]
    conv => enter [1, 1]; rw [← l2 X0 X1 X2 X3 X4]
  have l4 : ∀ X3 X4 X5 X0 X1 X2 : G, (X3 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5)) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X5)) := by
    intro X3 X4 X5 X0 X1 X2
    conv => enter [1]; rw [l3 X3 X4 X5 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) X5]
  have l5 : ∀ X3 X4 X5 X0 X1 X2 : G, (X3 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X5))) := by
    intro X3 X4 X5 X0 X1 X2
    conv => enter [1]; rw [l4 X3 X4 X5 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X5]
  have l6 : ∀ X3 X4 X5 X0 X1 X2 : G, (X3 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X5)))) := by
    intro X3 X4 X5 X0 X1 X2
    conv => enter [1]; rw [l5 X3 X4 X5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X5]
  have l7 : ∀ X0 X1 X2 X5 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X5)))) = (X3 ◇ (X3 ◇ ((X3 ◇ X4) ◇ X5))) := by
    intro X0 X1 X2 X5 X3 X4
    conv => enter [1]; rw [← l6 X3 X4 X5 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X3 (X3 ◇ X4) X5]
  have l8 : ∀ X3 X4 X5 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X5)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X5)))) := by
    intro X3 X4 X5 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X3 X4 X5]
    conv => enter [1]; rw [← l7 X0 X1 X2 X5 X3 X4]
  have l9 : ∀ X3 X0 X1 X2 X5 : G, (X3 ◇ (X3 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X5)))) := by
    intro X3 X0 X1 X2 X5
    conv => enter [1]; rw [h53808 X3 (X3 ◇ X5)]
    conv => enter [1]; rw [l8 X3 X3 X5 X0 X1 X2]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← l9 X3 X1 X2 X0 (X2 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [← l10 y x z x]

theorem Equation4276_53854_implies_Equation53858 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53854 : Equation53854 G) : Equation53858 G := by
  intro x y z w u
  conv => enter [1]; rw [h4276 x u]
  conv => enter [1]; rw [h53854 u y z w]

theorem Equation4276_53821_implies_Equation53858 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h53821 : Equation53821 G) : Equation53858 G := by
  have l0 : ∀ sK2 X0 X1 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 X0 X1 sK1 sK0
    conv => enter [1]; rw [h4276 sK2 X0]
    conv => enter [1]; rw [h53821 X0 X1 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

theorem Equation4276_4512_41529_implies_Equation41592 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation41592 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4276 X0 sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4276 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
  have l4 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4276 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l11 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4276 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l13 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l11 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
  have l17 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l18 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l17 sK0 X0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 X0]
  have l19 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l18 sK0 X0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [← l21 sK0 sK1]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4276 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l29 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l31 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l32 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l31 sK0 X0 sK1]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l34 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41529 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l41 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41529 X0]
    conv => enter [1, 2, 2]; rw [h4276 X0 sK0]
  have l42 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h41529 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X1]
  have l43 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [h41529 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))]
  have l44 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l43 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
  have l45 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l42 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l47 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41529 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l48 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l44 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l49 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l45 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1]
  have l51 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l47 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
  have l52 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l48 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l53 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l49 X0 X1]
    conv => enter [1]; rw [← l4 sK0 ((X0 ◇ X0) ◇ X1) X0]
  have l54 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l52 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 sK0 X0 X1]
  have l55 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l53 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l56 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l51 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l57 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l56 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l41 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1, 2]; rw [← l36 sK1 sK0]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1, 2]; rw [← l27 sK1 sK0]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l60 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l61 sK0 sK1]
  have l64 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l62 sK0 sK1]
  have l65 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l64 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1))]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l67 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l66 sK1 sK0]
  have l68 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l41 X0 sK0]
    conv => enter [1]; rw [l55 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l41 X0 sK0]
  have l69 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l65 sK1 sK0]
    conv => enter [1]; rw [l55 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1, 2, 2]; rw [l65 sK1 sK0]
  have l70 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l69 sK1 sK0]
    conv => enter [1, 2]; rw [l23 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l70 sK1 sK0]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l71 sK0 sK1]
  have l73 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [l55 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l72 sK0 sK1]
  have l74 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l75 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l74 sK0 sK1 X0]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l23 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [← l73 sK1 sK0]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [l76 sK0 sK1]
  have l78 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l77 sK0 sK1]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l78 sK0 sK1]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2]; rw [← l33 sK1 sK0]
  have l81 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l80 sK0 sK1]
  have l82 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l68 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l81 sK0 sK1]
  have l83 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l82 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l84 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l83 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l85 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l84 sK1 sK0 X0]
  have l86 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l35 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 (sK1 ◇ sK1)]
  have l87 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l86 sK0 sK1]
  have l88 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l87 sK0 sK1]
  have l89 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← l88 sK0 sK1]
  have l90 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l91 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l29 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l92 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l91 sK0 sK1]
    conv => enter [1, 2]; rw [← l75 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l93 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l90 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l92 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l39 sK0 sK1]
  have l95 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l93 sK1 sK0]
  have l96 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l97 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l95 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l98 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l85 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l96 sK0 sK1]
  have l99 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l97 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK0]
  have l100 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l98 sK1 sK0]
    conv => enter [1, 2]; rw [← l29 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l101 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l100 sK1 sK0]
    conv => enter [1, 2]; rw [← l72 sK0 sK1]
  have l102 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l67 sK1 sK0]
    conv => enter [1]; rw [l101 sK1 sK0]
  have l103 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l99 sK1 sK0]
  have l104 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l103 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l105 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l89 sK1 sK0]
    conv => enter [1]; rw [l104 sK0 sK1]
  have l106 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l105 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 X0]
  have l107 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l106 sK1 X0 sK0]
  have l108 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l102 sK1 sK0]
    conv => enter [1]; rw [← l29 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l109 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l102 sK1 sK0]
  have l110 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l107 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l109 sK0 sK1]
  have l111 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1]; rw [← l108 sK1 sK0]
  have l112 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)]
    conv => enter [1, 2]; rw [← l110 sK1 sK0]
  have l113 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l111 sK0 sK1]
    conv => enter [1]; rw [l112 sK1 sK0]
  have l114 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l113 sK0 sK1]
    conv => enter [1]; rw [l55 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l113 sK0 sK1]
  have l115 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l114 sK1 sK0]
    conv => enter [1, 2]; rw [l7 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l116 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l115 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l117 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l116 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l118 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l117 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l119 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l118 sK1 sK0]
    conv => enter [1, 2]; rw [← l21 sK0 sK1]
  have l120 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0]
    conv => enter [1]; rw [← l119 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l120 x y]

end Semigroup5
