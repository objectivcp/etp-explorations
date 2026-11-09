import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53822_53862_implies_Equation53874 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53862 : Equation53862 G) : Equation53874 G := by
  have l0 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← h53862 (X0 ◇ (X0 ◇ X0)) X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53862 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53862 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53862 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53862 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) ((X0 ◇ (X0 ◇ X0)) ◇ X1)]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X1)]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l12 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X0) ◇ X1) X0]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 X1]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 2]; rw [← l16 X0 X0 X1]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1]; rw [← l16 X0 X0 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l20 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1, 2]; rw [← l16 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1, 2]; rw [← l4 X0 (X0 ◇ (X0 ◇ X0)) X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l24 X0 X1]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l16 X0 X0 X0]
    conv => enter [1]; rw [l25 X0 X1]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X0 X0]
    conv => enter [1]; rw [l26 X0 X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h53862 X0 X0]
    conv => enter [1]; rw [l27 X0 X1]
  have l29 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) sK1 X0]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53822 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l29 sK1 sK2 (sK1 ◇ sK1)]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [← l29 sK1 sK2 sK1]
  have l33 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [← l32 sK1 sK2]
  have l34 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l33 sK1 sK2]
    conv => enter [1]; rw [h53822 sK1 X0]
    conv => enter [1, 2]; rw [← l33 sK1 sK2]
  have l35 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l33 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l36 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l35 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
  have l37 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l36 sK1 sK2 X0]
    conv => enter [1]; rw [← l28 sK1 X0]
  have l38 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l33 sK1 sK2]
    conv => enter [1]; rw [← l37 sK1 sK2 X0]
  have l39 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53822 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l38 sK1 sK2 (X0 ◇ (X0 ◇ X0))]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53822 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l41 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l39 sK0 sK1 sK2]
    conv => enter [1]; rw [← l40 sK0 sK1]
  have l42 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l41 sK1 sK2 sK0]
    conv => enter [1]; rw [← l30 sK0 sK1 sK0]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l42 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l43 x y z]
  conv => enter [1]; rw [l34 y z x]

theorem Equation4512_53822_53862_implies_Equation53896 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53862 : Equation53862 G) : Equation53896 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53862 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l9 x y]
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_53822_53862_implies_Equation53824 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53862 : Equation53862 G) : Equation53824 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h53862 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 sK0]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK2) sK0]
  have l4 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK2) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 sK2]
  have l5 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
    conv => enter [1]; rw [l4 sK0 sK2]
  have l6 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK2)) sK0 X0]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l6 sK0 sK2 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [l6 sK0 sK2 sK0]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 sK2]
    conv => enter [1]; rw [← l8 sK0 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l9 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_53822_53862_implies_Equation53834 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53862 : Equation53862 G) : Equation53834 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l3 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h53862 sK1 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) sK1]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53862 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l2 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l6 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l3 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK2)) sK1]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l9 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l6 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK1 X0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53822 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 (X0 ◇ (X0 ◇ X0))]
  have l11 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0 sK2 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l11 sK1 sK0 sK2]
    conv => enter [1]; rw [← l9 sK1 sK0 sK2 sK1]
  have l13 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2]
    conv => enter [1]; rw [← l12 sK1 sK0 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [← l13 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_53808_54202_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54202 : Equation54202 G) : Equation4280 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h53808 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l2 sK2 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53808 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l9 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l5 sK2 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [h54202 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l13 sK0 (X0 ◇ X0)]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54202 X0 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h54202 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54202 X0 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l17 X0 sK0]
  have l19 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l0 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l18 sK0 sK2]
  have l20 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l19 sK2 sK0]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l20 sK0 sK2]
    conv => enter [1]; rw [← l9 sK2 (sK0 ◇ sK0)]
  have l22 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [h54202 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l23 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [h54202 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54202 sK1 sK2]
    conv => enter [1]; rw [l23 sK2 sK1]
  have l25 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l22 sK2 sK1]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [← l25 sK2 sK1]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK2]
    conv => enter [1]; rw [← l26 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l27 x y z]

theorem Equation4512_53808_54202_implies_Equation54181 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54202 : Equation54202 G) : Equation54181 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h53808 sK0 X0]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h53808 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l2 sK2 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53808 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h54202 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h54202 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54202 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK0 X0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l16 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0 X0]
  have l17 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l16 sK1 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [h54202 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l16 sK1 sK0 (X0 ◇ X0)]
  have l18 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l17 sK1 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l5 sK2 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l18 sK2 sK1 sK0]
  have l20 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l17 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l19 sK2 sK1 sK0]
  have l21 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h54202 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l22 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h54202 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54202 sK0 sK2]
    conv => enter [1]; rw [l22 sK2 sK0]
  have l24 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l5 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l21 sK2 sK0]
  have l25 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l23 sK0 sK2]
    conv => enter [1]; rw [← l24 sK2 sK0]
  have l26 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l20 sK1 sK0 sK2]
    conv => enter [1]; rw [← l25 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l26 z x y]
  conv => enter [1]; rw [h54202 z x]

theorem Equation4512_53808_54202_implies_Equation54236 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54202 : Equation54202 G) : Equation54236 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53808 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53808 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 X0]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [h54202 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h54202 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 sK1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 X0]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 (X0 ◇ X0)]
    conv => enter [1]; rw [h54202 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l15 sK0 sK1 (X0 ◇ X0)]
  have l17 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53808 X0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l16 sK0 sK1 X0]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l17 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK0 sK1 X0]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l18 X0 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1 X0]
  have l20 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [← l19 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l21 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l20 sK0 sK1 X1 X0]
  have l22 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l21 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1 X1]
  have l23 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l22 X1 (X0 ◇ (X1 ◇ X1)) sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h54202 X0 X1]
  have l24 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l6 X1 X0 X1]
  have l25 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54202 X0 X1]
    conv => enter [1]; rw [← l24 sK0 sK1 X1 X0]
  have l26 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l25 X0 X1 sK0 sK1]
  have l27 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l15 sK0 sK1 X2]
    conv => enter [1]; rw [← l26 X0 X1 X2 sK0 sK1]
  have l28 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l27 sK0 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  intro x y z
  conv => enter [1]; rw [l28 x y z x y]

theorem Equation4512_53808_54202_implies_Equation54211 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54202 : Equation54202 G) : Equation54211 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h53808 sK0 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53808 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK0 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l14 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 1]; rw [l7 sK0 sK1]
  have l15 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l16 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l15 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 X0]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 X0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54202 X0 sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h54202 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54202 X0 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [← l20 X0 sK0]
  intro x y
  conv => enter [1]; rw [← l21 y x x]

theorem Equation4512_53808_54202_implies_Equation53824 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54202 : Equation54202 G) : Equation53824 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53808 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l3 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54202 X0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h54202 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54202 X0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0)) X1]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l13 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X1]
    conv => enter [1]; rw [l14 sK0 X1 X0]
  have l16 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 1]; rw [l11 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0)) X1]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l16 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l18 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [← l17 X0 sK0 X1]
  have l19 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l18 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

theorem Equation4512_53808_54202_implies_Equation53830 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h54202 : Equation54202 G) : Equation53830 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h53808 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l2 sK2 X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53808 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l9 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [h54202 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l10 sK0 (X0 ◇ X0)]
  have l12 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l11 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l6 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK2 sK0]
  have l14 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l11 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l13 sK2 sK0]
  have l15 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h54202 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l16 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h54202 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l17 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54202 sK0 sK2]
    conv => enter [1]; rw [l16 sK2 sK0]
  have l18 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l6 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l15 sK2 sK0]
  have l19 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l17 sK0 sK2]
    conv => enter [1]; rw [← l18 sK2 sK0]
  have l20 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0 sK2]
    conv => enter [1]; rw [← l19 sK0 sK2]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l20 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l21 x y z]

theorem Equation4512_53835_54165_54202_54240_implies_Equation54236 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53835 : Equation53835 G) (h54165 : Equation54165 G) (h54202 : Equation54202 G) (h54240 : Equation54240 G) : Equation54236 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h53835 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53835 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53835 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l3 sK1 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l7 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h54240 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l12 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53835 X0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 X0 (sK0 ◇ (sK1 ◇ sK1))]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l18 X0 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 X0 (sK0 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← h53835 X0 X1]
    conv => enter [1]; rw [l19 X0 sK0 sK1]
  have l21 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [← l19 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l22 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l21 sK0 sK1 X0 X1]
  have l23 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l22 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
  have l24 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l23 X0 X1 sK0 sK1]
    conv => enter [1]; rw [l20 X0 X1 sK0 sK1]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h54165 X0 X1]
    conv => enter [1]; rw [← h53835 (X1 ◇ X1) X0]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 ((X1 ◇ X1) ◇ (X1 ◇ X1))]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1, 2]; rw [← h54240 (X1 ◇ X1) X1 X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l27 X0 X1]
    conv => enter [1]; rw [← h54202 (X1 ◇ X1) X1]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 (X1 ◇ X1)]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l29 X0 X1]
    conv => enter [1]; rw [← h54202 X1 X1]
  have l31 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l30 X0 X1]
    conv => enter [1]; rw [l19 X1 sK0 sK1]
  have l32 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54240 X0 X1 X0]
    conv => enter [1]; rw [l31 X0 X1 sK0 sK1]
  have l33 : ∀ sK0 sK1 X0 X2 X1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro sK0 sK1 X0 X2 X1
    conv => enter [1, 1]; rw [← l32 X1 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l34 : ∀ sK0 sK1 X0 X2 X1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro sK0 sK1 X0 X2 X1
    conv => enter [1]; rw [l33 sK0 sK1 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l35 : ∀ sK0 sK1 X0 X2 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro sK0 sK1 X0 X2 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) X0 X2]
    conv => enter [1]; rw [l34 sK0 sK1 X0 X2 X1]
  have l36 : ∀ sK0 sK1 X2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro sK0 sK1 X2 X1 X0
    conv => enter [1]; rw [← l24 sK0 sK1 X0 X2]
    conv => enter [1]; rw [l35 sK0 sK1 X0 X2 X1]
  have l37 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 sK1 sK1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l37 x y z]

theorem Equation4512_53816_53864_implies_Equation53874 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53816 : Equation53816 G) (h53864 : Equation53864 G) : Equation53874 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53864 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53864 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h53816 sK1 (sK1 ◇ sK2)]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [h53864 sK1 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53816 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l8 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53816 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l9 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l8 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 X0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4512_53835_54013_54088_implies_Equation54053 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53835 : Equation53835 G) (h54013 : Equation54013 G) (h54088 : Equation54088 G) : Equation54053 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h53835 X0 X1]
    conv => enter [1]; rw [← h53835 (X1 ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 ((X1 ◇ X0) ◇ (X1 ◇ X0))]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h53835 (sK1 ◇ sK0) sK0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2, 2]; rw [← h54088 X0 X1 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← h54013 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [← h54088 X0 X1 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h54088 X0 X0 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53835 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h53835 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l9 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK1 sK0 X0]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l15 sK1 sK0 X0]
  have l17 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [← l9 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l17 sK1 sK0 sK2]
    conv => enter [1]; rw [← l16 sK0 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← h54088 sK0 sK1 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54088 sK0 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l22 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l18 sK1 sK0 sK2]
    conv => enter [1]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54088 sK0 sK1 sK1]
    conv => enter [1]; rw [← l22 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l23 x y z]

theorem Equation4512_53816_54022_implies_Equation54031 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53816 : Equation53816 G) (h54022 : Equation54022 G) : Equation54031 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l4 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l9 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l10 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 sK2]
  have l11 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK2 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l9 sK2 sK0 sK1]
  have l12 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l11 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l13 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l10 sK2 sK0 sK1]
  have l14 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l13 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
  have l15 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l14 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l16 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l15 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [l12 sK2 sK0 sK1 ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l17 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l16 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h54022 (sK2 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l18 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)]
    conv => enter [1, 2]; rw [l17 sK2 sK0 sK1 X0]
  have l19 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h53816 sK0 (sK1 ◇ sK0)]
  have l21 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h53816 sK0 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK1)) ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h53816 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 sK1 (X0 ◇ (X0 ◇ X0))]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h53816 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (X0 ◇ X0))]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53816 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53816 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l8 sK0 sK1 sK2 ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l26 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK0 ◇ sK1)) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h53816 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l27 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l26 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK1)) ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l17 sK2 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1 sK0]
    conv => enter [1]; rw [← h53816 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53816 (sK0 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l22 sK0 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l33 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l21 sK0 sK2 sK1]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ sK0)]
  have l37 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h53816 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l33 sK0 sK2 sK1 sK0]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l34 sK0 sK1 sK2]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l40 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l19 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l37 sK0 sK2 sK1]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l32 sK0 sK1]
    conv => enter [1]; rw [l41 sK0 sK1]
  have l43 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l40 sK0 sK2 sK1]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l44 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l10 sK2 sK0 sK1]
    conv => enter [1]; rw [← h54022 (sK0 ◇ (sK1 ◇ sK0)) sK2 (sK2 ◇ (sK0 ◇ sK1))]
  have l45 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54022 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ X0)]
  have l46 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l45 sK0 sK1 X0]
  have l47 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l9 sK2 sK0 sK1]
  have l48 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l46 sK0 sK1 X0]
  have l49 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l38 sK0 sK1 sK2]
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
  have l50 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l43 sK0 sK2 sK1]
    conv => enter [1]; rw [l49 sK0 sK1 sK2]
  have l51 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
  have l52 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l50 sK0 sK2 sK1]
    conv => enter [1]; rw [← l47 sK0 sK1 sK2]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l51 sK0 sK1 ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [← l52 sK0 sK2 sK1]
  have l54 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [← h54022 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
  have l55 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (sK2 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l54 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 X0]
  have l56 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l55 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h54022 sK0 sK2 X0]
  have l57 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h54022 sK0 sK2 sK1]
    conv => enter [1]; rw [← l56 sK0 sK2 sK1 X0]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [← l57 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l58 x y z]

theorem Equation4512_53835_53860_53934_implies_Equation53913 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53835 : Equation53835 G) (h53860 : Equation53860 G) (h53934 : Equation53934 G) : Equation53913 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53835 X0 X1]
    conv => enter [1]; rw [← h53934 X1 X0 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ sK1)]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X0 sK1]
  have l3 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h53934 X0 X0 sK2]
    conv => enter [1]; rw [← l2 sK2 sK1 X0]
  have l4 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l4 sK2 sK1 sK0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h53860 sK1 X0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53934 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l12 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l11 sK1 sK2]
  have l13 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53934 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [← l12 sK1 sK2]
  have l14 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l0 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l13 sK1 sK2]
  have l15 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53934 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l14 X0 sK1 sK2]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
  have l17 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 X0]
  have l18 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l17 X0 sK0 sK1]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l18 sK2 (sK2 ◇ sK1) sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK2 sK1 sK0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l21 x y z]

theorem Equation4512_53816_54176_implies_Equation54181 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53816 : Equation53816 G) (h54176 : Equation54176 G) : Equation54181 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53816 X0 X1]
    conv => enter [1]; rw [← h54176 X0 X1 X1]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (X0 ◇ X0)]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (X0 ◇ X0)]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54176 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54176 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK1 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54176 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l8 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK2]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK1 sK0 X0]
  have l11 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l0 sK0 sK2]
    conv => enter [1]; rw [l7 sK0 X0]
  have l12 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK2]
  have l13 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK0 sK2]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l14 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l11 sK0 sK2 X0]
  have l15 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l11 sK0 sK2 X0]
  have l16 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [← l15 sK0 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l17 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l10 sK1 sK0 sK1]
    conv => enter [1]; rw [l14 sK1 sK0 sK1 sK2]
  have l18 : ∀ sK0 X0 sK2 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK0 X0 sK2 X1
    conv => enter [1]; rw [h54176 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l16 sK0 sK2 X1 X0]
  have l19 : ∀ sK0 sK2 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l11 sK0 sK2 sK0]
    conv => enter [1]; rw [l18 sK0 sK0 sK2 X1]
  have l20 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l19 sK0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l12 sK0 sK2]
  have l21 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54176 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← l20 sK0 sK2]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0 sK1]
    conv => enter [1]; rw [← l17 sK1 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l24 x z y]

theorem Equation4512_53822_53835_53870_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53835 : Equation53835 G) (h53870 : Equation53870 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53822 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l10 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53835 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l15 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53835 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← h53835 (sK1 ◇ sK0) sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l19 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l16 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l27 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) X0]
  have l28 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l27 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53870 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l30 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← l31 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l31 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l34 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l39 x y]

theorem Equation4512_53822_53835_53870_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53835 : Equation53835 G) (h53870 : Equation53870 G) : Equation53832 G := by
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
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1, 1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53822 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h53835 X0 X1]
    conv => enter [1]; rw [← h53835 (X1 ◇ X0) X1]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53835 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 ((X1 ◇ X0) ◇ (X1 ◇ X0))]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h53835 (sK0 ◇ sK0) sK1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 2, 2]; rw [← h53870 X1 X0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l20 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [← l14 X0 sK0]
    conv => enter [1]; rw [l18 X1 X0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l22 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [l20 X1 sK0 X0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h53835 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [l14 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l26 sK1 sK0]
  have l28 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l14 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l29 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l28 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l30 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← h53870 X0 X1]
  have l31 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 X0 X1]
    conv => enter [1]; rw [← l22 sK0 X1 X0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l31 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53870 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l8 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53870 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2]; rw [← l11 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK1]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [← l39 sK1 sK0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l41 x y]

theorem Equation4512_53822_53835_53870_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53835 : Equation53835 G) (h53870 : Equation53870 G) : Equation53815 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53870 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53870 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X2))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53835 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [← l4 X1 X2 ((X1 ◇ X2) ◇ X0)]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← l4 X1 X2 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h53870 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X0 X1]
    conv => enter [1, 2]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l11 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X0))) X2]
  have l13 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l12 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
  have l14 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l13 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l15 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l14 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l15 X0 X2 X1]
  have l17 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l16 X0 X2 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0 (X0 ◇ (X1 ◇ X0))]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0 X0]
    conv => enter [1]; rw [← l18 X1 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h53835 X1 X0]
    conv => enter [1]; rw [l19 X0 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l20 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1 X0]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h53822 X0 X0]
    conv => enter [1]; rw [l21 X0 X1]
  intro x y
  conv => enter [1]; rw [l22 x y]
  conv => enter [1]; rw [← l10 x y]

theorem Equation4512_53816_54172_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53816 : Equation53816 G) (h54172 : Equation54172 G) : Equation53812 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54172 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h54172 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54172 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54172 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X0 ◇ (X1 ◇ X1))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l7 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1, 2]; rw [← h54172 X1 (X0 ◇ X1)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← l11 X0 X1 (X0 ◇ X1)]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l14 X0 X1]
    conv => enter [1]; rw [← l11 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1 X1]
    conv => enter [1]; rw [← l15 X0 X1]
  have l17 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53816 X2 X0]
    conv => enter [1, 2]; rw [h53816 X0 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 X0 X1]
    conv => enter [1, 2]; rw [← l16 X0 X1]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0 X1]
    conv => enter [1]; rw [← l18 X1 X0]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation4512_53808_53816_54172_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53816 : Equation53816 G) (h54172 : Equation54172 G) : Equation53810 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54172 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54172 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53816 X2 X0]
    conv => enter [1, 2]; rw [h53816 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h54172 X0 X1]
    conv => enter [1]; rw [← l7 X1 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ X1) X0 X1]
    conv => enter [1]; rw [l9 (X0 ◇ X1) X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2, 2]; rw [← h53808 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1 X0]
    conv => enter [1]; rw [← l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l14 X0 X1]
    conv => enter [1]; rw [l4 X0 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h53808 X0 X0]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation4512_53816_54172_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53816 : Equation53816 G) (h54172 : Equation54172 G) : Equation53815 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54172 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h54172 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54172 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54172 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X0 ◇ (X1 ◇ X1))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l7 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1, 2]; rw [← h54172 X1 (X0 ◇ X1)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← l11 X0 X1 (X0 ◇ X1)]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l14 X0 X1]
    conv => enter [1]; rw [← l11 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1 X1]
    conv => enter [1]; rw [← l15 X0 X1]
  have l17 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53816 X2 X0]
    conv => enter [1, 2]; rw [h53816 X0 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h54172 X0 X1]
    conv => enter [1]; rw [← l11 X1 X0 X1]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 X0 X1]
    conv => enter [1, 2]; rw [← l16 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0 X1]
    conv => enter [1]; rw [← l19 X1 X0]
  intro x y
  conv => enter [1]; rw [l20 x y]
  conv => enter [1]; rw [l18 x y]

theorem Equation53832_54240_implies_Equation4272 (G : Type*) [Magma G] (h53832 : Equation53832 G) (h54240 : Equation54240 G) : Equation4272 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53832 X0 X1]
    conv => enter [1]; rw [← h54240 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4512_53832_54240_implies_Equation54186 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53832 : Equation53832 G) (h54240 : Equation54240 G) : Equation54186 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53832 X0 X1]
    conv => enter [1]; rw [← h54240 X1 X0 X1]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 sK1]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 sK1]
  have l5 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [l7 sK1 sK0]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK1]
  have l10 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l8 sK2 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 sK2 sK1]
  have l11 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]
  conv => enter [1]; rw [l10 z y x]

theorem Equation4512_53810_53864_implies_Equation4268 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53810 : Equation53810 G) (h53864 : Equation53864 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53810 X0 X1]
    conv => enter [1]; rw [← h53864 X0 X1 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation53810_53864_implies_Equation53866 (G : Type*) [Magma G] (h53810 : Equation53810 G) (h53864 : Equation53864 G) : Equation53866 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53810 X0 X1]
    conv => enter [1]; rw [← h53864 X0 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_53832_54088_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53832 : Equation53832 G) (h54088 : Equation54088 G) : Equation53812 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h54088 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X3) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h54088 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X0)) X3]
  have l2 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X3)) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X3]
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X3]
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53832 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [← l3 X2 X1 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54088 (X0 ◇ X0) X1 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_53810_54022_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53810 : Equation53810 G) (h54022 : Equation54022 G) : Equation53809 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54022 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53810 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_53815_54201_implies_Equation53826 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53815 : Equation53815 G) (h54201 : Equation54201 G) : Equation53826 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X0) X2]
    conv => enter [1, 1]; rw [h54201 X1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54201 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X2))]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l4 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X2 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h53815 X0 X1]
    conv => enter [1]; rw [h53815 X0 X2]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53815 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← h53815 X0 X1]
    conv => enter [1]; rw [h54201 X0 X0]
    conv => enter [1, 2]; rw [h53815 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h54201 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [h53815 X0 X1]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h54201 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h53815 X0 X1]
  have l12 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h53815 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
  have l13 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l12 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l14 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) (X0 ◇ (X0 ◇ X0))]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l16 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l8 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l17 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l13 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l18 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [l6 X0 X0 (X1 ◇ (X1 ◇ X0))]
  have l20 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l17 X0 X2 X1]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h53815 X0 X0]
  have l22 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [← l9 X0 X1]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l20 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l21 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X0) (X0 ◇ X0)]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l22 X0 X1]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X1 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l24 X0 X1]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h53815 X0 X0]
    conv => enter [1]; rw [l25 X0 X1]
  have l28 : ∀ X2 X0 X1 : G, ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54201 (X2 ◇ (X2 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l7 X0 X2 X1]
  have l29 : ∀ X2 X0 X1 : G, ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l28 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X0) (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l30 : ∀ X2 X0 X1 : G, ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l29 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l31 : ∀ X2 X0 X1 : G, ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l30 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l9 X0 X1]
  have l32 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) = (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l31 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X2 (X2 ◇ X0) (X0 ◇ X0)]
  have l33 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l32 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X0 ◇ X0)]
  have l34 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l27 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2, 2]; rw [← h54201 X0 X1]
  have l35 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l27 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l36 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l27 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← l27 X0 X1]
  have l37 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l36 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X0) ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l38 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l35 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l39 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l34 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))]
  have l40 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l41 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l39 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))]
  have l42 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l40 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X0) (X0 ◇ (X0 ◇ X0))]
  have l43 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l41 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X1 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l44 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l42 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l45 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l43 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X0 (X1 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l46 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l44 X1 X0]
    conv => enter [1, 2, 2]; rw [l33 X0 X1 X0]
  have l47 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l45 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l16 X1 X0 X1]
  have l48 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l46 X1 X0]
    conv => enter [1]; rw [l23 X1 X1 (X0 ◇ (X0 ◇ X0))]
  have l49 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l47 X0 X1]
    conv => enter [1, 2]; rw [← l26 X0 X1]
  have l50 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l48 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X0) ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))]
  have l51 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l49 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l52 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l50 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))]
  have l53 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l51 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l54 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l52 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X0) (X1 ◇ (X1 ◇ X0))]
  have l55 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l53 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l56 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l54 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h54201 (X1 ◇ X0) X1]
  have l57 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l55 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h54201 (X1 ◇ X0) X0]
  have l58 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l56 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 (X1 ◇ X1)]
  have l59 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l57 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ X0)]
  have l60 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l38 X1 X0 X1]
    conv => enter [1]; rw [← l58 X1 X0]
  have l61 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l60 X0 X1]
    conv => enter [1]; rw [l59 X0 X1]
  have l62 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l27 X0 X2]
    conv => enter [1]; rw [← l6 X0 X1 (X2 ◇ (X2 ◇ X0))]
  have l63 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l61 X0 X1]
    conv => enter [1]; rw [← l62 X1 X0 X0]
  have l64 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h53815 X0 X1]
  have l65 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l64 X1 X0]
    conv => enter [1, 2]; rw [← l63 X0 X1]
  intro x y
  conv => enter [1]; rw [l63 x y]
  conv => enter [1]; rw [← l65 y x]

theorem Equation4512_53815_53899_implies_Equation53833 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53815 : Equation53815 G) (h53899 : Equation53899 G) : Equation53833 G := by
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
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53815 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53815 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h53815 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l10 sK1 sK0 X0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l11 sK1 sK0 X0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0]
  have l20 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l24 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l23 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK0]
  have l27 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
    conv => enter [1]; rw [l20 X0 X1 X2]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l29 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l27 X0 X1 X2]
    conv => enter [1]; rw [← l24 X1 X2 X0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l31 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l29 X0 X1 X2]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l19 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l18 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l4 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)]
  have l36 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ sK0)) = (sK0 ◇ (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l25 sK1 sK0]
  have l37 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) X0]
  have l38 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l37 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 X0]
  have l39 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l39 sK1 sK0]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1]
  have l43 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ sK0)]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 sK0]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l31 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 sK0]
    conv => enter [1]; rw [← l44 sK1 sK0]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l45 sK1 sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l30 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53815 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l30 sK0 sK1]
  have l50 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l51 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l50 sK0 sK1 X0]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0 sK0]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1, 2]; rw [← l51 sK0 sK1 (sK0 ◇ sK1)]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l53 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l55 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l60 sK0 sK1]
  have l63 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l62 sK0 sK1]
  have l64 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l63 sK1 sK0]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l65 sK0 sK1]
  have l67 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l47 sK1 sK0]
  have l68 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l67 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l61 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l69 sK0 sK1]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l70 sK0 sK1]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [← l71 sK0 sK1]
  have l73 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l73 sK0 sK1]
  have l75 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l74 sK0 sK1]
  have l76 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l76 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l75 sK1 sK0]
  have l78 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [l68 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l78 sK0 sK1]
  have l80 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l81 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l82 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1]; rw [← l81 sK1 sK0]
  have l83 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l79 sK0 sK1]
    conv => enter [1]; rw [← l80 sK0 sK1]
  have l84 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l83 sK0 sK1]
  have l85 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [← l82 sK0 sK1]
  have l86 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l87 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l85 sK0 sK1]
  have l88 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l87 sK0 sK1]
  have l89 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [← l88 sK0 sK1]
  have l90 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53815 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l89 sK0 sK1]
  have l91 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l90 sK1 sK0]
  have l92 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l91 sK0 sK1]
  have l93 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l92 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l94 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l93 sK0 sK1]
  have l95 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l94 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ sK1)]
  have l96 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [l95 sK1 sK0]
  have l97 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l96 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1 (sK1 ◇ sK1)]
  have l98 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0 sK1]
    conv => enter [1]; rw [← l97 sK0 sK1]
  have l99 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l84 sK0 sK1]
    conv => enter [1]; rw [← l98 sK1 sK0]
  have l100 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1, 2]; rw [← l99 sK0 sK1]
  have l101 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l100 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l101 x y]

theorem Equation4512_53815_54172_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53815 : Equation53815 G) (h54172 : Equation54172 G) : Equation53812 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54172 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h54172 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h53815 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_53815_53870_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53815 : Equation53815 G) (h53870 : Equation53870 G) : Equation53809 G := by
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
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53815 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53815 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53815 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53815 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53815 sK0 sK1]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53815 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l18 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l13 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK1 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l20 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l24 sK1 sK0]
  have l26 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ sK0) X0]
  have l27 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l26 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l22 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ (((sK1 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h53870 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h53870 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l14 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53870 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53870 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53870 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) X0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l35 sK0 sK1]
  have l38 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l36 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l40 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l38 sK0 sK1 X0]
    conv => enter [1]; rw [← h53870 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l40 sK0 sK1 X0]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [h53815 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l32 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l42 sK1 sK0]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l44 sK0 sK1]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1, 2]; rw [l34 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [l34 sK1 sK0]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) sK0]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l53 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l54 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l56 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l58 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l60 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l61 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l62 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l63 x y]

theorem Equation4512_53815_54202_implies_Equation54236 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53815 : Equation53815 G) (h54202 : Equation54202 G) : Equation54236 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [h54202 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54202 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X1)) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X2 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h53815 X0 X1]
    conv => enter [1]; rw [h53815 X0 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53815 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h53815 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
  have l7 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l5 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l9 X0 X2 X1]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l10 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h53815 X0 X1]
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1, 2]; rw [← h53815 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 (X0 ◇ X0) X1 X0]
    conv => enter [1, 2]; rw [← l13 X0 X0]
  have l15 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l15 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l14 X0 X1]
  have l18 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l16 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1]; rw [← l12 X0 X1 X1 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1 X0]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0 X0]
    conv => enter [1, 2]; rw [← l3 X0 X0 X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1 X1]
    conv => enter [1]; rw [← l22 X1 X0]
  have l24 : ∀ X1 X2 X0 : G, ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l4 (X1 ◇ X1) X2 X1]
    conv => enter [1, 2, 2]; rw [← l23 X0 X1]
  have l25 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X1 (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← l24 X1 X2 X0]
  have l26 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l25 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X1 (X2 ◇ (X2 ◇ (X1 ◇ X1)))]
  have l27 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l26 X1 X0 X2]
    conv => enter [1]; rw [← l12 X1 X2 X2 X1]
  have l28 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X2 ◇ (X2 ◇ (X1 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l27 X1 X0 X2]
    conv => enter [1]; rw [← l0 X2 X2 X1]
  have l29 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = (X2 ◇ (X2 ◇ (X1 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [l18 X0 X1 X1]
    conv => enter [1]; rw [l28 X1 X0 X2]
  have l30 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X1 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l18 X0 X1 X1]
    conv => enter [1]; rw [l29 X1 X0 X2]
  have l31 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X1]
    conv => enter [1]; rw [l30 X1 X0 X2]
  have l32 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1, 2, 2]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [l11 X0 X2 (X1 ◇ (X2 ◇ X2))]
  have l33 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← l11 X0 X2 (X1 ◇ (X0 ◇ X0))]
  have l34 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h54202 X1 X0]
    conv => enter [1]; rw [l33 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h54202 X1 X0]
  have l35 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [l32 X0 X2 X1]
  have l36 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l34 X0 X1 X2]
    conv => enter [1]; rw [← l12 X2 X2 X1 X0]
  have l37 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h54202 X1 X0]
    conv => enter [1]; rw [l36 X0 X1 X2]
  have l38 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l37 X1 X2 X0]
    conv => enter [1]; rw [l35 X0 X1 X2]
    conv => enter [1, 2]; rw [← l37 X1 X2 X0]
  have l39 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1]; rw [← l38 X1 X0 X1]
  have l40 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l31 X0 X1 X2]
    conv => enter [1]; rw [← l38 X2 X1 X2]
  have l41 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l39 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l42 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X2))) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [← l41 X0 X2 X1]
  have l43 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l42 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l44 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l43 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l40 x y x]
  conv => enter [1]; rw [← l44 z x y]

end Semigroup5
