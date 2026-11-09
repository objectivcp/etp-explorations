import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53973_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53973 : Equation53973 G) : Equation4277 G := by
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
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53973 X0 sK0 sK0]
  have l12 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h53973 X0 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK1]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53973 X0 X1 X0]
    conv => enter [1]; rw [← h53973 X2 X1 X0]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (X1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h53973 X0 X1 sK0]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53973 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1, 2]; rw [l10 sK0 (X1 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l14 sK0 X1 X0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ sK0)]
  have l18 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l12 X0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) sK1]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 X0 X1]
    conv => enter [1]; rw [l3 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l22 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l20 sK0 X0 X1]
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0)) (X1 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l22 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) sK0]
  have l24 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l25 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l18 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
  have l26 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK1]
    conv => enter [1]; rw [l25 sK1 sK2 sK0]
  have l27 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l18 (sK0 ◇ sK0) sK2 sK1]
    conv => enter [1, 2]; rw [← l26 sK1 sK2 sK0]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK1]
    conv => enter [1]; rw [l27 sK1 sK2 sK0]
  have l29 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l21 sK0 sK0]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l29 sK0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l30 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l32 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X3 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [h53973 X3 X1 X2]
    conv => enter [1]; rw [l13 X2 (X1 ◇ X2) X0]
  have l33 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l13 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l34 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ X1)]
    conv => enter [1, 2]; rw [l13 sK0 X1 X0]
  have l35 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l13 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 X1]
  have l36 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l35 X0 X1 sK0]
    conv => enter [1]; rw [← l31 sK0 X1]
  have l37 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l34 sK0 X1 sK0]
    conv => enter [1]; rw [l24 sK0 sK0 X1]
  have l38 : ∀ X3 X1 sK0 X2 : G, (X3 ◇ (X3 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X3 X1 sK0 X2
    conv => enter [1]; rw [l32 X3 X1 X3 X2]
    conv => enter [1]; rw [l33 X3 (X1 ◇ X2) sK0]
  have l39 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← l33 sK0 X1 sK0]
    conv => enter [1]; rw [l36 sK0 X1 sK0]
  have l40 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l31 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [l37 sK0 X1]
  have l41 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l33 sK0 X1 sK0]
    conv => enter [1]; rw [l38 sK0 X1 sK0 X2]
  have l42 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l40 sK0 X1]
    conv => enter [1]; rw [← l39 sK0 (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l43 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l41 sK0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l42 sK0 X1]
  have l44 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l43 sK0 X1]
    conv => enter [1]; rw [← l39 sK0 (sK0 ◇ X1)]
  have l45 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l41 sK0 sK0 X1]
    conv => enter [1]; rw [← l44 sK0 X1]
  have l46 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l45 sK0 X1]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l28 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l47 x y z]

@[equational_result]
theorem Equation4277_implies_Equation53974 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation53974 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [h4277 sK1 sK3 (sK2 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_53974_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53974 : Equation53974 G) : Equation4277 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53974 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [h53974 sK0 (sK0 ◇ sK0) X1 X2]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53974 X0 X1 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0 X1]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l4 sK0 X1 X0]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ X2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l2 sK0 sK0 X2]
    conv => enter [1]; rw [l3 sK0 ((sK0 ◇ sK0) ◇ X2) sK0]
  have l7 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (((sK0 ◇ sK0) ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l5 sK0 sK0 X1]
    conv => enter [1]; rw [l3 sK0 ((sK0 ◇ sK0) ◇ X1) sK0]
  have l8 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2
    conv => enter [1]; rw [l6 sK0 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X2 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l7 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 X1]
    conv => enter [1]; rw [← l9 sK0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0))]
    conv => enter [1]; rw [← h53974 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation4277_implies_Equation53979 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation53979 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [h4277 sK1 sK3 (sK0 ◇ sK1)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_53979_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53979 : Equation53979 G) : Equation4277 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h53979 X0 X1 sK0 sK0]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [← h53979 X0 X1 sK1 sK2]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53979 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l6 : ∀ X1 sK1 sK2 : G, (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [← h53979 (sK1 ◇ sK2) X1 X1 sK1]
    conv => enter [1]; rw [l3 (sK1 ◇ sK2) X1 sK1 sK2]
  have l7 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← l5 sK0 X0 sK1]
  have l8 : ∀ sK1 sK2 X1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← l6 X1 sK1 sK2]
    conv => enter [1]; rw [← l4 sK1 sK2 X1 (sK1 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK0 sK0]
  have l10 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l8 sK1 sK2 X0]
    conv => enter [1]; rw [l8 sK1 sK2 X1]
  have l11 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l10 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l4 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l4 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK0 sK0]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK0]
    conv => enter [1]; rw [← l13 sK0]
  intro x y z
  conv => enter [1]; rw [← l14 y z x]

@[equational_result]
theorem Equation4277_implies_Equation53981 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation53981 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [h4277 sK1 sK3 (sK0 ◇ sK3)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_53981_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53981 : Equation53981 G) : Equation4277 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53981 X0 X1 sK0 sK0]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53981 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK1]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l2 X0 X1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) sK1]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1]; rw [← l8 sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation4277_implies_Equation53982 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation53982 G := by
  have l0 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4277 sK3 sK3 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4277 sK3 sK0 sK0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [h4277 sK1 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation4512_53982_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation4277 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53982 X0 X1 sK0 sK0]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53982 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK2]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l2 X0 X1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) sK2]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1]; rw [← l8 sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation4277_implies_Equation53983 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation53983 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h4277 sK2 sK2 sK3]
    conv => enter [1]; rw [h4277 sK2 sK4 (sK1 ◇ sK0)]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation53983_implies_Equation4277 (G : Type*) [Magma G] (h53983 : Equation53983 G) : Equation4277 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4277_implies_Equation53999 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation53999 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [h4277 sK1 sK0 sK1]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4277 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [h4277 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 X1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_53999_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53999 : Equation53999 G) : Equation4277 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53999 X0 X1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l4 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l3 sK0 sK0 sK0]
    conv => enter [1]; rw [h53999 sK0 sK0 X1 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation4277_implies_Equation54001 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation54001 G := by
  have l0 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [h4277 sK1 sK0 sK3]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4277 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [h4277 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 X1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_54001_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54001 : Equation54001 G) : Equation4277 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54001 X0 X1 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

@[equational_result]
theorem Equation4277_implies_Equation54002 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation54002 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [h4277 sK1 sK0 sK0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4277 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [h4277 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 X1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_54002_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54002 : Equation54002 G) : Equation4277 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54002 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l0 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation4277_implies_Equation54003 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation54003 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h4277 sK2 sK2 sK3]
    conv => enter [1]; rw [h4277 sK2 sK1 sK0]
  have l1 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [h4277 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [h4277 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [← h4277 sK2 sK2 sK3]
    conv => enter [1]; rw [l1 sK2 X1 sK2 sK3]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK4]
    conv => enter [1, 2]; rw [l0 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation54003_implies_Equation4277 (G : Type*) [Magma G] (h54003 : Equation54003 G) : Equation4277 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54003 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54003 sK1 sK2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4277_implies_Equation53977 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation53977 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [h4277 sK1 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_53977_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53977 : Equation53977 G) : Equation4277 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53977 X0 X1 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation4277_implies_Equation53975 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation53975 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4277 sK1 sK1 sK2]
    conv => enter [1]; rw [h4277 sK1 sK0 (sK0 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_53975_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation4277 G := by
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
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53975 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53975 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l11 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ X2) ◇ X3)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X2) X3]
    conv => enter [1, 1]; rw [h53975 X1 X2 X0]
  have l12 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l11 X1 X2 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X3]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l12 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l16 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l13 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK0]
  have l17 : ∀ sK0 X0 X1 X2 X3 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1]; rw [← l13 X0 ((X0 ◇ X1) ◇ X3) sK0]
    conv => enter [1]; rw [← l15 X1 X2 X3 X0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l19 : ∀ sK0 X0 X1 X2 X3 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1]; rw [l17 sK0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X3]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1 sK0 sK0]
    conv => enter [1]; rw [l13 X1 (sK0 ◇ sK0) sK0]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [l20 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l22 sK0 sK0]
    conv => enter [1]; rw [← l21 sK0 X0 sK0]
  have l24 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1, 2]; rw [l22 sK0 sK0]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [← l25 sK0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l13 sK0 X0 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← l4 sK0]
  have l29 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 sK0]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l29 sK1 sK2 sK0]
    conv => enter [1]; rw [← l26 sK0]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [l28 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l31 sK1 sK2 sK0]
    conv => enter [1]; rw [← l32 sK0]
  intro x y z
  conv => enter [1]; rw [← l33 y z x]

@[equational_result]
theorem Equation4277_implies_Equation53911 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation53911 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4277 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4277 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

theorem Equation4512_53911_implies_Equation4277 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53911 : Equation53911 G) : Equation4277 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h53911 X0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h53911 sK0 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l3 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))]
    conv => enter [1]; rw [← h53911 X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l10 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2, 2]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h53911 X1 X0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [l10 X0 sK0 X1]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation4277_implies_Equation53978 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation53978 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4277 sK1 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4277 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l0 z w x y]

@[equational_result]
theorem Equation53978_implies_Equation4277 (G : Type*) [Magma G] (h53978 : Equation53978 G) : Equation4277 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X0 ◇ X1)) = (X4 ◇ (X4 ◇ X5)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h53978 X0 X1 X0 X0]
    conv => enter [1]; rw [← h53978 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation4278_implies_Equation4310 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4310 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4278 sK2 X0 sK0]
    conv => enter [1]; rw [h4278 sK2 X1 sK0]
  have l1 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h4278 sK2 sK3 sK0]
  have l2 : ∀ sK3 sK0 sK2 X0 X1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK2]
    conv => enter [1]; rw [h4278 sK2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x x y z w]

@[equational_result]
theorem Equation4310_implies_Equation4278 (G : Type*) [Magma G] (h4310 : Equation4310 G) : Equation4278 G := by
  intro x y z
  conv => enter [1]; rw [h4310 x x y z]

@[equational_result]
theorem Equation4278_implies_Equation4323 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4323 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4278 sK0 X0 sK1]
    conv => enter [1]; rw [h4278 sK0 X1 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4278 sK0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4278 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y y z]

@[equational_result]
theorem Equation4323_implies_Equation4278 (G : Type*) [Magma G] (h4323 : Equation4323 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4323 sK0 sK0 X0]
    conv => enter [1]; rw [h4323 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4278_implies_Equation4334 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4334 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK0]
    conv => enter [1]; rw [h4278 sK1 X1 sK0]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h4278 sK1 sK3 sK0]
  have l2 : ∀ sK3 sK0 sK1 X0 X1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x y x z w]

@[equational_result]
theorem Equation4334_implies_Equation4278 (G : Type*) [Magma G] (h4334 : Equation4334 G) : Equation4278 G := by
  intro x y z
  conv => enter [1]; rw [h4334 x x y z]

@[equational_result]
theorem Equation4278_implies_Equation4348 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4348 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4278 sK1 sK0 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4278 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4348_implies_Equation4278 (G : Type*) [Magma G] (h4348 : Equation4348 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4348 sK0 sK0 sK2]
    conv => enter [1]; rw [h4348 sK2 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4278_implies_Equation4354 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4354 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4278 sK2 sK1 sK2]
    conv => enter [1]; rw [h4278 sK2 X0 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4278 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

@[equational_result]
theorem Equation4354_implies_Equation4278 (G : Type*) [Magma G] (h4354 : Equation4354 G) : Equation4278 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4354 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4278_implies_Equation4367 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4367 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK0]
    conv => enter [1]; rw [h4278 sK3 X1 sK0]
  have l1 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [← h4278 sK3 sK2 sK0]
  have l2 : ∀ sK2 sK0 sK3 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z y w]

@[equational_result]
theorem Equation4367_implies_Equation4278 (G : Type*) [Magma G] (h4367 : Equation4367 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [h4367 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h4367 sK0 X1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4278_implies_Equation4378 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4378 G := by
  have l0 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ sK4)) = (X1 ◇ (sK0 ◇ sK4)) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4278 sK4 X0 sK0]
    conv => enter [1]; rw [h4278 sK4 X1 sK0]
  have l1 : ∀ sK1 sK0 sK4 : G, (sK1 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [← h4278 sK4 sK1 sK0]
  have l2 : ∀ sK1 sK0 sK4 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK4)) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK1 sK0 sK4 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

@[equational_result]
theorem Equation4378_implies_Equation4278 (G : Type*) [Magma G] (h4378 : Equation4378 G) : Equation4278 G := by
  intro x y z
  conv => enter [1]; rw [h4378 x x x y z]

theorem Equation4278_4512_implies_Equation54403 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54403 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK0]
    conv => enter [1]; rw [h4278 sK3 X1 sK0]
  have l1 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← h4278 sK3 sK1 sK0]
  have l2 : ∀ X0 X1 sK0 sK3 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK0 sK3 sK1
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 sK1]
  have l3 : ∀ X0 sK1 sK0 sK3 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK1 sK0 sK3
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK3 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK3 sK1]
  have l4 : ∀ sK1 sK0 sK3 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l5 : ∀ X0 sK1 sK0 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK1 sK0 sK3 X1
    conv => enter [1]; rw [l3 X0 sK1 sK0 sK3]
    conv => enter [1]; rw [← l3 X1 sK1 sK0 sK3]
  have l6 : ∀ sK2 sK1 sK0 sK3 X0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK1 sK0 sK3 X0
    conv => enter [1]; rw [l5 sK2 sK1 sK0 sK3 X0]
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK3 sK1 sK2]
  have l7 : ∀ sK3 X0 X1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK3)]
  have l8 : ∀ sK3 X0 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 sK1 sK0
    conv => enter [1]; rw [l7 sK3 X0 sK3 sK0]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK3 sK1]
  have l9 : ∀ sK3 X0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 X0 sK1 sK2
    conv => enter [1]; rw [l8 sK3 X0 sK1 sK3]
    conv => enter [1, 2]; rw [l4 sK1 sK3 sK3 sK1 sK2]
  have l10 : ∀ sK2 sK1 sK0 sK3 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK1 sK0 sK3
    conv => enter [1]; rw [l6 sK2 sK1 sK0 sK3 sK2]
    conv => enter [1]; rw [← l9 sK3 sK2 sK1 sK2]
  have l11 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [l4 sK1 sK0 sK3 sK3 sK3]
    conv => enter [1]; rw [← l10 sK2 sK1 sK0 sK3]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation4512_54403_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54403 : Equation54403 G) : Equation4278 G := by
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
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← h54403 sK0 (sK0 ◇ sK0) X1 X0]
  have l5 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ sK0 X2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l7 sK0 X2 X0 sK0]
    conv => enter [1]; rw [← h54403 X0 (sK0 ◇ (sK0 ◇ sK0)) X2 sK0]
  have l9 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l8 sK0 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l10 : ∀ sK0 X0 X2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [l9 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h54403 X2 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 X0 sK0 sK0]
  have l12 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0 X0 sK2]
  have l13 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4278_4512_implies_Equation54437 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54437 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK0]
    conv => enter [1]; rw [h4278 sK3 X1 sK0]
  have l1 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4278 sK3 sK3 sK0]
  have l2 : ∀ X0 X1 sK0 sK3 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK0 sK3
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 sK3]
  have l3 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK3 sK0
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK3 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK3]
  have l4 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l5 : ∀ X0 sK3 sK0 X1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X1 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK3 sK0 X1
    conv => enter [1]; rw [l3 X0 sK3 sK0]
    conv => enter [1]; rw [← l3 X1 sK3 sK0]
  have l6 : ∀ sK2 sK3 sK0 X0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [l5 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [l4 sK3 sK0 sK1 sK2]
  have l7 : ∀ sK3 X0 X1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK3)]
  have l8 : ∀ sK3 X0 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 sK0
    conv => enter [1]; rw [l7 sK3 X0 sK3 sK0]
  have l9 : ∀ sK3 X0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 X0 sK1 sK2
    conv => enter [1]; rw [l8 sK3 X0 sK3]
    conv => enter [1, 2]; rw [l4 sK3 sK3 sK1 sK2]
  have l10 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK2 sK3 sK0 sK2 sK2]
    conv => enter [1]; rw [← l9 sK3 sK2 sK2 sK2]
  have l11 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK3)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l4 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [← l10 sK2 sK3 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l4 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation4512_54437_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54437 : Equation54437 G) : Equation4278 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54437 X0 X1 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54437 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l2 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [h54437 X0 sK2 sK0 X1]
    conv => enter [1]; rw [h4512 sK2 sK0 (X1 ◇ sK0)]
  have l3 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 X1 sK0]
  have l4 : ∀ sK2 sK0 X1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [← l2 sK2 sK2 sK0 sK0]
    conv => enter [1]; rw [l2 sK2 sK2 sK0 X1]
  have l5 : ∀ sK2 sK0 X1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l4 sK2 sK0 X1]
    conv => enter [1]; rw [← l3 X1 sK0 (sK2 ◇ sK0)]
  have l6 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l5 sK2 sK0 X1]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x x]

theorem Equation4278_4512_implies_Equation54442 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54442 G := by
  have l0 : ∀ X0 sK0 sK1 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK0 sK1 sK3 X1
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK3) X0 sK0]
    conv => enter [1]; rw [h4278 (sK1 ◇ sK3) X1 sK0]
  have l1 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ sK3) ◇ ((sK1 ◇ sK3) ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK3) sK2 sK0]
  have l2 : ∀ sK2 sK0 sK1 sK3 X0 X1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK0 sK1 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 sK1 sK3]
    conv => enter [1]; rw [h4278 (sK1 ◇ sK3) X0 X1]
  have l3 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK1]
    conv => enter [1]; rw [h4278 sK3 X1 sK1]
  have l4 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [← h4278 sK3 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK3 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK0 sK1 sK3 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l6 : ∀ sK3 X0 X1 sK1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) := by
    intro sK3 X0 X1 sK1
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK3)]
  have l7 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [l2 sK2 sK0 sK1 sK3 sK2 sK2]
    conv => enter [1]; rw [← l6 sK3 sK2 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ (sK1 ◇ sK3)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK3 sK3 sK3]
    conv => enter [1]; rw [← l7 sK2 sK0 sK1 sK3]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

theorem Equation4512_54442_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54442 : Equation54442 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (sK2 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ X0) X1]
  have l4 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (sK2 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l3 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l5 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l4 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h54442 X0 sK2 X1 sK0]
  have l6 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l5 sK2 sK0 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l8 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← h54442 X0 (sK0 ◇ sK0) X1 sK0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l11 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK2 sK0 sK0]
  have l12 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) ◇ X1) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 sK2 ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l2 sK2 sK0 X0]
  have l13 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l12 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ X0) X1]
  have l14 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l11 sK2 sK0]
    conv => enter [1]; rw [l6 sK2 sK0 sK0 sK0]
  have l15 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l13 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l16 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK0) ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l15 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h54442 X0 (sK2 ◇ sK0) X1 sK0]
  have l17 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l6 sK2 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 sK0]
  have l18 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ ((sK2 ◇ sK0) ◇ X1)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [← l16 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l19 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ (sK2 ◇ X1)) = (X0 ◇ ((sK2 ◇ sK0) ◇ X1)) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [h54442 X0 sK2 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l18 X0 sK2 sK0 X1]
  have l20 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK2 sK0]
  have l21 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l20 sK2 sK0]
  have l22 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l21 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
  have l23 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l22 sK2 sK0 X0]
    conv => enter [1]; rw [l6 sK2 sK0 (sK0 ◇ sK0) X0]
  have l24 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l23 sK0 sK2 X0]
    conv => enter [1]; rw [l19 (sK0 ◇ sK0) sK2 X0 sK0]
  have l25 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK2 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [← l17 sK2 sK0]
  have l26 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (((sK2 ◇ sK0) ◇ sK0) ◇ X0)) = (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 ((sK2 ◇ sK0) ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l17 sK2 sK0]
  have l27 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (((sK2 ◇ sK0) ◇ sK0) ◇ X0)) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l26 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l28 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l24 sK0 sK2 sK0]
    conv => enter [1]; rw [l25 sK0 sK2]
  have l29 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (((sK2 ◇ sK0) ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l27 sK0 sK2 X0]
    conv => enter [1]; rw [l6 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l30 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l17 sK2 sK0]
    conv => enter [1]; rw [l28 sK0 sK2]
  have l31 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (((sK2 ◇ sK0) ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l29 sK0 sK2 X0]
    conv => enter [1]; rw [l19 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0 sK0]
  have l32 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l31 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK0) sK0 X0]
  have l33 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54442 sK0 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l32 sK0 sK2 X0]
  have l34 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l33 sK0 X0 sK2]
  have l35 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l30 sK2 sK0]
    conv => enter [1]; rw [← l1 sK0 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l36 : ∀ sK2 sK0 X0 : G, (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1, 1]; rw [l30 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l37 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l36 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l38 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l34 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [← l35 sK0 sK2]
  have l39 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54442 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l37 sK2 sK0 X0]
  have l40 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l38 sK0 sK2]
    conv => enter [1]; rw [← l24 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l41 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l39 sK0 X0 sK2]
    conv => enter [1]; rw [l6 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l42 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l41 sK0 X0 sK2]
    conv => enter [1]; rw [l19 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0 sK0]
  have l43 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0 sK0]
    conv => enter [1]; rw [← l42 sK0 X0 sK0]
  have l44 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l43 sK0 X0]
    conv => enter [1]; rw [l10 sK0 sK0 X0]
  have l45 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l40 sK0 sK2]
    conv => enter [1]; rw [← l30 sK2 sK0]
  have l46 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l44 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l47 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l44 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l48 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l44 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l49 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l47 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l50 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l46 sK0]
    conv => enter [1]; rw [l49 sK0]
  have l51 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l46 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l52 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0 sK2]
    conv => enter [1]; rw [← l51 sK2 sK0]
  have l53 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l52 sK0 sK2]
    conv => enter [1]; rw [l14 sK2 sK0]
  have l54 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l50 sK0]
    conv => enter [1]; rw [l53 sK0 sK2]
  have l55 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l54 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
  have l56 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l48 sK0 X0]
    conv => enter [1]; rw [l55 sK0 X0 sK2]
  have l57 : ∀ sK2 sK0 X2 X0 X1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ (X0 ◇ X1)))) = (sK2 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK2 sK0 X2 X0 X1
    conv => enter [1]; rw [l2 sK2 sK0 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← h54442 X0 (sK0 ◇ sK0) X1 X2]
  have l58 : ∀ sK2 sK0 X2 X0 X1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ (X0 ◇ X1)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ X1)) := by
    intro sK2 sK0 X2 X0 X1
    conv => enter [1]; rw [l57 sK2 sK0 X2 X0 X1]
    conv => enter [1]; rw [← h54442 (sK0 ◇ sK0) sK2 X1 X0]
  have l59 : ∀ sK2 sK0 X2 X0 X1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ (X0 ◇ X1)))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X1)) := by
    intro sK2 sK0 X2 X0 X1
    conv => enter [1]; rw [l58 sK2 sK0 X2 X0 X1]
    conv => enter [1]; rw [l19 (sK0 ◇ sK0) sK2 X1 sK0]
  have l60 : ∀ sK2 sK0 X2 X0 X1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ (X0 ◇ X1)))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X1)) := by
    intro sK2 sK0 X2 X0 X1
    conv => enter [1]; rw [l59 sK2 sK0 X2 X0 X1]
    conv => enter [1]; rw [← l24 sK0 sK2 X1]
  have l61 : ∀ sK0 X1 sK2 X2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 sK2 X2 X0
    conv => enter [1]; rw [l56 sK0 X1 sK2]
    conv => enter [1]; rw [← l60 sK2 sK0 X2 X0 X1]
  have l62 : ∀ sK0 X1 sK2 X2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (sK2 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 sK2 X2 X0
    conv => enter [1]; rw [l61 sK0 X1 sK2 X2 X0]
    conv => enter [1]; rw [l6 sK2 sK0 sK0 (X2 ◇ (X0 ◇ X1))]
  have l63 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X2 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l62 sK0 X1 sK0 X2 X0]
    conv => enter [1]; rw [← h54442 X2 sK0 (X0 ◇ X1) sK0]
  have l64 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X2 ◇ X1)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l63 sK0 X1 X2 X0]
    conv => enter [1]; rw [← h54442 X0 X2 X1 sK0]
  have l65 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l64 sK0 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l65 x y z]

theorem Equation4278_4512_implies_Equation54452 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54452 G := by
  have l0 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [← h4278 sK3 sK0 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 sK3]
  have l1 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h4278 (sK2 ◇ sK3) X0 sK2]
    conv => enter [1, 2]; rw [← h4278 sK3 sK2 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4278 sK3 sK1 sK2]
    conv => enter [1]; rw [l0 sK3 sK3 sK0]
  have l3 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK3]
    conv => enter [1]; rw [← l1 sK2 sK3 X0]
  have l4 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [l3 X0 sK0 sK3 sK2]
    conv => enter [1, 2]; rw [← h4278 sK3 (sK2 ◇ sK3) sK2]
  have l5 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [l4 X0 sK0 sK3 sK2]
    conv => enter [1, 2]; rw [l0 sK3 sK3 sK0]
  have l6 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l5 X0 X0 sK3 sK2]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK3 X0]
  have l7 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [l6 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [← l6 X1 sK1 sK2 sK3]
  have l8 : ∀ sK2 sK0 sK3 X0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK0 sK3 X0 sK1
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l7 sK2 sK1 sK2 sK3 X0]
  have l9 : ∀ sK3 X0 X1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK3]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ sK3)]
  have l10 : ∀ sK3 X0 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 sK0
    conv => enter [1]; rw [l9 sK3 X0 sK3]
    conv => enter [1, 2]; rw [l0 sK3 sK3 sK0]
  have l11 : ∀ sK3 X0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 X0 sK1 sK2
    conv => enter [1]; rw [l10 sK3 X0 sK3]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK3 sK3]
  have l12 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ (sK3 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [l8 sK2 sK0 sK3 sK2 sK2]
    conv => enter [1]; rw [← l11 sK3 sK2 sK2 sK2]
  have l13 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK3)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l0 sK0 sK3 sK3]
    conv => enter [1]; rw [← l12 sK2 sK0 sK3]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l13 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l14 x y z w]

theorem Equation4512_54452_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54452 : Equation54452 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54452 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h54452 X1 sK0 sK0 X0]
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
  have l4 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [← h54452 X0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4278_4512_implies_Equation54462 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54462 G := by
  have l0 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ sK4)) = (X1 ◇ (sK0 ◇ sK4)) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4278 sK4 X0 sK0]
    conv => enter [1]; rw [h4278 sK4 X1 sK0]
  have l1 : ∀ sK1 sK0 sK4 : G, (sK1 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [← h4278 sK4 sK1 sK0]
  have l2 : ∀ X0 X1 sK0 sK4 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 X1 sK0 sK4 sK1
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK4) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK4) sK0 sK4 sK1]
  have l3 : ∀ X0 sK1 sK0 sK4 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK4 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK4 sK1]
  have l4 : ∀ sK1 sK0 sK4 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK4)) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK1 sK0 sK4 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 X1]
  have l5 : ∀ X0 sK1 sK0 sK4 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4 X1
    conv => enter [1]; rw [l3 X0 sK1 sK0 sK4]
    conv => enter [1]; rw [← l3 X1 sK1 sK0 sK4]
  have l6 : ∀ sK3 sK1 sK0 sK4 X0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK1 sK0 sK4 X0 sK2
    conv => enter [1]; rw [l5 sK3 sK1 sK0 sK4 X0]
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK4 sK2 sK3]
  have l7 : ∀ sK4 X0 X1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK4 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK4)]
  have l8 : ∀ sK4 X0 sK1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 sK1 sK0
    conv => enter [1]; rw [l7 sK4 X0 sK4 sK0]
    conv => enter [1, 2]; rw [l0 sK4 sK0 sK4 sK1]
  have l9 : ∀ sK4 X0 sK2 sK3 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK4 X0 sK2 sK3
    conv => enter [1]; rw [l8 sK4 X0 sK4 sK4]
    conv => enter [1, 2]; rw [l4 sK4 sK4 sK4 sK2 sK3]
  have l10 : ∀ sK3 sK1 sK0 sK4 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l6 sK3 sK1 sK0 sK4 sK3 sK3]
    conv => enter [1]; rw [← l9 sK4 sK3 sK3 sK3]
  have l11 : ∀ sK1 sK0 sK4 sK3 : G, (sK1 ◇ (sK0 ◇ sK4)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK1 sK0 sK4 sK3
    conv => enter [1]; rw [l1 sK1 sK0 sK4]
    conv => enter [1]; rw [← l10 sK3 sK1 sK0 sK4]
  have l12 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 sK4 sK3]
  intro x y z w u
  conv => enter [1]; rw [l12 x y z w u]

theorem Equation4512_54462_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54462 : Equation54462 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h54462 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← h54462 X3 sK0 sK0 X0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54462 X0 sK0 sK0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l2 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l0 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK0 sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X1 ◇ sK0)]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 sK0 X1]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54462 X0 X1 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l7 sK0 X0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X1]
    conv => enter [1]; rw [← l8 X0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4278_4512_implies_Equation54480 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54480 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK0]
    conv => enter [1]; rw [h4278 sK3 X1 sK0]
  have l1 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← h4278 sK3 sK1 sK0]
  have l2 : ∀ X0 X1 sK0 sK3 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK0 sK3 sK1
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 sK1]
  have l3 : ∀ X0 sK1 sK0 sK3 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK1 sK0 sK3
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK3 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK3 sK1]
  have l4 : ∀ sK1 sK0 sK3 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l5 : ∀ X0 sK1 sK0 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK1 sK0 sK3 X1
    conv => enter [1]; rw [l3 X0 sK1 sK0 sK3]
    conv => enter [1]; rw [← l3 X1 sK1 sK0 sK3]
  have l6 : ∀ sK3 sK1 sK0 X0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 sK1 sK0 X0 sK2
    conv => enter [1]; rw [l5 sK3 sK1 sK0 sK3 X0]
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK3 sK1 sK2]
  have l7 : ∀ sK3 X0 X1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK3)]
  have l8 : ∀ sK3 X0 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 sK1 sK0
    conv => enter [1]; rw [l7 sK3 X0 sK3 sK0]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK3 sK1]
  have l9 : ∀ sK3 X0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 X0 sK1 sK2
    conv => enter [1]; rw [l8 sK3 X0 sK1 sK3]
    conv => enter [1, 2]; rw [l4 sK1 sK3 sK3 sK1 sK2]
  have l10 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [l6 sK3 sK1 sK0 sK3 sK3]
    conv => enter [1]; rw [← l9 sK3 sK3 sK1 sK3]
  have l11 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l4 sK1 sK0 sK3 sK3 sK3]
    conv => enter [1]; rw [← l10 sK3 sK1 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation4512_54480_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54480 : Equation54480 G) : Equation4278 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54480 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54480 sK0 X1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l10 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54480 sK0 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l11 : ∀ sK1 X1 X0 sK2 sK0 : G, (sK1 ◇ (X1 ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 X1 X0 sK2 sK0
    conv => enter [1]; rw [h54480 sK1 X1 X0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK0) X0]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54480 (sK0 ◇ sK0) X1 X0 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l13 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (X2 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← h54480 X2 (X0 ◇ X1) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54480 X0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l7 sK2 sK0 sK0]
    conv => enter [1]; rw [h54480 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l16 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54480 sK0 X0 sK0 sK0]
  have l17 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 sK0]
    conv => enter [1]; rw [h54480 sK2 sK0 sK0 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h54480 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0]
  have l19 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l7 sK2 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54480 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 sK0]
  have l20 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l19 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l18 sK0]
  have l22 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l17 sK2 sK0]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 sK0]
  have l23 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l16 sK2 sK0 X0]
  have l24 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l15 sK2 sK0]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 sK0]
  have l25 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l14 sK0 X0]
    conv => enter [1]; rw [← h54480 X0 sK2 sK0 sK0]
  have l26 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← l14 sK0 X2]
    conv => enter [1]; rw [l13 sK0 X2 X0 X1]
  have l27 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l20 sK2 sK0 X0]
    conv => enter [1]; rw [h54480 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
  have l28 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l22 sK2 sK0]
    conv => enter [1]; rw [l10 sK0 (sK2 ◇ sK0) sK0]
  have l30 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l23 sK2 sK0 sK2]
    conv => enter [1]; rw [l8 (sK2 ◇ sK0) sK2 sK0]
  have l31 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l24 sK2 sK0]
    conv => enter [1]; rw [l10 sK0 (sK2 ◇ sK0) sK0]
  have l32 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l26 (sK2 ◇ sK0) sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [l27 sK2 sK0 sK2]
  have l33 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l28 sK0]
  have l34 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l29 sK2 sK0]
  have l35 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h54480 (sK2 ◇ sK0) sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l30 sK2 sK0]
  have l36 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l31 sK2 sK0]
  have l37 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l33 sK0]
  have l38 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l34 sK0 sK2]
  have l39 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l32 sK2 sK0]
    conv => enter [1]; rw [l35 sK0 sK2]
  have l40 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [l8 (sK2 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l37 sK0]
  have l42 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l38 sK0 sK2]
  have l43 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l40 sK0 sK2]
    conv => enter [1]; rw [← l39 sK2 sK0]
  have l44 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l43 sK0 sK2]
  have l45 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l44 sK0 sK2]
  have l46 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h54480 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [l25 sK1 sK0 sK2]
  have l47 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l42 sK0 sK2]
  have l48 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l47 sK1 sK2 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2 sK0]
  have l49 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l48 sK1 sK2 sK0]
    conv => enter [1]; rw [l46 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0)) sK0 sK1 sK2]
  have l50 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l45 sK0 sK2]
  have l51 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l50 sK1 sK2 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2 sK0]
  have l52 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l51 sK1 sK2 sK0]
    conv => enter [1]; rw [l46 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0)) sK0 sK1 sK2]
  have l53 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l49 sK1 sK2 sK0]
    conv => enter [1]; rw [← l52 sK1 sK2 sK0]
  have l54 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h54480 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l53 sK1 sK2 sK0]
  have l55 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l26 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l54 X0 X1 sK0 sK0 sK0]
  have l56 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l41 sK0]
    conv => enter [1]; rw [l55 sK0 X0 X1]
  have l57 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h54480 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l58 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l57 sK0]
    conv => enter [1]; rw [h54480 X0 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l59 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l56 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l58 X0 sK0]
  have l60 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54480 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l59 sK0 X0]
  have l61 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l61 x y z]

theorem Equation4278_4512_implies_Equation54497 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54497 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK0]
    conv => enter [1]; rw [h4278 sK3 X1 sK0]
  have l1 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [← h4278 sK3 sK2 sK0]
  have l2 : ∀ X0 X1 sK0 sK3 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK0 sK3 sK2
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 sK2]
  have l3 : ∀ X0 sK2 sK0 sK3 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK2 sK0 sK3
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK3 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK3 sK2]
  have l4 : ∀ sK2 sK0 sK3 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l5 : ∀ X0 sK2 sK0 sK3 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK2 sK0 sK3 X1
    conv => enter [1]; rw [l3 X0 sK2 sK0 sK3]
    conv => enter [1]; rw [← l3 X1 sK2 sK0 sK3]
  have l6 : ∀ sK3 sK2 sK0 X0 sK1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 sK2 sK0 X0 sK1
    conv => enter [1]; rw [l5 sK3 sK2 sK0 sK3 X0]
    conv => enter [1, 2]; rw [l4 sK2 sK0 sK3 sK1 sK2]
  have l7 : ∀ sK3 X0 X1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK3)]
  have l8 : ∀ sK3 X0 sK2 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 sK2 sK0
    conv => enter [1]; rw [l7 sK3 X0 sK3 sK0]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK3 sK2]
  have l9 : ∀ sK3 X0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 X0 sK1 sK2
    conv => enter [1]; rw [l8 sK3 X0 sK2 sK3]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK3 sK1 sK2]
  have l10 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [l6 sK3 sK2 sK0 sK3 sK3]
    conv => enter [1]; rw [← l9 sK3 sK3 sK3 sK2]
  have l11 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [l4 sK2 sK0 sK3 sK3 sK3]
    conv => enter [1]; rw [← l10 sK3 sK2 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK2 sK0]
    conv => enter [1]; rw [l11 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation4512_54497_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54497 : Equation54497 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54497 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54497 X1 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l5 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [h54497 X0 sK2 sK0 X1]
    conv => enter [1, 2]; rw [l3 sK2 X1 sK0]
  have l6 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [l5 X0 sK2 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l7 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [l6 X1 sK2 sK0 X1]
    conv => enter [1]; rw [← l6 X0 sK2 sK0 X1]
  have l8 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l6 X0 sK2 sK0 sK0]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l1 sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l7 sK0 sK2 sK0 X0]
  have l10 : ∀ X0 sK2 sK0 X1 X2 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0 X1 X2
    conv => enter [1]; rw [l7 X0 sK2 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK0)]
  have l11 : ∀ X0 sK2 sK0 X1 sK1 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0 X1 sK1
    conv => enter [1]; rw [l10 X0 sK2 sK0 X1 X0]
    conv => enter [1, 2]; rw [l7 X0 sK2 sK0 sK1]
  have l12 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l9 sK0 sK2 sK0]
    conv => enter [1, 2]; rw [l7 sK0 sK2 sK0 sK1]
  have l13 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l11 sK1 sK2 sK0 X1 sK1]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [l12 sK0 sK2 sK1]
  have l15 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2]
  have l16 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l15 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l15 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l18 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l16 sK2 sK1 sK0]
    conv => enter [1]; rw [l4 (sK2 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l18 sK2 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK0 sK2]
    conv => enter [1]; rw [l19 sK2 sK1 sK0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54497 X0 sK0 sK0 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54497 X0 (sK0 ◇ sK0) sK0 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l24 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK0]
    conv => enter [1]; rw [← l23 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  have l25 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l24 sK1 sK2 sK0]
    conv => enter [1]; rw [← l21 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l25 sK1 sK2 sK0]
    conv => enter [1]; rw [h54497 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l27 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l26 sK1 sK2 sK0]
    conv => enter [1]; rw [← h54497 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l27 y z x x]

theorem Equation4278_4512_implies_Equation54519 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54519 G := by
  have l0 : ∀ X0 sK0 sK1 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK0 sK1 sK3 X1
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK3) X0 sK0]
    conv => enter [1]; rw [h4278 (sK1 ◇ sK3) X1 sK0]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ sK3) ◇ ((sK1 ◇ sK3) ◇ (sK1 ◇ sK3))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK3) sK3 sK0]
  have l2 : ∀ sK3 sK0 sK1 X0 X1 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK1]
    conv => enter [1]; rw [h4278 (sK1 ◇ sK3) X0 X1]
  have l3 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK1]
    conv => enter [1]; rw [h4278 sK3 X1 sK1]
  have l4 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [← h4278 sK3 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK3 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK0 sK1 sK3 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l6 : ∀ sK3 X0 X1 sK1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) := by
    intro sK3 X0 X1 sK1
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK3)]
  have l7 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l2 sK3 sK0 sK1 sK3 sK3]
    conv => enter [1]; rw [← l6 sK3 sK3 sK3 sK1]
  have l8 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ sK3)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l5 sK0 sK1 sK3 sK3 sK3]
    conv => enter [1]; rw [← l7 sK3 sK0 sK1]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

theorem Equation4512_54519_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54519 : Equation54519 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54519 sK0 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54519 sK0 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h54519 X0 X1 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4278_4512_implies_Equation54539 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54539 G := by
  have l0 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ sK4)) = (X1 ◇ (sK0 ◇ sK4)) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4278 sK4 X0 sK0]
    conv => enter [1]; rw [h4278 sK4 X1 sK0]
  have l1 : ∀ sK1 sK0 sK4 : G, (sK1 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [← h4278 sK4 sK1 sK0]
  have l2 : ∀ X0 X1 sK0 sK4 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 X1 sK0 sK4 sK1
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK4) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK4) sK0 sK4 sK1]
  have l3 : ∀ X0 sK1 sK0 sK4 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK4 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK4 sK1]
  have l4 : ∀ sK1 sK0 sK4 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK4)) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK1 sK0 sK4 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 X1]
  have l5 : ∀ X0 sK1 sK0 sK4 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4 X1
    conv => enter [1]; rw [l3 X0 sK1 sK0 sK4]
    conv => enter [1]; rw [← l3 X1 sK1 sK0 sK4]
  have l6 : ∀ sK4 sK1 sK0 X0 sK2 sK3 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK4 sK1 sK0 X0 sK2 sK3
    conv => enter [1]; rw [l5 sK4 sK1 sK0 sK4 X0]
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK4 sK2 sK3]
  have l7 : ∀ sK4 X0 X1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK4 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK4)]
  have l8 : ∀ sK4 X0 sK1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 sK1 sK0
    conv => enter [1]; rw [l7 sK4 X0 sK4 sK0]
    conv => enter [1, 2]; rw [l0 sK4 sK0 sK4 sK1]
  have l9 : ∀ sK4 X0 sK2 sK3 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK4 X0 sK2 sK3
    conv => enter [1]; rw [l8 sK4 X0 sK4 sK4]
    conv => enter [1, 2]; rw [l4 sK4 sK4 sK4 sK2 sK3]
  have l10 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l6 sK4 sK1 sK0 sK4 sK4 sK4]
    conv => enter [1]; rw [← l9 sK4 sK4 sK4 sK4]
  have l11 : ∀ sK1 sK0 sK4 : G, (sK1 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [l4 sK1 sK0 sK4 sK4 sK4]
    conv => enter [1]; rw [← l10 sK4 sK1 sK0]
  have l12 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l12 x y z w u]

@[equational_result]
theorem Equation54539_implies_Equation4278 (G : Type*) [Magma G] (h54539 : Equation54539 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h54539 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← h54539 X3 sK0 sK0 X0 X0]
  have l1 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h54539 X1 X2 sK0 X1 X1]
    conv => enter [1]; rw [← h54539 X0 sK0 sK0 X1 X1]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l1 X0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4278_4512_implies_Equation54555 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54555 G := by
  have l0 : ∀ sK1 sK3 X0 : G, (sK1 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK3 X0
    conv => enter [1]; rw [← h4278 sK3 sK1 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 sK3]
  have l1 : ∀ sK1 sK3 X0 sK2 : G, (sK1 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK3 X0 sK2
    conv => enter [1]; rw [l0 sK1 sK3 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 sK2]
  have l2 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [← h4278 sK3 (sK2 ◇ sK3) sK2]
  have l3 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4278 sK3 sK1 sK2]
    conv => enter [1]; rw [l0 sK3 sK3 sK1]
  have l4 : ∀ X0 X1 sK2 sK3 sK1 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK3 ◇ sK3))) := by
    intro X0 X1 sK2 sK3 sK1
    conv => enter [1]; rw [l2 X0 X1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK3 sK3 sK1]
  have l5 : ∀ X0 X1 sK2 sK3 sK1 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 X1 sK2 sK3 sK1
    conv => enter [1]; rw [l4 X0 X1 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK3]
  have l6 : ∀ X0 sK1 sK3 sK2 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK3 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK3 X0 sK2]
    conv => enter [1]; rw [l5 X0 X0 sK2 sK3 sK1]
  have l7 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3]
    conv => enter [1]; rw [l6 X0 sK1 sK3 sK2]
  have l8 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK3]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 sK3]
  have l9 : ∀ sK0 sK1 sK3 X0 X1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK1 sK3 X0 X1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK3 sK2]
    conv => enter [1]; rw [← l5 X0 X1 sK2 sK3 sK1]
  have l10 : ∀ sK0 sK1 sK3 X0 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK3 ◇ sK3))) := by
    intro sK0 sK1 sK3 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK3 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← l1 sK1 sK3 sK0 sK0]
  have l11 : ∀ sK0 sK1 sK3 X0 sK2 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK1 sK3 X0 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK3 X0]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK3]
  have l12 : ∀ sK3 X0 X1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK3]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ sK3)]
  have l13 : ∀ sK3 X0 sK1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 sK1
    conv => enter [1]; rw [l12 sK3 X0 sK3]
    conv => enter [1, 2]; rw [l0 sK3 sK3 sK1]
  have l14 : ∀ sK3 X0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 X0 sK1 sK2
    conv => enter [1]; rw [l13 sK3 X0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK3]
  have l15 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l11 sK0 sK1 sK3 sK0 sK0]
    conv => enter [1]; rw [← l14 sK3 sK0 sK1 sK0]
  have l16 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ sK3)) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK3))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK3]
    conv => enter [1]; rw [← l15 sK0 sK1 sK3]
  have l17 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3]
    conv => enter [1]; rw [l16 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l17 x y z w]

theorem Equation4512_54555_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54555 : Equation54555 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [h54555 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h54555 X1 X0 (sK0 ◇ sK0) X2]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h54555 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l0 X0 sK0 X2 X0]
    conv => enter [1, 2]; rw [← h54555 (sK0 ◇ sK0) sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54555 (sK0 ◇ sK0) sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 X0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54555 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h54555 X0 sK2 sK0 X0]
  have l6 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [l5 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4278_4512_implies_Equation54565 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54565 G := by
  have l0 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ sK4)) = (X1 ◇ (sK0 ◇ sK4)) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4278 sK4 X0 sK0]
    conv => enter [1]; rw [h4278 sK4 X1 sK0]
  have l1 : ∀ sK2 sK0 sK4 : G, (sK2 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK2 sK0 sK4
    conv => enter [1]; rw [← h4278 sK4 sK2 sK0]
  have l2 : ∀ X0 X1 sK0 sK4 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK2 ◇ (sK0 ◇ sK4))) := by
    intro X0 X1 sK0 sK4 sK2
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK4) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK4) sK0 sK4 sK2]
  have l3 : ∀ X0 sK2 sK0 sK4 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK2 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK2 sK0 sK4
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK4 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK4 sK2]
  have l4 : ∀ sK2 sK0 sK4 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK4)) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK2 sK0 sK4 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 X1]
  have l5 : ∀ sK1 sK2 sK0 sK4 X0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK4))) := by
    intro sK1 sK2 sK0 sK4 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 sK4]
    conv => enter [1]; rw [← l3 X0 sK2 sK0 sK4]
  have l6 : ∀ sK4 X0 X1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK4 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK4)]
  have l7 : ∀ sK4 X0 sK2 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 sK2 sK0
    conv => enter [1]; rw [l6 sK4 X0 sK4 sK0]
    conv => enter [1, 2]; rw [l0 sK4 sK0 sK4 sK2]
  have l8 : ∀ sK1 sK2 sK0 sK4 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK4))) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK2 sK0 sK4
    conv => enter [1]; rw [← l7 sK4 sK1 sK2 sK0]
  have l9 : ∀ sK2 sK0 sK4 sK1 : G, (sK2 ◇ (sK0 ◇ sK4)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK0 sK4 sK1
    conv => enter [1]; rw [l1 sK2 sK0 sK4]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0 sK4]
  have l10 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK3 sK4 sK2 sK0]
    conv => enter [1]; rw [l9 sK2 sK0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l10 x y z w u]

theorem Equation4512_54565_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54565 : Equation54565 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54565 X0 (sK0 ◇ sK0) sK0 X1 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54565 sK0 sK0 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [h54565 sK0 (sK0 ◇ sK0) sK0 X0 sK0]
  have l3 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l0 X0 sK0 X0]
    conv => enter [1]; rw [← h54565 X0 sK2 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l3 sK1 sK0 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l6 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4278_4512_implies_Equation54571 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54571 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK1]
    conv => enter [1]; rw [h4278 sK3 X1 sK1]
  have l1 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [← h4278 sK3 sK2 sK1]
  have l2 : ∀ X0 X1 sK1 sK3 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ sK3) ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro X0 X1 sK1 sK3 sK2
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 sK2]
  have l3 : ∀ X0 sK2 sK1 sK3 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ sK3) ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK2 sK1 sK3
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK3 X0]
    conv => enter [1]; rw [l2 X0 X0 sK1 sK3 sK2]
  have l4 : ∀ sK2 sK1 sK3 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK1 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l5 : ∀ sK0 sK2 sK1 sK3 X0 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK0 sK2 sK1 sK3 X0
    conv => enter [1]; rw [l3 sK0 sK2 sK1 sK3]
    conv => enter [1]; rw [← l3 X0 sK2 sK1 sK3]
  have l6 : ∀ sK3 X0 X1 sK1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) := by
    intro sK3 X0 X1 sK1
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK3)]
  have l7 : ∀ sK3 X0 sK2 sK1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK3 X0 sK2 sK1
    conv => enter [1]; rw [l6 sK3 X0 sK3 sK1]
    conv => enter [1, 2]; rw [l0 sK3 sK1 sK3 sK2]
  have l8 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [← l7 sK3 sK0 sK2 sK1]
  have l9 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 sK3 sK3]
    conv => enter [1]; rw [← l8 sK0 sK2 sK1 sK3]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK2 sK1]
    conv => enter [1]; rw [l9 sK2 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

theorem Equation4512_54571_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54571 : Equation54571 G) : Equation4278 G := by
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
  have l7 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l8 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (sK2 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ X0) X1]
  have l9 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (sK2 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l8 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l10 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l9 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h54571 X0 sK0 X1 sK2]
  have l11 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l10 sK2 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l13 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← h54571 X0 sK0 X1 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l16 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK2 sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l7 sK2 sK0 (sK0 ◇ X0)]
  have l17 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) ◇ X1) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 sK2 ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l7 sK2 sK0 X0]
  have l18 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l17 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ X0) X1]
  have l19 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54571 sK0 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l16 sK2 sK0 X0]
  have l20 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l18 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l21 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l19 sK0 X0 sK2]
  have l22 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ (sK0 ◇ X1)) = (sK2 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [h54571 X0 sK0 X1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l20 sK2 sK0 X0 X1]
  have l23 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ (sK0 ◇ X1)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [l22 X0 sK0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l24 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l23 X0 sK0 X1 X0]
    conv => enter [1]; rw [← h54571 X0 (sK0 ◇ sK0) X1 X0]
  have l25 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK0 sK2]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l26 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [l4 sK0]
  have l27 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l26 sK0 sK2]
    conv => enter [1]; rw [← l24 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l25 sK0 sK2]
    conv => enter [1]; rw [← l11 sK2 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l27 sK0 sK2]
    conv => enter [1]; rw [← l11 sK2 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l28 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l31 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l29 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l30 sK0 sK2]
    conv => enter [1, 2]; rw [l11 sK2 sK0 sK0 sK0]
  have l33 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l31 sK0 sK2]
    conv => enter [1, 2]; rw [l11 sK2 sK0 sK0 sK0]
  have l34 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l32 sK0 sK2]
    conv => enter [1]; rw [← l15 sK0 (sK2 ◇ sK0) (sK0 ◇ sK0)]
  have l35 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [← l15 sK0 (sK2 ◇ sK0) (sK0 ◇ sK0)]
  have l36 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l34 sK0 sK2]
  have l37 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l35 sK0 sK2]
  have l38 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l36 sK0 sK0]
    conv => enter [1]; rw [← l37 sK0 sK0]
  have l39 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l38 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l38 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [l39 sK0]
  have l42 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l41 sK0]
    conv => enter [1]; rw [← l7 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l41 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l44 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [l43 sK0]
  have l45 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l11 sK2 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l42 sK2 sK0]
  have l46 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l47 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l46 sK0 sK2]
  have l48 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l41 sK0]
    conv => enter [1]; rw [l47 sK0 sK2]
  have l49 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l44 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l50 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l49 sK0 X0]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l51 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l15 sK0 sK0 X0]
    conv => enter [1]; rw [← l50 sK0 X0]
  have l52 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l51 sK0 X0]
  have l53 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l48 sK0 sK2]
  have l54 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l55 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l54 sK0 X0 sK2]
    conv => enter [1]; rw [← l52 sK0 (((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l56 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l55 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ sK0) X0]
  have l57 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l56 sK0 X0 sK2]
    conv => enter [1]; rw [← h54571 (sK0 ◇ sK0) (sK2 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l58 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l52 sK0 X0]
    conv => enter [1]; rw [l57 sK0 X0 sK2]
  have l59 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l52 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0]
  have l60 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l41 sK0]
    conv => enter [1]; rw [← l59 sK0]
  have l61 : ∀ sK0 X1 X0 X2 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ X0))) = (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [h54571 sK0 X1 (sK0 ◇ X0) X2]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l62 : ∀ sK1 X1 sK2 sK0 X0 X2 : G, (sK1 ◇ (X1 ◇ ((sK2 ◇ sK0) ◇ X0))) = (X2 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0))) := by
    intro sK1 X1 sK2 sK0 X0 X2
    conv => enter [1]; rw [h54571 sK1 X1 ((sK2 ◇ sK0) ◇ X0) X2]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK2 ◇ sK0) X0]
  have l63 : ∀ X2 X1 sK0 X0 sK2 : G, (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK2 ◇ sK0) ◇ X0))) := by
    intro X2 X1 sK0 X0 sK2
    conv => enter [1, 2, 2]; rw [l58 sK0 X0 sK2]
    conv => enter [1]; rw [← h54571 (sK0 ◇ sK0) X1 ((sK2 ◇ sK0) ◇ X0) X2]
  have l64 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54571 sK0 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l65 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [← h54571 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l66 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK2 ◇ sK0) ◇ X1)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54571 X0 (sK2 ◇ sK0) X1 sK1]
  have l67 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54571 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l40 sK0 (X1 ◇ (X0 ◇ X2))]
    conv => enter [1, 2]; rw [← h54571 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
  have l68 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l67 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54571 X1 X0 X2 X0]
  have l69 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l65 X0 sK0 X0]
    conv => enter [1]; rw [l11 X0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l70 : ∀ X2 X1 sK0 X0 sK2 : G, (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK2 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro X2 X1 sK0 X0 sK2
    conv => enter [1]; rw [l63 X2 X1 sK0 X0 sK2]
    conv => enter [1]; rw [← h54571 (sK2 ◇ sK0) X1 X0 (sK0 ◇ sK0)]
  have l71 : ∀ sK1 X1 sK2 sK0 X0 : G, (sK1 ◇ (X1 ◇ ((sK2 ◇ sK0) ◇ X0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK1 X1 sK2 sK0 X0
    conv => enter [1]; rw [l62 sK1 X1 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [← h54571 (sK1 ◇ (sK2 ◇ sK0)) X1 X0 sK1]
  have l72 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l61 sK0 X1 X0 sK0]
    conv => enter [1]; rw [← h54571 (sK0 ◇ sK0) X1 X0 sK0]
  have l73 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l69 X0 sK0]
  have l74 : ∀ sK0 X1 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = ((sK2 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0 sK2
    conv => enter [1]; rw [h54571 (sK0 ◇ sK0) X1 X0 sK0]
    conv => enter [1]; rw [l70 sK0 X1 sK0 X0 sK2]
  have l75 : ∀ sK2 sK0 X1 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK2 sK0 X1 X0 sK1
    conv => enter [1]; rw [h54571 (sK2 ◇ sK0) X1 X0 sK1]
    conv => enter [1]; rw [l71 sK1 X1 sK2 sK0 X0]
  have l76 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l72 sK0 X1 X0]
    conv => enter [1]; rw [← h54571 sK0 X1 X0 sK0]
  have l77 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l40 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l73 sK0 X0]
  have l78 : ∀ sK0 X1 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 X1 X0 sK2]
    conv => enter [1]; rw [l75 sK2 sK0 X1 X0 sK1]
  have l79 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l52 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l77 sK0 X0]
  have l80 : ∀ sK0 X1 X0 sK1 sK2 : G, (sK0 ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0 sK1 sK2
    conv => enter [1]; rw [← l76 sK0 X1 X0]
    conv => enter [1]; rw [l78 sK0 X1 X0 sK1 sK2]
  have l81 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l60 sK0]
    conv => enter [1]; rw [l79 sK0 X0]
  have l82 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l57 sK0 X0 sK2]
    conv => enter [1]; rw [l76 sK0 (sK2 ◇ sK0) X0]
  have l83 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l52 sK0 X0]
    conv => enter [1]; rw [l82 sK0 X0 sK2]
  have l84 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [← l64 sK0 X0 (sK2 ◇ sK0)]
  have l85 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l84 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l68 sK1 (sK0 ◇ sK0) X0]
  have l86 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l85 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l76 sK0 sK1 X0]
  have l87 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [← l66 sK1 sK2 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l86 sK1 sK2 sK0 X0]
  have l88 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [← l76 sK0 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [l87 sK0 sK2 X0 sK1]
  have l89 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l83 sK0 X0 sK0]
    conv => enter [1]; rw [l88 sK0 sK0 X0 sK1]
  have l90 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l89 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← l53 sK1 sK2 sK0]
  have l91 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l90 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54571 sK0 (sK1 ◇ (sK2 ◇ sK0)) sK0 sK0]
  have l92 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0]
    conv => enter [1]; rw [l91 sK0 sK1 sK2]
  have l93 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l92 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54571 sK0 X0 ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) X1]
  have l94 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [l93 X1 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54571 (sK1 ◇ (sK2 ◇ sK0)) X0 sK0 sK0]
  have l95 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l80 sK0 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l94 X1 X0 sK0 sK0 sK0]
  have l96 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l95 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l81 sK0 X0]
  have l97 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l81 sK0 sK0]
    conv => enter [1]; rw [← l96 sK0 X0 sK0]
  have l98 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l97 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l99 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l98 sK0 X0 X1]
    conv => enter [1]; rw [← h54571 X1 X0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l99 x y z]

theorem Equation4278_4512_implies_Equation54581 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54581 G := by
  have l0 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4278 sK3 sK2 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 sK3]
  have l1 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l0 sK2 sK3 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 sK2]
  have l2 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [← h4278 sK3 (sK2 ◇ sK3) sK2]
  have l3 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4278 sK3 sK1 sK2]
    conv => enter [1]; rw [l0 sK3 sK3 sK2]
  have l4 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l2 X0 X1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK3 sK3 sK2]
  have l5 : ∀ X0 X1 sK2 sK3 sK1 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 X1 sK2 sK3 sK1
    conv => enter [1]; rw [l4 X0 X1 sK2 sK3]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK3]
  have l6 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1, 2]; rw [l1 sK2 sK3 X0]
    conv => enter [1]; rw [l5 X0 X0 sK2 sK3 sK1]
  have l7 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3]
    conv => enter [1]; rw [l6 X0 sK2 sK3 sK1]
  have l8 : ∀ sK0 sK2 sK3 sK1 : G, (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK3]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 sK3]
  have l9 : ∀ sK0 sK2 sK3 X0 X1 : G, (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3 X0 X1
    conv => enter [1]; rw [l8 sK0 sK2 sK3 sK0]
    conv => enter [1]; rw [← l5 X0 X1 sK2 sK3 sK0]
  have l10 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [l9 sK0 sK2 sK3 X0 sK0]
    conv => enter [1, 2]; rw [← l1 sK2 sK3 sK0]
  have l11 : ∀ sK0 sK2 sK3 X0 sK1 : G, (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3 X0 sK1
    conv => enter [1]; rw [l10 sK0 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK3]
  have l12 : ∀ sK3 X0 X1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK3]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ sK3)]
  have l13 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [l12 sK3 X0 sK3]
    conv => enter [1, 2]; rw [l0 sK3 sK3 sK2]
  have l14 : ∀ sK3 X0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 X0 sK1 sK2
    conv => enter [1]; rw [l13 sK3 X0 sK2]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK3]
  have l15 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l11 sK0 sK2 sK3 sK0 sK0]
    conv => enter [1]; rw [← l14 sK3 sK0 sK0 sK2]
  have l16 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK3]
    conv => enter [1]; rw [← l15 sK0 sK2 sK3]
  have l17 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3]
    conv => enter [1]; rw [l16 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l17 x y z w]

theorem Equation4512_54581_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54581 : Equation54581 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [← h54581 (X1 ◇ X2) sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h54581 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 X1 X2]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK2]
    conv => enter [1]; rw [← h54581 X0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4278_4512_implies_Equation54591 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54591 G := by
  have l0 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ sK4)) = (X1 ◇ (sK0 ◇ sK4)) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4278 sK4 X0 sK0]
    conv => enter [1]; rw [h4278 sK4 X1 sK0]
  have l1 : ∀ sK3 sK0 sK4 : G, (sK3 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK3 sK0 sK4
    conv => enter [1]; rw [← h4278 sK4 sK3 sK0]
  have l2 : ∀ X0 X1 sK0 sK4 sK3 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK3 ◇ (sK0 ◇ sK4))) := by
    intro X0 X1 sK0 sK4 sK3
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK4) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK4) sK0 sK4 sK3]
  have l3 : ∀ X0 sK3 sK0 sK4 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK3 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK3 sK0 sK4
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK4 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK4 sK3]
  have l4 : ∀ sK3 sK0 sK4 X0 X1 : G, (sK3 ◇ (sK0 ◇ sK4)) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK3 sK0 sK4 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 X1]
  have l5 : ∀ sK1 sK3 sK0 sK4 X0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK4))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK4))) := by
    intro sK1 sK3 sK0 sK4 X0
    conv => enter [1]; rw [l3 sK1 sK3 sK0 sK4]
    conv => enter [1]; rw [← l3 X0 sK3 sK0 sK4]
  have l6 : ∀ sK4 X0 X1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK4 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK4)]
  have l7 : ∀ sK4 X0 sK3 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 sK3 sK0
    conv => enter [1]; rw [l6 sK4 X0 sK4 sK0]
    conv => enter [1, 2]; rw [l0 sK4 sK0 sK4 sK3]
  have l8 : ∀ sK1 sK3 sK0 sK4 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK4))) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK3 sK0 sK4
    conv => enter [1]; rw [← l7 sK4 sK1 sK3 sK0]
  have l9 : ∀ sK3 sK0 sK4 sK1 : G, (sK3 ◇ (sK0 ◇ sK4)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK4))) := by
    intro sK3 sK0 sK4 sK1
    conv => enter [1]; rw [l1 sK3 sK0 sK4]
    conv => enter [1]; rw [← l8 sK1 sK3 sK0 sK4]
  have l10 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK3 sK4 sK3 sK0]
    conv => enter [1]; rw [l9 sK3 sK0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l10 x y z w u]

theorem Equation4512_54591_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54591 : Equation54591 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h54591 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← h54591 X3 sK0 sK0 X0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54591 X0 sK0 sK0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l2 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [l1 X2 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 sK0 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X1 sK0]
    conv => enter [1]; rw [← h54591 X0 X1 sK0 (sK0 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4278_4512_implies_Equation54597 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54597 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK1]
    conv => enter [1]; rw [h4278 sK3 X1 sK1]
  have l1 : ∀ sK3 sK1 : G, (sK3 ◇ (sK1 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK1
    conv => enter [1]; rw [← h4278 sK3 sK3 sK1]
  have l2 : ∀ X0 X1 sK1 sK3 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ sK3) ◇ (sK3 ◇ (sK1 ◇ sK3))) := by
    intro X0 X1 sK1 sK3
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 sK3]
  have l3 : ∀ X0 sK3 sK1 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ sK3) ◇ (sK3 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK3 sK1
    conv => enter [1, 2]; rw [l0 sK3 sK1 sK3 X0]
    conv => enter [1]; rw [l2 X0 X0 sK1 sK3]
  have l4 : ∀ sK3 sK1 X0 X1 : G, (sK3 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK3 sK1 X0 X1
    conv => enter [1]; rw [l1 sK3 sK1]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l5 : ∀ sK0 sK3 sK1 X0 : G, (sK0 ◇ (sK3 ◇ (sK1 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK3))) := by
    intro sK0 sK3 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK3 sK1]
    conv => enter [1]; rw [← l3 X0 sK3 sK1]
  have l6 : ∀ sK3 X0 X1 sK1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) := by
    intro sK3 X0 X1 sK1
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK3)]
  have l7 : ∀ sK3 X0 sK1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK3))) := by
    intro sK3 X0 sK1
    conv => enter [1]; rw [l6 sK3 X0 sK3 sK1]
  have l8 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ (sK3 ◇ (sK1 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [← l7 sK3 sK0 sK1]
  have l9 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ sK3)) = (sK0 ◇ (sK3 ◇ (sK1 ◇ sK3))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [l4 sK3 sK1 sK3 sK3]
    conv => enter [1]; rw [← l8 sK0 sK3 sK1]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK3 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l4 sK3 sK1 sK1 sK2]
    conv => enter [1]; rw [l9 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

theorem Equation4512_54597_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54597 : Equation54597 G) : Equation4278 G := by
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
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54597 sK0 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54597 X0 X1 sK0 sK0]
  have l7 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h54597 X0 X1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (X0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54597 X0 X1 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l7 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← l8 sK0 (sK2 ◇ sK0) X0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ sK0)]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l11 X0 X1 sK0]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l15 sK0 X0 X1]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l19 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 sK2 sK0]
  have l20 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← l16 sK0 X0 sK2]
    conv => enter [1]; rw [← l10 sK0 sK2 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l19 sK0 sK2]
    conv => enter [1]; rw [← l20 X0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l21 x y z]

theorem Equation4278_4512_implies_Equation54617 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54617 G := by
  have l0 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ sK4)) = (X1 ◇ (sK0 ◇ sK4)) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4278 sK4 X0 sK0]
    conv => enter [1]; rw [h4278 sK4 X1 sK0]
  have l1 : ∀ sK4 sK0 : G, (sK4 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK4 sK0
    conv => enter [1]; rw [← h4278 sK4 sK4 sK0]
  have l2 : ∀ X0 X1 sK0 sK4 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK4 ◇ (sK0 ◇ sK4))) := by
    intro X0 X1 sK0 sK4
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK4) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK4) sK0 sK4 sK4]
  have l3 : ∀ X0 sK4 sK0 : G, (X0 ◇ (sK4 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK4 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK4 sK0
    conv => enter [1, 2]; rw [l0 sK4 sK0 sK4 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK4]
  have l4 : ∀ sK4 sK0 X0 X1 : G, (sK4 ◇ (sK0 ◇ sK4)) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK4 sK0 X0 X1
    conv => enter [1]; rw [l1 sK4 sK0]
    conv => enter [1]; rw [h4278 sK4 X0 X1]
  have l5 : ∀ sK1 sK4 sK0 X0 : G, (sK1 ◇ (sK4 ◇ (sK0 ◇ sK4))) = (X0 ◇ (sK4 ◇ (sK0 ◇ sK4))) := by
    intro sK1 sK4 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK4 sK0]
    conv => enter [1]; rw [← l3 X0 sK4 sK0]
  have l6 : ∀ sK4 X0 X1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK4 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK4)]
  have l7 : ∀ sK4 X0 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK4 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 sK0
    conv => enter [1]; rw [l6 sK4 X0 sK4 sK0]
  have l8 : ∀ sK1 sK4 sK0 : G, (sK1 ◇ (sK4 ◇ (sK0 ◇ sK4))) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK4 sK0
    conv => enter [1]; rw [← l7 sK4 sK1 sK0]
  have l9 : ∀ sK4 sK0 sK1 : G, (sK4 ◇ (sK0 ◇ sK4)) = (sK1 ◇ (sK4 ◇ (sK0 ◇ sK4))) := by
    intro sK4 sK0 sK1
    conv => enter [1]; rw [l1 sK4 sK0]
    conv => enter [1]; rw [← l8 sK1 sK4 sK0]
  have l10 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK1 ◇ (sK4 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l4 sK4 sK0 sK2 sK3]
    conv => enter [1]; rw [l9 sK4 sK0 sK1]
  intro x y z w u
  conv => enter [1]; rw [l10 x y z w u]

theorem Equation4512_54617_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54617 : Equation54617 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54617 sK0 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54617 sK1 sK2 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4278_4512_implies_Equation54649 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54649 G := by
  have l0 : ∀ X0 sK0 sK2 sK4 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK4))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK4))) := by
    intro X0 sK0 sK2 sK4 X1
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK4) X0 sK0]
    conv => enter [1]; rw [h4278 (sK2 ◇ sK4) X1 sK0]
  have l1 : ∀ sK1 sK0 sK2 sK4 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK4))) = ((sK2 ◇ sK4) ◇ ((sK2 ◇ sK4) ◇ (sK2 ◇ sK4))) := by
    intro sK1 sK0 sK2 sK4
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK4) sK1 sK0]
  have l2 : ∀ sK1 sK0 sK2 sK4 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK4))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK4))) := by
    intro sK1 sK0 sK2 sK4 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK4]
    conv => enter [1]; rw [h4278 (sK2 ◇ sK4) X0 X1]
  have l3 : ∀ X0 sK2 sK4 X1 : G, (X0 ◇ (sK2 ◇ sK4)) = (X1 ◇ (sK2 ◇ sK4)) := by
    intro X0 sK2 sK4 X1
    conv => enter [1]; rw [← h4278 sK4 X0 sK2]
    conv => enter [1]; rw [h4278 sK4 X1 sK2]
  have l4 : ∀ sK0 sK2 sK4 : G, (sK0 ◇ (sK2 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK0 sK2 sK4
    conv => enter [1]; rw [← h4278 sK4 sK0 sK2]
  have l5 : ∀ sK0 sK2 sK4 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK4)) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK0 sK2 sK4 X0 X1
    conv => enter [1]; rw [l4 sK0 sK2 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 X1]
  have l6 : ∀ sK4 X0 X1 sK2 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK4))) := by
    intro sK4 X0 X1 sK2
    conv => enter [1]; rw [h4278 sK4 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK4)]
  have l7 : ∀ sK1 sK0 sK2 sK4 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK4))) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK0 sK2 sK4
    conv => enter [1]; rw [l2 sK1 sK0 sK2 sK4 sK1 sK1]
    conv => enter [1]; rw [← l6 sK4 sK1 sK1 sK2]
  have l8 : ∀ sK0 sK2 sK4 sK1 : G, (sK0 ◇ (sK2 ◇ sK4)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK4))) := by
    intro sK0 sK2 sK4 sK1
    conv => enter [1]; rw [l4 sK0 sK2 sK4]
    conv => enter [1]; rw [← l7 sK1 sK0 sK2 sK4]
  have l9 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK3 sK4 sK0 sK2]
    conv => enter [1]; rw [l8 sK0 sK2 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l9 x y z w u]

theorem Equation4512_54649_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54649 : Equation54649 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54649 sK0 sK0 sK0 X0 X1]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54649 sK0 X0 sK0 sK0 sK0]
  have l3 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro X2 sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h54649 X0 X1 sK0 X2 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4278_4512_implies_Equation54661 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54661 G := by
  have l0 : ∀ sK0 sK4 X0 : G, (sK0 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK4 ◇ sK4)) := by
    intro sK0 sK4 X0
    conv => enter [1]; rw [← h4278 sK4 sK0 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 sK4]
  have l1 : ∀ sK0 sK4 X0 sK3 : G, (sK0 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK0 sK4 X0 sK3
    conv => enter [1]; rw [l0 sK0 sK4 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 sK3]
  have l2 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ sK4) ◇ ((sK3 ◇ sK4) ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK4 ◇ (sK4 ◇ sK4))) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [h4278 (sK3 ◇ sK4) X0 sK3]
    conv => enter [1, 2]; rw [← h4278 sK4 sK3 sK3]
  have l3 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK0 ◇ (sK4 ◇ sK4)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h4278 sK4 sK2 sK3]
    conv => enter [1]; rw [l0 sK4 sK4 sK0]
  have l4 : ∀ X0 sK0 sK4 sK3 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK4))) = ((sK3 ◇ sK4) ◇ ((sK3 ◇ sK4) ◇ (sK3 ◇ sK4))) := by
    intro X0 sK0 sK4 sK3
    conv => enter [1, 2]; rw [l0 sK0 sK4 sK4]
    conv => enter [1]; rw [← l2 sK3 sK4 X0]
  have l5 : ∀ X0 sK0 sK4 sK3 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK4 ◇ (sK4 ◇ sK4))) := by
    intro X0 sK0 sK4 sK3
    conv => enter [1]; rw [l4 X0 sK0 sK4 sK3]
    conv => enter [1, 2]; rw [← h4278 sK4 (sK3 ◇ sK4) sK3]
  have l6 : ∀ X0 sK0 sK4 sK3 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK0 ◇ (sK4 ◇ sK4))) := by
    intro X0 sK0 sK4 sK3
    conv => enter [1]; rw [l5 X0 sK0 sK4 sK3]
    conv => enter [1, 2]; rw [l0 sK4 sK4 sK0]
  have l7 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [l6 X0 X0 sK4 sK3]
    conv => enter [1, 2]; rw [← l3 sK2 sK3 sK4 X0]
  have l8 : ∀ sK1 sK0 sK4 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK1 sK0 sK4 sK3 sK2
    conv => enter [1, 2]; rw [← l3 sK2 sK3 sK4 sK0]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK4]
  have l9 : ∀ X0 X1 sK3 sK4 sK0 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK0 ◇ (sK4 ◇ sK4))) := by
    intro X0 X1 sK3 sK4 sK0
    conv => enter [1]; rw [← h4278 (sK3 ◇ sK4) X0 X1]
    conv => enter [1, 2]; rw [← l1 sK0 sK4 (sK3 ◇ sK4) sK3]
  have l10 : ∀ X0 X1 sK3 sK4 sK2 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 X1 sK3 sK4 sK2
    conv => enter [1]; rw [l9 X0 X1 sK3 sK4 X0]
    conv => enter [1, 2]; rw [← l3 sK2 sK3 sK4 X0]
  have l11 : ∀ sK1 sK0 sK4 X0 X1 sK3 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK4))) = (X0 ◇ (X1 ◇ (sK3 ◇ sK4))) := by
    intro sK1 sK0 sK4 X0 X1 sK3
    conv => enter [1]; rw [l8 sK1 sK0 sK4 sK3 sK1]
    conv => enter [1]; rw [← l10 X0 X1 sK3 sK4 sK1]
  have l12 : ∀ sK1 sK0 sK4 X0 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK4))) = (X0 ◇ (sK0 ◇ (sK4 ◇ sK4))) := by
    intro sK1 sK0 sK4 X0
    conv => enter [1]; rw [l11 sK1 sK0 sK4 X0 sK1 sK1]
    conv => enter [1, 2]; rw [← l1 sK0 sK4 sK1 sK1]
  have l13 : ∀ sK1 sK0 sK4 X0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK1 sK0 sK4 X0 sK2 sK3
    conv => enter [1]; rw [l12 sK1 sK0 sK4 X0]
    conv => enter [1, 2]; rw [← l3 sK2 sK3 sK4 sK0]
  have l14 : ∀ sK4 X0 X1 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK4 ◇ sK4))) := by
    intro sK4 X0 X1
    conv => enter [1]; rw [h4278 sK4 (X0 ◇ X1) sK4]
    conv => enter [1]; rw [← h4512 X0 X1 (sK4 ◇ sK4)]
  have l15 : ∀ sK4 X0 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK0 ◇ (sK4 ◇ sK4))) := by
    intro sK4 X0 sK0
    conv => enter [1]; rw [l14 sK4 X0 sK4]
    conv => enter [1, 2]; rw [l0 sK4 sK4 sK0]
  have l16 : ∀ sK4 X0 sK2 sK3 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK4 X0 sK2 sK3
    conv => enter [1]; rw [l15 sK4 X0 sK4]
    conv => enter [1, 2]; rw [← l3 sK2 sK3 sK4 sK4]
  have l17 : ∀ sK1 sK0 sK4 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK4))) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [l13 sK1 sK0 sK4 sK1 sK1 sK1]
    conv => enter [1]; rw [← l16 sK4 sK1 sK1 sK1]
  have l18 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ (sK4 ◇ sK4)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK4))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [← h4278 sK4 sK0 sK4]
    conv => enter [1]; rw [← l17 sK1 sK0 sK4]
  have l19 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK3 sK4 sK0]
    conv => enter [1]; rw [l18 sK0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l19 x y z w u]

theorem Equation4512_54661_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54661 : Equation54661 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54661 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54661 X0 sK0 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54661 X0 sK2 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4278_4512_implies_Equation54679 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54679 G := by
  have l0 : ∀ X0 sK0 sK1 sK5 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK5))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK5))) := by
    intro X0 sK0 sK1 sK5 X1
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK5) X0 sK0]
    conv => enter [1]; rw [h4278 (sK1 ◇ sK5) X1 sK0]
  have l1 : ∀ sK2 sK0 sK1 sK5 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK5))) = ((sK1 ◇ sK5) ◇ ((sK1 ◇ sK5) ◇ (sK1 ◇ sK5))) := by
    intro sK2 sK0 sK1 sK5
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK5) sK2 sK0]
  have l2 : ∀ sK2 sK0 sK1 sK5 X0 X1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK5))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK5))) := by
    intro sK2 sK0 sK1 sK5 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 sK1 sK5]
    conv => enter [1]; rw [h4278 (sK1 ◇ sK5) X0 X1]
  have l3 : ∀ X0 sK1 sK5 X1 : G, (X0 ◇ (sK1 ◇ sK5)) = (X1 ◇ (sK1 ◇ sK5)) := by
    intro X0 sK1 sK5 X1
    conv => enter [1]; rw [← h4278 sK5 X0 sK1]
    conv => enter [1]; rw [h4278 sK5 X1 sK1]
  have l4 : ∀ sK0 sK1 sK5 : G, (sK0 ◇ (sK1 ◇ sK5)) = (sK5 ◇ (sK5 ◇ sK5)) := by
    intro sK0 sK1 sK5
    conv => enter [1]; rw [← h4278 sK5 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK5 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK5)) = (X0 ◇ (X1 ◇ sK5)) := by
    intro sK0 sK1 sK5 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 sK5]
    conv => enter [1]; rw [h4278 sK5 X0 X1]
  have l6 : ∀ sK5 X0 X1 sK1 : G, (sK5 ◇ (sK5 ◇ sK5)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK5))) := by
    intro sK5 X0 X1 sK1
    conv => enter [1]; rw [h4278 sK5 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK5)]
  have l7 : ∀ sK2 sK0 sK1 sK5 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK5))) = (sK5 ◇ (sK5 ◇ sK5)) := by
    intro sK2 sK0 sK1 sK5
    conv => enter [1]; rw [l2 sK2 sK0 sK1 sK5 sK2 sK2]
    conv => enter [1]; rw [← l6 sK5 sK2 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK5 sK2 : G, (sK0 ◇ (sK1 ◇ sK5)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK5))) := by
    intro sK0 sK1 sK5 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK5]
    conv => enter [1]; rw [← l7 sK2 sK0 sK1 sK5]
  have l9 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK5)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK5))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l5 sK3 sK4 sK5 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 sK5 sK2]
  intro x y z w u v
  conv => enter [1]; rw [l9 x y z w u v]

@[equational_result]
theorem Equation54679_implies_Equation4278 (G : Type*) [Magma G] (h54679 : Equation54679 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54679 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54679 X4 sK0 sK0 X0 X0 X0]
  have l1 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ sK0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h54679 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54679 X1 X2 sK0 X0 X0 X0]
  have l2 : ∀ sK0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [l1 sK0 sK0 X1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4278_4512_implies_Equation54510 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54510 G := by
  have l0 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ (X0 ◇ sK0))) = ((X0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [← h4278 (X0 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [← h4278 sK0 (X0 ◇ sK0) X0]
  have l1 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X2 ◇ (X0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h4512 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l0 X1 X2 X0 sK0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4278 sK0 X0 X0]
  have l3 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1, 2, 2]; rw [← h4278 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4278 sK0 sK1 sK2]
  have l4 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1, 2, 2]; rw [h4278 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 X0 sK0 sK1 sK2 X1]
  have l5 : ∀ X1 X2 sK1 sK2 sK0 X0 : G, (X1 ◇ (X2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4278 (sK1 ◇ (sK2 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [← l4 X0 sK0 (sK1 ◇ (sK2 ◇ sK0)) sK1 sK2]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 X0 sK0 sK0 sK0 sK0]
  have l7 : ∀ X1 X2 sK1 sK2 sK0 : G, (X1 ◇ (X2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 sK1 sK2 sK0
    conv => enter [1]; rw [l5 X1 X2 sK1 sK2 sK0 X1]
    conv => enter [1, 2]; rw [← l6 sK0 X1]
  have l8 : ∀ sK0 X1 X2 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l7 X1 X2 sK1 sK2 sK0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [h4278 sK0 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4278 (sK0 ◇ sK0) (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [h4278 sK0 sK1 sK2]
  have l12 : ∀ sK1 sK2 sK0 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1, 1]; rw [← h4278 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 X1 X0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK0 sK0 sK0 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l12 sK1 sK2 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4278 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l14 sK0 sK0 sK0]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4278 sK0 sK1 sK2]
    conv => enter [1]; rw [l15 sK0]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation4512_54510_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54510 : Equation54510 G) : Equation4278 G := by
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
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54510 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54510 X0 X1 sK0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54510 X0 sK2 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54510 X0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54510 X0 sK0 sK0]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l18 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 X0 sK2]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l14 sK0 X0]
    conv => enter [1, 2]; rw [l8 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l19 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l22 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l21 X0 sK0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l22 X0 sK0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l15 sK0 X1]
    conv => enter [1]; rw [l15 sK0 X0]
  have l26 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0]
  have l27 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l26 sK1 sK2 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l28 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l25 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l29 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l28 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l25 X0 sK0 sK0]
  have l30 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l27 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l29 X0 sK0 sK1]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l30 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l31 x y z]

theorem Equation4278_4512_implies_Equation54638 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54638 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4278 sK2 X0 sK0]
    conv => enter [1]; rw [h4278 sK2 X1 sK0]
  have l1 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h4278 sK2 sK3 sK0]
  have l2 : ∀ X0 X1 sK0 sK2 sK3 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK2 sK3
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 sK3]
  have l3 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK2 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK2 sK3]
  have l4 : ∀ sK3 sK0 sK2 X0 X1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK2]
    conv => enter [1]; rw [h4278 sK2 X0 X1]
  have l5 : ∀ X0 sK3 sK0 sK2 X1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK3 sK0 sK2 X1
    conv => enter [1]; rw [l3 X0 sK3 sK0 sK2]
    conv => enter [1]; rw [← l3 X1 sK3 sK0 sK2]
  have l6 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l4 sK1 sK1 sK2 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 sK2 X1]
    conv => enter [1, 2]; rw [l4 X0 X0 sK2 sK1 sK1]
  have l7 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK2 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l8 : ∀ sK2 X0 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK2 X0 sK3 sK0
    conv => enter [1]; rw [l7 sK2 X0 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK2 sK3]
  have l9 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l8 sK2 X0 sK2 sK2]
    conv => enter [1, 2]; rw [l4 sK2 sK2 sK2 sK1 sK1]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l9 sK2 sK1 sK1]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l4 sK2 sK2 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l11 w z x y]

theorem Equation4512_54638_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54638 : Equation54638 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54638 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X2)]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 X2]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK0 X0 sK0]
  have l5 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l3 X0 sK2 sK0 sK0]
  have l6 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4278_4512_implies_Equation54502 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54502 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [h4278 (sK1 ◇ sK0) X1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK0) sK0 sK0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4278 (sK1 ◇ sK0) X0 X1]
  have l3 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4278 sK0 X0 sK1]
    conv => enter [1]; rw [h4278 sK0 X1 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4278 sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4278 sK0 X0 X1]
  have l6 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4278 sK0 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK0 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l5 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [l8 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

end Semigroup5
