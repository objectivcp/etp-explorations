import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41621_implies_Equation41594 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41621 : Equation41621 G) : Equation41594 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l5 sK1 sK0]
  have l12 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l12 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))]
    conv => enter [1, 2]; rw [← l10 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41621 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41621 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41621 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41621 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l19 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1, 2]; rw [h41621 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)))]
  have l20 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X2]
    conv => enter [1, 1]; rw [← h41621 X0 X1]
  have l21 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l20 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l24 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41621 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l21 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK1 sK0]
    conv => enter [1]; rw [l22 sK1 sK0]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK1 sK0]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l25 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l31 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l30 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l33 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l29 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l29 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l37 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) X0]
  have l38 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l37 sK0 X0 sK1]
  have l39 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l31 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l40 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l39 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ sK0) X0]
  have l41 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l40 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l8 sK1 sK0 X0]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [l42 sK1 sK0]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l46 sK1 sK0]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) sK1]
    conv => enter [1, 2]; rw [← l4 sK1 sK0 X0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41621 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l33 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) sK1]
  have l52 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l31 (sK1 ◇ sK0) X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l33 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) sK1]
  have l53 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l52 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 ((sK1 ◇ sK0) ◇ X0)]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 (sK1 ◇ sK0)]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l50 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l57 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l2 sK0 sK1 X0]
    conv => enter [1]; rw [l48 sK0 sK1 X0]
  have l58 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l53 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l38 sK0 X0 sK1]
  have l59 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l32 sK0 sK1]
  have l60 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l58 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l61 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l62 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l55 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l63 sK0 sK1]
  have l65 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1]
    conv => enter [1, 2]; rw [← l45 sK1 sK0]
  have l67 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l66 sK0 sK1]
  have l68 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l47 sK1 sK0]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l70 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l71 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l70 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l72 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [l69 sK0 sK1]
  have l73 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0 sK0]
  have l74 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l71 sK1 sK0 X0]
    conv => enter [1]; rw [← l60 sK1 sK0 X0]
  have l75 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK0)) sK0 X0]
    conv => enter [1]; rw [l74 sK1 sK0 X0]
  have l76 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← l33 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) sK1]
  have l77 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))]
  have l78 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l77 sK1 sK0]
    conv => enter [1]; rw [← l57 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l79 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK1 sK0]
    conv => enter [1]; rw [l76 sK1 sK0]
  have l80 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l78 sK1 sK0]
    conv => enter [1, 2]; rw [← l64 sK0 sK1]
  have l81 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [l80 sK1 sK0]
  have l82 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l83 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l82 sK0 sK1]
  have l84 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [l8 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l85 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l86 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l87 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l61 sK1 sK0]
  have l88 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [l87 sK0 sK1]
  have l89 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l86 sK1 sK0]
    conv => enter [1]; rw [l73 sK1 sK0]
  have l90 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l85 sK0 sK1]
    conv => enter [1, 2]; rw [← l72 sK0 sK1]
  have l91 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l84 sK1 sK0]
    conv => enter [1, 2]; rw [l73 sK1 sK0]
  have l92 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [l91 sK1 sK0]
  have l93 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l67 sK0 sK1]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l65 sK1 sK0]
  have l95 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))]
  have l96 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l75 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))]
    conv => enter [1]; rw [← l95 sK0 sK1]
  have l97 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [l96 sK1 sK0]
  have l98 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [l97 sK1 sK0]
  have l99 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l81 sK1 sK0]
  have l100 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l81 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l101 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l81 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l102 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l81 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l103 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0))) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [← l102 sK1 sK0 X0]
  have l104 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l98 sK1 sK0]
    conv => enter [1]; rw [← l101 sK0 sK1]
  have l105 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l100 sK1 sK0]
  have l106 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l99 sK0 sK1]
  have l107 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← l103 sK0 sK1 X0]
  have l108 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l104 sK1 sK0]
    conv => enter [1]; rw [← l88 sK0 sK1]
  have l109 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l105 sK1 sK0]
  have l110 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l98 sK1 sK0]
    conv => enter [1]; rw [← l106 sK0 sK1]
  have l111 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l110 sK1 sK0]
    conv => enter [1, 2]; rw [l90 sK0 sK1]
  have l112 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l111 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0)]
  have l113 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l112 sK1 sK0]
    conv => enter [1]; rw [← l107 sK1 sK0 sK0]
  have l114 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l113 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l115 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l108 sK1 sK0]
    conv => enter [1]; rw [l114 sK1 sK0]
  have l116 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41621 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2, 2, 2]; rw [l108 sK1 sK0]
  have l117 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l108 sK1 sK0]
  have l118 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l117 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l119 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK1 sK0]
    conv => enter [1]; rw [l116 sK1 sK0]
  have l120 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l119 sK1 sK0]
    conv => enter [1, 2]; rw [l118 sK1 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0)]
  have l121 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0 sK0]
    conv => enter [1]; rw [← l120 sK1 sK0]
  have l122 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l121 sK1 sK0]
  have l123 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l122 sK1 sK0]
  have l124 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l109 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1]
  have l125 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK1 sK0]
    conv => enter [1, 2]; rw [← l123 sK1 sK0]
  have l126 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41621 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l123 sK1 sK0]
  have l127 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l123 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l128 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l127 sK1 sK0 X0]
  have l129 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l126 sK1 sK0]
    conv => enter [1]; rw [← l41 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l130 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l125 sK1 sK0]
  have l131 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l129 sK1 sK0]
    conv => enter [1, 2]; rw [← l115 sK0 sK1]
  have l132 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l130 sK0 sK1]
    conv => enter [1]; rw [← l128 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l133 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l132 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l134 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l133 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l135 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l88 sK0 sK1]
  have l136 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l135 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0))]
  have l137 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l136 sK1 sK0]
    conv => enter [1, 2]; rw [← l131 sK1 sK0]
  have l138 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l79 sK1 sK0]
    conv => enter [1]; rw [← l137 sK1 sK0]
  have l139 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l138 sK1 sK0]
    conv => enter [1]; rw [l89 sK1 sK0]
  have l140 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l128 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l139 sK1 sK0]
  have l141 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l140 sK1 sK0]
  have l142 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l141 sK1 sK0]
  have l143 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l134 sK0 sK1]
    conv => enter [1]; rw [l142 sK1 sK0]
  have l144 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l143 sK0 sK1]
    conv => enter [1]; rw [← l92 sK0 sK1]
  have l145 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l144 sK1 sK0]
  have l146 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l145 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l147 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l98 sK1 sK0]
    conv => enter [1]; rw [← l124 sK1 sK0]
  have l148 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l108 sK1 sK0]
    conv => enter [1]; rw [l147 sK1 sK0]
  have l149 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) = (((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 X0]
    conv => enter [1, 1]; rw [l148 sK0 sK1]
  have l150 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l149 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l151 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2, 2]; rw [← l44 sK0 sK1]
  have l152 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l151 sK0 sK1]
    conv => enter [1]; rw [← l107 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l153 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l152 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l154 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l93 sK0 sK1]
    conv => enter [1]; rw [l153 sK0 sK1]
  have l155 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l154 sK0 sK1]
  have l156 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l155 sK1 sK0]
    conv => enter [1]; rw [l146 sK1 sK0]
  have l157 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l156 sK1 sK0]
  have l158 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l157 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l159 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l158 sK0 sK1 X0]
  have l160 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l31 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l4 sK1 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))]
  have l161 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l160 sK1 sK0]
    conv => enter [1]; rw [l118 sK1 sK0 (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))]
  have l162 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l161 sK1 sK0]
    conv => enter [1]; rw [l150 sK0 sK1 (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))]
  have l163 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l162 sK1 sK0]
    conv => enter [1]; rw [← l159 sK0 sK1 (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))]
  have l164 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l163 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l23 sK0 sK1]
  have l165 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l164 sK1 sK0]
    conv => enter [1, 2]; rw [← l83 sK0 sK1]
  have l166 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [← l165 sK1 sK0]
  have l167 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l166 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l167 x y]

theorem Equation4512_41594_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41594 : Equation41594 G) : Equation41621 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l9 sK1 sK0]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK1 ◇ sK0) X0]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l13 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l15 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK1 ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41594 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l16 : ∀ sK1 sK0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41594 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41594 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41594 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41594 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41594 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ X0)))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41594 X0 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ X0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41594 X0 sK0]
  have l23 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h41594 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)))]
  have l24 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ X0))) X2]
    conv => enter [1, 1]; rw [← h41594 X0 X1]
  have l25 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41594 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)))]
  have l26 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l25 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
  have l27 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l24 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l28 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l23 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0 X0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l22 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l30 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l21 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41594 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l33 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41594 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ sK1 sK0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)))]
  have l35 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0))]
  have l36 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l26 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l37 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l27 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1 sK0]
    conv => enter [1]; rw [l8 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l32 sK1 sK0]
  have l40 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l41 : ∀ sK1 sK0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [← l14 sK1 sK0 (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)))]
  have l42 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l35 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))]
  have l43 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l37 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [l41 sK1 sK0]
  have l45 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)]
    conv => enter [1]; rw [l42 sK1 sK0 X0]
  have l46 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l43 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l44 sK1 sK0]
    conv => enter [1, 2]; rw [l8 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l48 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l28 sK1 sK0 X0]
    conv => enter [1]; rw [l45 sK1 sK0 X0]
  have l49 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l50 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l49 sK1 sK0]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l50 sK1 sK0]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK1 sK0]
    conv => enter [1]; rw [l51 sK1 sK0]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41594 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l39 sK1 sK0]
  have l55 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l56 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l55 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l56 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l59 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l58 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← l59 sK1 sK0]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l39 sK1 sK0]
  have l62 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l46 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ X0)))]
  have l63 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l62 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [← l56 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l65 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l63 sK0 X0 sK1]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l64 sK0 sK1]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← l53 sK1 sK0]
  have l68 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l69 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l68 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l20 sK0 sK1]
  have l71 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [← l69 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l72 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l71 sK0 sK1]
  have l73 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1, 2]; rw [← l66 sK0 sK1]
  have l74 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l75 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l66 sK0 sK1]
  have l76 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [← l18 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l77 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l78 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l77 sK0 sK1 X0]
  have l79 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41594 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l73 sK1 sK0]
  have l80 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l73 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l81 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l80 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l82 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l83 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l81 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [← l82 sK0 sK1]
  have l84 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l83 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l85 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [← l29 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l86 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l85 sK1 sK0]
    conv => enter [1, 2]; rw [← l76 sK0 sK1]
  have l87 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l8 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l86 sK1 sK0]
  have l88 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [l87 sK1 sK0]
  have l89 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l88 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l90 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l88 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l91 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l90 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l92 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l89 sK1 sK0]
    conv => enter [1]; rw [l8 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l93 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l92 sK1 sK0]
    conv => enter [1]; rw [← l30 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0]
  have l94 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l93 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l95 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l94 sK1 sK0]
  have l96 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l76 sK0 sK1]
    conv => enter [1]; rw [l95 sK0 sK1]
  have l97 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l98 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l97 sK1 sK0]
    conv => enter [1]; rw [← l78 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l99 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l98 sK1 sK0]
  have l100 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41594 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l99 sK1 sK0]
  have l101 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l99 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l102 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l101 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l103 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l100 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l104 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l102 sK1 sK0 X0]
  have l105 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l103 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l2 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l106 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l105 sK0 sK1]
    conv => enter [1]; rw [← l104 sK1 sK0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l107 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l106 sK0 sK1]
    conv => enter [1, 2]; rw [← l69 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l108 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l96 sK0 sK1]
    conv => enter [1]; rw [← l107 sK0 sK1]
  have l109 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l108 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l110 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [← l109 sK1 sK0]
  have l111 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l89 sK1 sK0]
    conv => enter [1]; rw [← l110 sK0 sK1]
  have l112 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 (sK1 ◇ sK0) (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l19 sK0 sK1]
  have l113 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l112 sK1 sK0]
    conv => enter [1]; rw [← l65 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l114 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l113 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l115 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l114 sK1 sK0]
    conv => enter [1, 2]; rw [l11 sK0 sK1]
  have l116 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l115 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)]
  have l117 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l116 sK1 sK0]
  have l118 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l117 sK1 sK0]
  have l119 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l118 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l91 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l120 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l119 sK0 sK1]
    conv => enter [1, 2]; rw [← l52 sK1 sK0]
  have l121 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l120 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l122 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41594 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l121 sK0 sK1]
  have l123 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l121 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l124 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l123 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l125 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l122 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0))]
  have l126 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l124 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l125 sK0 sK1]
  have l127 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l126 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l128 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l127 sK0 sK1]
    conv => enter [1, 2]; rw [← l60 sK0 sK1]
  have l129 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l111 sK1 sK0]
    conv => enter [1]; rw [← l128 sK0 sK1]
  have l130 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l129 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l131 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0]
    conv => enter [1]; rw [← l130 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l131 x y]

@[equational_result]
theorem Equation41685_implies_Equation41598 (G : Type*) [Magma G] (h41685 : Equation41685 G) : Equation41598 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41685 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41598_implies_Equation41685 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41598 : Equation41598 G) : Equation41685 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h41598 X1 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h41598 (X0 ◇ X1) X1 X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41598 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [← h41598 X0 X1 X0]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l5 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l5 X0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 X0 sK1]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 X0]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 sK1]
    conv => enter [1]; rw [← l7 sK1 X0]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 X0]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l11 sK1 X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l6 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l12 sK1 X0]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 X0]
  have l15 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h41598 sK3 sK2 sK0]
    conv => enter [1]; rw [l5 sK3 sK1]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 X0 sK1]
  have l17 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1 sK1]
    conv => enter [1]; rw [← l16 sK1 sK1]
  have l18 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l17 sK1]
    conv => enter [1]; rw [← l14 sK1 (sK1 ◇ sK1)]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1]
    conv => enter [1]; rw [← l15 sK2 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l19 x y z w]

@[equational_result]
theorem Equation41685_implies_Equation41673 (G : Type*) [Magma G] (h41685 : Equation41685 G) : Equation41673 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41685 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41673_implies_Equation41685 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41673 : Equation41673 G) : Equation41685 G := by
  have l0 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ X0) ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41673 sK1 (sK1 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41673 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l2 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 X0 (X1 ◇ ((sK1 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0)))]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0)))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l2 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 X0 ((sK1 ◇ sK1) ◇ X0)]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← l1 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41673 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) (X0 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) (sK1 ◇ sK1) (sK1 ◇ sK1) sK1]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [h41673 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK1]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l8 sK1]
  have l11 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h41673 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 2, 2]; rw [← l10 sK1 X0]
  have l12 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l11 X0 sK1 X0]
    conv => enter [1]; rw [← l10 sK1 X0]
  have l13 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h41673 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l13 x y z w]

theorem Equation4512_41600_implies_Equation41675 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41600 : Equation41600 G) : Equation41675 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41600 X1 X2 X0 (X2 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41600 X0 X2 X1 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41600 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41600 X0 X1 X1 X1]
  have l5 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41600 sK1 sK1 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l6 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1, 2]; rw [l4 X0 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l4 X0 sK1]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l4 X0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 sK1 sK1]
    conv => enter [1]; rw [← l8 sK1 X0]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 (sK1 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [← l6 sK1 X0 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0 sK1]
  have l12 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1 sK1]
    conv => enter [1]; rw [← l7 sK1 (sK1 ◇ sK1)]
  have l13 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l12 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [← l4 X0 sK1]
  have l15 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l14 sK1 X0]
    conv => enter [1]; rw [h41600 X0 sK2 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]

theorem Equation4512_41675_implies_Equation41600 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41675 : Equation41675 G) : Equation41600 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h41675 X1 X2 X3 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2, 2]; rw [← h41675 X0 X1 X1 X1]
  have l1 : ∀ sK1 X1 X2 sK2 sK3 sK0 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)))) := by
    intro sK1 X1 X2 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h41675 sK1 X1 X2 ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l2 : ∀ sK3 X1 X2 sK0 X0 : G, (sK3 ◇ sK3) = (X1 ◇ (X2 ◇ (X1 ◇ ((sK3 ◇ sK0) ◇ X0)))) := by
    intro sK3 X1 X2 sK0 X0
    conv => enter [1]; rw [h41675 sK3 X1 X2 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK3 sK0 X0]
  have l3 : ∀ sK3 sK0 : G, (sK3 ◇ sK3) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l2 sK3 sK3 sK3 sK0 sK3]
    conv => enter [1]; rw [← h41675 (sK3 ◇ sK0) sK3 sK3 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK1 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← h41675 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK1 sK1 sK1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1 X1 X0]
    conv => enter [1]; rw [← h41675 X0 X1 X1 X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [l5 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l7 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← l3 sK3 sK0]
    conv => enter [1]; rw [h41675 sK3 sK2 X0 sK0]
  have l8 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l6 sK1 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l7 sK3 sK0 sK2 X0]
  intro x y z w
  conv => enter [1]; rw [l8 x y x z w]

theorem Equation4512_41600_implies_Equation41688 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41600 : Equation41600 G) : Equation41688 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X1 sK2 X0 : G, (X1 ◇ X1) = (sK2 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [h41600 X1 sK2 sK2 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41600 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41600 X0 X1 X1 X1]
  have l3 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h41600 sK2 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l0 sK2 ((sK2 ◇ sK2) ◇ (X0 ◇ X1))]
  have l4 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l3 sK2 sK2 sK2]
    conv => enter [1]; rw [← l1 (sK2 ◇ sK2) sK2 (sK2 ◇ sK2)]
  have l5 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [l2 X1 sK2]
  have l6 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l2 (X0 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1]; rw [h41600 (X0 ◇ (sK2 ◇ sK2)) X0 sK2 sK2]
    conv => enter [1, 2]; rw [l2 (X0 ◇ (sK2 ◇ sK2)) sK2]
  have l7 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l4 sK2]
    conv => enter [1]; rw [l2 (sK2 ◇ sK2) sK2]
  have l8 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l7 sK2]
    conv => enter [1]; rw [l6 sK2 X0]
    conv => enter [1, 2]; rw [← l7 sK2]
  have l9 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l5 X0 X1 sK2]
    conv => enter [1, 2]; rw [← l7 sK2]
  have l10 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l8 sK2 sK2]
    conv => enter [1]; rw [← l9 X0 sK2 sK2]
  have l11 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l10 sK2 X0]
    conv => enter [1]; rw [h41600 X0 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l11 x y z w u]

@[equational_result]
theorem Equation41688_implies_Equation41600 (G : Type*) [Magma G] (h41688 : Equation41688 G) : Equation41600 G := by
  intro x y z w
  conv => enter [1]; rw [h41688 x y x z w]

theorem Equation4512_41602_implies_Equation41664 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation41664 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41602 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41602 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [h41602 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_41664_implies_Equation41602 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41664 : Equation41664 G) : Equation41602 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X2 ◇ X1))) X3]
    conv => enter [1, 1]; rw [← h41664 X0 X1 X2]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41664 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l3 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X2 ◇ X1)) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X1) X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [h41664 (X0 ◇ X1) X1 X0]
    conv => enter [1, 2, 2]; rw [l2 (X0 ◇ X1) sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) (sK0 ◇ sK0) X1 X0]
    conv => enter [1]; rw [← l9 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41664 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41664 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l13 sK0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 sK0]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ sK0) X0]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l15 X0 sK0]
    conv => enter [1]; rw [← l13 sK0]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK2]
    conv => enter [1]; rw [h41664 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

theorem Equation4512_41602_implies_Equation41717 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation41717 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41602 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41602 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK1 X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [← l0 sK1 X0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK3]
    conv => enter [1]; rw [h41602 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation41717_implies_Equation41602 (G : Type*) [Magma G] (h41717 : Equation41717 G) : Equation41602 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41717 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41717 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41717 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41604_implies_Equation41666 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41604 : Equation41604 G) : Equation41666 G := by
  have l0 : ∀ sK1 X1 X2 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ (X2 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X1 X2 X0
    conv => enter [1]; rw [h41604 sK1 X1 X2 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X2 X0 X1 : G, ((sK1 ◇ sK1) ◇ X2) = (X0 ◇ ((sK1 ◇ (X1 ◇ (sK1 ◇ sK1))) ◇ X2)) := by
    intro sK1 X2 X0 X1
    conv => enter [1, 1]; rw [h41604 sK1 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (X1 ◇ (sK1 ◇ sK1))) X2]
  have l2 : ∀ sK1 X2 X0 X1 : G, ((sK1 ◇ sK1) ◇ X2) = (X0 ◇ (sK1 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [l1 sK1 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (X1 ◇ (sK1 ◇ sK1)) X2]
  have l3 : ∀ sK1 X2 X0 X1 : G, ((sK1 ◇ sK1) ◇ X2) = (X0 ◇ (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2)))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [l2 sK1 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK1 ◇ sK1) X2]
  have l4 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l0 sK1 sK1 sK1 X2]
    conv => enter [1]; rw [← l3 sK1 X2 sK1 sK1]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 (X0 ◇ (sK1 ◇ (X0 ◇ sK1)))]
    conv => enter [1]; rw [← h41604 X0 (sK1 ◇ sK1) sK1 sK1]
  have l6 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK3]
    conv => enter [1]; rw [h41604 sK3 X0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

theorem Equation4512_41666_implies_Equation41604 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41666 : Equation41666 G) : Equation41604 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X2 sK1 X0 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro X1 X2 sK1 X0
    conv => enter [1]; rw [h41666 X1 X2 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41666 X1 X2 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41666 X0 X0 X1 X1]
  have l3 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41666 sK1 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 sK1 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1 X1]
    conv => enter [1]; rw [← l2 X0 X1 X1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l2 X0 sK1 sK1]
  have l7 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ X0) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [l2 X0 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK3 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [l5 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ X2)) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l2 sK1 X1 X2]
  have l10 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l9 sK1 X1 sK1]
  have l11 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l12 : ∀ sK3 sK1 sK0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK3 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK1 (sK1 ◇ sK0)]
  have l13 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK1 sK3]
    conv => enter [1]; rw [← l12 sK3 sK1 sK0]
  have l14 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 sK3 sK0]
  have l15 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK1]
    conv => enter [1]; rw [l14 sK1 sK3 sK0]
  have l16 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [← h41666 sK3 X0 sK1 sK0]
    conv => enter [1]; rw [l7 sK3 sK3 sK1 sK0]
  have l17 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l15 sK1 sK3 sK0]
    conv => enter [1]; rw [← l16 X0 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l17 x y z w]

theorem Equation4512_41604_implies_Equation41720 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41604 : Equation41604 G) : Equation41720 G := by
  have l0 : ∀ sK2 X1 X2 X0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ (X2 ◇ ((sK2 ◇ sK2) ◇ X0)))) := by
    intro sK2 X1 X2 X0
    conv => enter [1]; rw [h41604 sK2 X1 X2 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK2 X2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X2) = (X0 ◇ ((sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) ◇ X2)) := by
    intro sK2 X2 X0 X1
    conv => enter [1, 1]; rw [h41604 sK2 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) X2]
  have l2 : ∀ sK2 X2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X2) = (X0 ◇ (sK2 ◇ ((X1 ◇ (sK2 ◇ sK2)) ◇ X2))) := by
    intro sK2 X2 X0 X1
    conv => enter [1]; rw [l1 sK2 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 (X1 ◇ (sK2 ◇ sK2)) X2]
  have l3 : ∀ sK2 X2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X2) = (X0 ◇ (sK2 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ X2)))) := by
    intro sK2 X2 X0 X1
    conv => enter [1]; rw [l2 sK2 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK2 ◇ sK2) X2]
  have l4 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X2
    conv => enter [1]; rw [l0 sK2 sK2 sK2 X2]
    conv => enter [1]; rw [← l3 sK2 X2 sK2 sK2]
  have l5 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l4 sK2 (X0 ◇ (sK2 ◇ (X0 ◇ sK2)))]
    conv => enter [1]; rw [← h41604 X0 (sK2 ◇ sK2) sK2 sK2]
  have l6 : ∀ sK2 X0 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK4 ◇ sK0)))) := by
    intro sK2 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK4]
    conv => enter [1]; rw [h41604 sK4 X0 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z w u]

@[equational_result]
theorem Equation41720_implies_Equation41604 (G : Type*) [Magma G] (h41720 : Equation41720 G) : Equation41604 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41720 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41720 X0 X1 X1 X1 X1]
  have l1 : ∀ sK1 X1 sK3 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X1 sK3 sK0
    conv => enter [1]; rw [h41720 sK1 X1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_41607_implies_Equation41714 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41607 : Equation41607 G) : Equation41714 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41607 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41607 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ X0))]
  have l3 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← h41607 sK0 sK2 sK0]
  have l4 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l3 sK2 sK0]
  have l5 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l4 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l2 sK1 sK1]
    conv => enter [1]; rw [← h41607 (sK1 ◇ sK1) sK1 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1, 2, 2]; rw [← l7 sK1]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [← h41607 (sK1 ◇ sK1) sK1 sK1]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l10 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l12 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [← l7 sK1]
  have l13 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1]
  have l14 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ sK1)]
  have l15 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1]; rw [← l11 sK1 sK1]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41607 X0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK1]
  have l17 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l16 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l12 sK1]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41607 X0 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l3 X0 sK0]
  have l19 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41607 sK0 sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0))]
  have l20 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41607 sK0 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← h41607 (sK0 ◇ (sK2 ◇ sK0)) sK0 (sK2 ◇ sK0)]
  have l21 : ∀ X0 X1 sK0 sK2 : G, ((X0 ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X1)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1, 1]; rw [h41607 X0 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) X1]
  have l22 : ∀ X0 X1 sK0 sK2 : G, ((X0 ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l21 X0 X1 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) X1]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l20 sK0 sK2]
    conv => enter [1]; rw [l5 sK2 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l24 : ∀ X0 X1 sK0 sK2 : G, ((X0 ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1)))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l22 X0 X1 sK0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) X1]
  have l25 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ X1)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l24 X0 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [l5 X0 sK0 X1]
  have l26 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ X1)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l25 X0 X1 sK0]
  have l27 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l19 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l28 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l27 sK2 sK0]
    conv => enter [1]; rw [l5 sK2 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l29 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l23 sK0 sK2]
    conv => enter [1]; rw [← l28 sK2 sK0]
  have l30 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ sK0) = (sK0 ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 sK0]
    conv => enter [1]; rw [← l29 sK0 sK2]
  have l31 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41607 (sK1 ◇ sK1) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l11 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l32 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [l31 sK1 X0]
  have l33 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1]
    conv => enter [1]; rw [l32 sK1 X0]
  have l34 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h41607 X1 X0 X0]
    conv => enter [1, 2, 2, 2]; rw [l17 X0 sK1]
  have l35 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l17 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
    conv => enter [1]; rw [h41607 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l17 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l36 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l17 (X0 ◇ X1) sK1]
  have l37 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l36 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l38 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h4512 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l35 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ sK1)]
  have l39 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l34 X1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l33 sK1 X0]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l5 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l38 sK1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l5 sK1 sK0 (sK1 ◇ sK1)]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 (sK1 ◇ sK1) (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [← l40 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← l37 sK0 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [← l42 sK1 sK0]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [l44 sK1 sK0]
  have l46 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ sK0) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l45 sK0 sK1]
  have l47 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l30 sK2 sK0]
    conv => enter [1]; rw [l46 sK2 sK0 sK1]
  have l48 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l47 sK1 sK2 sK1]
  have l49 : ∀ X0 sK2 sK1 : G, (X0 ◇ X0) = (sK2 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h41607 X0 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l48 sK1 sK2]
  have l50 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ X0) = (sK2 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l48 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) X0]
  have l51 : ∀ X0 sK2 sK1 : G, (X0 ◇ X0) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l49 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← l39 (sK1 ◇ sK1) X0 sK1]
  have l52 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l51 X0 X0 sK1]
    conv => enter [1]; rw [← l50 sK1 (sK1 ◇ sK1) X0]
  have l53 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l52 X0 sK1]
    conv => enter [1]; rw [← l10 sK1]
  have l54 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l53 sK1 sK3]
    conv => enter [1]; rw [h41607 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l54 x y z w]

@[equational_result]
theorem Equation41714_implies_Equation41607 (G : Type*) [Magma G] (h41714 : Equation41714 G) : Equation41607 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41714 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41714 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41714 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41608_implies_Equation41662 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41608 : Equation41608 G) : Equation41662 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 sK1 X2 X0 : G, (X1 ◇ X1) = (sK1 ◇ (X1 ◇ (X2 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro X1 sK1 X2 X0
    conv => enter [1]; rw [h41608 X1 sK1 X2 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X4) = (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [h41608 X4 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41608 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4)))]
  have l4 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41608 sK1 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ ((sK1 ◇ sK1) ◇ X1))]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l3 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X4]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1 sK1 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l7 : ∀ X0 X2 : G, (X0 ◇ X0) = (X2 ◇ X2) := by
    intro X0 X2
    conv => enter [1]; rw [l5 X0 X0 X2 X0 X0]
    conv => enter [1]; rw [← l2 X2 X0 X0 X0 (X2 ◇ X0)]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l7 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l8 sK1 X0]
    conv => enter [1]; rw [h41608 X0 sK2 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

theorem Equation4512_41662_implies_Equation41608 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41662 : Equation41662 G) : Equation41608 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 sK1 X2 X0 : G, (X1 ◇ X1) = ((sK1 ◇ sK1) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro X1 sK1 X2 X0
    conv => enter [1]; rw [h41662 X1 (sK1 ◇ sK1) X2 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 X0]
  have l2 : ∀ X2 X3 X0 X1 X4 : G, (X2 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X3 X0 X1 X4
    conv => enter [1]; rw [h41662 X2 X3 (X0 ◇ X1) X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l1 X1 sK1 X1 X1]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ sK1) X1 X1 X1]
  have l4 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK3]
    conv => enter [1]; rw [h41662 sK3 sK2 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y x z w]

theorem Equation4512_41608_implies_Equation41715 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41608 : Equation41608 G) : Equation41715 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X1 sK2 X2 X0 : G, (X1 ◇ X1) = (sK2 ◇ (X1 ◇ (X2 ◇ ((sK2 ◇ sK2) ◇ X0)))) := by
    intro X1 sK2 X2 X0
    conv => enter [1]; rw [h41608 X1 sK2 X2 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK2 sK2 X0]
  have l2 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X4) = (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [h41608 X4 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41608 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4)))]
  have l4 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X1)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h41608 sK2 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l0 sK2 (X0 ◇ ((sK2 ◇ sK2) ◇ X1))]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l3 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X4]
  have l6 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l4 sK2 sK2 sK2]
    conv => enter [1]; rw [← l1 (sK2 ◇ sK2) sK2 sK2 sK2]
  have l7 : ∀ X2 X0 : G, (X2 ◇ X2) = (X0 ◇ X0) := by
    intro X2 X0
    conv => enter [1]; rw [l5 X2 X2 X0 X2 X2]
    conv => enter [1]; rw [← l2 X0 X2 X2 X2 (X0 ◇ X2)]
  have l8 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l6 sK2]
    conv => enter [1]; rw [l7 (sK2 ◇ sK2) X0]
  have l9 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l8 sK2 X0]
    conv => enter [1]; rw [h41608 X0 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l9 x y z w u]

@[equational_result]
theorem Equation41715_implies_Equation41608 (G : Type*) [Magma G] (h41715 : Equation41715 G) : Equation41608 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41715 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41715 X0 X1 X1 X1 X1]
  have l1 : ∀ sK1 sK2 X1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X1 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 X1 sK3 sK0
    conv => enter [1]; rw [h41715 sK1 sK2 X1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y x z w]

theorem Equation4512_41668_implies_Equation41614 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41614 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK3 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK3 ◇ (sK0 ◇ sK2))]
  have l2 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK3 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) X0]
  have l3 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = ((sK1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK1 ◇ X0) X2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 X0]
  have l4 : ∀ X1 sK3 sK0 sK2 X0 X2 sK1 : G, (X1 ◇ X1) = (((sK3 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0))))) := by
    intro X1 sK3 sK0 sK2 X0 X2 sK1
    conv => enter [1]; rw [h41668 X1 ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0) X2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l2 sK1 sK3 sK0 sK2 X0]
  have l5 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l6 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41668 sK1 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l0 sK1 (X0 ◇ X1)]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41668 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l8 : ∀ X1 sK3 sK0 sK2 X0 X2 sK1 : G, (X1 ◇ X1) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)))))) := by
    intro X1 sK3 sK0 sK2 X0 X2 sK1
    conv => enter [1]; rw [l4 X1 sK3 sK0 sK2 X0 X2 sK1]
    conv => enter [1]; rw [← h4512 (sK3 ◇ (sK0 ◇ sK2)) X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0))))]
  have l9 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = (sK1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [l3 X1 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 sK1 X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))]
  have l10 : ∀ X1 sK3 sK0 sK2 sK1 : G, (X1 ◇ X1) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro X1 sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l8 X1 sK3 sK0 sK2 X1 X1 sK1]
    conv => enter [1, 2]; rw [← l5 sK1 X1 X1 X1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))]
  have l11 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [l9 X1 sK1 X1 X1]
    conv => enter [1, 2]; rw [← l5 sK1 X1 X1 X1 (sK1 ◇ sK1)]
  have l12 : ∀ X1 sK1 : G, (X1 ◇ X1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l11 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l13 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [l12 (sK1 ◇ sK1) sK1]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [← l12 X0 sK1]
  have l15 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h41668 X0 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l14 (X0 ◇ (X0 ◇ X1)) sK1]
  have l16 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l15 sK1 X1 sK1]
  have l17 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l10 sK3 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [h41668 sK3 sK2 X0 sK0]
  have l18 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l16 sK1 (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l17 sK3 sK0 sK2 sK1 X0]
  intro x y z w
  conv => enter [1]; rw [l18 x y x z w]

theorem Equation4512_41614_implies_Equation41668 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41614 : Equation41614 G) : Equation41668 G := by
  have l0 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41614 sK1 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ sK1))]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41614 X0 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK1 X0 sK1]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0 sK1]
    conv => enter [1]; rw [← l1 X0 sK1]
  have l3 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [h41614 X0 sK2 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_41668_implies_Equation41707 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41707 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l3 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = ((sK1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK1 ◇ X0) X2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 X0]
  have l4 : ∀ X1 sK3 sK0 sK1 sK2 X0 X2 : G, (X1 ◇ X1) = (((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0))))) := by
    intro X1 sK3 sK0 sK1 sK2 X0 X2
    conv => enter [1]; rw [h41668 X1 ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) X2 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [l2 sK1 sK2 sK3 sK0 X0]
  have l5 : ∀ sK1 sK2 X0 X1 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)))) := by
    intro sK1 sK2 X0 X1 sK3 sK0
    conv => enter [1]; rw [h41668 (sK1 ◇ sK2) X0 X1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [l2 sK1 sK2 sK3 sK0 X0]
  have l6 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41668 sK1 sK1 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [← l5 sK1 sK2 sK1 sK1 sK1 sK1]
  have l8 : ∀ X1 sK3 sK0 sK1 sK2 X0 X2 : G, (X1 ◇ X1) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)))))) := by
    intro X1 sK3 sK0 sK1 sK2 X0 X2
    conv => enter [1]; rw [l4 X1 sK3 sK0 sK1 sK2 X0 X2]
    conv => enter [1]; rw [← h4512 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0))))]
  have l9 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = (sK1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [l3 X1 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 sK1 X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))]
  have l10 : ∀ X1 sK3 sK0 sK1 sK2 : G, (X1 ◇ X1) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro X1 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l8 X1 sK3 sK0 sK1 sK2 X1 X1]
    conv => enter [1, 2]; rw [← l6 sK1 X1 X1 X1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l11 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [l9 X1 sK1 X1 X1]
    conv => enter [1, 2]; rw [← l6 sK1 X1 X1 X1 (sK1 ◇ sK1)]
  have l12 : ∀ X1 sK1 : G, (X1 ◇ X1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l11 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l13 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1 sK1]
    conv => enter [1]; rw [l12 (sK1 ◇ sK1) sK1]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [← l12 X0 sK1]
  have l15 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h41668 X0 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l14 (X0 ◇ (X0 ◇ X1)) sK1]
  have l16 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l15 sK1 X1 sK1]
  have l17 : ∀ sK3 sK0 sK1 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l10 sK0 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [h41668 sK0 sK2 X0 sK1]
  have l18 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l16 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l17 sK1 sK0 sK1 sK2 X0]
  intro x y z w
  conv => enter [1]; rw [l18 x y z w]

theorem Equation4512_41707_implies_Equation41668 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41707 : Equation41707 G) : Equation41668 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41707 sK1 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41707 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h41707 sK1 sK1 sK1 X0]
    conv => enter [1]; rw [← h41707 X0 (sK1 ◇ sK1) sK1 sK1]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h41707 sK0 sK2 X0 sK1]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_41668_implies_Equation41727 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41727 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X1 sK2 X0 X2 : G, (X1 ◇ X1) = ((sK2 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))))) := by
    intro X1 sK2 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK2 ◇ X0) X2 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK2 X0]
  have l2 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ sK2 X1 X0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1)))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h41668 sK2 X1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l0 sK2 (X0 ◇ X1)]
  have l4 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l3 sK2 sK2 sK2]
    conv => enter [1]; rw [← h41668 (sK2 ◇ sK2) sK2 sK2 sK2]
  have l5 : ∀ X1 sK2 X0 X2 : G, (X1 ◇ X1) = (sK2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)))))) := by
    intro X1 sK2 X0 X2
    conv => enter [1]; rw [l1 X1 sK2 X0 X2]
    conv => enter [1]; rw [← h4512 sK2 X0 (X2 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))))]
  have l6 : ∀ X1 sK2 : G, (X1 ◇ X1) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK2
    conv => enter [1]; rw [l5 X1 sK2 X1 X1]
    conv => enter [1, 2]; rw [← l2 sK2 X1 X1 X1 (sK2 ◇ sK2)]
  have l7 : ∀ X1 sK2 : G, (X1 ◇ X1) = ((sK2 ◇ sK2) ◇ sK2) := by
    intro X1 sK2
    conv => enter [1]; rw [l6 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
  have l8 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ sK2) := by
    intro sK2
    conv => enter [1]; rw [l4 sK2]
    conv => enter [1]; rw [l7 (sK2 ◇ sK2) sK2]
  have l9 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l8 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
  have l10 : ∀ sK2 sK3 X0 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ sK2) = (sK3 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [← l7 sK1 sK2]
    conv => enter [1]; rw [h41668 sK1 sK3 X0 sK0]
  have l11 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l10 sK2 sK3 X0 sK1 sK0]
  have l12 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l9 sK2]
    conv => enter [1]; rw [l11 sK2 sK3 X0 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l12 x y z w u]

@[equational_result]
theorem Equation41727_implies_Equation41668 (G : Type*) [Magma G] (h41727 : Equation41727 G) : Equation41668 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41727 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41727 X0 X1 X1 X1 X1]
  have l1 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [h41727 sK1 sK2 X1 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_41709_implies_Equation41615 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41709 : Equation41709 G) : Equation41615 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ ((X4 ◇ (X5 ◇ (X0 ◇ X5))) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h41709 X1 X2 X3 (X4 ◇ (X5 ◇ (X0 ◇ X5)))]
    conv => enter [1, 2, 2, 2]; rw [← h41709 X0 X1 X4 X5]
  have l1 : ∀ sK1 X1 X2 sK3 sK0 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (((sK3 ◇ (sK0 ◇ sK3)) ◇ X0) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0)))) := by
    intro sK1 X1 X2 sK3 sK0 X0
    conv => enter [1]; rw [h41709 sK1 X1 X2 ((sK3 ◇ (sK0 ◇ sK3)) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2)))) = (X3 ◇ (X4 ◇ (X3 ◇ X4))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← h41709 (X3 ◇ X4) X0 X1 X2]
    conv => enter [1]; rw [← h4512 X3 X4 (X3 ◇ X4)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41709 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ X4)))]
  have l4 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X3 ◇ X4))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X4 X2]
  have l5 : ∀ sK1 X1 X2 sK3 sK0 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0))))) := by
    intro sK1 X1 X2 sK3 sK0 X0
    conv => enter [1]; rw [l1 sK1 X1 X2 sK3 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK3 ◇ (sK0 ◇ sK3)) X0 ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0)]
  have l6 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ ((X5 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l0 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X4 (X5 ◇ (X0 ◇ X5)) (X0 ◇ X0)]
  have l7 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK1 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK1 sK1 (sK3 ◇ (sK0 ◇ sK3)) sK1]
  have l8 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ ((X0 ◇ X5) ◇ (X0 ◇ X0)))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l6 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X5 (X0 ◇ X5) (X0 ◇ X0)]
  have l9 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X5 ◇ (X0 ◇ X0))))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l8 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X5 (X0 ◇ X0)]
  have l10 : ∀ X1 X2 X3 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X5 ◇ X0))))) := by
    intro X1 X2 X3 X5 X0
    conv => enter [1]; rw [l9 X1 X2 X3 X1 X5 X0]
    conv => enter [1, 2, 2]; rw [← l4 X5 X0 X1 X5 X0]
  have l11 : ∀ X1 X5 : G, (X1 ◇ X1) = (X5 ◇ X5) := by
    intro X1 X5
    conv => enter [1]; rw [l10 X1 X1 X1 X5 X1]
    conv => enter [1]; rw [← l3 X5 X1 X1 X5 X1]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1 sK1 sK1]
    conv => enter [1]; rw [l11 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l13 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h41709 sK0 X0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l13 x y z w]

theorem Equation4512_41615_implies_Equation41709 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41615 : Equation41615 G) : Equation41709 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41615 X2 X3 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h41615 (X0 ◇ X1) X2 X1 X0]
  have l2 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41615 sK1 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41615 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l1 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ X0 X2 : G, (X0 ◇ X0) = (X2 ◇ X2) := by
    intro X0 X2
    conv => enter [1]; rw [l4 X0 X0 X2 X0]
    conv => enter [1]; rw [← h41615 X2 X0 X0 X2]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [l5 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK3]
    conv => enter [1]; rw [h41615 sK3 X0 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

theorem Equation4512_41709_implies_Equation41729 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41709 : Equation41709 G) : Equation41729 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ ((X4 ◇ (X5 ◇ (X0 ◇ X5))) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h41709 X1 X2 X3 (X4 ◇ (X5 ◇ (X0 ◇ X5)))]
    conv => enter [1, 2, 2, 2]; rw [← h41709 X0 X1 X4 X5]
  have l1 : ∀ sK2 X1 X2 X0 : G, (sK2 ◇ sK2) = (X1 ◇ (X2 ◇ ((sK2 ◇ X0) ◇ ((sK2 ◇ sK2) ◇ X0)))) := by
    intro sK2 X1 X2 X0
    conv => enter [1]; rw [h41709 sK2 X1 X2 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK2 sK2 X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2)))) = (X3 ◇ (X4 ◇ (X3 ◇ X4))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← h41709 (X3 ◇ X4) X0 X1 X2]
    conv => enter [1]; rw [← h4512 X3 X4 (X3 ◇ X4)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41709 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ X4)))]
  have l4 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X3 ◇ X4))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X4 X2]
  have l5 : ∀ sK2 X1 X2 X0 : G, (sK2 ◇ sK2) = (X1 ◇ (X2 ◇ (sK2 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X0))))) := by
    intro sK2 X1 X2 X0
    conv => enter [1]; rw [l1 sK2 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 X0 ((sK2 ◇ sK2) ◇ X0)]
  have l6 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ ((X5 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l0 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X4 (X5 ◇ (X0 ◇ X5)) (X0 ◇ X0)]
  have l7 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l5 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [← l3 (sK2 ◇ sK2) sK2 sK2 sK2 sK2]
  have l8 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ ((X0 ◇ X5) ◇ (X0 ◇ X0)))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l6 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X5 (X0 ◇ X5) (X0 ◇ X0)]
  have l9 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X5 ◇ (X0 ◇ X0))))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l8 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X5 (X0 ◇ X0)]
  have l10 : ∀ X1 X2 X3 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X5 ◇ X0))))) := by
    intro X1 X2 X3 X5 X0
    conv => enter [1]; rw [l9 X1 X2 X3 X1 X5 X0]
    conv => enter [1, 2, 2]; rw [← l4 X5 X0 X1 X5 X0]
  have l11 : ∀ X1 X5 : G, (X1 ◇ X1) = (X5 ◇ X5) := by
    intro X1 X5
    conv => enter [1]; rw [l10 X1 X1 X1 X5 X1]
    conv => enter [1]; rw [← l3 X5 X1 X1 X5 X1]
  have l12 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l7 sK2]
    conv => enter [1]; rw [l11 (sK2 ◇ sK2) X0]
  have l13 : ∀ sK2 X0 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l12 sK2 sK0]
    conv => enter [1]; rw [h41709 sK0 X0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l13 x y z w u]

@[equational_result]
theorem Equation41729_implies_Equation41709 (G : Type*) [Magma G] (h41729 : Equation41729 G) : Equation41709 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41729 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41729 X0 X1 X1 X1 X1]
  have l1 : ∀ sK1 X1 sK3 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X1 sK3 sK0
    conv => enter [1]; rw [h41729 sK1 X1 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_41671_implies_Equation41617 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41671 : Equation41671 G) : Equation41617 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41671 X1 X2 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41671 X0 X1 X1 X1 X1]
  have l2 : ∀ sK2 X2 X0 X1 : G, (sK2 ◇ sK2) = (X2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1)))) := by
    intro sK2 X2 X0 X1
    conv => enter [1]; rw [h41671 sK2 X2 (sK2 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [l0 sK2 (X0 ◇ X1)]
  have l3 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l2 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [← h41671 (sK2 ◇ sK2) sK2 sK2 sK2 sK2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41671 X0 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [← l1 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l1 X0 sK2 sK2]
  have l6 : ∀ X0 sK4 sK1 sK0 : G, (X0 ◇ X0) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro X0 sK4 sK1 sK0
    conv => enter [1]; rw [l1 X0 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l7 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l3 sK2]
    conv => enter [1]; rw [l4 (sK2 ◇ sK2) X0]
  have l8 : ∀ sK2 X1 X2 : G, (sK2 ◇ sK2) = (X1 ◇ (X2 ◇ X2)) := by
    intro sK2 X1 X2
    conv => enter [1]; rw [l1 sK2 X1 X2]
  have l9 : ∀ sK2 X1 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X1
    conv => enter [1]; rw [l8 sK2 X1 sK2]
  have l10 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ X1) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1, 1]; rw [l9 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l11 : ∀ sK4 sK1 sK0 sK2 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK4 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK4 sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK2 (sK1 ◇ sK0)]
  have l12 : ∀ sK2 sK4 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ sK2) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK2 sK4]
    conv => enter [1]; rw [← l11 sK4 sK1 sK0 sK2]
  have l13 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l12 sK2 sK4 sK1 sK0]
  have l14 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK2]
    conv => enter [1]; rw [l13 sK2 sK4 sK1 sK0]
  have l15 : ∀ sK4 sK1 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [← l6 sK4 sK4 sK1 sK0]
    conv => enter [1]; rw [h41671 sK4 X0 X1 sK1 sK0]
  have l16 : ∀ sK2 X0 X1 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l14 sK2 sK4 sK1 sK0]
    conv => enter [1]; rw [l15 sK4 sK1 sK0 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [l16 x y x z w u]

theorem Equation4512_41617_implies_Equation41671 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41617 : Equation41617 G) : Equation41671 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41617 X1 X2 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41617 X0 X1 X1 X1 X1]
  have l2 : ∀ sK2 X0 X1 X2 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [h41617 sK2 (sK2 ◇ sK2) X0 X1 X2]
    conv => enter [1]; rw [l0 sK2 (X0 ◇ (X1 ◇ X2))]
  have l3 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l2 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [← h41617 (sK2 ◇ sK2) sK2 sK2 sK2 sK2]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1 X1]
    conv => enter [1]; rw [← l1 X0 X1 X1]
  have l5 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l3 sK2]
    conv => enter [1]; rw [l4 (sK2 ◇ sK2) X0]
  have l6 : ∀ sK2 X1 X0 sK1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 X1 X0 sK1 sK0
    conv => enter [1]; rw [l5 sK2 X0]
    conv => enter [1]; rw [h41617 X0 X1 sK2 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z w u]

theorem Equation4512_41671_implies_Equation41710 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41671 : Equation41671 G) : Equation41710 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41671 X1 X2 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41671 X0 X1 X1 X1 X1]
  have l2 : ∀ sK2 X2 X0 X1 : G, (sK2 ◇ sK2) = (X2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1)))) := by
    intro sK2 X2 X0 X1
    conv => enter [1]; rw [h41671 sK2 X2 (sK2 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [l0 sK2 (X0 ◇ X1)]
  have l3 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l2 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [← h41671 (sK2 ◇ sK2) sK2 sK2 sK2 sK2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41671 X0 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [← l1 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l1 X0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) (sK2 ◇ sK0)]
  have l6 : ∀ X0 sK4 sK1 sK2 sK0 : G, (X0 ◇ X0) = ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK4 sK1 sK2 sK0
    conv => enter [1]; rw [l1 X0 sK4 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0))]
  have l7 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l3 sK2]
    conv => enter [1]; rw [l4 (sK2 ◇ sK2) X0]
  have l8 : ∀ sK2 X1 X2 : G, (sK2 ◇ sK2) = (X1 ◇ (X2 ◇ X2)) := by
    intro sK2 X1 X2
    conv => enter [1]; rw [l1 sK2 X1 X2]
  have l9 : ∀ sK2 X1 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X1
    conv => enter [1]; rw [l8 sK2 X1 sK2]
  have l10 : ∀ sK4 sK1 sK2 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK4 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ (sK2 ◇ sK0)) sK1 sK2 sK0]
  have l11 : ∀ sK4 X0 sK1 sK2 sK0 : G, (sK4 ◇ (X0 ◇ X0)) = ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK4 X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l5 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
  have l12 : ∀ sK4 sK2 sK1 sK0 : G, (sK4 ◇ (sK2 ◇ sK2)) = ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK2 sK1 sK0
    conv => enter [1, 2]; rw [l7 sK2 sK4]
    conv => enter [1]; rw [l11 sK4 sK4 sK1 sK2 sK0]
  have l13 : ∀ sK4 sK1 sK2 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK4 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
  have l14 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK4]
    conv => enter [1]; rw [l12 sK4 sK2 sK1 sK0]
  have l15 : ∀ sK4 sK1 sK2 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [← l6 sK1 sK4 sK1 sK2 sK0]
    conv => enter [1]; rw [h41671 sK1 X0 X1 sK2 sK0]
  have l16 : ∀ sK4 sK1 sK2 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [← l13 sK4 sK1 sK2 sK0]
    conv => enter [1]; rw [l15 sK4 sK1 sK2 sK0 X0 X1]
  have l17 : ∀ sK2 X0 X1 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 X0 X1 sK1 sK0
    conv => enter [1]; rw [l14 sK2 sK2 sK1 sK0]
    conv => enter [1]; rw [l16 sK2 sK1 sK2 sK0 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [l17 x y z w u]

theorem Equation4512_41710_implies_Equation41671 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41710 : Equation41710 G) : Equation41671 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h41710 X1 X2 X3 X4 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2, 2]; rw [← h41710 X0 X1 X1 X1 X1]
  have l1 : ∀ sK1 X1 X2 X3 sK0 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (X3 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK1 X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h41710 sK1 X1 X2 X3 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l2 : ∀ sK2 X1 X2 X3 sK1 sK0 X0 : G, (sK2 ◇ sK2) = (X1 ◇ (X2 ◇ (X3 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)))) := by
    intro sK2 X1 X2 X3 sK1 sK0 X0
    conv => enter [1]; rw [h41710 sK2 X1 X2 X3 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK2 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK2 sK2 sK2 sK1 sK0 sK2]
    conv => enter [1]; rw [← h41710 (sK2 ◇ (sK1 ◇ sK0)) sK2 sK2 sK2 sK2]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK1 sK1 sK1 sK0 sK1]
    conv => enter [1]; rw [← h41710 (sK1 ◇ sK0) sK1 sK1 sK1 sK1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0 X0 X0 X1]
    conv => enter [1]; rw [← h41710 X1 X0 X0 X0 X1]
  have l6 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l3 sK2 sK2 sK2]
    conv => enter [1]; rw [l5 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l7 : ∀ sK1 sK0 X0 X1 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1 sK2
    conv => enter [1]; rw [← l4 sK1 sK0]
    conv => enter [1]; rw [h41710 sK1 X0 X1 sK2 sK0]
  have l8 : ∀ sK2 X0 X1 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 X0 X1 sK1 sK0
    conv => enter [1]; rw [l6 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l7 sK1 sK0 X0 X1 sK2]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z w u]

theorem Equation4512_41671_implies_Equation41731 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41671 : Equation41671 G) : Equation41731 G := by
  have l0 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ X0)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41671 X1 X2 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41671 X0 X1 X1 X1 X1]
  have l2 : ∀ sK3 X2 X0 X1 : G, (sK3 ◇ sK3) = (X2 ◇ (sK3 ◇ ((sK3 ◇ sK3) ◇ (X0 ◇ X1)))) := by
    intro sK3 X2 X0 X1
    conv => enter [1]; rw [h41671 sK3 X2 (sK3 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l0 sK3 (X0 ◇ X1)]
  have l3 : ∀ sK3 : G, (sK3 ◇ sK3) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3
    conv => enter [1]; rw [l2 sK3 sK3 sK3 sK3]
    conv => enter [1]; rw [← h41671 (sK3 ◇ sK3) sK3 sK3 sK3 sK3]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41671 X0 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [← l1 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l6 : ∀ X0 sK5 sK2 sK0 sK1 : G, (X0 ◇ X0) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK5 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK3 X0 : G, (sK3 ◇ sK3) = (X0 ◇ X0) := by
    intro sK3 X0
    conv => enter [1]; rw [l3 sK3]
    conv => enter [1]; rw [l4 (sK3 ◇ sK3) X0]
  have l8 : ∀ sK3 X1 X2 : G, (sK3 ◇ sK3) = (X1 ◇ (X2 ◇ X2)) := by
    intro sK3 X1 X2
    conv => enter [1]; rw [l1 sK3 X1 X2]
  have l9 : ∀ sK3 X1 : G, (sK3 ◇ sK3) = (X1 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X1
    conv => enter [1]; rw [l8 sK3 X1 sK3]
  have l10 : ∀ sK5 sK2 sK0 sK1 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK5 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l5 (sK2 ◇ (sK0 ◇ sK1)) sK2 sK0 sK1]
  have l11 : ∀ sK5 X0 sK2 sK0 sK1 : G, (sK5 ◇ (X0 ◇ X0)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK5 X0 sK2 sK0 sK1
    conv => enter [1, 2]; rw [l5 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l12 : ∀ sK5 sK3 sK2 sK0 sK1 : G, (sK5 ◇ (sK3 ◇ sK3)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK3 sK2 sK0 sK1
    conv => enter [1, 2]; rw [l7 sK3 sK5]
    conv => enter [1]; rw [l11 sK5 sK5 sK2 sK0 sK1]
  have l13 : ∀ sK5 sK2 sK0 sK1 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l10 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l14 : ∀ sK3 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK3) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l9 sK3 sK5]
    conv => enter [1]; rw [l12 sK5 sK3 sK2 sK0 sK1]
  have l15 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← l6 sK2 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [h41671 sK2 X0 X1 sK0 sK1]
  have l16 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← l13 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l15 sK5 sK2 sK0 sK1 X0 X1]
  have l17 : ∀ sK3 X0 X1 sK2 sK0 sK1 : G, (sK3 ◇ sK3) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l14 sK3 sK3 sK2 sK0 sK1]
    conv => enter [1]; rw [l16 sK3 sK2 sK0 sK1 X0 X1]
  intro x y z w u v
  conv => enter [1]; rw [l17 x y z w u v]

@[equational_result]
theorem Equation41731_implies_Equation41671 (G : Type*) [Magma G] (h41731 : Equation41731 G) : Equation41671 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41731 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h41731 X1 X0 X0 X0 X0 X0]
  have l1 : ∀ sK2 X1 X2 sK1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (X2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 X1 X2 sK1 sK0
    conv => enter [1]; rw [h41731 sK2 X1 X2 sK2 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]

theorem Equation4512_41661_implies_Equation41713 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41713 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK3) (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← h4512 sK2 sK3 (sK0 ◇ (sK2 ◇ sK3))]
  have l2 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ X0) = ((sK2 ◇ sK3) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK2 sK3 (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK3) (sK0 ◇ (sK2 ◇ sK3)) X0]
  have l3 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ X0)) = (((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) X0]
    conv => enter [1, 1]; rw [← l1 sK0 sK2 sK3]
  have l4 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [l3 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK3)) (sK0 ◇ (sK2 ◇ sK3)) X0]
  have l5 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ sK0) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)))) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [h41661 sK0 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) X0]
    conv => enter [1, 2, 2]; rw [l4 sK0 sK2 sK3 X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41661 sK1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41661 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l9 : ∀ X0 sK2 sK3 : G, (X0 ◇ X0) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [h41661 X0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK2 sK3 (X0 ◇ (sK2 ◇ sK3))]
  have l10 : ∀ sK2 sK3 sK0 X1 X0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X1)))) = ((sK2 ◇ sK3) ◇ (X0 ◇ X0)) := by
    intro sK2 sK3 sK0 X1 X0
    conv => enter [1]; rw [l2 sK2 sK3 sK0 (X1 ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X1)))]
    conv => enter [1, 2]; rw [← h41661 X0 (sK0 ◇ (sK2 ◇ sK3)) X1]
  have l11 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l7 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l12 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK3) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l5 sK0 sK2 sK3 sK0]
    conv => enter [1]; rw [l10 sK2 sK3 sK0 sK0 (sK0 ◇ (sK2 ◇ sK3))]
  have l13 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l11 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l14 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ sK0) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l12 sK0 sK2 sK3]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 (sK0 ◇ (sK2 ◇ sK3))]
  have l15 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l13 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l16 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l15 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l17 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l9 (sK0 ◇ (sK2 ◇ sK3)) sK2 sK3]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 (sK2 ◇ sK3)]
  have l18 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = (sK0 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [h4512 sK2 sK3 (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l9 sK0 sK2 sK3]
  have l19 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK2 sK3 sK0]
    conv => enter [1]; rw [l14 sK0 sK2 sK3]
  have l20 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) = ((sK2 ◇ sK3) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l9 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) sK2 sK3]
    conv => enter [1, 2]; rw [← l17 sK0 sK2 sK3]
  have l21 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l20 sK2 sK3 sK0]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 (sK0 ◇ (sK2 ◇ sK3))]
  have l22 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK2 sK3 sK0]
    conv => enter [1]; rw [← l21 sK2 sK3 sK0]
  have l23 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l8 (X0 ◇ X1) sK1]
  have l24 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l25 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l23 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l26 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l16 (sK1 ◇ sK1) (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l25 sK1 X0 X1]
  have l27 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l8 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l26 sK1 X0 X1]
  have l28 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l24 sK1]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l29 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l28 sK1]
  have l30 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41661 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l29 sK1]
  have l31 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l30 X0 sK1]
    conv => enter [1]; rw [← l27 sK1 (sK1 ◇ sK1) X0]
  have l32 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l31 X0 sK1]
    conv => enter [1]; rw [← l29 sK1]
  have l33 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l32 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))))]
    conv => enter [1]; rw [← l22 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l33 x y z w]

theorem Equation4512_41713_implies_Equation41661 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41713 : Equation41713 G) : Equation41661 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41713 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41713 X0 X1 X1 X1]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK2) ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [h41713 X0 sK1 sK2 X1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X1 ◇ (sK1 ◇ sK2))]
  have l2 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l1 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_41708_implies_Equation41669 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41708 : Equation41708 G) : Equation41669 G := by
  have l0 : ∀ sK1 X1 sK0 sK3 X0 X2 : G, (sK1 ◇ sK1) = (X1 ◇ (((sK0 ◇ sK3) ◇ X0) ◇ (X2 ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ X0)))) := by
    intro sK1 X1 sK0 sK3 X0 X2
    conv => enter [1]; rw [h41708 sK1 X1 ((sK0 ◇ sK3) ◇ X0) X2]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK3) X0]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h41708 X1 X2 (X3 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [← h41708 X0 X1 X1 X3]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41708 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ X3)))]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X3 (X0 ◇ X1) (X0 ◇ X0)]
  have l4 : ∀ sK1 X1 sK0 sK3 X0 X2 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK0 ◇ sK3) ◇ (X0 ◇ (X2 ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ X0))))) := by
    intro sK1 X1 sK0 sK3 X0 X2
    conv => enter [1]; rw [l0 sK1 X1 sK0 sK3 X0 X2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK3) X0 (X2 ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ X0))]
  have l5 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l3 X1 X2 X3 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X0)]
  have l6 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l4 sK1 sK1 sK0 sK3 sK1 sK1]
    conv => enter [1]; rw [← l2 (sK1 ◇ (sK0 ◇ sK3)) sK1 (sK0 ◇ sK3) sK1 sK1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X1 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1 X1 X0 X1]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l9 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h41708 sK0 X0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

theorem Equation4512_41669_implies_Equation41708 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41669 : Equation41669 G) : Equation41708 G := by
  have l0 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ sK3) ◇ ((sK0 ◇ (sK1 ◇ sK3)) ◇ X0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3)))) ◇ X0) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK3) (sK0 ◇ (sK1 ◇ sK3)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK3 (sK0 ◇ (sK1 ◇ sK3))]
  have l1 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ sK3) ◇ ((sK0 ◇ (sK1 ◇ sK3)) ◇ X0)) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) X0]
  have l2 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ X3) = (X4 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h41669 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ sK1 sK3 X1 X0 sK0 : G, ((sK1 ◇ sK3) ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK1 ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) ◇ X0)))) := by
    intro sK1 sK3 X1 X0 sK0
    conv => enter [1]; rw [h41669 (sK1 ◇ sK3) X1 X0 (sK0 ◇ (sK1 ◇ sK3))]
    conv => enter [1, 2, 2]; rw [l1 sK1 sK3 sK0 X0]
  have l4 : ∀ X3 X0 X1 X2 X4 X5 : G, (X3 ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ (X5 ◇ X1)))) := by
    intro X3 X0 X1 X2 X4 X5
    conv => enter [1]; rw [h41669 X3 (X2 ◇ (X3 ◇ (X4 ◇ X2))) X2 X4]
    conv => enter [1]; rw [h41669 (X2 ◇ (X3 ◇ (X4 ◇ X2))) X0 X1 X5]
  have l5 : ∀ X3 X0 X1 X2 X4 X5 : G, (X3 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ (X5 ◇ X1))))) := by
    intro X3 X0 X1 X2 X4 X5
    conv => enter [1]; rw [l4 X3 X0 X1 X2 X4 X5]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X3 ◇ (X4 ◇ X2)) (X5 ◇ X1)]
  have l6 : ∀ sK1 sK3 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK3) ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3
    conv => enter [1]; rw [h41669 sK1 sK1 sK1 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK3)))]
    conv => enter [1]; rw [← l3 sK1 sK3 sK1 sK1 sK1]
  have l7 : ∀ X2 X3 : G, (X2 ◇ X2) = (X3 ◇ X3) := by
    intro X2 X3
    conv => enter [1]; rw [l5 X2 X2 X2 X3 X2 X2]
    conv => enter [1]; rw [← l2 X3 X2 X2 (X2 ◇ (X2 ◇ X3)) X2]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 sK1]
    conv => enter [1]; rw [l7 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h41669 sK0 X0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

theorem Equation4512_41708_implies_Equation41728 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41708 : Equation41708 G) : Equation41728 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h41708 X1 X2 (X3 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [← h41708 X0 X1 X1 X3]
  have l2 : ∀ sK2 X1 X0 : G, (sK2 ◇ sK2) = (X1 ◇ (X0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h41708 sK2 X1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l0 sK2 X0]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41708 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ X3)))]
  have l4 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l2 sK2 sK2 sK2]
    conv => enter [1]; rw [← h41708 (sK2 ◇ sK2) sK2 sK2 sK2]
  have l5 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X3 (X0 ◇ X1) (X0 ◇ X0)]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l5 X1 X2 X3 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X1 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1 X1 X0 X1]
  have l8 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l4 sK2]
    conv => enter [1]; rw [l7 (sK2 ◇ sK2) X0]
  have l9 : ∀ sK2 X0 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4)))) := by
    intro sK2 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l8 sK2 sK0]
    conv => enter [1]; rw [h41708 sK0 X0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l9 x y z w u]

@[equational_result]
theorem Equation41728_implies_Equation41708 (G : Type*) [Magma G] (h41728 : Equation41728 G) : Equation41708 G := by
  intro x y z w
  conv => enter [1]; rw [h41728 x y z w x]

theorem Equation4512_41674_implies_Equation41686 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41674 : Equation41674 G) : Equation41686 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41674 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [l0 sK1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h41674 (X0 ◇ X1) X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41674 X0 (X0 ◇ X1) X1]
  have l3 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ (X0 ◇ X1)))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (X1 ◇ (sK1 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2]; rw [← h41674 X0 sK1 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41674 (sK1 ◇ sK1) sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l5 sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [← l6 sK1]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [h41674 (sK1 ◇ sK1) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK1]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 X0]
    conv => enter [1]; rw [l4 X0 (sK1 ◇ sK1)]
  have l10 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h41674 X0 (X0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l9 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l10 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l12 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l11 X0 sK1]
    conv => enter [1, 2]; rw [← l7 sK1]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1, 2]; rw [l12 X0 sK1]
  have l14 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41674 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l13 sK1 X0]
  have l15 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l14 X0 sK1]
    conv => enter [1]; rw [← l9 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 X0]
    conv => enter [1]; rw [l12 X0 sK1]
  have l17 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3)))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h41674 sK0 sK2 sK3]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l18 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [← l17 sK2 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l18 x y z w]

@[equational_result]
theorem Equation41686_implies_Equation41674 (G : Type*) [Magma G] (h41686 : Equation41686 G) : Equation41674 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41686 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41686 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41686 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41833_implies_Equation41846 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41833 : Equation41833 G) : Equation41846 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h41833 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41833 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 sK2]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ sK2) sK2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h41833 X0 (X1 ◇ X1) X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ (X1 ◇ X1))]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l4 X2 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1 X0 X1]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK1 sK2]
    conv => enter [1]; rw [l5 X0 (sK2 ◇ (sK1 ◇ sK2)) sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_41846_implies_Equation41833 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41846 : Equation41846 G) : Equation41833 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [h41846 X0 sK2 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l1 : ∀ X0 sK2 X1 : G, (X0 ◇ (((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) ◇ X1)) = ((X0 ◇ sK2) ◇ X1) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h4512 X0 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) X1]
    conv => enter [1, 1]; rw [← l0 X0 sK2]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK1 ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l0 sK1 sK2]
  have l3 : ∀ X0 sK2 X1 : G, (X0 ◇ (((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) ◇ X1)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l1 X0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 sK2 X1]
  have l4 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ X1)) = (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l3 X0 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X1]
  have l5 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41846 X0 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [l2 sK1 sK2]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l6 X0 sK1 sK2]
    conv => enter [1]; rw [← l4 X0 sK2 (sK1 ◇ sK2)]
  have l8 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l7 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK2 sK1]
  have l9 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41846 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l5 sK2 sK1]
  have l10 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l9 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l8 sK2 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_41897_implies_Equation41924 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41897 : Equation41897 G) : Equation41924 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ X0)]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l6 sK1 sK0 X0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41897 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41897 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l15 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [l5 sK1 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK0 X0]
    conv => enter [1, 1]; rw [← l16 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [← l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l25 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l26 y x]

theorem Equation4512_41924_implies_Equation41897 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41924 : Equation41924 G) : Equation41897 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l10 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l13 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l9 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l14 sK1 X0]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l12 sK1 sK0]
  have l17 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l16 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l13 sK1]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l18 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l13 sK1]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41924 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [l2 sK0 sK1 sK1]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41924 (sK0 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 (sK1 ◇ sK1)]
  have l23 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41924 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l24 : ∀ X0 sK1 : G, (X0 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41924 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l25 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h41924 X0 sK1]
  have l26 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l25 sK1 X0]
    conv => enter [1]; rw [← l4 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))]
  have l30 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1]; rw [← l15 sK1 sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2]; rw [l17 sK1 sK0 (sK1 ◇ sK1)]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l33 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l30 sK1]
    conv => enter [1, 2]; rw [← l9 sK1]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l33 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l26 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l35 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l40 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l35 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)]
  have l43 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l17 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l39 sK0 sK1]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l8 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l39 sK0 sK1]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l39 sK0 sK1]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l41 sK0 sK1]
    conv => enter [1]; rw [← l45 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l44 sK1 sK0]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0]
    conv => enter [1]; rw [← l26 sK1 sK0]
  have l49 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [l46 sK1 sK0]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1, 2]; rw [← l49 sK1 sK0]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) sK1]
    conv => enter [1]; rw [l48 sK1 sK0]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l53 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l42 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)]
    conv => enter [1]; rw [← l53 sK1 sK0]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l54 sK1 sK0]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1, 2]; rw [l51 sK1 sK0]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 (sK0 ◇ sK1)]
  have l58 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1, 2]; rw [l51 sK1 sK0]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l58 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 (sK0 ◇ sK1)]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l59 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l60 x y]

theorem Equation4512_41999_implies_Equation41913 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41999 : Equation41999 G) : Equation41913 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) X0]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ X0)]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l2 sK2 X0]
  have l4 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l5 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l4 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l6 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK2
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) sK2]
  have l7 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l6 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) sK2 X0]
  have l8 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [l7 sK2 X0]
  have l9 : ∀ sK2 X0 : G, (sK2 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))))) := by
    intro sK2 X0
    conv => enter [1]; rw [h41999 sK2 X0 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK2]
  have l10 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h41999 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l5 sK2 X0]
  have l11 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ X0))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h41999 X0 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (sK2 ◇ X0)]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41999 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ (X3 ◇ X0)))]
  have l13 : ∀ sK2 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = ((sK2 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l3 sK2 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 sK2 X1]
  have l14 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (sK0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK2)) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 (sK2 ◇ (sK2 ◇ sK2)) X1]
  have l15 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l14 sK0 sK2 sK0 X0]
    conv => enter [1]; rw [← h41999 X0 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) sK0]
  have l16 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [h41999 X0 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [l13 sK2 X0 X0]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h41999 X0 X2 X0]
  have l18 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l11 X0 X1 sK2]
    conv => enter [1, 2]; rw [← l3 sK2 X0]
  have l19 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l10 X0 X1 sK2]
    conv => enter [1, 2]; rw [← l3 sK2 ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)]
  have l20 : ∀ sK2 X0 : G, (sK2 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))))) := by
    intro sK2 X0
    conv => enter [1]; rw [l9 sK2 X0]
    conv => enter [1, 2, 2]; rw [← l8 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l21 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [h41999 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l22 : ∀ sK2 X0 : G, (sK2 ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h41999 sK2 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l23 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l19 X0 X1 sK2]
    conv => enter [1]; rw [← l18 ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) X1 sK2]
  have l24 : ∀ sK2 X0 : G, (sK2 ◇ X0) = ((sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l20 sK2 X0]
    conv => enter [1]; rw [← l18 (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))) X0 sK2]
  have l25 : ∀ sK2 X0 : G, (sK2 ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [l22 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l26 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l23 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) X0 X1]
  have l27 : ∀ sK2 X0 : G, (sK2 ◇ X0) = (sK2 ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l24 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) X0]
  have l28 : ∀ sK2 X0 : G, (sK2 ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [l27 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l29 : ∀ sK2 X0 : G, (sK2 ◇ X0) = (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ sK2) := by
    intro sK2 X0
    conv => enter [1]; rw [l28 sK2 X0]
    conv => enter [1]; rw [← l18 ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) sK2 sK2]
  have l30 : ∀ sK2 X0 : G, (sK2 ◇ X0) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l29 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) X0 sK2]
  have l31 : ∀ sK2 X0 : G, (sK2 ◇ X0) = (X0 ◇ sK2) := by
    intro sK2 X0
    conv => enter [1]; rw [l30 sK2 X0]
    conv => enter [1]; rw [← l26 X0 sK2 sK2]
  have l32 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK2 ◇ (sK2 ◇ (X0 ◇ sK2)))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h41999 X0 X1 sK2]
    conv => enter [1, 2, 2, 2]; rw [l31 sK2 X0]
  have l33 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l32 X0 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (X0 ◇ sK2)]
  have l34 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l33 X0 X1 sK2]
    conv => enter [1, 2]; rw [← l16 X0 sK2]
  have l35 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ sK2) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l21 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) (sK2 ◇ (sK2 ◇ sK2))]
  have l36 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l35 sK2]
  have l37 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l36 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK2)) (sK2 ◇ (sK2 ◇ sK2))]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l37 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l39 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l37 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) (sK2 ◇ (sK2 ◇ sK2))]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [l15 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) sK2]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
  have l42 : ∀ sK2 X0 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))))))) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [h41999 (sK2 ◇ (sK2 ◇ sK2)) X0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))))]
    conv => enter [1, 2, 2, 2]; rw [← l39 sK1 sK0 sK2]
  have l43 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))))))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [h41999 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) X0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))))]
    conv => enter [1, 2, 2, 2]; rw [← l41 sK0 sK1 sK2]
  have l44 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))))))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l43 sK0 sK2 X0 sK1]
    conv => enter [1, 2, 2]; rw [l17 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))))]
  have l45 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))))))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l44 sK0 sK2 X0 sK1]
    conv => enter [1, 2]; rw [l17 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) sK0 ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))))]
  have l46 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l45 sK0 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l42 sK2 sK0 sK0 sK0]
  have l47 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l46 sK0 sK2 X0]
    conv => enter [1]; rw [← l18 sK0 X0 sK2]
  have l48 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h41999 (sK2 ◇ (sK2 ◇ sK2)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← l25 sK2 sK2]
  have l49 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l48 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
  have l50 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l49 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l51 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [l50 sK2 X0]
  have l52 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l51 sK0 sK2 X0]
    conv => enter [1]; rw [← l34 X0 sK0 sK2]
  have l53 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [← l52 sK0 X0 X0]
    conv => enter [1]; rw [l47 sK0 X0 X0]
  have l54 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [h41999 X1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1]; rw [l47 sK0 sK2 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l55 : ∀ X1 sK0 sK2 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X1 sK0 sK2
    conv => enter [1]; rw [h41999 X1 sK0 X1]
    conv => enter [1]; rw [← l54 X1 sK0 sK2 X1]
  have l56 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [l55 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l56 x y z]

end Semigroup5
