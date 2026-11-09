import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54165_54172_implies_Equation54175 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54165 : Equation54165 G) (h54172 : Equation54172 G) : Equation54175 G := by
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
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [h54165 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h54172 X0 X1]
    conv => enter [1]; rw [l8 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h54172 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h54172 X0 X1]
    conv => enter [1]; rw [← l7 X1 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0 X0]
    conv => enter [1, 2]; rw [l10 X0 X1]
  have l12 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l9 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X1 X1 X0]
    conv => enter [1, 2, 2]; rw [← l10 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0 X1 X0]
    conv => enter [1]; rw [← l13 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h54165 X1 X0]
    conv => enter [1]; rw [← l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [← l7 X1 X0 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1]; rw [l11 X1 X0]
  intro x y
  conv => enter [1]; rw [l17 x y]
  conv => enter [1]; rw [← l11 x y]

theorem Equation4512_53863_53870_implies_Equation53860 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53863 : Equation53863 G) (h53870 : Equation53870 G) : Equation53860 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [h53870 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53870 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53870 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53870 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h53870 (sK0 ◇ sK1) X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h53870 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h53863 X0 (sK0 ◇ sK1)]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l29 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l30 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l30 sK0 sK1 X0]
  have l32 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l31 sK0 sK1 X0]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1 X0]
    conv => enter [1]; rw [l32 sK0 sK1 X0]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1 sK1]
    conv => enter [1]; rw [← h53870 (sK0 ◇ sK1) sK1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l37 x y]

theorem Equation4512_54057_54165_implies_Equation54047 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54057 : Equation54057 G) (h54165 : Equation54165 G) : Equation54047 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h54057 X0 X1]
    conv => enter [1]; rw [← h54165 X1 X0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54165 X0 sK0]
    conv => enter [1]; rw [← h54057 sK0 X0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 X0 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK1 sK0]
    conv => enter [1]; rw [h54165 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h54165 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l15 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) sK1 X0]
    conv => enter [1]; rw [l15 sK1 sK0 X0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK1]
    conv => enter [1]; rw [← h54165 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l16 sK1 sK0 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l19 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation4512_54057_54165_implies_Equation54050 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54057 : Equation54057 G) (h54165 : Equation54165 G) : Equation54050 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [h54165 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54057 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation54057_54165_implies_Equation4320 (G : Type*) [Magma G] (h54057 : Equation54057 G) (h54165 : Equation54165 G) : Equation4320 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54165 X0 sK0]
    conv => enter [1]; rw [← h54057 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation4512_54057_54165_implies_Equation54023 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54057 : Equation54057 G) (h54165 : Equation54165 G) : Equation54023 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [h54165 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54165 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54057 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h54057 X0 X1]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l3 sK1 sK0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l9 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l17 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l4 X0 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 X0 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation4512_54057_54165_implies_Equation54199 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54057 : Equation54057 G) (h54165 : Equation54165 G) : Equation54199 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h54165 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54165 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← h54057 sK1 sK0]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h54057 X0 X1]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l9 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l10 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l11 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l5 X0 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 X0 sK1]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation4512_53863_54014_implies_Equation54011 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53863 : Equation53863 G) (h54014 : Equation54014 G) : Equation54011 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 sK1]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ X0)]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l11 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1) X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l12 sK0 sK1]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l13 sK0 sK1]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l21 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l24 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h53863 sK0 (sK1 ◇ sK0)]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53863 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l31 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1 sK0]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l27 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) X0]
  have l38 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l38 sK0 sK1 X0]
    conv => enter [1]; rw [← l25 sK0 sK1 X0]
  have l40 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l39 sK0 sK1 X0]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l35 sK0 sK1 (sK1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h53863 sK1 X0]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l35 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [← l41 sK0 sK1 X0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l20 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1 sK0]
  have l44 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l35 sK0 sK1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l42 sK0 sK1 X0]
  have l45 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l35 sK0 sK1 X0]
    conv => enter [1]; rw [← l44 sK0 sK1 X0]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l40 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l51 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53863 X0 X1]
    conv => enter [1]; rw [← h54014 X0 X1]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [← l29 sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [l52 sK1 sK0]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l53 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l57 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← l59 sK0 sK1]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l15 sK0 sK1 X0]
    conv => enter [1, 2, 1]; rw [← l60 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l60 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 1]; rw [← l60 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1, 1]; rw [← l60 sK0 sK1]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l62 sK0 sK1]
  have l67 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l61 sK0 sK1 X0]
    conv => enter [1]; rw [l17 sK0 sK1 X0]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l60 sK0 sK1]
    conv => enter [1]; rw [l66 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1, 1]; rw [← l60 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1 sK0]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [l67 sK0 sK1 sK0]
  have l72 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l34 sK0 sK1]
    conv => enter [1]; rw [← l71 sK0 sK1]
  have l73 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l72 sK0 sK1]
    conv => enter [1]; rw [l65 sK0 sK1]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l60 sK0 sK1]
    conv => enter [1]; rw [← l73 sK0 sK1]
  have l75 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l69 sK0 sK1]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l75 sK0 sK1]
    conv => enter [1, 1]; rw [← l60 sK0 sK1]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l76 sK0 sK1]
  have l78 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1, 2]; rw [← l60 sK0 sK1]
  have l81 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [← h53863 X0 (sK0 ◇ (sK1 ◇ sK0))]
  have l82 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [l55 sK1 sK0]
  have l83 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [l55 sK1 sK0]
  have l84 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l85 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [l84 sK0 sK1]
  have l86 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l85 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK0) X0]
  have l87 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l82 sK1 sK0]
  have l88 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l82 sK1 sK0]
  have l89 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l88 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l90 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l87 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l91 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l85 sK0 sK1]
    conv => enter [1]; rw [← l90 sK0 sK1]
  have l92 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53863 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l91 sK0 sK1]
  have l93 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l78 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l94 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l93 sK1 sK0]
  have l95 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l94 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l96 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l95 sK1 sK0]
    conv => enter [1]; rw [l89 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l97 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l96 sK1 sK0]
    conv => enter [1, 2]; rw [← l78 sK1 sK0]
  have l98 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l97 sK1 sK0]
    conv => enter [1]; rw [l81 sK1 sK0 sK1]
  have l99 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [← l51 sK1 (sK1 ◇ sK0)]
  have l100 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l92 sK1 sK0 sK1]
    conv => enter [1]; rw [l99 sK1 sK0]
  have l101 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l98 sK1 sK0]
    conv => enter [1]; rw [l100 sK1 sK0]
  have l102 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l101 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  have l103 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l102 sK0 sK1]
  have l104 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l103 sK0 sK1]
  have l105 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [l104 sK0 sK1]
  have l106 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [l105 sK0 sK1]
  have l107 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l60 sK0 sK1]
    conv => enter [1]; rw [l106 sK0 sK1]
  have l108 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l55 sK1 sK0]
  have l109 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l107 sK0 sK1]
    conv => enter [1]; rw [← l108 sK0 sK1]
  have l110 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [← l109 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l110 x y]

theorem Equation4512_53863_54014_implies_Equation54021 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53863 : Equation53863 G) (h54014 : Equation54014 G) : Equation54021 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_53863_54014_implies_Equation4283 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53863 : Equation53863 G) (h54014 : Equation54014 G) : Equation4283 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_53863_54014_implies_Equation54023 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53863 : Equation53863 G) (h54014 : Equation54014 G) : Equation54023 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53863 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [← h54014 sK1 sK0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53863 X0 X1]
    conv => enter [1]; rw [← h54014 X0 X1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l11 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation4512_53863_54014_implies_Equation53872 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53863 : Equation53863 G) (h54014 : Equation54014 G) : Equation53872 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53863 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation4512_54014_54201_implies_Equation54047 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54014 : Equation54014 G) (h54201 : Equation54201 G) : Equation54047 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) sK0 X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l13 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l14 sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l15 sK0 sK1]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X0]
    conv => enter [1, 1]; rw [l17 sK1 sK0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l24 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54014 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54014 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l8 sK0 sK1 (sK1 ◇ sK0)]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54014 sK0 X0]
  have l30 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l4 sK1 sK0 (sK0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54014 sK0 X0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0))) = (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54014 sK0 X0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l33 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0)))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l30 sK1 sK0 X0]
    conv => enter [1]; rw [l4 sK1 sK0 (X0 ◇ sK0)]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l27 sK1 sK0]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l26 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l37 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1, 2]; rw [l14 sK0]
  have l38 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [l32 sK0 X0]
  have l41 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l33 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0 (X0 ◇ X0)]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l34 sK0 sK1]
  have l43 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l44 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [← l11 sK0]
  have l45 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l41 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ X0)]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l47 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l43 sK0]
  have l48 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l44 sK0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l46 sK0 sK1]
  have l50 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l47 sK0]
  have l51 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l48 sK0]
    conv => enter [1]; rw [l50 sK0]
  have l52 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l48 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l48 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l54 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l48 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l55 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l48 sK0]
    conv => enter [1]; rw [l52 sK0]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l51 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l58 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l55 sK0]
    conv => enter [1]; rw [← l18 sK1 sK0]
  have l60 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l56 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l61 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0) X0]
  have l62 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l36 sK1 sK0]
    conv => enter [1, 2]; rw [← l56 sK1 sK0]
  have l63 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [l36 sK1 sK0]
  have l64 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l63 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1 X0]
  have l65 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l64 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l66 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l65 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l60 sK1 sK0 X0]
  have l67 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l68 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1]; rw [← l49 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 sK0 sK1]
    conv => enter [1]; rw [l54 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l15 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l72 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [l71 sK1 sK0]
  have l73 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l72 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l74 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l73 sK1 sK0 X0]
  have l75 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
    conv => enter [1, 2]; rw [l68 sK0 sK1]
  have l76 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l75 sK1 sK0]
  have l77 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l76 sK1 sK0]
    conv => enter [1]; rw [← l74 sK1 sK0 sK0]
  have l78 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l77 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l79 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l78 sK1 sK0]
    conv => enter [1]; rw [l66 sK1 sK0 (sK0 ◇ sK0)]
  have l80 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [← l79 sK1 sK0]
  have l81 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l80 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l82 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54014 X0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l80 sK1 sK0]
  have l83 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l81 sK1 sK0 X0]
  have l84 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1, 2]; rw [← l59 sK1 sK0]
  have l85 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) X0]
  have l86 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l85 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0) X0]
  have l87 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l86 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l61 sK1 sK0 X0]
  have l88 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l87 sK1 sK0 X0]
  have l89 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l77 sK1 sK0]
    conv => enter [1]; rw [l88 sK1 sK0 sK0]
  have l90 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
    conv => enter [1]; rw [← l89 sK1 sK0]
  have l91 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l90 sK1 sK0]
    conv => enter [1]; rw [← l80 sK1 sK0]
  have l92 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l91 sK1 sK0]
  have l93 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [l92 sK1 sK0]
  have l94 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l93 sK1 sK0]
  have l95 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l94 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l96 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [l94 sK1 sK0]
  have l97 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l96 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l98 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 sK0]
  have l99 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [l17 sK1 sK0]
  have l100 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l72 sK1 sK0]
  have l101 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l61 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l102 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l103 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l4 sK1 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l104 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l61 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54201 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l105 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l29 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l104 sK1 sK0]
  have l106 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l103 sK0 sK1]
    conv => enter [1]; rw [l45 sK1 sK0 (sK1 ◇ sK0)]
  have l107 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l66 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l102 sK0 sK1]
  have l108 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l29 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l101 sK1 sK0]
  have l109 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l74 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l100 sK0 sK1]
  have l110 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l99 sK0 sK1]
    conv => enter [1]; rw [l21 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l111 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l98 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l112 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l105 sK0 sK1]
    conv => enter [1]; rw [← l83 sK1 sK0 (sK0 ◇ sK0)]
  have l113 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l106 sK0 sK1]
    conv => enter [1]; rw [l88 sK1 sK0 (sK1 ◇ sK0)]
  have l114 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l107 sK1 sK0]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l115 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l61 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l108 sK0 sK1]
  have l116 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l109 sK1 sK0]
    conv => enter [1, 2]; rw [← l80 sK1 sK0]
  have l117 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l110 sK0 sK1]
    conv => enter [1]; rw [← l58 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l118 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l111 sK0 sK1]
    conv => enter [1]; rw [← h54201 (sK0 ◇ sK0) sK1]
  have l119 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l112 sK0 sK1]
    conv => enter [1, 2]; rw [← l59 sK1 sK0]
  have l120 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l113 sK0 sK1]
    conv => enter [1]; rw [l97 sK1 sK0 (sK1 ◇ sK0)]
  have l121 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l115 sK1 sK0]
    conv => enter [1, 2]; rw [l17 sK1 sK0]
  have l122 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l116 sK1 sK0]
    conv => enter [1]; rw [l88 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0))]
  have l123 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l117 sK0 sK1]
    conv => enter [1]; rw [l88 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l124 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l29 sK0 sK1]
    conv => enter [1]; rw [← l118 sK0 sK1]
  have l125 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
    conv => enter [1]; rw [l119 sK0 sK1]
  have l126 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l120 sK0 sK1]
    conv => enter [1, 2]; rw [l84 sK1 sK0]
  have l127 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l114 sK1 sK0]
    conv => enter [1, 2]; rw [← l56 sK1 sK0]
  have l128 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l121 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l129 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l122 sK0 sK1]
    conv => enter [1]; rw [l97 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0))]
  have l130 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l97 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l123 sK0 sK1]
  have l131 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l124 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l132 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l125 sK0 sK1]
  have l133 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l126 sK0 sK1]
    conv => enter [1, 2]; rw [l94 sK1 sK0]
  have l134 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l127 sK0 sK1]
  have l135 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l128 sK1 sK0]
  have l136 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l129 sK0 sK1]
    conv => enter [1, 2]; rw [← l83 sK1 sK0 (sK1 ◇ sK0)]
  have l137 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l130 sK1 sK0]
    conv => enter [1, 2]; rw [← l80 sK1 sK0]
  have l138 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [l132 sK0 sK1]
  have l139 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l133 sK0 sK1]
  have l140 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [← l135 sK0 sK1]
  have l141 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l136 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l84 sK1 sK0]
  have l142 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l137 sK1 sK0]
    conv => enter [1]; rw [l95 sK0 sK1]
  have l143 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l138 sK0 sK1]
    conv => enter [1]; rw [← l134 sK0 sK1]
  have l144 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l139 sK0 sK1]
    conv => enter [1, 2]; rw [← l134 sK0 sK1]
  have l145 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l141 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l94 sK1 sK0]
  have l146 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l56 sK1 sK0]
    conv => enter [1]; rw [l142 sK1 sK0]
  have l147 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l140 sK1 sK0]
    conv => enter [1]; rw [l143 sK0 sK1]
  have l148 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l144 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l149 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l82 sK1 sK1 sK0]
    conv => enter [1]; rw [← l145 sK0 sK1]
  have l150 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l134 sK0 sK1]
    conv => enter [1]; rw [l146 sK1 sK0]
  have l151 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l131 sK0 sK1]
    conv => enter [1]; rw [l148 sK0 sK1]
  have l152 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l134 sK0 sK1]
    conv => enter [1]; rw [← l149 sK1 sK0]
  have l153 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l147 sK1 sK0]
    conv => enter [1]; rw [l150 sK0 sK1]
  have l154 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l152 sK0 sK1]
    conv => enter [1, 2]; rw [l62 sK1 sK0]
  have l155 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l134 sK0 sK1]
    conv => enter [1]; rw [← l154 sK0 sK1]
  have l156 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l155 sK1 sK0]
    conv => enter [1]; rw [← l22 sK0 sK1]
  have l157 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l156 sK1 sK0]
    conv => enter [1, 2]; rw [l84 sK1 sK0]
  have l158 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l157 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l159 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l153 sK1 sK0]
    conv => enter [1]; rw [← l158 sK1 sK0]
  have l160 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l159 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l161 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l151 sK0 sK1]
    conv => enter [1]; rw [← l160 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l161 x y]

theorem Equation4512_54014_54201_implies_Equation54048 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54014 : Equation54014 G) (h54201 : Equation54201 G) : Equation54048 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 sK1]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ X0)]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l12 sK0 sK1 X0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [l15 sK0 sK1]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 X0]
    conv => enter [1, 1]; rw [l19 sK1 sK0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h54014 sK0 (sK1 ◇ sK0)]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h54014 (sK1 ◇ sK0) (sK0 ◇ sK1)]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l31 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54014 X0 X1]
  have l32 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54014 sK0 X0]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l32 sK0 sK1 X0]
    conv => enter [1]; rw [← l14 sK0 sK1 (X0 ◇ sK0)]
  have l34 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l31 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l27 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [l26 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l43 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l34 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [l39 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 sK0 sK1]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l41 sK0 sK1]
  have l49 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l43 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [l45 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l48 sK0 sK1]
  have l52 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l49 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l54 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l38 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [l55 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l56 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l57 sK0 sK1]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l42 sK0 sK1]
  have l61 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [l60 sK1 sK0]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l59 sK0 sK1]
  have l63 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l59 sK0 sK1]
  have l64 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l63 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l65 sK0 sK1]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK1 ◇ sK0) ◇ sK0)]
  have l68 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l68 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l70 sK0 sK1]
  have l72 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l54 sK0 sK1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l73 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l54 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l74 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l38 sK1 sK0]
  have l75 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l54 sK0 sK1 sK1]
  have l76 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [l64 sK0 sK1 sK1]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1, 2]; rw [← l53 sK1 sK0]
  have l78 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l77 sK0 sK1]
  have l79 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l76 sK0 sK1]
    conv => enter [1]; rw [← l54 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [l79 sK0 sK1]
  have l81 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l54 sK0 sK1 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 (sK1 ◇ sK0)]
  have l82 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l54 sK0 sK1 sK0]
  have l83 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
    conv => enter [1]; rw [l81 sK0 sK1]
  have l84 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l83 sK0 sK1]
  have l85 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l54 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l86 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [← l85 sK1 sK0]
  have l87 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l86 sK1 sK0]
  have l88 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l89 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l88 sK0 sK1 X0]
  have l90 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l87 sK1 sK0]
  have l91 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [← l90 sK1 sK0 X0]
  have l92 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l93 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l94 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l93 sK0 sK1]
    conv => enter [1]; rw [← l73 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l95 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l92 sK1 sK0]
    conv => enter [1]; rw [← l91 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l96 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1]; rw [← l89 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l97 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [l95 sK1 sK0]
  have l98 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l96 sK0 sK1]
  have l99 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l98 sK0 sK1]
    conv => enter [1]; rw [l59 sK0 sK1]
  have l100 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l101 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) X0]
  have l102 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l101 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l103 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l100 sK1 sK0]
    conv => enter [1, 2]; rw [l11 sK0 sK1 sK0]
  have l104 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l102 sK1 sK0 X0]
  have l105 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l103 sK1 sK0]
    conv => enter [1, 2]; rw [← l50 sK0 sK1]
  have l106 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l105 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l107 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK1 ◇ sK0) ◇ sK0)]
  have l108 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l107 sK0 sK1]
    conv => enter [1]; rw [← l72 sK0 sK1 sK0]
  have l109 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l108 sK0 sK1]
  have l110 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l71 sK0 sK1]
  have l111 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← l110 sK0 sK1 X0]
  have l112 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l111 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l113 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l112 sK0 sK1 X0]
    conv => enter [1]; rw [← l89 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l114 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l97 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l115 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l97 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l116 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l115 sK0 sK1]
    conv => enter [1]; rw [← l78 sK0 sK1]
  have l117 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l114 sK1 sK0]
    conv => enter [1, 2]; rw [← l44 sK0 sK1]
  have l118 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [l116 sK0 sK1]
  have l119 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l117 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))]
  have l120 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l119 sK1 sK0]
    conv => enter [1]; rw [l37 sK1 sK0]
  have l121 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l106 sK1 sK0]
    conv => enter [1]; rw [l120 sK1 sK0]
  have l122 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l118 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l123 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l122 sK0 sK1 X0]
  have l124 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l121 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ sK0) X0]
  have l125 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l124 sK1 sK0 X0]
  have l126 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l106 sK1 sK0]
  have l127 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l126 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l128 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l109 sK0 sK1]
    conv => enter [1]; rw [← h54014 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l129 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0 sK1]
    conv => enter [1]; rw [l128 sK0 sK1]
  have l130 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l118 sK0 sK1]
    conv => enter [1]; rw [l129 sK0 sK1]
  have l131 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [← l82 sK1 sK0]
  have l132 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
    conv => enter [1, 2]; rw [← l82 sK1 sK0]
  have l133 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l132 sK1 sK0]
    conv => enter [1, 2]; rw [← l121 sK1 sK0]
  have l134 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l131 sK1 sK0]
    conv => enter [1]; rw [← l121 sK1 sK0]
  have l135 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l133 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l136 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l11 sK0 sK1 sK0]
    conv => enter [1]; rw [l135 sK1 sK0]
  have l137 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l136 sK1 sK0]
  have l138 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l137 sK1 sK0]
  have l139 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l134 sK1 sK0]
  have l140 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l139 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l141 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l84 sK0 sK1]
    conv => enter [1, 2]; rw [← l121 sK1 sK0]
  have l142 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l84 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) X0]
  have l143 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l142 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ sK0) X0]
  have l144 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l141 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l145 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l143 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l125 sK1 sK0 X0]
  have l146 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l145 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)]
  have l147 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l146 sK0 sK1 X0]
  have l148 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54201 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h54014 X0 X1]
  have l149 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54201 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h54201 X0 X1]
  have l150 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l61 sK1 sK0]
  have l151 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l80 sK0 sK1]
  have l152 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l51 sK0 sK1]
  have l153 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l54 sK0 sK1 sK0]
  have l154 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l134 sK1 sK0]
  have l155 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54201 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l156 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l157 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h54201 sK0 sK1]
  have l158 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 (sK0 ◇ sK1)]
  have l159 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l54 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l160 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54201 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l161 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h54201 sK1 sK0]
  have l162 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l13 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l163 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l54 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)]
  have l164 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l163 sK1 sK0]
    conv => enter [1]; rw [← l89 sK0 sK1 sK1]
  have l165 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l162 sK0 sK1]
    conv => enter [1]; rw [← l113 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l166 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l161 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l167 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l160 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l168 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [← l159 sK0 sK1]
  have l169 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [← l158 sK0 sK1]
  have l170 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l157 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l171 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l156 sK0 sK1]
  have l172 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l155 X0 X1 X2]
  have l173 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l154 sK0 sK1]
    conv => enter [1]; rw [l140 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l174 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l153 sK1 sK0]
    conv => enter [1]; rw [← l72 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l175 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l152 sK1 sK0]
    conv => enter [1]; rw [← l54 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l176 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l151 sK0 sK1]
    conv => enter [1]; rw [← l89 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l177 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l150 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l178 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54201 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l14 sK0 sK1 sK0]
  have l179 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l149 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X1))]
  have l180 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l148 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) (X0 ◇ (X1 ◇ X0))]
  have l181 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [← l164 sK1 sK0]
  have l182 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l123 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l165 sK0 sK1]
  have l183 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 sK1]
    conv => enter [1]; rw [l166 sK0 sK1]
  have l184 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l167 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l185 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1 sK1]
    conv => enter [1]; rw [← l168 sK1 sK0]
  have l186 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l169 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK0]
  have l187 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l170 sK1 sK0]
  have l188 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l173 sK0 sK1]
    conv => enter [1]; rw [← h54201 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ sK0)]
  have l189 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l174 sK1 sK0]
    conv => enter [1]; rw [← h54201 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l190 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l118 sK0 sK1]
    conv => enter [1]; rw [← l175 sK1 sK0]
  have l191 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l176 sK0 sK1]
    conv => enter [1]; rw [← h54201 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l192 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l177 sK0 sK1]
    conv => enter [1]; rw [← l104 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l193 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l178 sK0 sK1]
  have l194 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l179 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ (X1 ◇ X1))]
  have l195 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l180 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 (X0 ◇ (X1 ◇ X0))]
  have l196 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l181 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l197 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l182 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l198 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1]; rw [l184 X0 X1 X2]
  have l199 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l185 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l200 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l125 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l188 sK0 sK1]
  have l201 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l118 sK0 sK1]
    conv => enter [1]; rw [← l189 sK1 sK0]
  have l202 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l190 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l203 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l191 sK0 sK1]
    conv => enter [1]; rw [l21 sK1 sK0 sK0]
  have l204 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l192 sK0 sK1]
    conv => enter [1]; rw [l140 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l205 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l194 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h54014 X0 X1]
  have l206 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l195 X0 X1]
    conv => enter [1]; rw [← l52 X0 X1 (X0 ◇ (X1 ◇ X0))]
  have l207 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l196 sK0 sK1]
  have l208 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l197 sK0 sK1]
    conv => enter [1]; rw [l64 sK0 sK1 sK1]
  have l209 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l198 X0 X1 X2]
  have l210 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l199 sK0 sK1]
    conv => enter [1]; rw [l183 sK0 sK1]
  have l211 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l147 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l200 sK1 sK0]
  have l212 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l201 sK0 sK1]
    conv => enter [1, 2]; rw [l193 sK0 sK1]
  have l213 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l171 sK0 sK1]
    conv => enter [1]; rw [← l203 sK0 sK1]
  have l214 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l91 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l204 sK0 sK1]
  have l215 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l205 X0 X1]
    conv => enter [1, 2, 2]; rw [← h54201 X0 X1]
  have l216 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l206 X0 X1]
    conv => enter [1]; rw [← l172 X1 X0 X0]
  have l217 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l202 sK0 sK1]
    conv => enter [1]; rw [← l207 sK0 sK1]
  have l218 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l211 sK0 sK1]
    conv => enter [1, 2]; rw [← l121 sK1 sK0]
  have l219 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l171 sK0 sK1]
    conv => enter [1]; rw [← l212 sK0 sK1]
  have l220 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l213 sK0 sK1]
    conv => enter [1]; rw [l64 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l221 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l214 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 (sK1 ◇ sK1)]
  have l222 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h54014 X0 X1]
    conv => enter [1]; rw [← l215 X0 X1]
  have l223 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l216 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) (X0 ◇ X0)]
  have l224 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l208 sK0 sK1]
    conv => enter [1]; rw [l99 sK0 sK1]
  have l225 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l218 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l226 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l219 sK0 sK1]
    conv => enter [1]; rw [l186 sK0 sK1]
  have l227 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l130 sK0 sK1]
    conv => enter [1]; rw [← l220 sK0 sK1]
  have l228 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l221 sK1 sK0]
    conv => enter [1]; rw [l33 sK0 sK1 sK1]
  have l229 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l222 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) (X1 ◇ X1)]
  have l230 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l223 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ X0)]
  have l231 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [l224 sK0 sK1]
  have l232 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l138 sK1 sK0]
    conv => enter [1]; rw [← l225 sK0 sK1]
  have l233 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l229 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 (X1 ◇ X1)]
  have l234 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h54014 X1 X0]
    conv => enter [1]; rw [← l230 X1 X0]
  have l235 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l232 sK1 sK0]
    conv => enter [1, 2]; rw [← l87 sK1 sK0]
  have l236 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l228 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l237 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l209 X1 X0 X1]
    conv => enter [1]; rw [← l233 X1 X0]
  have l238 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h54201 X1 X0]
    conv => enter [1]; rw [l234 X0 X1]
  have l239 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l235 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l240 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l236 sK0 sK1]
    conv => enter [1, 2]; rw [l127 sK0 sK1]
  have l241 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h54201 X0 X1]
    conv => enter [1]; rw [← l237 X1 X0]
  have l242 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l144 sK0 sK1]
    conv => enter [1]; rw [← l239 sK1 sK0]
  have l243 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l240 sK0 sK1]
    conv => enter [1]; rw [← l138 sK1 sK0]
  have l244 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l243 sK0 sK1]
    conv => enter [1]; rw [l210 sK1 sK0]
  have l245 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l227 sK0 sK1]
    conv => enter [1]; rw [l244 sK0 sK1]
  have l246 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l187 sK1 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 sK1]
  have l247 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l187 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l248 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l187 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l249 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l248 sK1 sK0 X0]
  have l250 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l247 sK0 sK1]
  have l251 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [← l246 sK1 sK0]
  have l252 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l250 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l253 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l251 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l254 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l253 sK1 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l255 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l254 sK1 sK0]
    conv => enter [1, 2]; rw [l226 sK0 sK1]
  have l256 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l255 sK1 sK0]
    conv => enter [1, 2]; rw [← l231 sK0 sK1]
  have l257 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l256 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l258 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l257 sK1 sK0]
    conv => enter [1]; rw [← l242 sK0 sK1]
  have l259 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l252 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l260 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l259 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l261 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l252 sK0 sK1]
    conv => enter [1]; rw [← l217 sK0 sK1]
  have l262 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l217 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l263 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l262 sK0 sK1 X0]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l264 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l260 sK0 sK1 X0]
    conv => enter [1]; rw [← l263 sK0 sK1 X0]
  have l265 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l264 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l266 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1, 2]; rw [← l245 sK0 sK1]
  have l267 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l266 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l268 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l144 sK0 sK1]
    conv => enter [1]; rw [← l267 sK0 sK1]
  have l269 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l261 sK0 sK1]
    conv => enter [1]; rw [l268 sK0 sK1]
  have l270 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l258 sK1 sK0]
  have l271 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l270 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l272 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l265 sK0 sK1 X0]
    conv => enter [1]; rw [← l271 sK1 sK0 X0]
  have l273 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l238 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l274 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l249 sK1 sK0 sK1]
    conv => enter [1]; rw [← l273 sK0 sK1]
  have l275 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l274 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l276 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l187 sK1 sK0]
    conv => enter [1]; rw [← l275 sK1 sK0]
  have l277 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l276 sK1 sK0]
    conv => enter [1]; rw [← l272 sK0 sK1 sK1]
  have l278 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l269 sK0 sK1]
    conv => enter [1]; rw [← l277 sK1 sK0]
  have l279 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l241 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l280 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l187 sK1 sK0]
    conv => enter [1]; rw [← l279 sK1 sK0]
  have l281 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l280 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l282 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l281 sK1 sK0]
  have l283 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l278 sK0 sK1]
    conv => enter [1]; rw [← l282 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l283 x y]

theorem Equation4512_54014_54201_implies_Equation4314 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54014 : Equation54014 G) (h54201 : Equation54201 G) : Equation4314 G := by
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
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l6 sK1 sK0 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l4 sK1 sK0 X0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK0 sK0]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0))) = (sK1 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54014 sK0 X0]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK0) ◇ sK0)]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [l17 sK1 sK0]
  have l22 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)) = (((sK1 ◇ sK0) ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 ((sK1 ◇ sK0) ◇ sK0) X0]
    conv => enter [1, 1]; rw [l17 sK1 sK0]
  have l23 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l22 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [l21 sK1 sK0]
  have l25 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l23 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK0) ◇ sK1)]
    conv => enter [1, 2]; rw [← l24 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ sK0) ◇ sK1) X0]
    conv => enter [1, 1]; rw [l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l29 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1]
  have l32 : ∀ sK1 sK0 : G, (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 ((sK1 ◇ sK0) ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l27 sK0 sK1]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
    conv => enter [1]; rw [l33 sK1 sK0]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l30 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← h54201 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [← h54201 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l41 sK1 sK0]
    conv => enter [1]; rw [← l11 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l42 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0 sK0]
    conv => enter [1]; rw [← l44 sK0 sK1]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l45 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l46 sK1 sK0]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l17 sK1 sK0]
    conv => enter [1]; rw [l38 sK1 sK0]
  have l49 : ∀ sK1 sK0 : G, (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 ((sK1 ◇ sK0) ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [l38 sK1 sK0]
  have l50 : ∀ sK1 sK0 : G, (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l51 : ∀ sK1 sK0 : G, (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l52 : ∀ sK1 sK0 : G, (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [← l11 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l53 : ∀ sK1 sK0 : G, (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l53 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 (sK1 ◇ sK1)]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l15 sK1 sK0 sK1]
    conv => enter [1]; rw [← l54 sK0 sK1]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l55 sK1 sK0]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l56 sK1 sK0]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l27 sK0 sK1]
    conv => enter [1, 2]; rw [l48 sK1 sK0]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l58 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1, 2]; rw [← l59 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [← h54014 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l61 x y]

theorem Equation4512_54014_54201_implies_Equation54024 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54014 : Equation54014 G) (h54201 : Equation54201 G) : Equation54024 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK0]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK0)]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l6 sK1]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) sK0 X0]
    conv => enter [1, 1]; rw [l7 sK1 sK0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK0) X0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l3 sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l6 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [l7 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l13 sK0 sK1]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK1 sK0 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l15 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l17 sK1 sK0]
    conv => enter [1]; rw [← h54201 (sK1 ◇ sK0) (sK1 ◇ sK1)]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l18 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l16 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l23 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h54014 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l24 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h54014 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK0]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 (sK1 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [l11 sK1 sK0 sK0]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [l9 sK1 ((sK1 ◇ sK0) ◇ sK0)]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 ((sK1 ◇ sK0) ◇ sK0)]
  have l29 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1, 2]; rw [l6 sK1]
  have l30 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l22 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK1 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l27 sK1 sK0]
  have l34 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l28 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ sK1)]
  have l35 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l29 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l36 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l30 sK1]
    conv => enter [1]; rw [← l3 sK1]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l33 sK1 sK0]
  have l38 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l35 sK1]
  have l39 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l36 sK1]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1, 2]; rw [l34 sK1 sK0]
  have l41 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [l38 sK1]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))]
  have l43 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l39 sK1]
    conv => enter [1]; rw [l41 sK1]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l42 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l39 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l46 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l39 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l47 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l39 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l48 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l39 sK1]
    conv => enter [1]; rw [l46 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l43 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l48 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l51 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1 X0]
  have l52 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) X0]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1, 2]; rw [← l49 sK0 sK1]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [l11 sK1 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l49 sK0 sK1]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [l55 sK1 sK0]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [l56 sK1 sK0]
  have l58 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l11 sK1 sK0 X0]
    conv => enter [1]; rw [l47 sK1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [l11 sK1 sK0 X0]
  have l59 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l7 sK1 sK0]
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1, 2]; rw [l7 sK1 sK0]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK0)]
  have l61 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l58 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ sK0) ◇ X0)]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l60 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK0)]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l62 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l53 sK0 sK1]
    conv => enter [1]; rw [l63 sK0 sK1]
  have l65 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK0) X0]
  have l66 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l65 sK0 sK1 X0]
  have l67 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l44 sK1 sK0]
  have l68 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l68 sK0 sK1]
    conv => enter [1]; rw [← l66 sK0 sK1 (sK1 ◇ sK1)]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l69 sK0 sK1]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l57 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l71 sK1 sK0]
    conv => enter [1]; rw [← l61 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l73 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l57 sK1 sK0]
    conv => enter [1]; rw [← l72 sK1 sK0]
  have l74 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l73 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l75 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l74 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l76 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l75 sK1 sK0 X0]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1 ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [l31 sK1 sK0]
  have l78 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [← l66 sK0 sK1 sK1]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l78 sK0 sK1]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1]; rw [← l66 sK0 sK1 sK0]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1, 2]; rw [l53 sK0 sK1]
  have l82 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l83 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l82 sK1 sK0]
  have l84 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l45 sK0 sK1]
  have l85 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK1]
  have l86 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l52 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l87 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l88 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l0 sK1 sK0 ((sK1 ◇ sK1) ◇ sK0)]
  have l89 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK0]
  have l90 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l76 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l86 sK0 sK1]
  have l91 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l85 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l92 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l84 sK1 sK0]
  have l93 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l89 sK0 sK1]
    conv => enter [1]; rw [← h54201 (sK1 ◇ sK0) sK1]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l90 sK1 sK0]
  have l95 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l91 sK1 sK0]
  have l96 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [l92 sK0 sK1]
    conv => enter [1, 2]; rw [← l70 sK0 sK1]
  have l97 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l87 sK0 sK1]
  have l98 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1, 2]; rw [← l70 sK0 sK1]
  have l99 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l96 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l100 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l93 sK0 sK1]
  have l101 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l98 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l102 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l39 sK1]
    conv => enter [1]; rw [l100 sK0 sK1]
  have l103 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l101 sK0 sK1]
    conv => enter [1]; rw [← l99 sK0 sK1]
  have l104 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l103 sK0 sK1]
  have l105 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l97 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK1)]
  have l106 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l97 sK1 sK0]
  have l107 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l106 sK1 sK0]
    conv => enter [1, 2]; rw [← l2 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l108 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l102 sK0 sK1]
    conv => enter [1]; rw [← l105 sK1 sK0]
  have l109 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l107 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK0))]
  have l110 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l108 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l111 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 sK0]
    conv => enter [1]; rw [l109 sK1 sK0]
  have l112 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l31 sK1 sK0]
    conv => enter [1]; rw [l111 sK1 sK0]
  have l113 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l110 sK0 sK1]
    conv => enter [1]; rw [← l52 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l114 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l112 sK1 sK0]
    conv => enter [1]; rw [← l113 sK0 sK1]
  have l115 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l114 sK1 sK0]
    conv => enter [1]; rw [← l70 sK0 sK1]
  have l116 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l104 sK0 sK1]
    conv => enter [1]; rw [← l115 sK1 sK0]
  have l117 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l116 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l118 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l104 sK0 sK1]
    conv => enter [1]; rw [l117 sK0 sK1]
  have l119 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l118 sK0 sK1]
    conv => enter [1]; rw [← l95 sK1 sK0]
  have l120 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l119 sK0 sK1]
  have l121 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l120 sK0 sK1]
    conv => enter [1]; rw [← l83 sK1 sK0]
  have l122 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l121 sK0 sK1]
    conv => enter [1]; rw [← l99 sK0 sK1]
  have l123 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l104 sK0 sK1]
    conv => enter [1]; rw [← l122 sK0 sK1]
  have l124 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l123 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l125 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1, 2]; rw [← l97 sK1 sK0]
  have l126 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l125 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l127 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l126 sK0 sK1]
    conv => enter [1]; rw [← l124 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l127 x y]

end Semigroup5
