import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_4753_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4753 : Equation4753 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4753 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4753 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4753 sK0 X0 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation10_4512_implies_Equation4757 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4757 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1]; rw [h10 (sK0 ◇ sK0) sK1]
    conv => enter [1, 1]; rw [l2 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_4757_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4757 : Equation4757 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4757 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h4757 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4757 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [l3 X0]
    conv => enter [1]; rw [← h4757 X0 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l7 sK1 sK0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l10 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l3 X0]
    conv => enter [1]; rw [l5 X0]
  have l11 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l9 X0 X0]
    conv => enter [1]; rw [l10 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [l11 X0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l11 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l11 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 2]; rw [l12 (sK1 ◇ sK0)]
  have l17 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [← l15 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation10_4512_implies_Equation4760 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4760 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_4760_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4760 : Equation4760 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h4760 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4760 X0 X0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4760 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) X2]
    conv => enter [1, 1]; rw [← h4760 X0 X1]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4760 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)))]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ X0))) X2]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
  have l10 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l8 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l12 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))))) := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))]
  have l13 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l11 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l14 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))))) := by
    intro X0
    conv => enter [1]; rw [l12 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X0]
  have l15 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l14 X0]
    conv => enter [1]; rw [← l13 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0) X0]
  have l16 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l15 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l17 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l16 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4760 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2]; rw [← l23 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l27 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4760 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l32 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l31 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l17 (sK0 ◇ (sK1 ◇ sK0))]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l37 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l36 sK0 sK1 ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1 ((sK1 ◇ sK0) ◇ sK0)]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l41 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l41 x y]

theorem Equation10_4512_implies_Equation4763 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4763 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h10 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_4763_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4763 : Equation4763 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4763 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h4763 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X2)))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X2)))]
    conv => enter [1]; rw [← h4763 X2 (X0 ◇ X1) X3]
  have l2 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X2))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X3 ◇ X2)]
    conv => enter [1]; rw [l1 X2 X0 X1 X3]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4763 (X1 ◇ X1) X2 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 X0 X1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l4 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X1 (X2 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l6 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 (X2 ◇ (X0 ◇ X1))]
  have l8 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l7 X1 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 X1 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l8 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4763 X1 (X0 ◇ X1) X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0]
  have l12 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l11 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation10_4512_implies_Equation4767 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4767 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l3 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1]; rw [h10 (sK0 ◇ sK0) sK2]
    conv => enter [1, 1]; rw [l2 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK1]
    conv => enter [1, 1]; rw [← l3 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_4767_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4767 : Equation4767 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4767 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h4767 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4767 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l9 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation10_4512_implies_Equation4771 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4771 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK2]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_4771_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4771 : Equation4771 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4771 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l4 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4771 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation10_4512_implies_Equation4775 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4775 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [h10 (sK2 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK0)) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK0]
  have l3 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l1 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l3 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l5 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) sK0]
  have l6 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h10 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_4775_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4775 : Equation4775 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4775 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h4775 X0 (X0 ◇ X0) X0]
  have l3 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4775 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ (X0 ◇ sK0))]
  have l4 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (X0 ◇ sK0))]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 (sK1 ◇ sK0)]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [← l5 (sK1 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation10_4512_implies_Equation4779 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4779 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h10 sK1 sK0]
  have l1 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1, 2]; rw [h10 (sK3 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK1)) (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) sK1]
  have l3 : ∀ sK2 sK1 sK3 sK0 X0 : G, (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1, 2]; rw [l1 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l3 sK2 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l5 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK1) sK1]
  have l6 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK3 sK0 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_4779_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4779 : Equation4779 G) : Equation10 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4779 (X0 ◇ (X1 ◇ (X2 ◇ X0))) X3 X0 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4779 X0 X0 X1 X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4779 (X1 ◇ X0) X0 X0 X1]
    conv => enter [1, 2]; rw [← h4779 X0 (X1 ◇ X0) X1 X1]
  have l2 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))))) = X2 := by
    intro X2 X0 X1 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X2)))]
    conv => enter [1]; rw [← h4779 X2 (X0 ◇ X1) X3 X4]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1]; rw [l2 X0 X1 X2 X0 (X0 ◇ (X1 ◇ (X2 ◇ X0)))]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 (X1 ◇ X0) X1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation10_4512_implies_Equation4784 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4784 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_4784_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4784 : Equation4784 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h4784 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h4784 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4784 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l3 X0]
    conv => enter [1]; rw [← h4784 X0 X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 2]; rw [l4 sK0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← l3 X0]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← h4784 X0 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l8 X0]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l10 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l10 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l10 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l7 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation10_4512_implies_Equation4787 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4787 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h10 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h10 sK0 sK1]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h10 X2 (X0 ◇ X1)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK1 ◇ sK0)]
  have l5 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (X0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_4787_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4787 : Equation4787 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4787 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4787 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ X0)) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l4 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4787 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 2]; rw [← l11 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation10_4512_implies_Equation4790 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4790 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h10 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ (sK2 ◇ sK0)) sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l2 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_4790_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4790 : Equation4790 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4790 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4790 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4790 (sK0 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4790 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 sK0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 (sK1 ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation10_4512_implies_Equation4794 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4794 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ sK0) sK1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_4794_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4794 : Equation4794 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4794 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) X2]
    conv => enter [1, 1]; rw [← h4794 X0 X1]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4794 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4794 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ (X0 ◇ X0))) X2]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X0)) X2]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l8 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 X2]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)))]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l5 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4794 X0 X1]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 ((sK1 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 sK1]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l9 X0 (X0 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK1 sK0 X0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 ((sK1 ◇ sK0) ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 (sK1 ◇ sK0) (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0 (sK1 ◇ sK0)]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l14 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l19 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l19 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [l19 sK1 sK0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 2]; rw [l19 sK1 sK0]
  have l26 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1]; rw [← l18 sK0 sK0 sK0]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [l12 (sK1 ◇ sK0) sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l26 sK0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK0]
    conv => enter [1, 2, 2]; rw [← l26 sK0]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [l12 (sK1 ◇ sK0) sK0]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← l31 sK1 sK0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l36 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l29 sK1 sK0]
  have l37 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1 (sK1 ◇ sK0)]
  have l38 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l38 x y]

theorem Equation10_4512_implies_Equation4797 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4797 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h10 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l6 sK1 sK0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2]; rw [l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [l17 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation4512_4797_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4797 : Equation4797 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4797 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h4797 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h4797 X0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0 X0]
    conv => enter [1]; rw [l7 X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l8 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l8 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l8 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l9 (sK1 ◇ sK0)]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4797 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l12 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l17 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l18 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 (sK1 ◇ sK0)]
  have l19 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation10_4512_implies_Equation4800 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4800 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_4800_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4800 : Equation4800 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4800 (X1 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h4800 X0 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 (X0 ◇ X1) (X0 ◇ X1)]
    conv => enter [1]; rw [← h4800 X1 (X0 ◇ X1) X0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation10_4512_implies_Equation4804 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4804 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ sK0) sK2]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l2 sK2 sK0]
    conv => enter [1, 2]; rw [l3 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l4 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK0)) sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_4804_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4804 : Equation4804 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4804 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4804 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h4804 X0 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l7 sK0 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l10 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l8 (sK1 ◇ sK0) sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation10_4512_implies_Equation4808 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4808 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) sK0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [h10 (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) sK0]
  have l6 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h10 sK0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK2 sK1 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_4808_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4808 : Equation4808 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X3 := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4808 X3 X2 (X0 ◇ X1)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4808 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h4808 X0 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h4808 (X0 ◇ X0) X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l4 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l7 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l7 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l7 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [← l8 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l7 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l16 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4808 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 sK1 sK0]
  have l17 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l18 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← l15 sK0 sK1 (X0 ◇ (sK1 ◇ sK0))]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4808 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l14 sK1 sK0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1]; rw [← l15 sK0 sK1 ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [← l15 sK0 sK1 (X0 ◇ (sK1 ◇ sK0))]
  have l22 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1 sK0]
    conv => enter [1]; rw [← l21 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation10_4512_implies_Equation4812 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4812 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [h10 (sK2 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK0)) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l5 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) sK0]
  have l6 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h10 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_4812_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4812 : Equation4812 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h4812 (X1 ◇ (X1 ◇ X0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← h4812 X0 X1 X1]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4812 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h4812 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X0) (X0 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 (X0 ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2, 2]; rw [← l2 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h4812 X0 X1 X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l9 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← l2 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ X0))]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l11 X0]
    conv => enter [1, 2]; rw [← l8 X0 X0]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l12 X0]
    conv => enter [1]; rw [l9 X0 X0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l13 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l13 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l14 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation10_4512_implies_Equation4816 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4816 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h10 sK1 sK0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) sK1]
  have l2 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 2]; rw [h10 (sK3 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ sK1)) (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l5 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK1) sK1]
  have l6 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK3 sK0 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_4816_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4816 : Equation4816 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4816 (X1 ◇ X0) X0 X0 X1]
    conv => enter [1, 2]; rw [← h4816 X0 X0 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l1 (X0 ◇ (X1 ◇ X2)) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← h4816 X2 (X0 ◇ (X1 ◇ X2)) X0 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [l2 X2 X0 X1]
  have l6 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l5 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation10_4512_implies_Equation4821 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4821 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l0 sK2 sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_4821_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4821 : Equation4821 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4821 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l6 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK0]
  have l11 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4821 (sK1 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l6 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l13 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l15 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l15 sK1 sK0 sK1]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation10_4512_implies_Equation4825 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4825 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h10 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ (sK1 ◇ sK0)) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_4825_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4825 : Equation4825 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4825 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h4825 X0 X1 (X1 ◇ X0)]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3)))))) = X3 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3)))]
    conv => enter [1]; rw [← h4825 X3 (X0 ◇ X1) X2]
  have l2 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3))))))) = X3 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l1 X3 X0 X1 X2]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4825 (X1 ◇ X1) X0 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 X0 X1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l4 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X1 (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))))]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l6 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 (X0 ◇ X1)]
  have l8 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l7 X1 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 X1 X1]
  have l9 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4825 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 sK1 sK0]
  have l10 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l3 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l12 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l8 (sK0 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation10_4512_implies_Equation4829 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4829 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h10 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← h10 sK0 sK2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← h10 X0 X1]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h10 X2 (X0 ◇ X1)]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) (sK2 ◇ sK0)]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) ◇ X0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) X0]
    conv => enter [1]; rw [l4 sK0 ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) X0]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l3 X0 X1 X2]
    conv => enter [1]; rw [← l4 X1 (X2 ◇ X0) X0]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l7 sK0 ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) ◇ X0) sK0]
  have l9 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) ◇ X0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))))]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 X0]
  have l10 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l9 sK0 (sK2 ◇ sK0) sK1 sK2]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 sK2]
    conv => enter [1]; rw [l10 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation4512_4829_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4829 : Equation4829 G) : Equation10 G := by
  have l0 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4829 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4829 sK0 X0 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l6 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation10_4512_implies_Equation4833 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4833 G := by
  have l0 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [h10 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h10 (sK1 ◇ (sK0 ◇ sK1)) sK3]
  have l1 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK3 sK1 sK0]
    conv => enter [1, 2]; rw [← h10 sK1 sK0]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ sK1) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1, 2]; rw [l1 sK3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l2 sK2 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_4833_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4833 : Equation4833 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4833 (X1 ◇ X0) X0 X1 X0]
    conv => enter [1, 2]; rw [← h4833 X0 X1 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h4833 X0 X1 X2 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [l1 X2 X0]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4833 sK0 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l5 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l3 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation10_4512_implies_Equation4838 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4838 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ sK0) sK1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK0]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l5 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_4838_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4838 : Equation4838 G) : Equation10 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4838 X0 sK0 sK1]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4838 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4838 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l3 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h4838 X0 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l7 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h4838 X1 X0 (X0 ◇ (X1 ◇ X1))]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l7 X1]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l10 X0 X1]
    conv => enter [1]; rw [l12 X1 X0]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l13 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation10_4512_implies_Equation4842 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4842 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [h10 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) (X0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (X0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l6 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h10 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 sK2 sK1 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_4842_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4842 : Equation4842 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))))) = X3 := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [← h4842 X3 X2 (X0 ◇ X1)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4842 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h4842 X0 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h4842 (X0 ◇ X0) X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l4 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l7 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l7 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l7 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [← l8 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l7 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l16 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4842 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 sK1 sK0]
  have l17 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l18 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [l7 (sK1 ◇ sK0)]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4842 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l14 sK1 sK0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1]; rw [← l15 sK0 sK1 (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [l7 (sK1 ◇ sK0)]
  have l22 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1 sK0]
    conv => enter [1]; rw [← l21 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation10_4512_implies_Equation4846 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4846 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) sK0]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [h10 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK2 ◇ sK0)) sK0]
  have l6 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h10 sK0 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 sK2 sK1 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_4846_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4846 : Equation4846 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h4846 (X1 ◇ (X0 ◇ X0)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h4846 X0 X1 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4846 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h4846 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h4846 X0 X0 X0]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0 X0]
    conv => enter [1]; rw [l5 X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l8 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l8 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 sK0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 X0]
    conv => enter [1]; rw [← h4846 X0 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l9 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l13 X1 X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l11 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation10_4512_implies_Equation4850 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4850 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h10 sK1 sK0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) sK1]
  have l2 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) sK1]
  have l3 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 2]; rw [h10 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) (X0 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) (X0 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l5 : ∀ sK3 sK2 sK0 sK1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1, 2]; rw [l2 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK2 ◇ (sK0 ◇ sK1)) sK1]
  have l6 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [h10 sK1 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l5 sK3 sK2 sK0 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK3 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_4850_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4850 : Equation4850 G) : Equation10 G := by
  have l0 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1)))) = X1 := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4850 X1 sK0 sK1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4850 (X1 ◇ X0) X0 X1 X1]
    conv => enter [1, 2]; rw [← h4850 X0 X1 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l3 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))) = X1 := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X1 sK0 sK1 X0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 (X0 ◇ X1) X1 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4850 X1 (X0 ◇ X1) (X1 ◇ (X1 ◇ X1)) X0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation10_4512_implies_Equation4855 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4855 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ sK0) sK2]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l2 sK2 sK0]
    conv => enter [1, 2]; rw [l3 sK0]
  have l5 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l4 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK0 ◇ sK0)) sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l5 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_4855_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4855 : Equation4855 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4855 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4855 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h4855 X0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0 X0]
    conv => enter [1]; rw [← h4855 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation10_4512_implies_Equation4859 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4859 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) sK0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [h10 (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) sK0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l3 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK1 ◇ sK0)) sK0]
  have l6 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h10 sK0 (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 sK2 sK1 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_4859_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4859 : Equation4859 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4859 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h4859 X0 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h4859 (X0 ◇ X0) X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l6 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0]
    conv => enter [1]; rw [← h4859 X0 X0 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l9 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l9 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l9 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l9 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l10 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l9 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l18 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4859 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l11 sK1 sK0]
  have l19 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l20 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l10 X0 (sK1 ◇ sK0)]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4859 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l16 sK1 sK0]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1]; rw [← l17 sK0 sK1 (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l10 X0 (sK1 ◇ sK0)]
  have l24 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l24 x y]

theorem Equation10_4512_implies_Equation4863 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4863 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [h10 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
  have l4 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) sK0]
  have l5 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l4 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) sK0]
  have l6 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h10 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_4863_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4863 : Equation4863 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4863 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h4863 X0 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h4863 X0 X1 X0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation10_4512_implies_Equation4867 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4867 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h10 sK1 sK0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) sK1]
  have l2 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 2]; rw [h10 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))]
  have l3 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK1) sK1]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))]
  have l5 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l3 sK3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ (sK0 ◇ sK1)) sK1]
  have l6 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l5 sK3 sK0 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_4867_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4867 : Equation4867 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4867 (X1 ◇ X0) X0 X1 X1]
    conv => enter [1, 2]; rw [← h4867 X0 X1 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [l1 (X0 ◇ X1) (X0 ◇ X1)]
    conv => enter [1]; rw [← h4867 X1 X2 (X0 ◇ X1) X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [l1 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X1 X2 X0]
  have l6 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l5 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation10_4512_implies_Equation4872 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4872 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h10 (sK1 ◇ sK1) sK0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [l3 sK1]
  have l5 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l6 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1, 2]; rw [l5 sK3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l6 sK2 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

theorem Equation4512_4872_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4872 : Equation4872 G) : Equation10 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))))) = X4 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X4)))]
    conv => enter [1]; rw [← h4872 X4 (X0 ◇ X1) X2 X3]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X1 X0 X0 X0]
    conv => enter [1, 2, 2]; rw [← h4872 X0 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4872 X0 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation10_4512_implies_Equation4877 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4877 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [h10 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h10 sK1 sK2]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) sK1]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) sK1]
  have l3 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 2]; rw [h10 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))]
  have l5 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK2 ◇ sK1)) sK1]
  have l6 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [h10 sK1 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l5 sK3 sK0 sK2 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK3 sK0 sK2]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_4877_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4877 : Equation4877 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4877 (X1 ◇ X0) X0 X1 X1]
    conv => enter [1, 2]; rw [← h4877 X0 X1 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4877 sK0 (sK1 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l6 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation10_4512_implies_Equation4882 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4882 G := by
  have l0 : ∀ sK3 sK1 : G, (sK3 ◇ sK1) = ((sK3 ◇ sK1) ◇ sK1) := by
    intro sK3 sK1
    conv => enter [1]; rw [h10 (sK3 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h10 sK1 sK3]
  have l1 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ (sK3 ◇ sK1)) = ((sK0 ◇ (sK3 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK3 sK1
    conv => enter [1, 2]; rw [l0 sK3 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK3 ◇ sK1) sK1]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) sK1]
  have l3 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 2]; rw [h10 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))) X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))) (X0 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) (X0 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))]
  have l5 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))) = ((sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))) ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK3 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK3 ◇ sK1)) sK1]
  have l6 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l5 sK3 sK0 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_4882_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4882 : Equation4882 G) : Equation10 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)))) = X0 := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [← h4882 X0 X1 sK0 sK1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4882 (X1 ◇ X0) X0 X1 X1]
    conv => enter [1, 2]; rw [← h4882 X0 X1 X1 X1]
  have l2 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))))) = X4 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X2 ◇ X4)))]
    conv => enter [1]; rw [← h4882 X4 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) = X0 := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l0 X0 X1 sK0 sK1]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4882 (X1 ◇ X1) X2 X0 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 X0 X1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l5 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 X1 (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1))))]
  have l8 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l7 X1 X1 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 X1 X1 X1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l10 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation10_4512_implies_Equation4887 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4887 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h10 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1]
  have l3 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 2]; rw [h10 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) (X0 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (X0 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l5 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l6 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l5 sK3 sK0 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_4887_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4887 : Equation4887 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4887 (X1 ◇ X0) X0 X1 X1]
    conv => enter [1, 2]; rw [← h4887 X0 X1 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h4887 X0 X1 X2 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [l1 X2 X0]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l6 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l5 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation10_4512_implies_Equation4892 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4892 G := by
  have l0 : ∀ sK0 sK2 : G, (sK0 ◇ sK2) = ((sK0 ◇ sK2) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [h10 (sK0 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h10 sK2 sK0]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) sK2]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, sK2 = ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ sK2) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h10 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) sK2]
  have l3 : ∀ sK3 sK4 sK1 sK0 sK2 X0 : G, (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK3 sK4 sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [h10 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1, 2]; rw [l3 sK3 sK4 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l5 : ∀ sK4 sK1 sK0 sK2 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK2) := by
    intro sK4 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ (sK0 ◇ sK2)) sK2]
  have l6 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [h10 sK2 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l5 sK4 sK1 sK0 sK2]
  have l7 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ sK2) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK3 sK4 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l6 sK2 sK4 sK1 sK0]
  have l8 : ∀ sK2 sK3 sK4 sK1 sK0 : G, sK2 = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l7 sK2 sK3 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z w u]

theorem Equation4512_4892_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4892 : Equation4892 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4892 (X1 ◇ X0) X0 X1 X1 X1]
    conv => enter [1, 2]; rw [← h4892 X0 X1 X1 X1 X1]
  have l1 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))))) = X5 := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5)))]
    conv => enter [1]; rw [← h4892 X5 (X0 ◇ X1) X2 X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l3 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1))))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4892 (X1 ◇ X1) X2 X3 X4 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X0 X1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1)))))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [l3 X1 X2 X3 X4 X0]
    conv => enter [1]; rw [← h4512 X1 X1 (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1))))]
  have l6 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l5 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X1 X1 X1]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l7 sK1 sK0 (sK1 ◇ sK0)]
  have l9 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4892 (sK1 ◇ sK0) X0 X1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4892 sK0 (sK1 ◇ sK0) sK0 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation11_implies_Equation414 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation414 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [← h11 sK0 sK1]
    conv => enter [1]; rw [← h11 X0 sK0]
  intro x y
  conv => enter [1]; rw [← l0 x x y]

theorem Equation414_4512_implies_Equation11 (G : Type*) [Magma G] (h414 : Equation414 G) (h4512 : Equation4512 G) : Equation11 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h414 sK0 sK1]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h414 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation11_4512_implies_Equation417 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation417 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h11 X0 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l0 x x y]

theorem Equation417_4512_implies_Equation11 (G : Type*) [Magma G] (h417 : Equation417 G) (h4512 : Equation4512 G) : Equation11 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h417 X0 X1]
    conv => enter [1]; rw [← h417 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X2]
    conv => enter [1, 1]; rw [← h417 X0 X1]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h417 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l13 : ∀ sK1 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h417 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l14 : ∀ sK1 X0 : G, sK1 = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h417 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ X0))]
  have l15 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [h417 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1, 2]; rw [← l12 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1]
    conv => enter [1]; rw [← l10 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l18 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l17 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l18 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l13 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) X0]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l20 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l22 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l21 sK1 X0]
    conv => enter [1, 2]; rw [← l19 sK1 X0]
  have l23 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ (sK1 ◇ X0)) ◇ X1)) = (sK1 ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l14 sK1 X0]
  have l24 : ∀ sK1 X1 X0 : G, (sK1 ◇ X1) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ X0) ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l23 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ X0) X1]
  have l25 : ∀ sK1 X1 X0 : G, (sK1 ◇ X1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l24 sK1 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 X0 X1]
  have l26 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l14 sK1 X0]
    conv => enter [1]; rw [← l22 sK1 (X0 ◇ (sK1 ◇ X0))]
  have l27 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h417 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l19 sK1 (X0 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l28 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (((sK1 ◇ sK1) ◇ X0) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ X0)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l3 ((sK1 ◇ sK1) ◇ X0) sK1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l22 sK1 X0]
  have l29 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2, 2]; rw [l26 sK1 X0]
    conv => enter [1]; rw [l3 X0 sK1]
  have l30 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) X2]
  have l31 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l30 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) X2]
  have l32 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ X0))))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l28 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) X0 (((sK1 ◇ sK1) ◇ X0) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ X0)))))]
  have l33 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l31 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X2]
  have l34 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ X0)))))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l32 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK1) X0 (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ X0))))]
  have l35 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l33 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l36 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ X0))))))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l34 sK1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK1) X0 (sK1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ X0)))]
  have l37 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l35 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l38 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ X0)))))))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l36 sK1 X0]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK1) X0 (sK1 ◇ X0)]
  have l39 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l37 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l40 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ X0))))))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l38 sK1 X0]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← l22 sK1 (X0 ◇ (sK1 ◇ X0))]
  have l41 : ∀ X0 X2 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2
    conv => enter [1]; rw [l39 X0 X2 X0]
    conv => enter [1, 2, 2]; rw [← l11 X0 X2 X0]
  have l42 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ X0)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l40 sK1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l25 sK1 (sK1 ◇ X0) X0]
  have l43 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l42 sK1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l44 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l43 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l27 sK1 X0]
  have l45 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l44 sK1 X0]
    conv => enter [1]; rw [← h417 X0 (sK1 ◇ sK1)]
  have l46 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (sK1 ◇ sK1))) ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1, 1]; rw [← l29 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) X1]
  have l47 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ X1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l46 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (sK1 ◇ sK1)) X1]
  have l48 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l47 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l49 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l48 X0 X1 sK1]
    conv => enter [1]; rw [← l41 X0 ((sK1 ◇ sK1) ◇ X1)]
  have l50 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X0 sK1
    conv => enter [1]; rw [← l45 (X0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [← l44 sK1 X0]
  have l51 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l50 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) ((X0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l52 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X0 sK1
    conv => enter [1]; rw [l51 X0 sK1]
    conv => enter [1]; rw [← l49 X0 ((X0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) sK1]
  have l53 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l52 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
  have l54 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X0 sK1
    conv => enter [1]; rw [l53 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l49 (sK1 ◇ sK1) X0 sK1]
  have l55 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1]; rw [l54 X0 sK1]
    conv => enter [1]; rw [l45 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l55 x y]

theorem Equation11_4512_implies_Equation427 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation427 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h11 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h11 sK1 sK0]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation427_4512_implies_Equation11 (G : Type*) [Magma G] (h427 : Equation427 G) (h4512 : Equation4512 G) : Equation11 G := by
  have l0 : ∀ sK1 : G, sK1 = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h427 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h427 sK1 sK1]
  have l1 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) sK1]
  have l2 : ∀ sK1 : G, sK1 = (sK1 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h427 sK1 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l1 sK1]
  have l3 : ∀ sK1 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) sK1 sK1]
  have l4 : ∀ sK1 : G, sK1 = (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h427 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK1]
  have l5 : ∀ sK1 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h427 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h427 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ sK0)]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1, 2]; rw [← l9 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK0))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h427 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2, 2]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation11_implies_Equation444 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation444 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [← h11 sK1 sK2]
    conv => enter [1]; rw [← h11 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

@[equational_result]
theorem Equation444_implies_Equation11 (G : Type*) [Magma G] (h444 : Equation444 G) : Equation11 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h444 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h444 X1 (X0 ◇ X0) (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation11_4512_implies_Equation452 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation452 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h11 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h11 X0 (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1, 1]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation452_4512_implies_Equation11 (G : Type*) [Magma G] (h452 : Equation452 G) (h4512 : Equation4512 G) : Equation11 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 1]; rw [h452 X0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) X1]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l1 X0 X1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l3 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l2 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h452 X0 sK0 (sK1 ◇ sK1)]
  have l5 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) = X1 := by
    intro X1 X0 sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [← l4 X0 sK0 sK1]
    conv => enter [1]; rw [← h452 X1 X0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l6 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)))) = X1 := by
    intro X1 X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l5 X1 X0 sK0 sK1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X0 X1 X1]
    conv => enter [1]; rw [l6 X1 X0 X1 X1]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation11_4512_implies_Equation455 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation455 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h11 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l1 : ∀ sK1 sK2 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h11 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1))]
  have l2 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l3 : ∀ sK2 sK1 : G, sK2 = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [h11 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 sK1]
  have l4 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK2 ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l3 sK2 sK1]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l4 sK2 sK1]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [h11 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2]
    conv => enter [1]; rw [← l5 sK1 sK2]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← h11 X0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1, 1]; rw [l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation455_implies_Equation11 (G : Type*) [Magma G] (h455 : Equation455 G) : Equation11 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h455 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h455 X1 (X0 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation14_4512_implies_Equation464 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation464 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h14 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h14 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation464_4512_implies_Equation14 (G : Type*) [Magma G] (h464 : Equation464 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h464 X0 X1]
    conv => enter [1]; rw [← h464 X1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h464 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2]; rw [← h464 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h464 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l4 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l6 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation14_4512_implies_Equation481 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation481 G := by
  have l0 : ∀ sK2 : G, sK2 = ((sK2 ◇ sK2) ◇ sK2) := by
    intro sK2
    conv => enter [1]; rw [h14 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h14 sK2 sK2]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l0 sK2]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h14 (sK1 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h14 sK1 sK2]
    conv => enter [1]; rw [← l2 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 1]; rw [← l3 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation481_4512_implies_Equation14 (G : Type*) [Magma G] (h481 : Equation481 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h481 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h481 X2 (X0 ◇ X1) X3]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3)))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X3 ◇ X3)]
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
  have l3 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [l0 X2 X0 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation14_implies_Equation489 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation489 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 sK0 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 1]; rw [← h14 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation489_implies_Equation14 (G : Type*) [Magma G] (h489 : Equation489 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h489 (X0 ◇ X1) X0 X1]
    conv => enter [1]; rw [← h489 X0 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation14_4512_implies_Equation492 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation492 G := by
  have l0 : ∀ sK1 sK2 : G, sK1 = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h14 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h14 sK2 sK1]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK2 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) sK2 X0]
  have l2 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK2 ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h14 sK2 sK1]
  have l3 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h14 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK2 sK1]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1]
    conv => enter [1]; rw [← l1 sK1 sK2 sK2]
  have l5 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h14 sK1 sK2]
    conv => enter [1, 2]; rw [l4 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 sK0 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 1]; rw [← l5 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

end Semigroup5
