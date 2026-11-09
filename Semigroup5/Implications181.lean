import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54520_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54520 : Equation54520 G) : Equation4274 G := by
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
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54520 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK2 X0 X1 sK1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X1)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1)) := by
    intro sK0 sK2 X0 X1 sK1
    conv => enter [1]; rw [h54520 (sK0 ◇ sK2) X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) sK1]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ sK0 sK2 X0 sK1 : G, (((sK0 ◇ sK2) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1 ((sK0 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 sK0 X0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l6 sK0 X1 X0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ X0)]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l6 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ X0)]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l6 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK2) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1]; rw [← l8 sK0 sK2 X0 X0]
  have l16 : ∀ X2 sK0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X1 ◇ X2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X2 sK0 X1
    conv => enter [1]; rw [l7 X2 sK0 X2 X1]
    conv => enter [1]; rw [l6 sK0 X2 (X1 ◇ X2)]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0 X1 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [l14 sK0 X0]
  have l19 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l15 X0 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ X2 sK0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 sK0 X1
    conv => enter [1]; rw [l16 X2 sK0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0 X1 X0]
  have l22 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l19 X0 sK0 sK2]
    conv => enter [1]; rw [l5 sK0 sK2 X0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l23 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0 X1 X0]
  have l24 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l22 X0 sK0 sK1 X0]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK1 ◇ (sK0 ◇ X0))]
  have l25 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [l23 sK0 X1 X0]
  have l26 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l24 X0 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l26 X0 sK0 sK0]
  have l28 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54520 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l27 sK0 X0]
  have l29 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l28 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l20 (sK0 ◇ (sK0 ◇ sK0)) sK0 X2]
  have l30 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l29 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l30 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l31 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l33 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l32 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l33 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54521 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54521 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK0)]
  have l1 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK2 ◇ sK0)]
  have l2 : ∀ X1 sK1 sK2 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X1 sK1 sK2 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK2 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK2 ◇ sK0)) sK1 sK2 sK0 X0]
  have l3 : ∀ X0 sK1 sK2 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro X0 sK1 sK2 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 sK0 X2 X0]
  have l4 : ∀ sK4 sK1 sK2 sK0 X1 X2 : G, (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro sK4 sK1 sK2 sK0 X1 X2
    conv => enter [1]; rw [l3 sK4 sK1 sK2 sK0 X1 X2]
  have l5 : ∀ sK4 sK1 sK2 sK0 X1 X0 : G, (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK2 sK0 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK0)) sK4]
  have l6 : ∀ X0 sK4 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK4 sK1 sK2 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK1 sK2 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK4 sK1 sK2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 X2 sK4 sK1 sK2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK4 sK1 sK2 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z z w x u]

theorem Equation4512_54521_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54521 : Equation54521 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l1 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54521 sK0 (sK0 ◇ sK0) sK0 X0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54521 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [h54521 sK0 sK2 X0 X1 sK0]
  have l7 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54521 sK0 X0 (sK0 ◇ sK0) X1 sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 X1 X0]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK2 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54521 sK0 sK0 (sK0 ◇ sK0) sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54521 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [h54521 sK0 sK0 (sK0 ◇ sK0) sK0 sK0]
  have l12 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l8 sK0 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l13 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h54521 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK2 sK0]
  have l14 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l6 sK0 sK2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l12 sK0 sK0 sK2]
  have l15 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l13 sK0 sK2]
    conv => enter [1]; rw [l14 sK0 sK2]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l11 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l11 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [h54521 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 sK0]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l22 sK0 X0]
    conv => enter [1]; rw [h54521 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 sK0]
  have l24 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l23 sK0 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0 sK0]
    conv => enter [1]; rw [← l15 sK0 sK0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [← l25 sK0 X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [h54521 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 sK0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l27 sK0 X0]
  have l29 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [← h54521 sK0 X1 X1 sK0 sK0]
    conv => enter [1]; rw [h54521 sK0 X1 X1 sK1 sK2]
  have l30 : ∀ sK0 X1 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X1 sK1 sK2
    conv => enter [1]; rw [l28 sK0 X1]
    conv => enter [1]; rw [l29 X1 sK0 sK1 sK2]
  have l31 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [h54521 X0 X1 X2 X3 (X0 ◇ (sK0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l30 sK0 X0 X0 X0]
  have l32 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l31 X0 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l28 sK0 X0]
  have l33 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l32 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l28 sK0 X2]
  intro x y z
  conv => enter [1]; rw [← l33 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54522 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54522 G := by
  have l0 : ∀ X0 sK0 sK2 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK2 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK2 ◇ sK1)]
  have l1 : ∀ X0 sK0 sK2 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK2 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK2 ◇ sK1)]
  have l2 : ∀ X1 sK0 sK2 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X2)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X1 sK0 sK2 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK2 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK2 ◇ sK1)) sK0 sK2 sK1 X0]
  have l3 : ∀ X0 sK0 sK2 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro X0 sK0 sK2 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 sK1 X2 X0]
  have l4 : ∀ sK3 sK0 sK2 sK1 X1 X2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro sK3 sK0 sK2 sK1 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK1 X1 X2]
  have l5 : ∀ sK3 sK0 sK2 sK1 X1 X0 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK2 sK1 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK2 sK1 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK2 ◇ sK1)) sK3]
  have l6 : ∀ X0 sK3 sK0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK3 sK0 sK2 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 X2 sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z w y x]

theorem Equation4512_54522_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54522 : Equation54522 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [l3 sK0 sK2 X0]
  have l12 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (sK0 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l11 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK2) ◇ X0) X1]
  have l13 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l12 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) X0 X1]
  have l14 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l13 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h54522 X1 X0 sK0 (sK0 ◇ sK2)]
  have l15 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [← l14 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l16 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h54522 X1 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l15 X1 X0 sK0 X1]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ X0)]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l5 sK0 X0]
  have l19 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h54522 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← h54522 X0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l16 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l20 sK0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l16 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l6 sK0]
    conv => enter [1]; rw [l23 sK0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l27 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l25 sK0]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← l26 sK0 X0]
    conv => enter [1]; rw [← h54522 X0 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l28 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l30 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l27 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l30 sK0 X0]
  have l32 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← l22 sK0 X0]
    conv => enter [1]; rw [l31 sK0 X0]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l22 sK0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l34 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l22 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l8 sK0]
  have l35 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l29 (sK0 ◇ sK0) sK0]
  have l37 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1, 2]; rw [← l27 sK0]
  have l38 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l38 sK0]
  have l40 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l39 sK0]
    conv => enter [1]; rw [← l27 sK0]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l39 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l42 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l41 sK0 X0]
    conv => enter [1]; rw [← l32 X0 sK0]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1]; rw [← l40 sK0]
  have l44 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l42 sK0 X0]
  have l45 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l3 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [l29 sK2 sK0]
  have l46 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l47 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54522 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l46 sK0 sK2]
  have l48 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [l47 sK0 sK2]
  have l49 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l44 sK0 sK0]
    conv => enter [1]; rw [l48 sK0 sK2]
  have l50 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l49 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l51 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l50 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l52 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l51 sK0 X0 sK0]
    conv => enter [1]; rw [← h54522 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ sK0)]
  have l53 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l52 sK0 X0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l54 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l53 sK0 X0]
    conv => enter [1, 2]; rw [← l43 sK0]
  have l55 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l54 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l56 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l49 sK0 sK2]
    conv => enter [1]; rw [← l55 sK0 sK2]
  have l57 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l56 sK0 sK2]
    conv => enter [1]; rw [l22 sK0 sK2]
  have l58 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ X1)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h54522 (sK0 ◇ X0) sK0 X1 X2]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l59 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1, 2, 2]; rw [l49 sK0 sK2]
    conv => enter [1]; rw [← h54522 ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X0 X1]
  have l60 : ∀ sK2 X0 sK0 X1 X2 : G, ((sK2 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X1)) = (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 sK0 X1 X2
    conv => enter [1]; rw [h54522 (sK2 ◇ X0) (sK0 ◇ sK0) X1 X2]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK2 X0]
  have l61 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54522 sK0 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l62 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l61 sK0 X0 X1]
  have l63 : ∀ sK2 X0 sK0 X1 : G, ((sK2 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X1)) = (((sK0 ◇ sK2) ◇ X0) ◇ (sK0 ◇ X1)) := by
    intro sK2 X0 sK0 X1
    conv => enter [1]; rw [l60 sK2 X0 sK0 X1 sK2]
    conv => enter [1]; rw [← h54522 ((sK0 ◇ sK2) ◇ X0) sK0 X1 sK2]
  have l64 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l59 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ X0)]
  have l65 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ X0) ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54522 X0 (sK0 ◇ sK0) X1 X0]
    conv => enter [1]; rw [← l58 sK0 X0 X1 X0]
  have l66 : ∀ sK2 X0 sK0 X1 : G, ((sK2 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK2 X0 sK0 X1
    conv => enter [1]; rw [l63 sK2 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) X0 (sK0 ◇ X1)]
  have l67 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l64 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← h54522 X0 sK0 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0))]
  have l68 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l65 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ X1)]
  have l69 : ∀ sK2 X0 sK0 X1 : G, ((sK2 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 X0 sK0 X1
    conv => enter [1]; rw [l66 sK2 X0 sK0 X1]
    conv => enter [1]; rw [← h54522 X1 sK0 (sK0 ◇ sK2) X0]
  have l70 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l62 sK0 X0 sK0]
    conv => enter [1]; rw [l67 X0 sK0 sK0 sK2]
  have l71 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l68 X0 sK0 X1]
    conv => enter [1]; rw [← h54522 X1 sK0 sK0 X0]
  have l72 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [← l69 sK2 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 sK2 X0 ((sK0 ◇ sK0) ◇ X1)]
  have l73 : ∀ X1 sK0 sK2 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK0 sK2
    conv => enter [1]; rw [h54522 X1 (sK0 ◇ sK0) sK2 X1]
    conv => enter [1]; rw [← l72 X1 sK0 sK2 X1]
  have l74 : ∀ sK0 X1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [l70 sK0 X1 sK2]
    conv => enter [1]; rw [← l73 X1 sK0 sK2]
  have l75 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [← l71 X1 sK0 sK2]
    conv => enter [1]; rw [← l74 sK0 X1 sK2]
  have l76 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l75 sK0 sK0 X1]
  have l77 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l76 sK0 (sK0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h54522 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l78 : ∀ X0 sK0 X1 X2 X3 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1 X2 X3
    conv => enter [1]; rw [h54522 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← l77 sK0 X1 X0]
  have l79 : ∀ X0 sK0 X1 X2 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l78 X0 sK0 X1 X2 X0]
    conv => enter [1]; rw [← l62 sK0 X2 X0]
  have l80 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l76 sK0 X2]
    conv => enter [1]; rw [← l79 X0 sK0 X1 X2]
  have l81 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l80 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) (X1 ◇ X2)]
  have l82 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [l81 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h54522 X2 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l82 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54523 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54523 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4274 sK2 sK0 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 sK2]
  have l1 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 sK0 sK2]
  have l2 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 sK2]
    conv => enter [1]; rw [l1 sK2 X0 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4274 sK2 sK1 sK3]
    conv => enter [1]; rw [l0 sK2 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l2 w y z]

theorem Equation4512_54523_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54523 : Equation54523 G) : Equation4274 G := by
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
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54523 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l4 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54523 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h54523 X1 sK0 sK0 X0]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54523 (X0 ◇ X1) sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54523 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0]
  have l11 : ∀ X1 sK0 X2 X3 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X2 ◇ (X3 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X2 X3 X0
    conv => enter [1]; rw [h54523 X1 (sK0 ◇ sK0) X2 X3]
    conv => enter [1, 2, 2]; rw [l6 (sK0 ◇ sK0) sK0 X0]
  have l12 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l6 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l12 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l6 X0 sK0 sK0]
  have l14 : ∀ X2 sK0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X2 sK0 X1
    conv => enter [1, 2]; rw [l7 sK0 X2 X2]
    conv => enter [1]; rw [← l11 X1 sK0 X2 X2 X2]
  have l15 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l13 sK0 sK0 X1]
  have l16 : ∀ sK0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l5 X2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 X2 sK0 X1]
  have l17 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l16 sK0 X1 X2]
  have l18 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X1 X2]
  have l19 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l6 X0 sK0 sK0]
  have l20 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l18 sK0 sK0 X1]
    conv => enter [1]; rw [l19 sK0 sK0 X1]
  have l21 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54523 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l20 sK0 (X1 ◇ X1)]
  have l22 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l21 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l15 sK0 X2]
  intro x y z
  conv => enter [1]; rw [← l22 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54525 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54525 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK2 ◇ sK0)]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK2 ◇ sK0)]
  have l2 : ∀ X1 sK0 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X1 sK0 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK2 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK2 ◇ sK0)) sK0 sK2 X0]
  have l3 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 X2 X0]
  have l4 : ∀ sK3 sK0 sK2 X1 X2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro sK3 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 X1 X2]
  have l5 : ∀ sK3 sK0 sK2 X1 X0 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK2 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK2 ◇ sK0)) sK3]
  have l6 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 X2 sK3 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z w y]

theorem Equation4512_54525_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54525 : Equation54525 G) : Equation4274 G := by
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
  have l7 : ∀ sK2 X1 sK0 X0 : G, (sK2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 X1 sK0 X0
    conv => enter [1]; rw [← h54525 X0 (sK0 ◇ sK0) sK2 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54525 X0 (sK0 ◇ sK0) (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54525 X0 (sK0 ◇ sK0) X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54525 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l11 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54525 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l11 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 X0 sK0 X1]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l8 sK0 X1 X0]
    conv => enter [1, 2]; rw [l9 X1 sK0 X1]
  have l15 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← l7 sK2 X1 sK0 X0]
    conv => enter [1, 2]; rw [l9 X1 sK0 X1]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 sK0 X0]
    conv => enter [1, 2]; rw [l12 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l15 X0 sK0 sK2 X0]
    conv => enter [1, 2]; rw [l12 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l12 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 sK0 sK0]
  have l19 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l17 X0 sK0 sK2]
    conv => enter [1]; rw [← l13 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK2]
  have l20 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l19 X0 sK0 sK2]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [← l20 X0 sK0 sK2]
  have l22 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK0 sK2]
    conv => enter [1]; rw [l12 sK0 sK0 (sK0 ◇ sK2)]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l12 sK0 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l12 (sK0 ◇ sK0) sK0 X0]
  have l25 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l24 sK0 sK2]
    conv => enter [1]; rw [← l12 X0 sK0 sK2]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l23 sK0 sK0]
  have l27 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l23 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l27 sK0 sK2]
    conv => enter [1]; rw [← l22 sK0 sK2]
  have l29 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l28 sK0 sK2]
    conv => enter [1]; rw [← l23 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l29 sK0 sK2]
  have l31 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l30 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK2]
  have l32 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l31 sK0 sK2]
  have l33 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l32 sK0 sK2]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [l25 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l34 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54526 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54526 G := by
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
  have l4 : ∀ sK4 sK1 sK3 sK0 X1 X2 : G, (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro sK4 sK1 sK3 sK0 X1 X2
    conv => enter [1]; rw [l3 sK4 sK1 sK3 sK0 X1 X2]
  have l5 : ∀ sK4 sK1 sK3 sK0 X1 X0 : G, (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK1 sK3 sK0 X1 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK3 sK0 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK3 ◇ sK0)) sK4]
  have l6 : ∀ X0 sK4 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK4 sK1 sK3 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK1 sK3 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK4 sK1 sK3 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro X1 X0 X2 sK4 sK1 sK3 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK4 sK1 sK3 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z z w y u]

theorem Equation4512_54526_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54526 : Equation54526 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h54526 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← h54526 X3 sK0 sK0 X0 X0]
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
  have l4 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [h54526 X0 X1 X2 X3 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 X1 sK0 sK0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l4 X0 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X0]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l3 sK0 X2]
  intro x y z
  conv => enter [1]; rw [← l6 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54537 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54537 G := by
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
  intro x y z w u
  conv => enter [1]; rw [l8 x y z w u x]
  conv => enter [1]; rw [l6 w u x z]

theorem Equation4512_54537_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54537 : Equation54537 G) : Equation4274 G := by
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
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54537 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l8 : ∀ sK0 X0 X1 X2 X3 X4 X5 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X0)) ◇ (X5 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2 X3 X4 X5
    conv => enter [1, 2]; rw [h54537 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [h54537 sK0 X2 (X3 ◇ (X4 ◇ X0)) X5 sK0]
  have l9 : ∀ sK0 X0 X1 X2 X3 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h54537 sK0 (X0 ◇ X1) X2 X3 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54537 sK0 (sK0 ◇ sK0) sK0 X0 sK0]
  have l11 : ∀ sK0 X2 X3 X0 X1 : G, (sK0 ◇ (X2 ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 X3 X0 X1
    conv => enter [1]; rw [h54537 sK0 X2 X3 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54537 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h54537 sK0 (sK0 ◇ sK0) X0 X1 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l12 sK0 X0]
  have l15 : ∀ X3 sK0 X0 X2 : G, (X3 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X2 ◇ X3)) := by
    intro X3 sK0 X0 X2
    conv => enter [1, 2]; rw [l13 sK0 X0 X3]
    conv => enter [1]; rw [← l11 sK0 X2 X3 X0 X3]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54537 sK0 sK0 (sK0 ◇ sK0) sK0 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54537 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [h54537 sK0 sK0 (sK0 ◇ sK0) sK0 sK0]
  have l18 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l9 sK0 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l13 sK0 X2 sK0]
  have l19 : ∀ sK0 X0 X1 X2 X3 X4 X5 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ ((X4 ◇ X0) ◇ (X5 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [l8 sK0 X0 X1 X2 X3 X4 X5]
    conv => enter [1]; rw [← h4512 X3 (X4 ◇ X0) (X5 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [h54537 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l21 : ∀ X3 sK0 X0 : G, (X3 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X3 sK0 X0
    conv => enter [1]; rw [l15 X3 sK0 X0 X3]
    conv => enter [1]; rw [h54537 sK0 X3 X3 sK0 sK0]
  have l22 : ∀ sK0 X2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = ((X1 ◇ X2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [← l18 sK0 sK0 X1 X2]
    conv => enter [1]; rw [h54537 sK0 sK0 (X1 ◇ X2) sK0 sK0]
  have l23 : ∀ sK0 X0 X1 X2 X5 X3 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((X5 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X3)) := by
    intro sK0 X0 X1 X2 X5 X3
    conv => enter [1]; rw [l19 sK0 X0 X1 X2 X3 sK0 X5]
    conv => enter [1]; rw [l7 X3 (sK0 ◇ X0) (X5 ◇ (sK0 ◇ sK0)) sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l20 sK0]
  have l25 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [h4512 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l22 sK0 X2 X1]
  have l26 : ∀ sK0 X0 X1 X2 X5 X3 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = (X5 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X3))) := by
    intro sK0 X0 X1 X2 X5 X3
    conv => enter [1]; rw [l23 sK0 X0 X1 X2 X5 X3]
    conv => enter [1]; rw [← h4512 X5 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X3)]
  have l27 : ∀ sK0 X0 X1 X2 X5 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = (X5 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2 X5
    conv => enter [1]; rw [l26 sK0 X0 X1 X2 X5 sK0]
    conv => enter [1, 2]; rw [l21 (sK0 ◇ sK0) sK0 sK0]
  have l28 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l25 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l27 sK0 X0 X1 X2 sK0]
  have l29 : ∀ sK0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((X1 ◇ X2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l28 sK0 sK0 X1 X2]
    conv => enter [1]; rw [h54537 sK0 sK0 (X1 ◇ X2) sK0 sK0]
  have l30 : ∀ sK0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l29 sK0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l4 sK0]
    conv => enter [1]; rw [l30 sK0 X1 X2]
  have l32 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l31 sK0 X1 X2]
  have l33 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h54537 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l17 sK0]
  have l34 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l32 sK0 X1 sK0]
    conv => enter [1]; rw [← l33 sK0 X0 X1 sK0]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l16 sK0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l35 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [h54537 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 sK0]
  have l38 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l37 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l38 sK0 X0 X1]
    conv => enter [1]; rw [l25 X0 X1 sK0]
  have l40 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l34 sK0 sK0 X1]
    conv => enter [1]; rw [l39 sK0 sK0 X1]
  have l41 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [l40 sK0 X1]
  have l42 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [h54537 X0 X1 X2 X3 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l41 sK0 X0]
  have l43 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54537 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l41 sK0 (X0 ◇ X0)]
  have l44 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l42 X0 X1 X2 X0 sK0]
    conv => enter [1]; rw [l43 X2 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l45 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l44 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l24 sK0]
  have l46 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l45 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l35 sK0]
  intro x y z
  conv => enter [1]; rw [← l46 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54538 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54538 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK3]
    conv => enter [1]; rw [h4274 sK0 X1 sK3]
  have l1 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK3]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK3]
  have l2 : ∀ X1 sK0 sK3 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) = ((sK0 ◇ sK3) ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X1 sK0 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 X0]
  have l3 : ∀ X0 sK0 sK3 X1 X2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro X0 sK0 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 (sK0 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 X2 X0]
  have l4 : ∀ sK1 sK0 sK3 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro sK1 sK0 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK3 X1 X2]
  have l5 : ∀ sK1 sK0 sK3 X1 X0 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK3) sK1]
  have l6 : ∀ sK1 sK0 sK3 X0 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK3 X0 (sK0 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 sK1]
  have l7 : ∀ X0 sK1 sK0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK1 sK0 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK1 sK0 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro X1 X0 X2 sK1 sK0 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK1 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z w u y]
  conv => enter [1]; rw [l6 w u y z]

theorem Equation4512_54538_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54538 : Equation54538 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h54538 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← h54538 X3 sK0 sK0 X0 X0]
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
  have l4 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X1 X2 sK0 X0
    conv => enter [1, 2, 2]; rw [l3 sK0 X1]
    conv => enter [1]; rw [← h54538 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 X2 X1]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l4 X1 X2 sK0 X1]
    conv => enter [1]; rw [← l5 sK0 X1 X1]
  have l7 : ∀ X1 sK0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X1 sK0
    conv => enter [1, 2]; rw [l3 sK0 X1]
    conv => enter [1]; rw [l6 X1 X1 sK0]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 X1]
    conv => enter [1]; rw [l7 X1 sK0]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54538 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l8 sK0 (X0 ◇ X1)]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l9 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l3 sK0 X2]
  have l11 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h54538 X0 sK0 sK2 X0 X0]
    conv => enter [1]; rw [← h54538 X1 sK0 sK2 X0 X0]
  have l12 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l10 sK0 sK0 sK2 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54540 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54540 G := by
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
  intro x y z w u
  conv => enter [1]; rw [l8 x y z w u]
  conv => enter [1]; rw [l6 w u z]

theorem Equation4512_54540_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54540 : Equation54540 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54540 X0 X1 X2 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 X0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK0 X0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 (sK0 ◇ sK0) sK0 X0 sK0]
  have l7 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [← l3 X0 sK0 sK2 sK0]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l8 sK0 sK2]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK2)]
  have l10 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 sK2]
  have l11 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 sK2]
  have l12 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 sK2]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0]
  have l14 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0 sK2]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK2)]
  have l16 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l12 sK0 sK2]
    conv => enter [1]; rw [← l15 sK0 sK2]
  have l17 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l16 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK2]
  have l18 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l17 sK0 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK2]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54541 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54541 G := by
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
  intro x y z w u
  conv => enter [1]; rw [l6 x y z w u]
  conv => enter [1]; rw [l5 w u z]

theorem Equation4512_54541_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54541 : Equation54541 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 X2 X3 X1 : G, ((sK0 ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 X2 X3 X1
    conv => enter [1]; rw [← h54541 X1 (sK0 ◇ sK0) (sK0 ◇ X0) X2 X3]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54541 X0 X1 X2 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54541 X0 X1 X2 sK1 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK2)]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ X1 sK0 X0 X2 X3 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) := by
    intro X1 sK0 X0 X2 X3
    conv => enter [1]; rw [← l2 sK0 X0 X2 X3 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 (X2 ◇ (X3 ◇ X3))]
  have l7 : ∀ X1 sK0 X0 X2 X3 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((X2 ◇ (X3 ◇ X3)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0 X2 X3
    conv => enter [1]; rw [l6 X1 sK0 X0 X2 X3]
    conv => enter [1]; rw [l5 sK0 X0 (X2 ◇ (X3 ◇ X3)) sK0]
  have l8 : ∀ X1 sK0 X0 X2 X3 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X2 ◇ ((X3 ◇ X3) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0 X2 X3
    conv => enter [1]; rw [l7 X1 sK0 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X2 (X3 ◇ X3) (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ X1 sK0 X0 sK1 sK2 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro X1 sK0 X0 sK1 sK2
    conv => enter [1]; rw [l8 X1 sK0 X0 X1 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X1) (sK0 ◇ (sK0 ◇ sK0)) sK1 sK0 sK2]
  have l10 : ∀ X1 sK0 X0 sK2 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0 sK2
    conv => enter [1]; rw [l9 X1 sK0 X0 X1 sK2]
    conv => enter [1]; rw [l5 (sK0 ◇ (sK0 ◇ sK0)) (X1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) sK0]
  have l11 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l5 X0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1]; rw [l10 X0 sK0 X0 sK2]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l5 sK0 sK0 X0 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l5 (sK0 ◇ sK0) sK0 X0 sK0]
  have l14 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l5 X0 sK0 sK2 sK0]
    conv => enter [1]; rw [l11 sK2 sK0 sK2]
  have l15 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l14 X0 sK0 sK2]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l12 sK0 X0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [l5 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l21 sK0 X0]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l15 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l23 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54542 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54542 G := by
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
  have l6 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK2]
  have l7 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l8 x y z w u v]
  conv => enter [1]; rw [l6 w u v z]

theorem Equation4512_54542_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54542 : Equation54542 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54542 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54542 X4 sK0 sK0 X0 X0 X0]
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
  have l4 : ∀ X2 sK0 sK2 X0 : G, (X2 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X2 sK0 sK2 X0
    conv => enter [1]; rw [h54542 X2 sK0 sK2 sK0 X2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h54542 X0 sK0 sK0 X2 sK0 sK2]
  have l5 : ∀ sK2 sK0 X2 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 X2
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK2]
    conv => enter [1]; rw [← l4 X2 sK0 sK2 sK2]
  have l6 : ∀ sK0 X2 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [l5 sK2 sK0 X2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54548 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54548 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK1)]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK2 ◇ sK1)]
  have l2 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK2 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK2 X0]
  have l3 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 X2 X0]
  have l4 : ∀ sK0 sK1 sK2 X1 X2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro sK0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X1 X2]
  have l5 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK1)) sK0]
  have l6 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 X2 sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w x y]

theorem Equation4512_54548_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54548 : Equation54548 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54548 sK0 sK0 X1 X0]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l2 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ X1) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 X1 sK0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54548 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (X1 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l8 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54549 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54549 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4274 sK2 sK1 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 sK2]
  have l1 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 sK1 sK2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [l1 sK2 X0 sK1]
  have l3 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 sK2 sK1 sK3]
    conv => enter [1]; rw [l0 sK2 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l2 x y w]

theorem Equation4512_54549_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54549 : Equation54549 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54549 sK0 sK0 X1 X0]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 X1 X0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l3 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ X1) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 X1 sK0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54549 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (X1 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [← l8 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54551 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54551 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK0)]
  have l1 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK2 ◇ sK0)]
  have l2 : ∀ X1 sK1 sK2 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X1 sK1 sK2 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK2 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK2 ◇ sK0)) sK1 sK2 sK0 X0]
  have l3 : ∀ X0 sK1 sK2 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro X0 sK1 sK2 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 sK0 X2 X0]
  have l4 : ∀ sK0 sK1 sK2 X1 X2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro sK0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 X1 X2]
  have l5 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK0)) sK0]
  have l6 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 X2 sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w x y]

theorem Equation4512_54551_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54551 : Equation54551 G) : Equation4274 G := by
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
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l5 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54551 sK0 sK0 X1 X0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54551 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54551 (sK0 ◇ sK0) X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54551 (sK0 ◇ sK0) X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l7 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l8 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l12 sK0 X1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ X3)) = (((sK0 ◇ sK0) ◇ X2) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h54551 X1 X2 X3 ((sK0 ◇ sK0) ◇ X2)]
    conv => enter [1, 2, 2]; rw [← l12 sK0 X0 X2]
  have l16 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [l15 X1 X2 X3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X2 (X1 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l13 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l18 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l16 X1 X2 X3 sK0 X1]
    conv => enter [1]; rw [l11 sK0 X2 (X1 ◇ ((sK0 ◇ sK0) ◇ X1))]
  have l19 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l17 sK0 X1 X0]
    conv => enter [1]; rw [l9 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l20 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l18 X1 X2 X3 sK0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0)) (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l14 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 sK0 X0]
  have l22 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l20 X1 X2 X3 sK0]
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l23 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l22 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l21 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK0]
  have l25 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l23 sK0 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h54551 X0 sK0 sK2 sK0]
  have l26 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l25 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l26 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54552 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54552 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK2 sK3 sK0 X1
    conv => enter [1]; rw [← h4274 sK2 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK2 X1 (sK3 ◇ sK0)]
  have l1 : ∀ X0 sK2 sK3 sK0 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK0 X1
    conv => enter [1]; rw [← h4274 sK2 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 (sK3 ◇ sK0)]
  have l2 : ∀ X1 sK2 sK3 sK0 X2 X0 : G, (X1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X2)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X1 sK2 sK3 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ (sK3 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ (sK3 ◇ sK0)) sK2 sK3 sK0 X0]
  have l3 : ∀ X0 sK2 sK3 sK0 X1 X2 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro X0 sK2 sK3 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK2 sK3 sK0 X2 X0]
  have l4 : ∀ sK1 sK2 sK3 sK0 X1 X2 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro sK1 sK2 sK3 sK0 X1 X2
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 X1 X2]
  have l5 : ∀ sK1 sK2 sK3 sK0 X1 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ (sK3 ◇ sK0)) sK1]
  have l6 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 sK3 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X1 X0 X2 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2 sK3 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w x y u]

theorem Equation4512_54552_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54552 : Equation54552 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (sK0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X2]
    conv => enter [1]; rw [h54552 sK0 sK0 X2 X0 X1]
  have l3 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l2 sK0 X2 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X1]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ X1) X0]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 X1]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54552 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (X1 ◇ X0))]
  have l9 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l8 sK0 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h54552 X0 sK0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54553 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54553 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK3 ◇ sK1))) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK3 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK3 ◇ sK1)]
  have l1 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK1)))) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK3 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK3 ◇ sK1)]
  have l2 : ∀ X1 sK1 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK3 ◇ sK1)) ◇ X2)) = ((sK1 ◇ (sK3 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK1)))) := by
    intro X1 sK1 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK3 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK3 ◇ sK1)) sK1 sK3 X0]
  have l3 : ∀ X0 sK1 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK3 ◇ sK1)) ◇ X2)) := by
    intro X0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK3 (sK1 ◇ (sK3 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK1 sK3 X2 X0]
  have l4 : ∀ sK0 sK1 sK3 X1 X2 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK3 ◇ sK1)) ◇ X2)) := by
    intro sK0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l3 sK0 sK1 sK3 X1 X2]
  have l5 : ∀ sK0 sK1 sK3 X1 X0 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK3 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK3 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK3 ◇ sK1)) sK0]
  have l6 : ∀ X0 sK0 sK1 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK1))) := by
    intro X0 sK0 sK1 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK1))) := by
    intro X1 X0 X2 sK0 sK1 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w x z]

theorem Equation4512_54553_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54553 : Equation54553 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54553 sK0 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l6 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h54553 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← l5 sK0 X1]
  have l7 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 X0 X1]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [← l4 sK0 X0]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X1]
    conv => enter [1]; rw [← l12 X0 sK0 X1]
  have l14 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l7 sK0 X1 sK0]
    conv => enter [1]; rw [← l13 sK0 X1 sK0]
  have l15 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l11 sK0 sK0 X1]
    conv => enter [1]; rw [← l14 sK0 X1]
  have l16 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54553 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l15 sK0 (X0 ◇ (X2 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l16 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54554 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54554 G := by
  have l0 : ∀ X0 sK1 sK3 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK3 ◇ sK2))) := by
    intro X0 sK1 sK3 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK3 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK3 ◇ sK2)]
  have l1 : ∀ X0 sK1 sK3 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK2)))) := by
    intro X0 sK1 sK3 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK3 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK3 ◇ sK2)]
  have l2 : ∀ X1 sK1 sK3 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK3 ◇ sK2)) ◇ X2)) = ((sK1 ◇ (sK3 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK2)))) := by
    intro X1 sK1 sK3 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK3 ◇ sK2)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK3 ◇ sK2)) sK1 sK3 sK2 X0]
  have l3 : ∀ X0 sK1 sK3 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK2))) = (X1 ◇ ((sK1 ◇ (sK3 ◇ sK2)) ◇ X2)) := by
    intro X0 sK1 sK3 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK3 sK2 (sK1 ◇ (sK3 ◇ sK2))]
    conv => enter [1]; rw [← l2 X1 sK1 sK3 sK2 X2 X0]
  have l4 : ∀ sK0 sK1 sK3 sK2 X1 X2 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2))) = (X1 ◇ ((sK1 ◇ (sK3 ◇ sK2)) ◇ X2)) := by
    intro sK0 sK1 sK3 sK2 X1 X2
    conv => enter [1]; rw [l3 sK0 sK1 sK3 sK2 X1 X2]
  have l5 : ∀ sK0 sK1 sK3 sK2 X1 X0 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK3 sK2 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK3 sK2 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK3 ◇ sK2)) sK0]
  have l6 : ∀ X0 sK0 sK1 sK3 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2))) := by
    intro X0 sK0 sK1 sK3 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 sK3 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 sK3 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2))) := by
    intro X1 X0 X2 sK0 sK1 sK3 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w x z y]

theorem Equation4512_54554_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54554 : Equation54554 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l12 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1]; rw [← h54554 sK0 X1 X0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l15 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK0 sK2 X0]
  have l16 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [l3 sK0 sK2 X0]
  have l17 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (sK0 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l16 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK2) ◇ X0) X1]
  have l18 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l15 sK0 sK2 X0]
    conv => enter [1]; rw [← h54554 sK0 X0 (sK0 ◇ sK2) sK0]
  have l19 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l17 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) X0 X1]
  have l20 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (X0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l18 sK0 sK2 X0]
    conv => enter [1]; rw [l14 sK0 sK2 X0]
  have l21 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK0 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l19 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h54554 (sK0 ◇ sK2) X1 X0 sK0]
  have l22 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ sK2) ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [← l21 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l23 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ sK2) ◇ (X1 ◇ X0)) = (sK2 ◇ (X1 ◇ X0)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [l22 sK0 sK2 X1 X0]
    conv => enter [1]; rw [← h54554 sK2 X1 X0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ X0)]
  have l25 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l5 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK0 sK2 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l5 sK0 X0]
  have l27 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l5 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l5 sK0 X0]
  have l29 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 1]; rw [l5 sK0 X0]
  have l30 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X1]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [← h54554 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l32 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l27 sK0 sK2]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK2)]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [← h54554 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l34 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54554 sK0 X0 (sK0 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l25 sK0 sK2 X0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← h54554 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 sK0]
  have l36 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l31 sK0 X0]
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ sK0) X0]
  have l38 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l32 sK0 sK2]
    conv => enter [1]; rw [← l20 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l33 sK0 X0]
    conv => enter [1]; rw [← h54554 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0) sK0]
  have l40 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l34 sK0 X0 sK2]
    conv => enter [1]; rw [← h54554 (sK0 ◇ (sK0 ◇ sK0)) X0 sK2 sK0]
  have l41 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l14 sK0 X0 sK0]
    conv => enter [1]; rw [← l35 sK0 X0]
  have l42 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l36 sK0 X0 X1]
    conv => enter [1]; rw [← h54554 (sK0 ◇ (sK0 ◇ sK0)) X1 X0 sK0]
  have l43 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l14 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l39 sK0 X0]
  have l44 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l14 sK0 X0 sK2]
    conv => enter [1]; rw [← l40 sK0 X0 sK2]
  have l45 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l41 sK0 X0]
  have l46 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l14 sK0 X1 X0]
    conv => enter [1]; rw [← l42 sK0 X0 X1]
  have l47 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l43 sK0 X0]
  have l48 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [l44 sK0 sK2 X0]
  have l49 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l46 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l50 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l49 sK0 X0 X1]
    conv => enter [1]; rw [← h54554 (sK0 ◇ sK0) X1 X0 (sK0 ◇ sK0)]
  have l51 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l38 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))]
  have l52 : ∀ sK0 sK2 X0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l38 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) X0]
  have l53 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [l52 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK2) X0]
  have l54 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l51 sK0 sK2]
  have l55 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l53 sK0 sK2 X0]
    conv => enter [1]; rw [← h54554 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK2) sK0]
  have l56 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l54 sK0 sK2]
    conv => enter [1]; rw [← l48 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l57 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l14 sK0 X0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l55 sK0 sK2 X0]
  have l58 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l57 sK0 sK2 X0]
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ sK2) X0]
  have l59 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l48 sK0 sK2 X0]
    conv => enter [1]; rw [← l58 sK0 sK2 X0]
  have l60 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l45 sK0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l61 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l45 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l9 sK0]
  have l62 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK2) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0 sK2]
    conv => enter [1, 2]; rw [l10 sK0 sK2]
  have l63 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK2) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l62 sK0 sK2]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK2)]
  have l64 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l61 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l65 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l60 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l66 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK2) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l63 sK0 sK2]
    conv => enter [1]; rw [← l48 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l67 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l64 sK0]
    conv => enter [1]; rw [l37 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l68 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l65 sK0]
  have l69 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l66 sK0 sK2]
    conv => enter [1]; rw [← l56 sK0 sK2]
  have l70 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l67 sK0]
    conv => enter [1, 2]; rw [l9 sK0]
  have l71 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
    conv => enter [1]; rw [l69 sK0 sK2]
  have l72 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l70 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l73 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l68 sK0]
    conv => enter [1]; rw [← l72 sK0]
  have l74 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l73 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
  have l75 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l73 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l76 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l75 sK0 X0]
    conv => enter [1]; rw [← l50 sK0 X0 (sK0 ◇ sK0)]
  have l77 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l74 sK0]
    conv => enter [1, 2]; rw [l9 sK0]
  have l78 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l77 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l79 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l68 sK0]
    conv => enter [1]; rw [← l78 sK0]
  have l80 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l79 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l81 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0 X0]
    conv => enter [1]; rw [← l80 sK0 X0]
  have l82 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l48 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l83 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l48 sK0 sK2 sK0]
  have l84 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l71 sK0 sK2]
    conv => enter [1]; rw [l83 sK0 sK2]
  have l85 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l82 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h54554 X0 (sK0 ◇ sK2) X1 sK0]
  have l86 : ∀ X2 X1 sK0 sK2 X0 : G, (X2 ◇ (X1 ◇ ((sK0 ◇ sK2) ◇ X0))) = (X1 ◇ ((X0 ◇ (sK0 ◇ sK2)) ◇ sK0)) := by
    intro X2 X1 sK0 sK2 X0
    conv => enter [1, 2, 2]; rw [l48 sK0 sK2 X0]
    conv => enter [1]; rw [← h54554 X1 (X0 ◇ (sK0 ◇ sK2)) sK0 X2]
  have l87 : ∀ X1 sK2 X0 sK0 X2 : G, (X1 ◇ ((sK2 ◇ X0) ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)))) := by
    intro X1 sK2 X0 sK0 X2
    conv => enter [1]; rw [h54554 X1 (sK2 ◇ X0) (sK0 ◇ sK0) X2]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK2 X0]
  have l88 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1, 2]; rw [l84 sK0 sK2]
    conv => enter [1]; rw [h54554 X0 (sK0 ◇ sK2) sK0 X1]
  have l89 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h54554 sK0 (sK0 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [← l48 sK0 sK2 X0]
  have l90 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ X0) = (X1 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l59 sK0 sK2 X0]
    conv => enter [1]; rw [l89 sK0 sK2 X0 X1]
  have l91 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l88 X0 sK0 sK2 X0]
    conv => enter [1]; rw [← h54554 X0 (sK0 ◇ sK2) sK0 X0]
  have l92 : ∀ X1 sK2 X0 sK0 : G, (X1 ◇ ((sK2 ◇ X0) ◇ (sK0 ◇ sK0))) = (X1 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ sK0)) := by
    intro X1 sK2 X0 sK0
    conv => enter [1]; rw [l87 X1 sK2 X0 sK0 X1]
    conv => enter [1]; rw [← h54554 X1 ((sK0 ◇ sK2) ◇ X0) sK0 X1]
  have l93 : ∀ X2 X1 sK0 sK2 X0 : G, (X2 ◇ (X1 ◇ ((sK0 ◇ sK2) ◇ X0))) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ sK0))) := by
    intro X2 X1 sK0 sK2 X0
    conv => enter [1]; rw [l86 X2 X1 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK2) sK0]
  have l94 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l90 sK0 sK2 sK0 X0]
    conv => enter [1]; rw [← l91 X0 sK0 sK2]
  have l95 : ∀ X1 sK2 X0 sK0 : G, (X1 ◇ ((sK2 ◇ X0) ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ sK0))) := by
    intro X1 sK2 X0 sK0
    conv => enter [1]; rw [l92 X1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) X0 sK0]
  have l96 : ∀ X2 X1 sK0 sK2 X0 : G, (X2 ◇ (X1 ◇ ((sK0 ◇ sK2) ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro X2 X1 sK0 sK2 X0
    conv => enter [1]; rw [l93 X2 X1 sK0 sK2 X0]
    conv => enter [1]; rw [← h54554 X0 sK0 (sK0 ◇ sK2) X1]
  have l97 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l84 sK0 sK2]
    conv => enter [1]; rw [l94 sK0 sK2 X0]
  have l98 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ X0)) = (X1 ◇ ((sK2 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h54554 (sK0 ◇ sK2) sK0 X0 X1]
    conv => enter [1]; rw [← l95 X1 sK2 X0 sK0]
  have l99 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [h54554 X1 X0 (sK0 ◇ sK2) X1]
    conv => enter [1]; rw [l96 X1 X1 sK0 sK2 X0]
  have l100 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ X0)) = ((sK2 ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l98 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [← h54554 (sK2 ◇ X0) sK0 sK0 sK0]
  have l101 : ∀ sK0 sK2 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [l97 sK0 sK2 X0]
    conv => enter [1]; rw [← l99 X1 X0 sK0 sK2]
  have l102 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ X0)) = (sK2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l100 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 X0 (sK0 ◇ sK0)]
  have l103 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l102 sK0 sK2 X0]
    conv => enter [1]; rw [← l23 sK0 sK2 X0 (sK0 ◇ sK0)]
  have l104 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54554 X0 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l103 sK0 sK2 X0]
  have l105 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l85 sK0 sK2 sK0 X0]
    conv => enter [1]; rw [← l104 X0 sK0 sK2]
  have l106 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l90 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [l105 sK0 sK2 X0]
  have l107 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [← l106 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l47 sK0 (sK0 ◇ sK2)]
  have l108 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l81 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l107 sK0 sK2]
  have l109 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l108 sK0 sK2]
    conv => enter [1]; rw [← l76 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l110 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l68 sK0]
    conv => enter [1]; rw [← l109 sK0 sK2]
  have l111 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l110 sK0 sK2]
    conv => enter [1]; rw [← l71 sK0 sK2]
  have l112 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l110 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l113 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l112 sK0 X0 sK2]
    conv => enter [1]; rw [← l50 sK0 X0 (sK0 ◇ sK2)]
  have l114 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l113 sK0 X0 sK2]
    conv => enter [1]; rw [← l101 sK0 sK2 sK0 X0]
  have l115 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l114 sK0 X0 sK0]
  have l116 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54554 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l115 sK0 (X0 ◇ (X2 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [← l116 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54556 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54556 G := by
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
  have l4 : ∀ sK0 sK1 sK3 X1 X2 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro sK0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l3 sK0 sK1 sK3 sK0 X1 X2]
  have l5 : ∀ sK0 sK1 sK3 X1 X0 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK3 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK3 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK3 ◇ sK0)) sK0]
  have l6 : ∀ X0 sK0 sK1 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK0 sK1 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro X1 X0 X2 sK0 sK1 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w x z]

theorem Equation4512_54556_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54556 : Equation54556 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54556 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (X2 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← h54556 X2 (X0 ◇ X1) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54556 X0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54556 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [h54556 X0 X2 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54556 X0 X1 sK0 sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← l2 sK0 X2]
    conv => enter [1]; rw [l1 sK0 X2 X0 X1]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l6 X0 X1 X2 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) X0 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0 sK0 sK0]
  have l11 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l9 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l11 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h54556 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h54556 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l14 sK0 X0]
  have l16 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54556 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l15 sK0 (X0 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  intro x y z
  conv => enter [1]; rw [← l16 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54557 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54557 G := by
  have l0 : ∀ X0 sK2 sK4 sK0 X1 : G, (X0 ◇ (sK2 ◇ (sK4 ◇ sK0))) = (X1 ◇ (sK2 ◇ (sK4 ◇ sK0))) := by
    intro X0 sK2 sK4 sK0 X1
    conv => enter [1]; rw [← h4274 sK2 X0 (sK4 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK2 X1 (sK4 ◇ sK0)]
  have l1 : ∀ X0 sK2 sK4 sK0 X1 : G, (X0 ◇ (sK2 ◇ (sK4 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK4 ◇ sK0)))) := by
    intro X0 sK2 sK4 sK0 X1
    conv => enter [1]; rw [← h4274 sK2 X0 (sK4 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 (sK4 ◇ sK0)]
  have l2 : ∀ X1 sK2 sK4 sK0 X2 X0 : G, (X1 ◇ ((sK2 ◇ (sK4 ◇ sK0)) ◇ X2)) = ((sK2 ◇ (sK4 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK4 ◇ sK0)))) := by
    intro X1 sK2 sK4 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ (sK4 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ (sK4 ◇ sK0)) sK2 sK4 sK0 X0]
  have l3 : ∀ X0 sK2 sK4 sK0 X1 X2 : G, (X0 ◇ (sK2 ◇ (sK4 ◇ sK0))) = (X1 ◇ ((sK2 ◇ (sK4 ◇ sK0)) ◇ X2)) := by
    intro X0 sK2 sK4 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK4 sK0 (sK2 ◇ (sK4 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK2 sK4 sK0 X2 X0]
  have l4 : ∀ sK1 sK2 sK4 sK0 X1 X2 : G, (sK1 ◇ (sK2 ◇ (sK4 ◇ sK0))) = (X1 ◇ ((sK2 ◇ (sK4 ◇ sK0)) ◇ X2)) := by
    intro sK1 sK2 sK4 sK0 X1 X2
    conv => enter [1]; rw [l3 sK1 sK2 sK4 sK0 X1 X2]
  have l5 : ∀ sK1 sK2 sK4 sK0 X1 X0 : G, (sK1 ◇ (sK2 ◇ (sK4 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK4 sK0 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK4 sK0 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ (sK4 ◇ sK0)) sK1]
  have l6 : ∀ X0 sK1 sK2 sK4 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ (sK4 ◇ sK0))) := by
    intro X0 sK1 sK2 sK4 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK4 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 sK4 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ (sK4 ◇ sK0))) := by
    intro X1 X0 X2 sK1 sK2 sK4 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w x z u]

theorem Equation4512_54557_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54557 : Equation54557 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54557 sK0 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [h54557 X0 X1 X2 X3 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X2]
  have l3 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l4 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54563 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54563 G := by
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
  have l4 : ∀ sK2 sK0 X1 X2 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK2 sK0 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK2 X1 X2]
  have l5 : ∀ sK2 sK0 X1 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK2) sK2]
  have l6 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l4 sK2 sK0 X0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 sK2]
  have l7 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK0]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z x u]
  conv => enter [1]; rw [l6 x u w]

theorem Equation4512_54563_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54563 : Equation54563 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ X1)) = (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h54563 sK0 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l0 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0 X1 sK0]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0 sK2 sK0]
  have l4 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l4 sK0 X0 sK0]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54563 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l5 sK0 (X0 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l6 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54564 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54564 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK3]
    conv => enter [1]; rw [h4274 sK0 X1 sK3]
  have l1 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK3]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK3]
  have l2 : ∀ X1 sK0 sK3 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) = ((sK0 ◇ sK3) ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X1 sK0 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 X0]
  have l3 : ∀ X0 sK0 sK3 X1 X2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro X0 sK0 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 (sK0 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 X2 X0]
  have l4 : ∀ sK2 sK0 sK3 X1 X2 : G, (sK2 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro sK2 sK0 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK3 X1 X2]
  have l5 : ∀ sK2 sK0 sK3 X1 X0 : G, (sK2 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK3) sK2]
  have l6 : ∀ sK2 sK0 sK3 X0 : G, (sK2 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK0 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK3 X0 (sK0 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 sK2]
  have l7 : ∀ X0 sK2 sK0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK2 sK0 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK0 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK0 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z x u y]
  conv => enter [1]; rw [l6 x u y w]

theorem Equation4512_54564_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54564 : Equation54564 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54564 sK0 sK0 X1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l1 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54564 X0 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [← h54564 X0 sK0 (sK0 ◇ sK0) X0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 X0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54566 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54566 G := by
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
  have l6 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK2]
  have l7 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK0 sK1]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z x u w]
  conv => enter [1]; rw [l6 x u w w]

theorem Equation4512_54566_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54566 : Equation54566 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54566 X0 X1 X2 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54566 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l1 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l2 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54567 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54567 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [h4274 sK0 sK2 sK0]
  have l3 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK2 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4274 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 sK2 sK0]
  have l5 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l3 sK2 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0 sK2]
  have l6 : ∀ X1 X0 X2 sK2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK2 sK0]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z x u]
  conv => enter [1]; rw [l5 x u w]

theorem Equation4512_54567_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54567 : Equation54567 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ X1)) = (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h54567 sK0 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l0 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0 X1 sK0]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0 sK2 sK0]
  have l4 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l4 sK0 X0 sK0]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54567 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l5 sK0 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l6 sK0 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h54567 X0 sK0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54568 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54568 G := by
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
  intro x y z w u v
  conv => enter [1]; rw [l8 x y z x u v]
  conv => enter [1]; rw [l6 x u v w]

theorem Equation4512_54568_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54568 : Equation54568 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54568 X0 (sK0 ◇ sK0) sK0 X1 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54568 sK0 sK0 X1 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54568 X0 sK0 sK2 X0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54569 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54569 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK2 sK1]
  have l3 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK2 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 sK2 sK1]
  have l5 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 sK2]
  have l6 : ∀ X1 X0 X2 sK2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l6 x y z y x]
  conv => enter [1]; rw [l5 y x w]

theorem Equation4512_54569_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54569 : Equation54569 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54569 sK0 sK0 X1 X0]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 X1 X0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l3 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ X1) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 X1 sK0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54569 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 (X1 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l8 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54570 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54570 G := by
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
  have l4 : ∀ sK2 sK1 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK2 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK2 X1 X2]
  have l5 : ∀ sK2 sK1 X1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK2) sK2]
  have l6 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 sK2]
  have l7 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l8 x y z y x]
  conv => enter [1]; rw [l6 y x w]

theorem Equation4512_54570_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54570 : Equation54570 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54570 sK0 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54570 sK0 (sK0 ◇ sK0) X1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54570 X0 (sK0 ◇ sK0) X1 sK0]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l1 X0 sK0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l3 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK0 X2]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54570 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 (X1 ◇ (X0 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [← l7 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54572 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54572 G := by
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
  intro x y z w
  conv => enter [1]; rw [l8 x y z y x w]
  conv => enter [1]; rw [l6 y x w w]

theorem Equation4512_54572_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54572 : Equation54572 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54572 sK0 sK0 X1 X0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [h54572 sK0 (sK0 ◇ sK0) X1 X0]
  have l5 : ∀ X0 sK0 sK2 sK1 X1 : G, (X0 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ X0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro X0 sK0 sK2 sK1 X1
    conv => enter [1]; rw [← h54572 sK1 (sK0 ◇ sK2) X1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) X1]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54572 X0 (sK0 ◇ sK0) X1 sK0]
  have l7 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54572 X0 (sK0 ◇ sK2) X1 sK1]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54572 X0 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK0 sK2 X0 (sK1 ◇ X0)]
    conv => enter [1]; rw [l5 X0 sK0 sK2 sK1 X1]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 X1 X0]
    conv => enter [1]; rw [← l6 sK0 X0 (sK0 ◇ X0)]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1 X0]
    conv => enter [1]; rw [l8 X0 sK0 (sK0 ◇ X0)]
  have l12 : ∀ sK1 sK0 sK2 X0 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2) := by
    intro sK1 sK0 sK2 X0 X2
    conv => enter [1]; rw [← l9 sK1 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [l9 sK1 sK0 sK2 sK1 X2]
  have l13 : ∀ X1 X2 X3 sK1 sK0 sK2 X0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro X1 X2 X3 sK1 sK0 sK2 X0
    conv => enter [1]; rw [h54572 X1 X2 X3 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l12 sK1 sK0 sK2 (X2 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) X0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1]; rw [← l10 sK0 X1 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0 sK0]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 sK0]
  have l18 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l13 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK1 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l15 sK0 (sK1 ◇ sK1)]
  have l19 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l18 sK1 sK0 sK2 X0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0 sK2 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54573 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54573 G := by
  have l0 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK0]
    conv => enter [1]; rw [h4274 sK2 X1 sK0]
  have l1 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK0]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK0]
  have l2 : ∀ X1 sK2 sK0 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK0) ◇ X2)) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X1 sK2 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK0) sK2 sK0 X0]
  have l3 : ∀ X0 sK2 sK0 X1 X2 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ ((sK2 ◇ sK0) ◇ X2)) := by
    intro X0 sK2 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK2 sK0 X2 X0]
  have l4 : ∀ sK3 sK2 sK0 X1 X2 : G, (sK3 ◇ (sK2 ◇ sK0)) = (X1 ◇ ((sK2 ◇ sK0) ◇ X2)) := by
    intro sK3 sK2 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK2 sK0 X1 X2]
  have l5 : ∀ sK3 sK2 sK0 X1 X0 : G, (sK3 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK2 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK2 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK0) sK3]
  have l6 : ∀ sK3 sK2 sK0 X0 : G, (sK3 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK2 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK2 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK0) sK2 sK0 sK3]
  have l7 : ∀ X0 sK3 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK3 sK2 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK2 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK3 sK2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro X1 X0 X2 sK3 sK2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK3 sK2 sK0]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z y x u]
  conv => enter [1]; rw [l6 y x u w]

theorem Equation4512_54573_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54573 : Equation54573 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (sK0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X2]
    conv => enter [1]; rw [h54573 sK0 sK0 X2 X0 X1]
  have l3 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l2 sK0 X2 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X1]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ X1) X0]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 X1]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54573 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l7 sK0 (X1 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l8 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54579 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54579 G := by
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
  conv => enter [1]; rw [l2 x y z w (z ◇ x)]

theorem Equation4512_54579_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54579 : Equation54579 G) : Equation4274 G := by
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
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X1 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← h54579 X1 sK0 X0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← l5 sK0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l5 sK0 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ X0)]
  have l8 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X2 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l7 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h54579 X0 X2 sK0 X1]
  have l9 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [l6 X2 sK0 X0 X1]
    conv => enter [1]; rw [← h54579 X2 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ sK0)) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [h54579 X2 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1 X2]
  have l11 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ (sK0 ◇ X0)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h54579 X1 sK0 X0 X2]
    conv => enter [1]; rw [l9 X2 sK0 X0 X1]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [l10 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← l11 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l14 sK0 X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l15 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l18 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l17 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54580 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54580 G := by
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
  conv => enter [1]; rw [l2 x y z w (z ◇ y)]

theorem Equation4512_54580_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54580 : Equation54580 G) : Equation4274 G := by
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
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l3 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ X1 sK0 X2 X3 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X2 X3 X0
    conv => enter [1]; rw [h54580 X1 (sK0 ◇ sK0) X2 X3]
    conv => enter [1, 2, 2]; rw [h54580 X2 sK0 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54580 (sK0 ◇ sK0) sK0 sK0 X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1]; rw [h54580 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 X0]
  have l9 : ∀ X1 sK0 X2 X3 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X3 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X2 X3 X0
    conv => enter [1]; rw [h54580 X1 (sK0 ◇ (sK0 ◇ sK0)) X2 X3]
    conv => enter [1, 2, 2]; rw [← h54580 X0 sK0 sK0 X2]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54580 X0 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l9 X1 sK0 X2 X3 X1]
    conv => enter [1, 2]; rw [← l10 sK0 X1]
  have l12 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l6 X1 sK0 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [← h54580 sK0 sK0 sK0 X1]
  have l13 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l11 X1 sK0 X2 X3]
    conv => enter [1, 2, 2]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l12 X1 sK0 X2 X3]
    conv => enter [1, 2]; rw [← l7 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X3 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l13 X1 sK0 X2 X3]
    conv => enter [1, 2]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l14 X1 sK0 X2 X3]
    conv => enter [1, 2]; rw [← h54580 sK0 sK0 sK0 sK0]
  have l17 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X3 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l15 X1 sK0 X2 X3]
    conv => enter [1, 2, 2]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h54580 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l16 X1 sK0 X2 sK0]
  have l19 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X3 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l17 X1 sK0 X2 X3]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l19 X1 sK0 X2 X3]
    conv => enter [1, 2]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l18 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l20 X1 sK0 X2 sK0]
  have l22 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [h54580 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l23 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l21 sK0 sK0 X1]
    conv => enter [1]; rw [← l22 sK0 X1 sK0]
  have l24 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54580 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l23 sK0 (X1 ◇ (X2 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [← l24 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54582 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54582 G := by
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
  conv => enter [1]; rw [l2 x y z w (z ◇ w)]

theorem Equation4512_54582_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54582 : Equation54582 G) : Equation4274 G := by
  have l0 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (sK0 ◇ sK2)) = (X0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [h54582 X1 sK0 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l0 X0 sK0 sK2 X0]
    conv => enter [1]; rw [← l0 X1 sK0 sK2 X0]
  have l2 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l0 sK1 sK0 sK2 X1]
  have l3 : ∀ sK1 sK0 sK2 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1, 1]; rw [l1 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK2) X1]
  have l4 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l2 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [← l3 sK1 sK0 sK2 X1 X1]
  have l5 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54582 X0 X1 X2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l4 sK1 sK0 sK2 (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  intro x y z
  conv => enter [1]; rw [l5 x x x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54583 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54583 G := by
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
  conv => enter [1]; rw [l2 x y z w (z ◇ u)]

theorem Equation4512_54583_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54583 : Equation54583 G) : Equation4274 G := by
  have l0 : ∀ X2 sK0 sK2 X0 X1 : G, (X2 ◇ ((sK0 ◇ sK2) ◇ X0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X2 sK0 sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [← h54583 X1 sK0 sK2 X2 X0]
  have l1 : ∀ X0 sK0 sK2 X3 : G, (X0 ◇ (sK0 ◇ sK2)) = (X3 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X3
    conv => enter [1]; rw [← l0 X0 sK0 sK2 X0 X0]
    conv => enter [1]; rw [l0 X0 sK0 sK2 X0 X3]
  have l2 : ∀ X0 sK0 sK2 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro X0 sK0 sK2 sK1 X1
    conv => enter [1]; rw [← l0 sK1 sK0 sK2 X1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) X1]
  have l3 : ∀ X1 X2 X3 X0 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X1 X2 X3 X0 sK0 sK2
    conv => enter [1]; rw [h54583 X1 X2 X3 (X1 ◇ (sK0 ◇ sK2)) X1]
    conv => enter [1]; rw [← l2 X0 sK0 sK2 X1 (X2 ◇ (X3 ◇ X1))]
  have l4 : ∀ sK1 sK0 sK2 X1 X2 X3 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X2 ◇ X3)) := by
    intro sK1 sK0 sK2 X1 X2 X3
    conv => enter [1]; rw [l3 sK1 sK0 sK2 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l4 x x x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54589 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54589 G := by
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
  intro x y z w u
  conv => enter [1]; rw [l8 x y z y u x]
  conv => enter [1]; rw [l6 y u x w]

theorem Equation4512_54589_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54589 : Equation54589 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54589 sK0 sK0 X1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l1 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [h54589 X1 X2 X3 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l0 X0 sK0 (X2 ◇ (X1 ◇ X1))]
  have l2 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X3)) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h54589 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X1 X2 X3 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54590 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54590 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK3]
    conv => enter [1]; rw [h4274 sK0 X1 sK3]
  have l1 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK3]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK3]
  have l2 : ∀ X1 sK0 sK3 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) = ((sK0 ◇ sK3) ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X1 sK0 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 X0]
  have l3 : ∀ X0 sK0 sK3 X1 X2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro X0 sK0 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 (sK0 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 X2 X0]
  have l4 : ∀ sK3 sK0 X1 X2 : G, (sK3 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro sK3 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK3 X1 X2]
  have l5 : ∀ sK3 sK0 X1 X0 : G, (sK3 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK3) sK3]
  have l6 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK0 X0 (sK0 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 sK3]
  have l7 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK3 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro X1 X0 X2 sK3 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK3 sK0]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z y u]
  conv => enter [1]; rw [l6 y u w]

theorem Equation4512_54590_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54590 : Equation54590 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ X1)) = (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h54590 X0 sK0 X1 X2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X2 sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X1 X2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54592 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54592 G := by
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
  intro x y z w u
  conv => enter [1]; rw [l8 x y z y u w]
  conv => enter [1]; rw [l6 y u w w]

theorem Equation4512_54592_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54592 : Equation54592 G) : Equation4274 G := by
  have l0 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54592 X1 sK0 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h54592 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← h54592 X3 sK0 sK0 X0 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [l2 X0 sK0 X0]
  have l5 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← h54592 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

end Semigroup5
