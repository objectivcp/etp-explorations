import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54436_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54436 : Equation54436 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l1 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l4 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h54436 X0 sK0 sK2 X1]
    conv => enter [1]; rw [h4512 sK0 sK2 (X1 ◇ sK0)]
  have l5 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l4 X0 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l4 (X0 ◇ X1) sK0 sK2 sK0]
  have l7 : ∀ X0 sK0 sK2 X1 : G, ((X0 ◇ (sK0 ◇ sK2)) ◇ X1) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1, 1]; rw [l4 X0 sK0 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK0) X1]
  have l8 : ∀ sK0 X1 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((X0 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK0 X1 X0 sK2
    conv => enter [1]; rw [← h54436 (sK0 ◇ sK2) (sK0 ◇ sK0) X1 sK0]
    conv => enter [1]; rw [← l7 X0 sK0 sK2 X1]
  have l9 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l6 X0 X1 sK0 sK2]
  have l10 : ∀ sK0 X1 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro sK0 X1 X0 sK2
    conv => enter [1]; rw [l8 sK0 X1 X0 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK2) X1]
  have l11 : ∀ X0 sK1 sK0 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [h54436 X0 (sK0 ◇ sK2) (sK0 ◇ sK0) X1]
  have l12 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l4 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK0) X0]
  have l13 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [h54436 (sK0 ◇ sK2) (sK0 ◇ sK0) X0 sK0]
  have l14 : ∀ X0 sK1 sK0 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ ((X1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1]; rw [l11 X0 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [h54436 (sK0 ◇ sK2) (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK2)) sK0]
  have l15 : ∀ X0 sK1 sK0 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1]; rw [l14 X0 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [← l13 sK1 sK0 sK2 (X1 ◇ (sK0 ◇ sK2))]
  have l16 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l15 X0 sK1 sK0 sK2 sK1]
  have l17 : ∀ X0 sK1 sK0 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X2 ◇ X1))) := by
    intro X0 sK1 sK0 sK2 X1 X2
    conv => enter [1, 2]; rw [l16 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [h54436 X0 X1 (sK1 ◇ (sK0 ◇ sK2)) X2]
  have l18 : ∀ sK1 sK0 sK2 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1, 1]; rw [l16 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ sK2)) X1]
  have l19 : ∀ X0 sK1 sK0 sK2 X2 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X2 ◇ X1)) := by
    intro X0 sK1 sK0 sK2 X2 X1
    conv => enter [1]; rw [l17 X0 sK1 sK0 sK2 X1 X2]
    conv => enter [1]; rw [← l18 sK1 sK0 sK2 (X2 ◇ X1) X1]
  have l20 : ∀ sK1 sK0 sK2 X2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X2 ◇ X1)) := by
    intro sK1 sK0 sK2 X2 X1
    conv => enter [1]; rw [l16 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l19 sK1 sK1 sK0 sK2 X2 X1]
  have l21 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l3 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l5 sK2 sK0 sK2]
  have l22 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK2]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l23 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [← l13 sK1 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l9 sK1 sK0 sK2 (sK0 ◇ sK0) (sK0 ◇ sK2)]
    conv => enter [1]; rw [l23 sK0 sK2 sK1]
  have l25 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l24 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l26 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l25 sK1 sK0 sK2 X0]
  have l27 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54436 X0 X1 X2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l26 sK1 sK0 sK2 X1]
  have l28 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [l27 X0 X1 X2 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l16 sK1 sK0 sK2 X2]
  have l29 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [l28 X0 X1 X2 sK1 sK0 sK2]
    conv => enter [1]; rw [← l16 sK1 sK0 sK2 X1]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54436 sK0 sK0 X0 sK0]
  have l31 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l29 sK1 sK0 sK2 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l30 sK0 X0]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l31 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l32 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54438 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54438 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [h4274 sK0 sK3 sK0]
  have l3 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK3 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [h4274 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 sK3 sK0]
  have l5 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l3 sK3 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0 sK3]
  have l6 : ∀ X1 X0 X2 sK3 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK3 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z z w]
  conv => enter [1]; rw [l5 z w y]

theorem Equation4512_54438_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54438 : Equation54438 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54438 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK0]
  have l4 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (X1 ◇ X1)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h54438 X0 sK0 sK2 X1]
    conv => enter [1]; rw [h4512 sK0 sK2 (X1 ◇ X1)]
  have l5 : ∀ X0 sK1 sK0 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ X1)) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1]; rw [h54438 X0 sK1 (sK0 ◇ sK2) X1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (X1 ◇ X1)]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l0 sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l5 X0 sK1 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 sK1 sK0 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1]; rw [l5 X0 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l5 X1 sK1 sK0 sK2 X0]
  have l10 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l7 (sK1 ◇ (sK0 ◇ sK2)) sK0 sK0]
    conv => enter [1]; rw [← l8 X0 sK1 sK0 sK2]
  have l11 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l10 sK0 X0 sK1 sK2]
  have l12 : ∀ sK1 sK0 sK2 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ X1)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [← l5 sK1 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [l5 sK1 sK1 sK0 sK2 sK0]
  have l13 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l5 (X0 ◇ X1) sK1 sK0 sK2 sK0]
  have l14 : ∀ X1 X2 X3 X0 sK1 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = (X2 ◇ (X3 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro X1 X2 X3 X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54438 X1 X2 X3 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [l9 (sK1 ◇ (sK0 ◇ sK2)) sK1 sK0 sK2 X0]
  have l15 : ∀ X2 sK1 sK0 sK2 X3 X1 X0 : G, (X2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X3 ◇ X3))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X2 sK1 sK0 sK2 X3 X1 X0
    conv => enter [1]; rw [← h54438 X1 X2 (sK1 ◇ (sK0 ◇ sK2)) X3]
    conv => enter [1, 2]; rw [l9 X2 sK1 sK0 sK2 X0]
  have l16 : ∀ sK1 sK0 sK2 X2 X3 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (X2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X3 ◇ X3))) := by
    intro sK1 sK0 sK2 X2 X3
    conv => enter [1]; rw [← l13 sK1 sK1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l15 X2 sK1 sK0 sK2 X3 sK1 sK1]
  have l17 : ∀ X1 X2 X3 sK1 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = (X2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK1 sK0 sK2
    conv => enter [1]; rw [l14 X1 X2 X3 X1 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l13 X3 X1 sK1 sK0 sK2]
  have l18 : ∀ sK1 sK0 sK2 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (X2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X2
    conv => enter [1]; rw [l16 sK1 sK0 sK2 X2 sK1]
    conv => enter [1, 2]; rw [l12 sK1 sK0 sK2 sK1]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK0 sK1 sK0 sK2 sK0]
  have l20 : ∀ X1 X2 X3 sK1 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = (X3 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK1 sK0 sK2
    conv => enter [1]; rw [l14 X1 X2 X3 X1 sK1 sK0 sK2]
    conv => enter [1]; rw [l17 X2 X3 (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK1 sK0 sK2]
  have l21 : ∀ X1 X2 X3 sK1 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X3 sK1 sK0 sK2
    conv => enter [1]; rw [l20 X1 X2 X3 sK1 sK0 sK2]
    conv => enter [1]; rw [← l18 sK1 sK0 sK2 X3]
  have l22 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l21 X1 X2 X3 X1 sK0 X1]
    conv => enter [1]; rw [← l19 sK0 X1 X1]
  have l23 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l4 (X0 ◇ X1) sK0 sK2 sK0]
  have l24 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l23 X0 X1 sK0 sK2]
  have l25 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l24 sK1 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [l22 sK1 sK1 (sK0 ◇ sK2) sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54438 sK0 sK0 X0 sK0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [l22 sK0 X0 (sK0 ◇ sK0) sK0]
  have l28 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [← l27 sK0 X0]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l28 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l29 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54439 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54439 G := by
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
  have l4 : ∀ sK4 sK1 sK0 X1 X2 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK4 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK4 sK1 sK0 X1 X2]
  have l5 : ∀ sK4 sK1 sK0 X1 X0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK4]
  have l6 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 sK4]
  have l7 : ∀ X0 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK4 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK1 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK4 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK4 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z z w u]
  conv => enter [1]; rw [l6 z w u y]

theorem Equation4512_54439_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54439 : Equation54439 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [h54439 X0 sK0 sK2 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK2 (X1 ◇ X2)]
  have l1 : ∀ sK0 sK2 X1 X2 : G, ((sK0 ◇ sK2) ◇ (X1 ◇ X2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X1 X2
    conv => enter [1]; rw [← l0 sK0 sK0 sK2 X1 X2]
    conv => enter [1]; rw [l0 sK0 sK0 sK2 sK0 sK0]
  have l2 : ∀ sK1 sK0 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro sK1 sK0 sK2 X1 X2
    conv => enter [1]; rw [l0 sK1 sK0 sK2 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK2 X1 X2]
  have l3 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l0 sK1 sK0 sK2 sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK0) X0]
  have l4 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK0 sK2 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l3 sK1 sK0 sK2 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54439 X0 sK0 sK0 sK0 sK0]
  have l6 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l7 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK0 sK2]
    conv => enter [1]; rw [l5 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l7 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54440 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54440 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK0 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l4 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 sK0]
  have l6 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w x]
  conv => enter [1]; rw [l5 w x y]

theorem Equation4512_54440_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54440 : Equation54440 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54440 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54440 sK0 sK0 X1 X0]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [h54440 sK0 (sK0 ◇ sK0) X1 X0]
  have l6 : ∀ sK2 X0 sK0 X1 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ X1) := by
    intro sK2 X0 sK0 X1
    conv => enter [1]; rw [← h54440 sK0 sK2 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK2 X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ X0) = ((sK0 ◇ sK2) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← l6 sK2 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK2 sK0 sK0 X1]
  have l9 : ∀ X0 X1 X2 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK2 sK0
    conv => enter [1]; rw [h54440 X0 X1 X2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← l6 sK2 sK0 sK0 (X0 ◇ X0)]
  have l10 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l5 sK0 X0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l10 sK0 X0 sK2]
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK2) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK2]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK0]
  have l14 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK2 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK0 sK2]
  have l15 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l14 sK0 sK2 X0]
    conv => enter [1]; rw [← l13 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54440 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l7 sK0 X0 (sK0 ◇ sK0)]
  have l17 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ X3)) = (X2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h54440 X1 X2 X3 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK0 (X1 ◇ X1) X0]
  have l18 : ∀ X1 X2 X3 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0 sK2
    conv => enter [1]; rw [l17 X1 X2 X3 sK0 X1]
    conv => enter [1]; rw [l9 X2 sK0 (X1 ◇ (sK0 ◇ sK0)) sK2 sK0]
  have l19 : ∀ X1 X2 X3 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0 sK2
    conv => enter [1]; rw [l18 X1 X2 X3 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l19 X1 X2 X3 sK0 X1]
    conv => enter [1]; rw [l15 sK0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l20 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l21 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54441 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54441 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK1 ◇ sK2)]
  have l2 : ∀ X1 sK0 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK0 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK1 ◇ sK2)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2 X0]
  have l3 : ∀ X0 sK0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2)) := by
    intro X0 sK0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 sK2 X2 X0]
  have l4 : ∀ sK2 sK0 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2)) := by
    intro sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK1 sK2 X1 X2]
  have l5 : ∀ sK2 sK0 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK1 ◇ sK2)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 X2 sK2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z y w x]

theorem Equation4512_54441_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54441 : Equation54441 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l6 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l5 sK0 sK2]
  have l7 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l8 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h54441 sK2 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l7 sK0 sK2 X0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54441 sK0 sK0 X1 X0]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [h54441 sK0 (sK0 ◇ sK0) X1 X0]
  have l11 : ∀ sK2 X0 sK0 X1 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ X1) := by
    intro sK2 X0 sK0 X1
    conv => enter [1]; rw [← h54441 sK0 sK2 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK2 X1]
  have l12 : ∀ sK0 sK2 X0 sK1 X1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK0 sK2 X0 sK1 X1
    conv => enter [1]; rw [← h54441 sK1 (sK0 ◇ sK2) X1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54441 X0 (sK0 ◇ sK0) X1 sK0]
  have l14 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [l8 sK2 X0 X1 sK0]
    conv => enter [1]; rw [← l13 sK0 X0 ((sK0 ◇ sK2) ◇ X0)]
  have l15 : ∀ sK0 sK2 X1 X2 X3 X0 : G, ((sK0 ◇ sK2) ◇ (X1 ◇ X2)) = (X1 ◇ (X3 ◇ (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 X1 X2 X3 X0
    conv => enter [1]; rw [h54441 (sK0 ◇ sK2) X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← l11 sK2 X0 sK0 X1]
  have l16 : ∀ sK0 sK2 X3 X1 X0 : G, ((sK0 ◇ sK2) ◇ (X3 ◇ (X1 ◇ (sK0 ◇ sK2)))) = (X1 ◇ (sK2 ◇ (X0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X3 X1 X0
    conv => enter [1]; rw [← h54441 X1 (sK0 ◇ sK2) sK0 X3]
    conv => enter [1, 2]; rw [← l11 sK2 X0 sK0 sK0]
  have l17 : ∀ sK0 sK2 X3 X1 X0 : G, ((sK0 ◇ sK2) ◇ (X3 ◇ (X1 ◇ (sK0 ◇ sK2)))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X3 X1 X0
    conv => enter [1]; rw [l16 sK0 sK2 X3 X1 X0]
    conv => enter [1, 2]; rw [l14 sK2 X0 (sK0 ◇ sK2) sK0]
  have l18 : ∀ sK0 sK2 X1 X2 X3 X0 : G, ((sK0 ◇ sK2) ◇ (X1 ◇ X2)) = (X1 ◇ (X3 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK2 X1 X2 X3 X0
    conv => enter [1]; rw [l15 sK0 sK2 X1 X2 X3 X0]
    conv => enter [1, 2, 2]; rw [l14 sK2 X0 (sK0 ◇ sK2) sK0]
  have l19 : ∀ sK2 sK1 sK0 X1 X0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK1 sK0 X1 X0
    conv => enter [1]; rw [l11 sK2 sK1 sK0 (sK2 ◇ (X1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [l17 sK0 sK2 sK2 X1 X0]
  have l20 : ∀ sK2 sK1 sK0 X1 X3 X0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X1 ◇ (X3 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK2 sK1 sK0 X1 X3 X0
    conv => enter [1]; rw [l11 sK2 sK1 sK0 (X1 ◇ sK2)]
    conv => enter [1]; rw [l18 sK0 sK2 X1 sK2 X3 X0]
  have l21 : ∀ sK2 sK1 sK0 X1 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK1 sK0 X1
    conv => enter [1]; rw [l20 sK2 sK1 sK0 X1 sK2 sK2]
    conv => enter [1, 2]; rw [← l19 sK2 sK1 sK0 sK2 sK2]
  have l22 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l12 sK0 sK2 sK1 sK1 X0]
    conv => enter [1]; rw [← l11 sK2 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l23 : ∀ X0 X1 X2 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 X2 sK2 sK1 sK0
    conv => enter [1]; rw [h54441 X0 X1 X2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← l11 sK2 sK1 sK0 (X0 ◇ X1)]
  have l24 : ∀ X0 X1 X2 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK2 sK1 sK0
    conv => enter [1]; rw [l23 X0 X1 X2 sK2 sK1 sK0]
    conv => enter [1]; rw [← l21 sK2 sK1 sK0 X1]
  have l25 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1]; rw [← l10 sK0 X1 sK0]
  have l26 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ X3)) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h54441 X1 X2 X3 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l10 sK0 (X1 ◇ X2) X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l26 X1 X2 X3 sK0 X1]
    conv => enter [1]; rw [← l13 sK0 X2 (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l29 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l28 X1 X2 X3 sK0]
    conv => enter [1]; rw [l27 sK0 (X2 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0]
  have l31 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h54441 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK0 (sK0 ◇ sK0) sK2 sK1 sK0]
  have l32 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l31 sK0 sK2 sK1]
    conv => enter [1]; rw [← l22 sK1 sK0 sK2 X0]
  have l33 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l31 sK0 sK2 sK0]
    conv => enter [1]; rw [l11 sK2 sK0 sK0 X0]
  have l34 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (X2 ◇ (X0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2 X2
    conv => enter [1, 2]; rw [l33 sK0 sK2 X0]
    conv => enter [1]; rw [h54441 X0 (sK0 ◇ sK2) X0 X2]
  have l35 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l34 X0 sK0 sK2 X0]
    conv => enter [1]; rw [← l11 sK2 sK1 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK2)))]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 sK0 sK0]
    conv => enter [1]; rw [← l35 X0 sK0 sK0 sK0]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l32 sK0 sK0 sK0 (sK0 ◇ sK0)]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 sK0]
    conv => enter [1]; rw [← l37 sK0 X0]
  have l39 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l30 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l29 X0 sK0 sK2 sK0]
  have l40 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l38 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l39 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l40 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54443 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54443 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK1 ◇ sK0)]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK1 ◇ sK0)]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK1 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK2 sK0 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2)) := by
    intro sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X1 X2]
  have l5 : ∀ sK2 sK0 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK1 ◇ sK0)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 X0 X2 sK2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z y w x]

theorem Equation4512_54443_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54443 : Equation54443 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54443 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK0 X0 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l1 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X2 ◇ (sK0 ◇ X2))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [← l1 sK0 X0 X0]
    conv => enter [1]; rw [h54443 sK0 X0 X0 X2]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54443 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [l1 sK0 X0 sK0]
  have l7 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l5 X0 sK0 X2]
    conv => enter [1]; rw [l6 X0 X2 (sK0 ◇ X2) sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [l1 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54443 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l9 sK0 X0]
  have l11 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l10 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l7 (sK0 ◇ (sK0 ◇ sK0)) sK0 X1]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l11 X0 X1 X2 sK0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l13 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l14 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54444 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54444 G := by
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
  have l4 : ∀ sK3 sK1 sK2 sK0 X1 X2 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro sK3 sK1 sK2 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK1 sK2 sK0 X1 X2]
  have l5 : ∀ sK3 sK1 sK2 sK0 X1 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK2 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l6 : ∀ X0 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK2 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK1 sK2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 X2 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK1 sK2 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z y w x u]

@[equational_result]
theorem Equation54444_implies_Equation4274 (G : Type*) [Magma G] (h54444 : Equation54444 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54444 sK0 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [h54444 sK0 X0 (sK0 ◇ sK0) sK0 sK0]
  have l1 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [h54444 X0 X1 X2 X3 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l1 X0 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 X0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l0 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l3 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54450 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54450 G := by
  have l0 : ∀ X0 sK0 sK3 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro X0 sK0 sK3 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK3 ◇ sK1)]
  have l1 : ∀ X0 sK0 sK3 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro X0 sK0 sK3 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK3 ◇ sK1)]
  have l2 : ∀ X1 sK0 sK3 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ X2)) = ((sK0 ◇ (sK3 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro X1 sK0 sK3 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK3 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK3 ◇ sK1)) sK0 sK3 sK1 X0]
  have l3 : ∀ X0 sK0 sK3 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ X2)) := by
    intro X0 sK0 sK3 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 sK1 (sK0 ◇ (sK3 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 sK1 X2 X0]
  have l4 : ∀ sK2 sK0 sK3 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ X2)) := by
    intro sK2 sK0 sK3 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK3 sK1 X1 X2]
  have l5 : ∀ sK2 sK0 sK3 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK3 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK3 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK3 ◇ sK1)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK3 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro X0 sK2 sK0 sK3 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK3 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK3 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro X1 X0 X2 sK2 sK0 sK3 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z y w z x]

theorem Equation4512_54450_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54450 : Equation54450 G) : Equation4274 G := by
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
  have l8 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h54450 X1 (sK0 ◇ sK0) X0 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [l3 sK0 sK2 X0]
  have l14 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (sK0 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l13 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK2) ◇ X0) X1]
  have l15 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l14 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) X0 X1]
  have l16 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (X1 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l15 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h54450 X1 sK0 X0 (sK0 ◇ sK2)]
  have l17 : ∀ X1 sK0 X0 sK2 : G, (X1 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro X1 sK0 X0 sK2
    conv => enter [1]; rw [← l16 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l18 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54450 X1 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l17 X1 sK0 X0 X1]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ X0)]
  have l20 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l5 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK0 sK2 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l5 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← h54450 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l23 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l20 sK0 sK2 X0]
    conv => enter [1]; rw [← h54450 X0 (sK0 ◇ sK0) (sK0 ◇ sK2) sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← h54450 X0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [l18 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l18 X0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l23 sK0 sK2 X0]
  have l27 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l25 sK0 X0]
    conv => enter [1]; rw [← h54450 X0 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l26 X0 sK0 sK2]
    conv => enter [1]; rw [← h54450 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l24 sK0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l30 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l24 sK0 sK2]
    conv => enter [1, 2]; rw [l8 sK0 sK2]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [l24 sK0 X0]
  have l32 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54450 X0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l31 sK0 X0]
  have l33 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l18 (sK0 ◇ sK0) sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l30 sK2 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l27 (sK0 ◇ sK0) sK0]
  have l35 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l27 X0 sK0]
    conv => enter [1]; rw [l32 X0 sK0]
  have l36 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l28 (sK0 ◇ sK0) sK0 sK2]
    conv => enter [1]; rw [l33 sK0 sK2]
  have l37 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK0)]
  have l38 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l18 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l37 sK0 sK2]
  have l39 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l28 sK0 sK0 sK2]
    conv => enter [1]; rw [l38 sK0 sK2]
  have l40 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l27 (X0 ◇ X1) sK0]
  have l41 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l40 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l42 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l41 X0 X1 sK0]
    conv => enter [1]; rw [← h54450 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 X1]
  have l43 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l12 sK0 X0 sK0]
    conv => enter [1]; rw [← l42 X0 X1 sK0]
  have l44 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l18 sK0 sK0 X0]
    conv => enter [1]; rw [l43 sK0 X0 X1]
  have l45 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l44 sK0 X0 X1]
  have l46 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l3 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l35 sK2 sK0]
  have l47 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l35 X0 sK0]
  have l48 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0 sK0 X0]
    conv => enter [1]; rw [← l47 sK0 X0]
  have l49 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l39 sK0 sK2]
    conv => enter [1]; rw [l46 sK0 sK2]
  have l50 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 X0]
    conv => enter [1]; rw [l12 sK0 X0 (sK0 ◇ sK0)]
  have l51 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l28 sK0 sK0 sK2]
    conv => enter [1]; rw [l49 sK0 sK2]
  have l52 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l18 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [← l50 sK0 X0]
  have l53 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l52 sK0 X0]
  have l54 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l51 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l55 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l54 sK0 sK2]
  have l56 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l55 sK0 sK2]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK2)]
  have l57 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l56 sK0 sK2]
  have l58 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l57 sK0 sK2]
    conv => enter [1]; rw [l24 sK0 (sK0 ◇ sK2)]
  have l59 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l39 sK0 sK2]
    conv => enter [1]; rw [← l58 sK0 sK2]
  have l60 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [← l59 sK0 sK2]
  have l61 : ∀ sK0 X0 sK2 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK2)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK2 X1
    conv => enter [1]; rw [h54450 (sK0 ◇ sK0) X0 sK2 X1]
    conv => enter [1, 2, 2]; rw [← l36 sK0 sK2]
  have l62 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54450 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l24 sK0 X0]
  have l63 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1, 2]; rw [l35 X0 sK0]
    conv => enter [1]; rw [← h54450 (sK0 ◇ sK0) X1 X0 (sK0 ◇ sK0)]
  have l64 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK0 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [h54450 X0 sK0 X1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (X1 ◇ X0)]
  have l65 : ∀ sK0 X2 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (X1 ◇ X0))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X2 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54450 X0 (sK0 ◇ sK0) X1 X2]
  have l66 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [h54450 X1 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l65 sK0 X2 X1 X0]
  have l67 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l45 sK0 X1 X0]
    conv => enter [1]; rw [l63 X1 X0 sK0]
  have l68 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l45 sK0 X0 X1]
    conv => enter [1]; rw [l62 X0 X1 sK0]
  have l69 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l61 sK0 X0 sK2 sK0]
    conv => enter [1]; rw [← h54450 (sK0 ◇ sK2) X0 (sK0 ◇ sK0) sK0]
  have l70 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54450 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 X0]
    conv => enter [1]; rw [← l66 X1 sK0 X0 X0]
  have l71 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l43 sK0 X1 X0]
  have l72 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l64 (sK0 ◇ sK0) sK0 X0 sK2]
    conv => enter [1]; rw [← l69 sK0 X0 sK2]
  have l73 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l68 sK0 sK0 X1]
    conv => enter [1]; rw [← l70 X0 sK0 X1]
  have l74 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l45 sK0 X1 sK0]
    conv => enter [1]; rw [← l71 sK0 X1 sK0]
  have l75 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l67 sK0 X0 sK0]
    conv => enter [1]; rw [← l72 sK0 X0 sK0]
  have l76 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l73 sK0 X0 X1]
  have l77 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l53 sK0 X0]
    conv => enter [1]; rw [← l75 sK0 X0]
  have l78 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l76 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l74 sK0 X1]
  have l79 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l78 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l77 sK0 sK0]
  have l80 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l60 sK0 sK2]
    conv => enter [1]; rw [l28 X0 sK0 sK2]
  have l81 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l79 sK0 X0]
    conv => enter [1]; rw [l80 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l81 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54451 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54451 G := by
  have l0 : ∀ X0 sK0 sK3 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro X0 sK0 sK3 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK3 ◇ sK2)]
  have l1 : ∀ X0 sK0 sK3 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro X0 sK0 sK3 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK3 ◇ sK2)]
  have l2 : ∀ X1 sK0 sK3 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK3 ◇ sK2)) ◇ X2)) = ((sK0 ◇ (sK3 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro X1 sK0 sK3 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK3 ◇ sK2)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK3 ◇ sK2)) sK0 sK3 sK2 X0]
  have l3 : ∀ X0 sK0 sK3 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK2)) ◇ X2)) := by
    intro X0 sK0 sK3 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 sK2 (sK0 ◇ (sK3 ◇ sK2))]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 sK2 X2 X0]
  have l4 : ∀ sK2 sK0 sK3 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK2)) ◇ X2)) := by
    intro sK2 sK0 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK3 sK2 X1 X2]
  have l5 : ∀ sK2 sK0 sK3 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK3 ◇ sK2)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro X0 sK2 sK0 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro X1 X0 X2 sK2 sK0 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z y w z]

theorem Equation4512_54451_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54451 : Equation54451 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54451 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h54451 X1 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54451 X0 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54451 (X0 ◇ X1) sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l6 : ∀ X1 sK0 X2 X3 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = ((sK0 ◇ sK0) ◇ (X3 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X2 X3 X0
    conv => enter [1]; rw [h54451 X1 (sK0 ◇ sK0) X2 X3]
    conv => enter [1, 2, 2]; rw [l2 X2 sK0 X0]
  have l7 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l2 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l7 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l2 X0 sK0 sK0]
  have l9 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l6 X1 sK0 X2 sK0 sK0]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0 X1]
  have l11 : ∀ sK0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X1 X2]
  have l12 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l11 sK0 X1 X2]
  have l13 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X1 X2]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l15 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l13 sK0 sK0 X1]
    conv => enter [1]; rw [← l14 sK0 X1 sK0]
  have l16 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54451 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l15 sK0 (X2 ◇ X1)]
  have l17 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l16 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l10 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l17 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54453 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54453 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK3 ◇ sK0)]
  have l1 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK3 ◇ sK0)]
  have l2 : ∀ X1 sK0 sK3 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro X1 sK0 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK3 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK3 ◇ sK0)) sK0 sK3 X0]
  have l3 : ∀ X0 sK0 sK3 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 (sK0 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 X2 X0]
  have l4 : ∀ sK2 sK0 sK3 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro sK2 sK0 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK3 X1 X2]
  have l5 : ∀ sK2 sK0 sK3 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK3 ◇ sK0)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK2 sK0 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro X1 X0 X2 sK2 sK0 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z y w z]

theorem Equation4512_54453_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54453 : Equation54453 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54453 X0 X1 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ X1 X0 sK0 X2 : G, (X1 ◇ ((X0 ◇ sK0) ◇ X2)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X1 X0 sK0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ sK0) X2]
    conv => enter [1, 1]; rw [l3 X1 X0 sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 X0 sK0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l3 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l10 : ∀ X1 X0 sK0 X2 : G, (X1 ◇ ((X0 ◇ sK0) ◇ X2)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X1 X0 sK0 X2
    conv => enter [1]; rw [l5 X1 X0 sK0 X2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l11 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X1 ◇ (X0 ◇ (sK0 ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [← l10 X1 X0 sK0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X2]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l3 X0 sK0 sK0]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54453 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l3 X2 sK0 sK0]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) sK0 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l16 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l13 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l11 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0 sK0]
  have l18 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l16 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l8 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l19 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l18 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l19 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l17 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l20 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54454 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54454 G := by
  have l0 : ∀ X0 sK1 sK4 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK4 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK4 ◇ sK0))) := by
    intro X0 sK1 sK4 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK4 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK4 ◇ sK0)]
  have l1 : ∀ X0 sK1 sK4 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK4 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK4 ◇ sK0)))) := by
    intro X0 sK1 sK4 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK4 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK4 ◇ sK0)]
  have l2 : ∀ X1 sK1 sK4 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK4 ◇ sK0)) ◇ X2)) = ((sK1 ◇ (sK4 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK4 ◇ sK0)))) := by
    intro X1 sK1 sK4 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK4 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK4 ◇ sK0)) sK1 sK4 sK0 X0]
  have l3 : ∀ X0 sK1 sK4 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK4 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK4 ◇ sK0)) ◇ X2)) := by
    intro X0 sK1 sK4 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK4 sK0 (sK1 ◇ (sK4 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK1 sK4 sK0 X2 X0]
  have l4 : ∀ sK3 sK1 sK4 sK0 X1 X2 : G, (sK3 ◇ (sK1 ◇ (sK4 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK4 ◇ sK0)) ◇ X2)) := by
    intro sK3 sK1 sK4 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK1 sK4 sK0 X1 X2]
  have l5 : ∀ sK3 sK1 sK4 sK0 X1 X0 : G, (sK3 ◇ (sK1 ◇ (sK4 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK1 sK4 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK4 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK4 ◇ sK0)) sK3]
  have l6 : ∀ X0 sK3 sK1 sK4 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ (sK4 ◇ sK0))) := by
    intro X0 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK4 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK1 sK4 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ (sK4 ◇ sK0))) := by
    intro X1 X0 X2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z y w z u]

theorem Equation4512_54454_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54454 : Equation54454 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h54454 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← h54454 X3 sK0 sK0 X0 X0]
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
  have l4 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [h54454 X0 X1 X2 X3 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 X2 sK0 sK0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l4 X0 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X0]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l3 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l6 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54460 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54460 G := by
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
  conv => enter [1]; rw [l6 w u x y]

theorem Equation4512_54460_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54460 : Equation54460 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54460 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l3 : ∀ X0 X1 X2 sK0 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 sK0 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54460 sK0 (X0 ◇ X1) X3 X2 sK0]
  have l4 : ∀ X0 X1 X2 sK0 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 sK0 X3
    conv => enter [1]; rw [l3 X0 X1 X2 sK0 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54460 sK0 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [h54460 sK0 X0 (sK0 ◇ sK0) sK0 sK0]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l4 X0 X1 X2 sK0 X0]
    conv => enter [1]; rw [h54460 sK0 X0 (X1 ◇ X0) sK0 sK0]
  have l7 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l2 X0 X1 (X1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l6 X0 X1 X1 sK0]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l7 X1 sK0 X0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0 X1]
    conv => enter [1]; rw [← l9 sK0 X1 sK0]
  have l11 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54460 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l10 sK0 (X0 ◇ X0)]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l11 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l5 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l12 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54461 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54461 G := by
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
  conv => enter [1]; rw [l6 w u y y]

theorem Equation4512_54461_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54461 : Equation54461 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h54461 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← h54461 X3 sK0 sK0 X0 X0]
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
  have l4 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h54461 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 X0]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 X1 sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54461 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54463 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54463 G := by
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
  conv => enter [1]; rw [l6 w u y]

theorem Equation4512_54463_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54463 : Equation54463 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54463 X0 X1 X2 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1)) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54463 X0 X1 X2 sK1 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) sK1]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l0 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1)) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [h54463 X0 sK0 sK2 X1 X0]
    conv => enter [1]; rw [l1 sK0 X1 (X0 ◇ X1) sK1 sK0 sK2]
  have l4 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1)) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [h54463 X0 sK0 sK0 X1 X0]
    conv => enter [1]; rw [l1 sK0 X1 (X0 ◇ X1) sK1 sK0 sK2]
  have l5 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l3 X0 sK0 sK2 X0 sK1]
    conv => enter [1]; rw [l2 X0 (sK1 ◇ (sK0 ◇ sK2)) sK1 sK0]
  have l6 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l4 X0 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l2 X0 (sK1 ◇ (sK0 ◇ sK2)) sK1 sK0]
  have l7 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l5 X0 sK0 sK2 sK1]
  have l8 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l9 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l8 sK1 sK0 sK2 sK1 X1]
    conv => enter [1]; rw [l2 sK1 X1 (sK0 ◇ sK2) sK0]
  have l10 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l6 X0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l10 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54464 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54464 G := by
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
  conv => enter [1]; rw [l5 w u y]

theorem Equation4512_54464_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54464 : Equation54464 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54464 X0 X1 X2 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54464 X0 X1 X2 sK1 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK2)]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l0 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [h54464 X0 sK0 sK2 X1 X0]
    conv => enter [1]; rw [l1 sK0 X1 (X0 ◇ X0) sK1 sK0 sK2]
  have l4 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [h54464 X0 sK0 sK0 X1 X0]
    conv => enter [1]; rw [l1 sK0 X1 (X0 ◇ X0) sK1 sK0 sK2]
  have l5 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l3 X0 sK0 sK2 X0 sK1]
    conv => enter [1]; rw [l2 X0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) sK0]
  have l6 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l4 X0 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l2 X0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) sK0]
  have l7 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l5 X0 sK0 sK2 sK1]
  have l8 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l9 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l8 sK1 sK0 sK2 sK1 X1]
    conv => enter [1]; rw [l2 sK1 X1 (sK0 ◇ sK2) sK0]
  have l10 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l6 X0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l10 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54465 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54465 G := by
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
  conv => enter [1]; rw [l6 w u v y]

theorem Equation4512_54465_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54465 : Equation54465 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54465 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54465 X4 sK0 sK0 X0 X0 X0]
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
  have l4 : ∀ X0 sK0 X1 X2 X3 X4 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro X0 sK0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [l0 sK0 sK0 X1]
    conv => enter [1]; rw [h54465 X0 X1 (sK0 ◇ sK0) X2 X3 X4]
  have l5 : ∀ sK0 X1 X2 X3 X4 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK0 X1 X2 X3 X4
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X1 X2 X3 X4]
  have l6 : ∀ X1 X4 X5 X6 X0 sK0 sK2 : G, (X1 ◇ (X4 ◇ (X5 ◇ X6))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X1 X4 X5 X6 X0 sK0 sK2
    conv => enter [1]; rw [← h54465 sK0 X1 (X1 ◇ X1) X4 X5 X6]
    conv => enter [1]; rw [← h54465 X0 sK0 sK2 X1 X1 X1]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l5 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 sK0 sK0 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54473 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54473 G := by
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
  have l4 : ∀ sK3 sK1 sK2 sK0 X1 X2 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro sK3 sK1 sK2 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK1 sK2 sK0 X1 X2]
  have l5 : ∀ sK3 sK1 sK2 sK0 X1 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK2 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l6 : ∀ X0 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK2 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK1 sK2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 X2 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z x y w]

theorem Equation4512_54473_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54473 : Equation54473 G) : Equation4274 G := by
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
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h54473 sK0 X0 (sK0 ◇ sK0) X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK0 sK2 X0]
  have l14 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK2 X0]
    conv => enter [1]; rw [← h54473 sK0 (sK0 ◇ sK2) sK0 X0]
  have l15 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l14 sK0 sK2 sK0]
    conv => enter [1]; rw [l12 sK0 sK2 sK0]
  have l16 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l15 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (((sK0 ◇ sK2) ◇ sK0) ◇ X0)) = (((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ sK2) ◇ sK0) X0]
    conv => enter [1, 1]; rw [l16 sK0 sK2]
  have l18 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (((sK0 ◇ sK2) ◇ sK0) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l17 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l18 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) sK0 X0]
  have l20 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l19 sK0 sK2 X0]
    conv => enter [1]; rw [← h54473 (sK0 ◇ sK2) sK0 sK0 X0]
  have l21 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l20 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l20 sK0 sK2 X0]
  have l23 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l22 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK0)]
  have l24 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l21 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l25 : ∀ sK0 sK2 X0 : G, (((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l21 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l26 : ∀ sK0 sK2 X0 : G, (((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK2) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l25 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l27 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l24 sK1 sK0 sK2]
  have l28 : ∀ sK0 sK2 X0 : G, (((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l26 sK0 sK2 X0]
    conv => enter [1]; rw [← h54473 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK2) X0]
  have l29 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK2) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l28 sK0 sK2 X0]
  have l30 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l20 sK0 sK2 sK0]
    conv => enter [1]; rw [l29 sK0 sK2 sK0]
  have l31 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l23 sK1 sK0 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK0 sK2 X0]
  have l32 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l31 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← h54473 sK0 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2)) sK1]
  have l33 : ∀ sK1 sK0 sK2 X0 : G, (((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l27 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l34 : ∀ sK1 sK0 sK2 X0 : G, (((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l33 sK1 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l35 : ∀ sK1 sK0 sK2 X0 : G, (((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l34 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h54473 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l36 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l35 sK1 sK0 sK2 X0]
  have l37 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l23 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l36 sK1 sK0 sK2 sK1]
  have l38 : ∀ sK0 sK2 X0 : G, (((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l30 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) X0]
  have l39 : ∀ sK0 sK2 X0 : G, (((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l38 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK2) X0]
  have l40 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ sK0)) = (((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h54473 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK2) sK0 X0]
    conv => enter [1]; rw [← l39 sK0 sK2 X0]
  have l41 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ sK0)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l40 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK0) X0]
  have l42 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l20 sK0 sK2 sK0]
    conv => enter [1]; rw [← l41 sK0 sK2 sK0]
  have l43 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0 sK2]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK2) sK0]
  have l44 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l32 sK1 sK0 sK2]
  have l45 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l44 sK0 sK2 sK1]
  have l46 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l43 sK0 sK2]
    conv => enter [1]; rw [l45 sK0 sK2 sK1]
  have l47 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l37 sK1 sK0 sK2]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l47 sK0 sK1 sK2]
  have l49 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l46 sK0 sK2 sK0]
    conv => enter [1]; rw [← l48 sK0 sK0 sK2]
  have l50 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l49 sK0 sK2]
    conv => enter [1, 2]; rw [l7 sK0]
  have l51 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l50 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l52 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [h54473 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 sK2]
    conv => enter [1, 2, 2]; rw [l8 sK0 sK2]
  have l53 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54473 sK0 sK0 X1 X0]
  have l54 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h54473 (sK0 ◇ sK0) sK0 X1 X0]
  have l55 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54473 sK0 X0 sK0 X1]
  have l56 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l20 sK0 sK2 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54473 (sK0 ◇ sK0) X0 (sK0 ◇ sK2) sK0]
  have l57 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l51 sK0 sK2]
    conv => enter [1]; rw [l56 sK0 sK2 X0]
  have l58 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l54 X1 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l59 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [← l53 X1 sK0 X0]
  have l60 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54473 X0 (sK0 ◇ sK0) X1 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l52 X0 sK0 X1 X0]
  have l61 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l57 sK0 X0 sK0]
    conv => enter [1]; rw [l55 sK0 X0 (sK0 ◇ sK0)]
  have l62 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l58 X0 sK0 X1]
    conv => enter [1]; rw [← l60 X0 sK0 X1]
  have l63 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l59 sK0 X0 sK0]
    conv => enter [1]; rw [← l62 sK0 X0 sK0]
  have l64 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l63 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l65 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l63 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0]
  have l66 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l63 sK0 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← h54473 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l67 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l55 sK0 X0 (X1 ◇ sK0)]
    conv => enter [1]; rw [l66 sK0 X0 X1 sK0]
  have l68 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l65 sK0]
  have l69 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l64 sK0]
  have l70 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l61 sK0 X0]
    conv => enter [1]; rw [l67 sK0 X0 X1]
  have l71 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l63 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l70 sK0 X0 X1]
  have l72 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l68 sK0]
    conv => enter [1]; rw [l71 sK0 X0 X1]
  have l73 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l69 sK0]
    conv => enter [1]; rw [l72 sK0 X0 X1]
  have l74 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l73 sK0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l75 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54473 X1 X2 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l74 sK0 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [← l75 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54478 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54478 G := by
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
  intro x y z w
  conv => enter [1]; rw [l8 x y z x w]
  conv => enter [1]; rw [l6 x w z]

theorem Equation4512_54478_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54478 : Equation54478 G) : Equation4274 G := by
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
    conv => enter [1]; rw [h54478 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h54478 sK0 X0 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l6 sK0 (X0 ◇ X1) X2]
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
  have l11 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [l6 sK0 sK2 X0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l6 sK0 X1 X0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ X0)]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l6 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ X0)]
  have l14 : ∀ sK0 X1 X0 X2 : G, (sK0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [h4512 sK0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l6 sK0 X1 X0]
  have l15 : ∀ sK0 X1 X0 X2 : G, (sK0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l14 sK0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l16 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l6 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK2) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1]; rw [← l8 sK0 sK2 X0 X0]
  have l19 : ∀ X1 X2 sK0 : G, ((X1 ◇ X2) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← l6 sK0 X1 (X1 ◇ X2)]
    conv => enter [1]; rw [l7 sK0 X1 X1 X2]
  have l20 : ∀ X0 sK0 X2 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X2 ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro X0 sK0 X2 sK2
    conv => enter [1]; rw [← l15 sK0 X0 X0 X2]
    conv => enter [1]; rw [l5 sK0 (X0 ◇ X0) X2 sK2]
  have l21 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 sK0 X1 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [l17 sK0 X0]
  have l23 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l18 X0 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ X2 sK0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 sK0 X1
    conv => enter [1]; rw [← l19 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ X0 sK0 X2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l20 X0 sK0 X2 X0]
    conv => enter [1, 2]; rw [l11 sK0 X0 sK0]
  have l26 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0 X1 X0]
  have l27 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l23 X0 sK0 sK2]
    conv => enter [1]; rw [h54478 (sK0 ◇ sK2) X0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l28 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l24 sK0 sK0 X2]
    conv => enter [1]; rw [← l25 X0 sK0 X2]
  have l29 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l26 sK0 X1 X0]
  have l30 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l27 X0 sK0 sK2 sK1]
    conv => enter [1]; rw [← l12 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2)]
  have l31 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [l28 sK0 X0 X2]
  have l32 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [l29 sK0 X1 X0]
  have l33 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l30 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l33 X0 sK0 sK0 sK0]
  have l35 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l36 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l31 sK0 sK0 X1]
    conv => enter [1]; rw [← l35 sK0 X1 sK0]
  have l37 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54478 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l36 sK0 X0]
  have l38 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l37 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l24 X0 sK0 X2]
  have l39 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l38 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l34 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l39 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54479 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54479 G := by
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
  intro x y z w
  conv => enter [1]; rw [l8 x y z x w y]
  conv => enter [1]; rw [l6 x w y z]

theorem Equation4512_54479_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54479 : Equation54479 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [← h54479 sK0 X1 (sK0 ◇ sK0) X0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l12 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 sK2 X0]
  have l13 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l12 sK0 sK2 X0]
    conv => enter [1]; rw [← h54479 sK0 X0 sK0 (sK0 ◇ sK2)]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l13 sK0 sK0 X0]
    conv => enter [1]; rw [l11 sK0 sK0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ X0)]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l4 sK0 X0]
  have l17 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54479 sK0 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← h54479 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← h54479 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l11 sK0 X0 sK0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l11 sK0 X0 sK0]
    conv => enter [1]; rw [← l22 sK0 X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l23 sK0 X0]
  have l27 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l24 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l25 sK0 X0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l26 sK0 X0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l28 sK0 X0]
  have l31 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l27 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l32 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l33 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [← l14 sK0 X0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l33 sK0 X0]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [l34 sK0 X0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l29 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l37 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l29 sK0 X0]
  have l38 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l37 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l40 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l38 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l39 sK0 sK0]
  have l42 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l40 sK0 X1 sK0]
    conv => enter [1]; rw [← h54479 (sK0 ◇ (sK0 ◇ sK0)) X1 (sK0 ◇ sK0) sK0]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l41 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l44 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l11 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l42 sK0 X1]
  have l45 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l44 sK0 X1]
  have l46 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l7 sK0]
    conv => enter [1]; rw [l45 sK0 X1]
  have l47 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l43 sK0]
    conv => enter [1]; rw [l46 sK0 X1]
  have l48 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 X0 sK0]
    conv => enter [1]; rw [← h54479 X0 (sK0 ◇ sK0) sK0 sK0]
  have l50 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l49 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l51 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l50 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l52 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l35 sK0 sK0]
  have l53 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l52 sK0]
  have l54 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l53 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l55 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l54 sK0 X0]
    conv => enter [1]; rw [← l47 sK0 X0]
  have l56 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l53 sK0]
    conv => enter [1]; rw [← l55 sK0 X0]
  have l57 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54479 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l56 sK0 X1]
  have l58 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l57 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l51 sK0 X2 X0]
  have l59 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l58 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l53 sK0]
  intro x y z
  conv => enter [1]; rw [← l59 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54481 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54481 G := by
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
  intro x y z w
  conv => enter [1]; rw [l6 x y z x w]
  conv => enter [1]; rw [l5 x w z]

theorem Equation4512_54481_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54481 : Equation54481 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54481 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK0 (sK0 ◇ X0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l14 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54481 X0 sK0 sK2 sK0]
    conv => enter [1]; rw [h54481 sK2 X0 (sK0 ◇ sK0) sK0]
  have l15 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l14 X0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l15 X0 sK0 sK2]
  have l17 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54482 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54482 G := by
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
  intro x y z w u
  conv => enter [1]; rw [l8 x y z x w u]
  conv => enter [1]; rw [l6 x w u z]

theorem Equation4512_54482_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54482 : Equation54482 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l1 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54482 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54482 sK0 sK0 X0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h54482 sK0 (sK0 ◇ sK0) X0 sK0 sK0]
  have l7 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [h54482 sK0 sK2 X0 sK0 sK0]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [h54482 sK0 X1 X0 sK0 sK0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54482 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 X1 X0]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X1 X0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X1 X0]
  have l12 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X1 X0]
  have l13 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK2) ◇ X0) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 sK2 X0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0]
  have l15 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54482 X0 sK0 sK2 sK0 sK2]
    conv => enter [1]; rw [l4 sK2 X0 (sK0 ◇ sK2) sK0]
  have l16 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l15 X0 sK0 sK2]
    conv => enter [1]; rw [← l13 sK0 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK2]
  have l17 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l16 X0 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l17 X0 sK0 sK2]
  have l19 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l18 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54486 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54486 G := by
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
  conv => enter [1]; rw [l6 y x w z]

theorem Equation4512_54486_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54486 : Equation54486 G) : Equation4274 G := by
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
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← h54486 X0 sK0 (sK0 ◇ sK0) X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [l5 sK0 X0 sK0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l5 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 X0 sK0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l10 sK0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l12 : ∀ X2 X1 X0 sK0 : G, (X2 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X2 X1 X0 sK0
    conv => enter [1]; rw [h54486 X2 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l11 sK0 X0 X1 X2]
  have l13 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l12 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54495 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54495 G := by
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
  intro x y z w
  conv => enter [1]; rw [l8 x y z y w x]
  conv => enter [1]; rw [l6 y w x z]

theorem Equation4512_54495_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54495 : Equation54495 G) : Equation4274 G := by
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
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← h54495 X1 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← l5 sK0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l5 sK0 X1 X0]
  have l8 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l7 sK0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l9 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [l6 X2 sK0 X0 X2]
    conv => enter [1]; rw [← h54495 X2 X0 (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l10 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [← l5 sK0 (X2 ◇ X0) X2]
    conv => enter [1]; rw [l8 sK0 X2 X0 X2]
  have l11 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l9 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X2]
  have l12 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l11 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l13 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l12 X0 sK0 X2 X1]
    conv => enter [1]; rw [← h54495 X2 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X2]
    conv => enter [1]; rw [l13 X0 sK0 X2 X1]
  have l15 : ∀ X2 sK0 X1 X0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 sK0 X1 X0
    conv => enter [1]; rw [l10 X2 sK0 X0]
    conv => enter [1]; rw [l14 X0 sK0 X2 X1]
  have l16 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ (X3 ◇ X4)) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h54495 X2 X3 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l17 : ∀ X2 X3 X4 X1 : G, (X2 ◇ (X3 ◇ X4)) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := by
    intro X2 X3 X4 X1
    conv => enter [1]; rw [l16 X2 X3 X4 X2 X1]
    conv => enter [1]; rw [← h54495 (X1 ◇ X2) X3 X4 X2]
  have l18 : ∀ X2 X3 X4 X1 : G, (X2 ◇ (X3 ◇ X4)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro X2 X3 X4 X1
    conv => enter [1]; rw [l17 X2 X3 X4 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X4)]
  have l19 : ∀ X1 sK0 X2 X3 X4 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X3 ◇ X4)) := by
    intro X1 sK0 X2 X3 X4
    conv => enter [1]; rw [l15 X1 sK0 X2 (X3 ◇ X4)]
    conv => enter [1]; rw [← l18 X2 X3 X4 X1]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l19 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54496 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54496 G := by
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
  intro x y z w
  conv => enter [1]; rw [l8 x y z y w]
  conv => enter [1]; rw [l6 y w z]

theorem Equation4512_54496_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54496 : Equation54496 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54496 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54496 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 X0 sK0 X0]
    conv => enter [1]; rw [← l1 X1 sK0 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
  have l6 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h54496 X0 sK0 sK2 X0]
    conv => enter [1]; rw [← h54496 X1 sK0 sK2 X0]
  have l7 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l2 sK2 sK0 X0]
  have l8 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [← l7 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54498 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54498 G := by
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
  intro x y z w
  conv => enter [1]; rw [l6 x y z y w]
  conv => enter [1]; rw [l5 y w z]

theorem Equation4512_54498_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54498 : Equation54498 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54498 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54498 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ X1)]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 X0 sK0 X0]
    conv => enter [1]; rw [← l1 X1 sK0 X0]
  have l4 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l3 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l4 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l3 X0 sK0 sK0]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 sK0 X1]
  have l7 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h54498 X0 sK0 sK2 X0]
    conv => enter [1]; rw [← h54498 X1 sK0 sK2 X0]
  have l8 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l2 X0 sK0 sK2]
  have l9 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [← l8 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54499 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54499 G := by
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
  have l4 : ∀ sK3 sK1 sK0 X1 X2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK3 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK1 sK0 X1 X2]
  have l5 : ∀ sK3 sK1 sK0 X1 X0 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK3]
  have l6 : ∀ sK3 sK1 sK0 X0 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 sK3]
  have l7 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK3 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK3 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z y w u]
  conv => enter [1]; rw [l6 y w u z]

theorem Equation4512_54499_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54499 : Equation54499 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h54499 X0 sK0 sK0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ X2)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X0 X0]
    conv => enter [1]; rw [← l2 X1 sK0 X0 X0]
  have l4 : ∀ sK0 sK2 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro sK0 sK2 X1 X2
    conv => enter [1]; rw [← l2 sK0 sK0 sK0 sK2]
    conv => enter [1]; rw [l2 sK0 sK0 X1 X2]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l1 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK2]
  have l6 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X1 X2]
  have l7 : ∀ X0 sK0 X1 sK1 sK2 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1)) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1, 1]; rw [l2 X0 sK0 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK2)) X1]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l7 X0 sK0 X1 sK0 sK0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l1 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0 sK0]
  have l14 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l9 sK0 sK0 X1]
    conv => enter [1]; rw [← l10 sK0 X1 sK0]
  have l15 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l14 sK0 X1]
  have l16 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (sK0 ◇ sK2)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [h54499 X1 sK0 sK2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l17 : ∀ X1 sK0 sK2 : G, (X1 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 sK2
    conv => enter [1]; rw [l16 X1 sK0 sK2 X1]
    conv => enter [1, 2]; rw [← l15 sK0 X1]
  have l18 : ∀ sK0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [l13 sK0 sK2]
    conv => enter [1]; rw [← l17 X1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54517 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54517 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK0 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l4 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 sK0]
  have l6 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w x]
  conv => enter [1]; rw [l5 w x z]

theorem Equation4512_54517_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54517 : Equation54517 G) : Equation4274 G := by
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
    conv => enter [1]; rw [h54517 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK2 X0 X1 sK1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X1)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0 X1 sK1
    conv => enter [1]; rw [h54517 (sK0 ◇ sK2) X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK2)]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 sK2 X0 sK1 : G, (((sK0 ◇ sK2) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1 ((sK0 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 sK0 X0]
  have l10 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [l6 sK0 sK2 X0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l6 sK0 X1 X0]
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
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK2) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1]; rw [← l7 sK0 sK2 X0 X0]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l10 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 sK1 (sK0 ◇ sK2)]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0 X1 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [l14 sK0 X0]
  have l19 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l15 X0 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
  have l21 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0 X1 X0]
  have l22 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l19 X0 sK0 sK2]
    conv => enter [1]; rw [l5 sK0 sK2 X0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
  have l24 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0 X1 X0]
  have l25 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l22 X0 sK0 X0 sK2]
    conv => enter [1]; rw [l11 sK0 (X0 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2)]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
  have l27 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 X1 X0]
  have l28 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l25 X0 sK0 sK2]
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ sK2)]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l28 X0 sK0 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l33 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l33 sK0 X0 sK0 sK0]
  have l35 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54517 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l34 sK0 (X0 ◇ X0)]
  have l36 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l35 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l30 sK0 X2]
  intro x y z
  conv => enter [1]; rw [← l36 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54518 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54518 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK1 ◇ sK2)]
  have l2 : ∀ X1 sK0 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK0 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK1 ◇ sK2)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2 X0]
  have l3 : ∀ X0 sK0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2)) := by
    intro X0 sK0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 sK2 X2 X0]
  have l4 : ∀ sK3 sK0 sK1 sK2 X1 X2 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2)) := by
    intro sK3 sK0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK1 sK2 X1 X2]
  have l5 : ∀ sK3 sK0 sK1 sK2 X1 X0 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK1 sK2 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK1 ◇ sK2)) sK3]
  have l6 : ∀ X0 sK3 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK1 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 X2 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z w x y]

theorem Equation4512_54518_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54518 : Equation54518 G) : Equation4274 G := by
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
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h54518 X0 X1 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [l3 sK0 sK2 X0]
  have l14 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (sK0 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l13 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK2) ◇ X0) X1]
  have l15 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l14 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) X0 X1]
  have l16 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ X1)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l15 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h54518 X0 X1 sK0 (sK0 ◇ sK2)]
  have l17 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [← l16 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l18 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54518 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l17 X0 X1 sK0 X0]
  have l19 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l20 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l6 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l22 sK0]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l12 sK0 X0 (X1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l12 sK0 X0 X1]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l12 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0]
  have l26 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l24 X0 X1 sK0]
    conv => enter [1]; rw [← h54518 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l25 sK0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l26 X0 X1 sK0]
    conv => enter [1]; rw [l18 X0 (X1 ◇ (sK0 ◇ sK0)) sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l27 sK0]
  have l30 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l28 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) sK0]
  have l31 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54518 (sK0 ◇ sK0) sK0 X0 X1]
    conv => enter [1]; rw [← l30 X0 X1 sK0]
  have l32 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l31 sK0 X0 X1]
  have l33 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l12 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l33 X0 sK0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0 sK0]
    conv => enter [1]; rw [← l34 sK0 X0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [← l23 sK0]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [← l29 sK0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l18 sK0 sK0 sK0]
    conv => enter [1]; rw [← l37 sK0 X0]
  have l39 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l23 sK0]
  have l40 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l39 sK0]
    conv => enter [1]; rw [l18 (sK0 ◇ sK0) sK0 sK0]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l40 sK0]
  have l42 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l18 X0 sK0 sK0]
    conv => enter [1]; rw [← l41 sK0 X0]
  have l43 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l38 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l42 X0 sK0]
  have l44 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54518 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l38 sK0 (X0 ◇ X1)]
  have l45 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l44 X0 X1 X2 sK0]
    conv => enter [1]; rw [l18 X2 sK0 sK0]
  have l46 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l45 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l43 sK0 X2]
  intro x y z
  conv => enter [1]; rw [← l46 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54520 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54520 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK1 ◇ sK0)]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK1 ◇ sK0)]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK1 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK3 sK0 sK1 X1 X2 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2)) := by
    intro sK3 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK1 X1 X2]
  have l5 : ∀ sK3 sK0 sK1 X1 X0 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK1 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK1 ◇ sK0)) sK3]
  have l6 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 X0 X2 sK3 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z w x]

end Semigroup5
