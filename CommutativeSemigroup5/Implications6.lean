import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_54625_implies_Equation54317 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54625 : Equation54625 G) : Equation54317 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK1) X0]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l6 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [h54625 X0 X1 X2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK0 X0 sK1 sK2]
  have l7 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h54625 X0 X1 X2 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 X0]
  have l8 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h54625 X0 X1 X2 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 X0]
  have l9 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [l7 X0 X1 X2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l10 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54625 sK1 X0 X0 X0 sK1]
    conv => enter [1]; rw [l8 sK1 X0 X0 sK0 sK1]
  have l11 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l10 X0 sK1 sK0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 sK0 sK1]
  have l12 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l11 X0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
  have l13 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l12 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK0 (sK1 ◇ sK2) sK0 sK1 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
    conv => enter [1]; rw [← l13 X0 sK1 sK0 sK0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 X0 X0 (sK1 ◇ sK1) sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
  have l17 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK1 sK2]
    conv => enter [1]; rw [← l0 X0 sK2 sK1]
  have l18 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l9 X0 sK2 sK1 sK0 sK1]
    conv => enter [1]; rw [l17 X0 sK2 sK1]
  have l19 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l18 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l20 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l18 sK0 sK1 X0 sK2]
  have l21 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l20 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l16 sK0 sK1 X0]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l19 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l21 sK1 sK2 X0 sK0]
  have l23 : ∀ sK0 sK1 sK2 X0 X2 X3 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X2 ◇ X3)) := by
    intro sK0 sK1 sK2 X0 X2 X3
    conv => enter [1]; rw [l22 sK0 sK1 sK2 ((sK1 ◇ sK2) ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← h54625 X0 X2 X3 (sK1 ◇ sK2) sK0]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l23 sK0 sK1 sK2 sK0 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l4 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l24 x y z x]

theorem Equation43_4512_54625_implies_Equation54327 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54625 : Equation54625 G) : Equation54327 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l2 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l3 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l4 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l3 sK0 sK3 X0]
  have l5 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK2) X0]
  have l6 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l7 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l0 sK1 (sK3 ◇ sK0) X0]
  have l8 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h54625 X0 X1 X2 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l5 sK1 X0 sK2]
  have l9 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h54625 X0 X1 X2 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l6 sK1 X0 sK2]
  have l10 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h54625 X0 X1 X2 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 X0]
  have l11 : ∀ X0 X1 X2 sK1 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 X2 sK1 sK3 sK0
    conv => enter [1]; rw [h54625 X0 X1 X2 sK1 (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [l7 sK1 X0 sK3 sK0]
  have l12 : ∀ X0 X1 X2 sK1 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 X2 sK1 sK3 sK0
    conv => enter [1]; rw [h54625 X0 X1 X2 sK1 (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK1 sK3 sK0 X0]
  have l13 : ∀ X0 X1 X2 sK1 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 X2 sK1 sK3 sK0
    conv => enter [1]; rw [l10 X0 X1 X2 sK1 X0]
    conv => enter [1]; rw [l11 sK1 (sK1 ◇ (sK1 ◇ (X0 ◇ X0))) X0 sK1 sK3 sK0]
  have l14 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l8 X0 X1 X2 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 X0]
  have l15 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK2)) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h54625 sK2 X0 X0 X0 sK2]
    conv => enter [1]; rw [l12 sK2 X0 X0 sK1 sK3 sK0]
  have l16 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l13 X0 X1 X2 sK1 X0 X0]
    conv => enter [1]; rw [l9 sK1 sK1 (sK1 ◇ (X0 ◇ X0)) sK1 sK2]
  have l17 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK1)) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l15 X0 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ (sK3 ◇ sK0)) sK2 sK1 sK3 sK0]
  have l18 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l16 X0 X1 X2 sK1 sK2]
    conv => enter [1]; rw [l14 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1 sK2]
  have l19 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l17 X0 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK3 ◇ sK0)) sK1]
  have l20 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l18 X0 X1 X2 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1]
  have l21 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l19 X0 sK2 sK1 X0 X0]
    conv => enter [1]; rw [l9 sK1 sK1 (sK1 ◇ (X0 ◇ X0)) sK1 sK2]
  have l22 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1) = (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l14 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1 sK2]
    conv => enter [1]; rw [← l21 X0 sK2 sK1]
  have l23 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l14 X0 X0 (sK2 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [← l22 sK1 sK2 X0]
  have l24 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l23 sK1 sK2 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1]
  have l25 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l24 sK1 sK2 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l26 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l25 sK1 sK2 X0]
    conv => enter [1]; rw [l25 sK1 sK2 X1]
  have l27 : ∀ X0 sK3 sK0 sK1 sK2 : G, (X0 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 X0 sK3]
    conv => enter [1]; rw [l20 sK0 X0 sK3 sK1 sK2]
  have l28 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK1 sK2]
    conv => enter [1]; rw [l20 sK1 X0 (sK2 ◇ sK2) sK1 sK2]
  have l29 : ∀ sK1 sK3 sK0 X0 sK2 : G, (sK1 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [l27 sK1 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l26 sK1 sK1 sK2 X0]
  have l30 : ∀ sK1 sK3 sK0 X0 sK2 : G, (sK1 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [l29 sK1 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [← l28 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l30 x y z x w]

theorem Equation43_4512_54625_implies_Equation54645 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54625 : Equation54625 G) : Equation54645 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l4 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK3)) X0]
  have l5 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ X0) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l7 : ∀ sK2 X0 sK3 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l2 sK2 (sK3 ◇ sK3) X0]
  have l8 : ∀ sK2 X0 sK3 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK3)))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK2 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [l2 sK2 (sK2 ◇ (sK3 ◇ sK3)) X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [l6 X2 X0 X1]
  have l10 : ∀ sK1 sK0 X1 X2 X0 sK4 : G, ((sK1 ◇ sK0) ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X1 X2 X0 sK4
    conv => enter [1]; rw [h54625 (sK1 ◇ sK0) X1 X2 X0 sK4]
    conv => enter [1, 2, 2]; rw [h43 (sK1 ◇ sK0) sK4]
  have l11 : ∀ X0 X1 X2 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro X0 X1 X2 sK2 sK3
    conv => enter [1]; rw [h54625 X0 X1 X2 sK2 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l7 sK2 X0 sK3]
  have l12 : ∀ X0 X1 X2 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))))) := by
    intro X0 X1 X2 sK2 sK3
    conv => enter [1]; rw [h54625 X0 X1 X2 sK2 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1, 2]; rw [l8 sK2 X0 sK3]
  have l13 : ∀ X0 X1 X2 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ X0)) := by
    intro X0 X1 X2 sK2 sK3
    conv => enter [1]; rw [h54625 X0 X1 X2 sK2 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1, 2]; rw [← l4 sK2 sK3 X0]
  have l14 : ∀ X0 X1 X2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro X0 X1 X2 sK3
    conv => enter [1]; rw [h54625 X0 X1 X2 sK3 sK3]
    conv => enter [1, 2]; rw [← l5 sK3 X0]
  have l15 : ∀ X0 X1 X2 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ X0) := by
    intro X0 X1 X2 sK2 sK3
    conv => enter [1]; rw [l11 X0 X1 X2 sK2 sK3]
    conv => enter [1]; rw [← l4 sK2 sK3 X0]
  have l16 : ∀ X0 sK4 sK1 sK0 sK3 : G, (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← l10 sK1 sK0 X0 X0 X0 sK4]
    conv => enter [1]; rw [l14 (sK1 ◇ sK0) X0 X0 sK3]
  have l17 : ∀ sK3 X0 sK4 sK1 sK0 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ sK3)) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [← l14 sK3 (sK3 ◇ sK3) (sK1 ◇ sK0) sK3]
    conv => enter [1]; rw [← l16 X0 sK4 sK1 sK0 sK3]
  have l18 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ X0) = (sK3 ◇ ((sK3 ◇ sK3) ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← l15 X0 X0 (sK2 ◇ (sK2 ◇ sK2)) sK2 sK3]
    conv => enter [1]; rw [← l17 sK3 X0 sK2 sK2 sK2]
  have l19 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ X0) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l18 sK2 sK3 X0]
    conv => enter [1]; rw [l2 sK3 (sK3 ◇ sK3) sK3]
  have l20 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l19 sK2 sK3 X0]
    conv => enter [1]; rw [l13 sK3 sK3 (sK3 ◇ sK3) sK2 sK3]
  have l21 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ X0) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l20 sK2 sK3 X0]
    conv => enter [1]; rw [l9 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) sK3]
  have l22 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l21 sK2 sK3 X0]
    conv => enter [1]; rw [l12 sK2 sK3 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) sK2 sK3]
  have l23 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ sK2) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l22 sK2 sK3 X0]
    conv => enter [1]; rw [l15 sK2 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) sK2 sK3]
  have l24 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l23 sK2 sK3 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) sK2]
  have l25 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← l24 sK2 sK3 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) X0]
  have l26 : ∀ sK2 sK3 X0 X2 X3 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) = (X0 ◇ (X2 ◇ X3)) := by
    intro sK2 sK3 X0 X2 X3
    conv => enter [1]; rw [← l24 sK2 sK3 ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ (X0 ◇ sK2))]
    conv => enter [1]; rw [← h54625 X0 X2 X3 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) sK2]
  have l27 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← l25 sK2 sK3 X0]
    conv => enter [1]; rw [l25 sK2 sK3 X1]
  have l28 : ∀ sK1 sK0 X0 sK2 sK3 : G, ((sK1 ◇ sK0) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK1 sK0 X0 sK2 sK3
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← l26 sK2 sK3 sK0 X0 sK1]
  have l29 : ∀ X0 sK3 sK2 : G, (X0 ◇ (sK3 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro X0 sK3 sK2
    conv => enter [1]; rw [l2 X0 sK3 sK3]
    conv => enter [1]; rw [← l26 sK2 sK3 sK3 X0 sK3]
  have l30 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [h43 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l28 sK1 sK0 sK4 sK2 sK3]
  have l31 : ∀ sK4 sK1 sK0 X0 sK2 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK4 sK1 sK0 X0 sK2 sK3
    conv => enter [1]; rw [l30 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l27 sK2 sK2 sK3 X0]
  have l32 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l30 sK4 sK1 sK0 sK4 sK4]
    conv => enter [1]; rw [l26 sK4 sK4 X0 sK4 (sK4 ◇ (sK4 ◇ (sK4 ◇ sK4)))]
    conv => enter [1, 2]; rw [← l30 sK4 sK1 sK0 sK4 sK4]
  have l33 : ∀ sK4 sK1 sK0 X0 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK4 sK1 sK0 X0 sK3
    conv => enter [1]; rw [l31 sK4 sK1 sK0 sK4 sK4 sK3]
    conv => enter [1]; rw [← l29 X0 sK3 sK4]
  have l34 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l33 sK2 sK3 sK3 sK2 sK2]
    conv => enter [1]; rw [l32 sK2 sK2 sK2 X0]
    conv => enter [1, 2]; rw [l33 sK2 sK2 sK2 sK2 sK3]
  intro x y z w u
  conv => enter [1]; rw [l33 x y z w u]
  conv => enter [1]; rw [l34 w u w]

theorem Equation43_4512_54625_implies_Equation54319 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54625 : Equation54625 G) : Equation54319 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK0) X0]
  have l3 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l5 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (X0 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← l0 sK2 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l6 : ∀ X0 X1 X2 sK1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 X1 X2 sK1 sK2 sK3
    conv => enter [1]; rw [h54625 X0 X1 X2 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK1 X0 sK2 sK3]
  have l7 : ∀ X0 X1 X2 sK1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 X1 X2 sK1 sK2 sK3
    conv => enter [1]; rw [h54625 X0 X1 X2 sK1 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [l4 sK1 X0 sK2 sK3]
  have l8 : ∀ X0 X1 X2 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 X2 sK1 sK2 sK0
    conv => enter [1]; rw [h54625 X0 X1 X2 sK1 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK0 X0]
  have l9 : ∀ X0 X1 X2 sK1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro X0 X1 X2 sK1 sK2 sK3
    conv => enter [1]; rw [l6 X0 X1 X2 sK1 sK2 sK3]
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 X0]
  have l10 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← h54625 sK2 X0 X0 X0 sK0]
    conv => enter [1]; rw [l8 sK2 X0 X0 sK1 sK2 sK0]
  have l11 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l10 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK2 ◇ sK0)) sK2 sK1 sK2 sK0]
  have l12 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l11 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ sK0)) sK1]
  have l13 : ∀ X0 sK2 sK0 sK1 sK3 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [l12 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 sK1 (sK1 ◇ (sK2 ◇ sK0)) sK1 sK2 sK3]
  have l14 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [← l9 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1 sK2 sK3]
    conv => enter [1]; rw [← l13 X0 sK2 sK0 sK1 sK3]
  have l15 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← l9 X0 X0 (sK2 ◇ sK1) sK1 sK2 sK3]
    conv => enter [1]; rw [← l14 sK1 sK2 sK3 X0 sK1]
  have l16 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l15 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1]
  have l17 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← l16 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l18 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← l17 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l17 sK1 sK2 sK3 X1]
  have l19 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [l18 X0 sK1 sK2 sK3 X1]
    conv => enter [1]; rw [h43 X1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l20 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l5 X0 sK2 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 sK2]
  have l21 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [← l9 X0 sK0 sK2 sK1 sK2 sK3]
    conv => enter [1]; rw [l20 X0 sK0 sK2]
  have l22 : ∀ X0 sK2 sK0 X1 sK1 sK3 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK2 sK0 X1 sK1 sK3
    conv => enter [1]; rw [← l21 sK1 sK2 sK3 X0 sK0]
    conv => enter [1]; rw [← l19 X1 sK1 sK2 sK3 X0]
  have l23 : ∀ sK2 sK0 X1 X0 sK1 sK3 : G, ((sK2 ◇ sK0) ◇ X1) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK0 X1 X0 sK1 sK3
    conv => enter [1]; rw [h43 (sK2 ◇ sK0) X1]
    conv => enter [1]; rw [l22 X1 sK2 sK0 X0 sK1 sK3]
  have l24 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ X1) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l22 sK1 sK2 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← l23 sK2 sK0 X1 sK1 sK1 sK1]
  have l25 : ∀ sK1 sK2 sK0 X0 X2 X3 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (X2 ◇ X3)) := by
    intro sK1 sK2 sK0 X0 X2 X3
    conv => enter [1]; rw [l24 sK1 sK2 sK0 ((sK2 ◇ sK0) ◇ (X0 ◇ sK1))]
    conv => enter [1]; rw [← h54625 X0 X2 X3 (sK2 ◇ sK0) sK1]
  have l26 : ∀ sK1 sK2 sK0 X0 sK3 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK0 X0 sK3
    conv => enter [1]; rw [l25 sK1 sK2 sK0 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l3 sK1 X0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l26 x y z x w]

theorem Equation43_4512_54625_implies_Equation54328 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54625 : Equation54625 G) : Equation54328 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK4)) X0]
  have l2 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l5 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ sK4) X0]
  have l6 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK3 ◇ sK4)) X0]
  have l7 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ sK0) X0]
  have l8 : ∀ X0 X1 X2 sK2 sK3 sK4 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro X0 X1 X2 sK2 sK3 sK4
    conv => enter [1]; rw [h54625 X0 X1 X2 sK2 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l5 sK2 X0 sK3 sK4]
  have l9 : ∀ X0 X1 X2 sK2 sK3 sK4 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro X0 X1 X2 sK2 sK3 sK4
    conv => enter [1]; rw [h54625 X0 X1 X2 sK2 (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1, 2]; rw [l6 sK2 X0 sK3 sK4]
  have l10 : ∀ X0 X1 X2 sK2 sK3 sK4 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0)) := by
    intro X0 X1 X2 sK2 sK3 sK4
    conv => enter [1]; rw [h54625 X0 X1 X2 sK2 (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1, 2]; rw [← l1 sK2 sK3 sK4 X0]
  have l11 : ∀ X0 X1 X2 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 X2 sK2 sK1 sK0
    conv => enter [1]; rw [h54625 X0 X1 X2 sK2 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l7 sK2 X0 sK1 sK0]
  have l12 : ∀ X0 X1 X2 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 X2 sK2 sK1 sK0
    conv => enter [1]; rw [h54625 X0 X1 X2 sK2 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK2 sK1 sK0 X0]
  have l13 : ∀ X0 X1 X2 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 X2 sK2 sK1 sK0
    conv => enter [1]; rw [l10 X0 X1 X2 sK2 X0 X0]
    conv => enter [1]; rw [l11 sK2 (sK2 ◇ (sK2 ◇ (X0 ◇ X0))) X0 sK2 sK1 sK0]
  have l14 : ∀ X0 X1 X2 sK2 sK3 sK4 : G, (X0 ◇ (X1 ◇ X2)) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) := by
    intro X0 X1 X2 sK2 sK3 sK4
    conv => enter [1]; rw [l8 X0 X1 X2 sK2 sK3 sK4]
    conv => enter [1]; rw [← l1 sK2 sK3 sK4 X0]
  have l15 : ∀ X0 sK3 sK4 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK4))) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK3)) := by
    intro X0 sK3 sK4 sK2 sK1 sK0
    conv => enter [1]; rw [← h54625 sK3 X0 X0 X0 sK4]
    conv => enter [1]; rw [l12 sK3 X0 X0 sK2 sK1 sK0]
  have l16 : ∀ X0 X1 X2 sK2 sK3 sK4 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro X0 X1 X2 sK2 sK3 sK4
    conv => enter [1]; rw [l13 X0 X1 X2 sK2 X0 X0]
    conv => enter [1]; rw [l9 sK2 sK2 (sK2 ◇ (X0 ◇ X0)) sK2 sK3 sK4]
  have l17 : ∀ X0 sK3 sK4 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK4))) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2)) := by
    intro X0 sK3 sK4 sK2 sK1 sK0
    conv => enter [1]; rw [l15 X0 sK3 sK4 sK2 sK1 sK0]
    conv => enter [1]; rw [l12 sK2 (sK2 ◇ (sK1 ◇ sK0)) sK3 sK2 sK1 sK0]
  have l18 : ∀ X0 X1 X2 sK2 sK3 sK4 : G, (X0 ◇ (X1 ◇ X2)) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ sK2) := by
    intro X0 X1 X2 sK2 sK3 sK4
    conv => enter [1]; rw [l16 X0 X1 X2 sK2 sK3 sK4]
    conv => enter [1]; rw [l14 sK2 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) sK2 sK3 sK4]
  have l19 : ∀ X0 sK3 sK4 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK4))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK3 sK4 sK2 sK1 sK0
    conv => enter [1]; rw [l17 X0 sK3 sK4 sK2 sK1 sK0]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK1 ◇ sK0)) sK2]
  have l20 : ∀ X0 X1 X2 sK2 sK3 sK4 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro X0 X1 X2 sK2 sK3 sK4
    conv => enter [1]; rw [l18 X0 X1 X2 sK2 sK3 sK4]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) sK2]
  have l21 : ∀ X0 sK3 sK4 sK2 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK4))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro X0 sK3 sK4 sK2
    conv => enter [1]; rw [l19 X0 sK3 sK4 sK2 X0 X0]
    conv => enter [1]; rw [l9 sK2 sK2 (sK2 ◇ (X0 ◇ X0)) sK2 sK3 sK4]
  have l22 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ sK2) = (X0 ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← l14 sK2 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) sK2 sK3 sK4]
    conv => enter [1]; rw [← l21 X0 sK3 sK4 sK2]
  have l23 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ sK2) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← l14 X0 X0 (sK3 ◇ sK4) sK2 sK3 sK4]
    conv => enter [1]; rw [← l22 sK2 sK3 sK4 X0]
  have l24 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l23 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) sK2]
  have l25 : ∀ sK2 sK3 sK4 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← l24 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) X0]
  have l26 : ∀ X0 sK2 sK3 sK4 X1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro X0 sK2 sK3 sK4 X1
    conv => enter [1]; rw [← l25 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [l25 sK2 sK3 sK4 X1]
  have l27 : ∀ X0 sK1 sK0 sK2 sK3 sK4 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro X0 sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [← l4 sK0 X0 sK1]
    conv => enter [1]; rw [l20 sK0 X0 sK1 sK2 sK3 sK4]
  have l28 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [l5 X0 sK2 sK3 sK4]
    conv => enter [1]; rw [l20 sK2 X0 (sK3 ◇ sK4) sK2 sK3 sK4]
  have l29 : ∀ sK2 sK1 sK0 X0 sK3 sK4 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK1 sK0 X0 sK3 sK4
    conv => enter [1]; rw [l27 sK2 sK1 sK0 sK2 sK3 sK4]
    conv => enter [1]; rw [l26 sK2 sK2 sK3 sK4 X0]
  have l30 : ∀ sK2 sK1 sK0 X0 sK3 sK4 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK1 sK0 X0 sK3 sK4
    conv => enter [1]; rw [l29 sK2 sK1 sK0 sK2 sK3 sK4]
    conv => enter [1]; rw [← l28 X0 sK2 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l30 x y z x w u]

theorem Equation43_4512_54625_implies_Equation54622 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54625 : Equation54625 G) : Equation54622 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l2 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l3 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l4 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l5 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l6 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK2 ◇ sK3) ◇ (X0 ◇ sK0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l5 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 sK3 (X0 ◇ sK0)]
  have l7 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK3) ◇ (X0 ◇ sK0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [l6 sK2 sK3 sK0 X0]
  have l8 : ∀ X0 X3 X4 X2 X1 : G, (X0 ◇ (X3 ◇ X4)) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X3 X4 X2 X1
    conv => enter [1]; rw [h54625 X0 X3 X4 X2 X1]
    conv => enter [1, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 X2 sK1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro X0 X1 X2 sK1 sK2 sK3
    conv => enter [1]; rw [h54625 X0 X1 X2 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK3 X0]
  have l10 : ∀ X0 X1 X2 sK1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro X0 X1 X2 sK1 sK2 sK3
    conv => enter [1]; rw [h54625 X0 X1 X2 sK1 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK3 X0]
  have l11 : ∀ X0 X1 X2 sK2 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 X2 sK2 sK3 sK0
    conv => enter [1]; rw [h54625 X0 X1 X2 sK2 (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK2 sK3 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK3 ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro X0 X1 X2 sK3 sK0
    conv => enter [1]; rw [h54625 X0 X1 X2 sK3 sK0]
    conv => enter [1, 2]; rw [← l5 sK3 sK0 X0]
  have l13 : ∀ X0 X1 X2 sK2 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 X2 sK2 sK3 sK0
    conv => enter [1]; rw [h54625 X0 X1 X2 (sK2 ◇ sK3) sK0]
    conv => enter [1, 2]; rw [← l7 sK2 sK3 sK0 X0]
  have l14 : ∀ X0 X1 X2 sK1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro X0 X1 X2 sK1 sK2 sK3
    conv => enter [1]; rw [l9 X0 X1 X2 sK1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l15 : ∀ X0 X3 X4 sK2 sK3 sK0 X2 : G, (X0 ◇ (X3 ◇ X4)) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro X0 X3 X4 sK2 sK3 sK0 X2
    conv => enter [1]; rw [l8 X0 X3 X4 X2 X0]
    conv => enter [1]; rw [l13 X2 (X0 ◇ X0) X2 sK2 sK3 sK0]
  have l16 : ∀ X0 X3 X4 sK3 sK0 sK2 : G, (X0 ◇ (X3 ◇ X4)) = (sK3 ◇ ((sK3 ◇ sK0) ◇ (sK2 ◇ sK3))) := by
    intro X0 X3 X4 sK3 sK0 sK2
    conv => enter [1]; rw [l15 X0 X3 X4 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l12 (sK2 ◇ sK3) (sK2 ◇ (sK3 ◇ sK0)) X0 sK3 sK0]
  have l17 : ∀ X0 X3 X4 sK3 sK0 : G, (X0 ◇ (X3 ◇ X4)) = (sK3 ◇ ((sK3 ◇ sK0) ◇ sK3)) := by
    intro X0 X3 X4 sK3 sK0
    conv => enter [1]; rw [l16 X0 X3 X4 sK3 sK0 X0]
    conv => enter [1]; rw [l12 sK3 (sK3 ◇ sK0) (X0 ◇ sK3) sK3 sK0]
  have l18 : ∀ X0 X3 X4 sK3 sK0 : G, (X0 ◇ (X3 ◇ X4)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro X0 X3 X4 sK3 sK0
    conv => enter [1]; rw [l17 X0 X3 X4 sK3 sK0]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK0) sK3]
  have l19 : ∀ X0 X3 X4 sK2 sK3 sK0 : G, (X0 ◇ (X3 ◇ X4)) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK3)) := by
    intro X0 X3 X4 sK2 sK3 sK0
    conv => enter [1]; rw [l18 X0 X3 X4 sK3 sK0]
    conv => enter [1]; rw [l11 sK3 sK3 (sK3 ◇ sK0) sK2 sK3 sK0]
  have l20 : ∀ X0 X3 X4 sK2 sK3 sK0 : G, (X0 ◇ (X3 ◇ X4)) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2)) := by
    intro X0 X3 X4 sK2 sK3 sK0
    conv => enter [1]; rw [l19 X0 X3 X4 sK2 sK3 sK0]
    conv => enter [1]; rw [l11 sK2 (sK2 ◇ (sK3 ◇ sK0)) sK3 sK2 sK3 sK0]
  have l21 : ∀ X0 X3 X4 sK2 sK3 sK0 : G, (X0 ◇ (X3 ◇ X4)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X3 X4 sK2 sK3 sK0
    conv => enter [1]; rw [l20 X0 X3 X4 sK2 sK3 sK0]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK3 ◇ sK0)) sK2]
  have l22 : ∀ X0 X3 X4 sK1 sK2 sK3 : G, (X0 ◇ (X3 ◇ X4)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2)) := by
    intro X0 X3 X4 sK1 sK2 sK3
    conv => enter [1]; rw [l21 X0 X3 X4 sK2 sK3 X0]
    conv => enter [1]; rw [l10 sK2 sK2 (sK2 ◇ (sK3 ◇ X0)) sK1 sK2 sK3]
  have l23 : ∀ X0 X3 X4 sK1 sK2 sK3 : G, (X0 ◇ (X3 ◇ X4)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1)) := by
    intro X0 X3 X4 sK1 sK2 sK3
    conv => enter [1]; rw [l22 X0 X3 X4 sK1 sK2 sK3]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK2 sK1 sK2 sK3]
  have l24 : ∀ X0 X3 X4 sK1 sK2 sK3 : G, (X0 ◇ (X3 ◇ X4)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 X3 X4 sK1 sK2 sK3
    conv => enter [1]; rw [l23 X0 X3 X4 sK1 sK2 sK3]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1]
  have l25 : ∀ sK1 sK2 sK3 X0 X3 X4 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = (X0 ◇ (X3 ◇ X4)) := by
    intro sK1 sK2 sK3 X0 X3 X4
    conv => enter [1]; rw [← l14 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1 sK2 sK3]
    conv => enter [1]; rw [← l24 X0 X3 X4 sK1 sK2 sK3]
  have l26 : ∀ sK1 sK2 sK3 X0 X3 X4 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ (X3 ◇ X4)) := by
    intro sK1 sK2 sK3 X0 X3 X4
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [l25 sK1 sK2 sK3 X0 X3 X4]
  have l27 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [← l0 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [← l26 sK1 sK2 sK3 sK1 (sK2 ◇ sK3) X0]
  have l28 : ∀ sK2 sK3 X0 sK1 : G, ((sK2 ◇ sK3) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 X0 sK1
    conv => enter [1]; rw [l3 sK2 sK3 X0]
    conv => enter [1]; rw [← l26 sK1 sK2 sK3 sK2 X0 sK3]
  have l29 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [l28 sK2 sK3 sK0 sK1]
  have l30 : ∀ sK2 sK3 sK0 X0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [l29 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l27 X0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l30 x y z w w]

theorem Equation43_4512_54625_implies_Equation54646 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54625 : Equation54625 G) : Equation54646 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK3 sK4 sK5 X0 : G, ((sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) ◇ X0) = (sK3 ◇ (X0 ◇ (sK3 ◇ (sK4 ◇ sK5)))) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ (sK4 ◇ sK5)) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ (sK4 ◇ sK5)) X0]
  have l2 : ∀ sK3 X0 sK4 sK5 : G, (sK3 ◇ (X0 ◇ (sK4 ◇ sK5))) = (X0 ◇ (sK3 ◇ (sK4 ◇ sK5))) := by
    intro sK3 X0 sK4 sK5
    conv => enter [1, 2]; rw [h43 X0 (sK4 ◇ sK5)]
    conv => enter [1]; rw [l0 sK3 (sK4 ◇ sK5) X0]
  have l3 : ∀ X0 X1 X2 sK3 sK4 sK5 : G, (X0 ◇ (X1 ◇ X2)) = (sK3 ◇ (X0 ◇ (sK3 ◇ (sK4 ◇ sK5)))) := by
    intro X0 X1 X2 sK3 sK4 sK5
    conv => enter [1]; rw [h54625 X0 X1 X2 sK3 (sK4 ◇ sK5)]
    conv => enter [1, 2]; rw [l2 sK3 X0 sK4 sK5]
  have l4 : ∀ X0 X1 X2 sK3 sK4 sK5 : G, (X0 ◇ (X1 ◇ X2)) = ((sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) ◇ X0) := by
    intro X0 X1 X2 sK3 sK4 sK5
    conv => enter [1]; rw [l3 X0 X1 X2 sK3 sK4 sK5]
    conv => enter [1]; rw [← l1 sK3 sK4 sK5 X0]
  have l5 : ∀ sK3 sK4 sK5 X0 : G, ((sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) ◇ X0) = ((sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) ◇ sK3) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1]; rw [l1 sK3 sK4 sK5 X0]
    conv => enter [1]; rw [l4 sK3 X0 (sK3 ◇ (sK4 ◇ sK5)) sK3 sK4 sK5]
  have l6 : ∀ sK3 sK4 sK5 X0 : G, ((sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) ◇ X0) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK4 ◇ sK5)))) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1]; rw [l5 sK3 sK4 sK5 X0]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) sK3]
  have l7 : ∀ X0 sK3 sK4 sK5 : G, (X0 ◇ (sK3 ◇ (sK4 ◇ sK5))) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK4 ◇ sK5)))) := by
    intro X0 sK3 sK4 sK5
    conv => enter [1]; rw [l4 X0 sK3 (sK4 ◇ sK5) sK3 sK4 sK5]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) X0]
  have l8 : ∀ X0 sK4 sK5 sK3 : G, (X0 ◇ (sK4 ◇ sK5)) = (X0 ◇ (sK3 ◇ (sK4 ◇ sK5))) := by
    intro X0 sK4 sK5 sK3
    conv => enter [1]; rw [l4 X0 sK4 sK5 sK3 sK4 sK5]
    conv => enter [1]; rw [← l4 X0 sK3 (sK4 ◇ sK5) sK3 sK4 sK5]
  have l9 : ∀ sK4 sK5 X0 sK3 : G, ((sK4 ◇ sK5) ◇ X0) = ((sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) ◇ X0) := by
    intro sK4 sK5 X0 sK3
    conv => enter [1]; rw [h43 (sK4 ◇ sK5) X0]
    conv => enter [1]; rw [l4 X0 sK4 sK5 sK3 sK4 sK5]
  have l10 : ∀ sK4 sK5 X0 sK3 : G, ((sK4 ◇ sK5) ◇ X0) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK4 ◇ sK5)))) := by
    intro sK4 sK5 X0 sK3
    conv => enter [1]; rw [l9 sK4 sK5 X0 sK3]
    conv => enter [1]; rw [l6 sK3 sK4 sK5 X0]
  have l11 : ∀ sK3 sK4 sK5 X0 : G, (sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) = ((sK4 ◇ sK5) ◇ X0) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1]; rw [l7 sK3 sK3 sK4 sK5]
    conv => enter [1]; rw [← l10 sK4 sK5 X0 sK3]
  have l12 : ∀ sK3 sK4 sK5 X0 : G, (sK3 ◇ (sK4 ◇ sK5)) = ((sK4 ◇ sK5) ◇ X0) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1]; rw [l8 sK3 sK4 sK5 sK3]
    conv => enter [1]; rw [l11 sK3 sK4 sK5 X0]
  have l13 : ∀ sK3 sK4 sK5 X0 : G, (sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) = (X0 ◇ (sK3 ◇ (sK4 ◇ sK5))) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1, 2]; rw [l12 sK3 sK4 sK5 X0]
    conv => enter [1]; rw [l0 sK3 (sK4 ◇ sK5) X0]
  have l14 : ∀ sK3 sK4 sK5 X0 : G, (sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) = ((sK3 ◇ (sK4 ◇ sK5)) ◇ X0) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1, 2]; rw [l12 sK3 sK4 sK5 X0]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK5) X0]
  have l15 : ∀ sK3 sK4 sK5 X0 : G, (sK3 ◇ (sK4 ◇ sK5)) = ((sK3 ◇ (sK4 ◇ sK5)) ◇ X0) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1]; rw [l8 sK3 sK4 sK5 sK3]
    conv => enter [1]; rw [l14 sK3 sK4 sK5 X0]
  have l16 : ∀ sK3 sK4 sK5 X0 : G, (sK3 ◇ (sK4 ◇ sK5)) = (X0 ◇ (sK3 ◇ (sK4 ◇ sK5))) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1]; rw [l8 sK3 sK4 sK5 sK3]
    conv => enter [1]; rw [l13 sK3 sK4 sK5 X0]
  have l17 : ∀ sK3 sK4 sK5 X0 sK0 sK1 : G, ((sK3 ◇ (sK4 ◇ sK5)) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK5 X0 sK0 sK1
    conv => enter [1, 1]; rw [l16 sK3 sK4 sK5 sK3]
    conv => enter [1]; rw [← l4 X0 sK0 sK1 sK3 sK4 sK5]
  have l18 : ∀ sK3 sK4 sK5 X0 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK5)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK5 X0 sK0 sK1
    conv => enter [1]; rw [l15 sK3 sK4 sK5 X0]
    conv => enter [1]; rw [l17 sK3 sK4 sK5 X0 sK0 sK1]
  have l19 : ∀ sK3 sK4 sK5 sK0 sK1 X0 : G, (sK3 ◇ (sK4 ◇ sK5)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK3 sK4 sK5 sK0 sK1 X0
    conv => enter [1]; rw [l18 sK3 sK4 sK5 X0 sK0 sK1]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK1)]
  have l20 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK5)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l19 sK3 sK4 sK5 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK2]
  intro x y z w u v
  conv => enter [1]; rw [l20 x y z w u v]
  conv => enter [1]; rw [l16 w u v w]

theorem Equation43_4512_54622_implies_Equation4271 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X1]
    conv => enter [1]; rw [h54622 sK1 sK2 X1 X0]
  have l2 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l1 sK1 sK2 X0 sK0]
  have l3 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l2 X0 sK1 sK2 X0]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 X0]
  have l4 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l3 X0 sK1 sK2 X1]
    conv => enter [1]; rw [h43 X1 (sK1 ◇ sK2)]
  have l5 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X1]
  have l6 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 ((sK1 ◇ sK2) ◇ (X0 ◇ X1))]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0 X0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l7 x y z x]

theorem Equation43_4512_54622_implies_Equation54340 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54340 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK3 sK0 X1 X0 : G, ((sK3 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X1]
    conv => enter [1]; rw [h54622 sK3 sK0 X1 X0]
  have l2 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ X0) = ((sK3 ◇ sK0) ◇ X1) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 X0 sK3]
    conv => enter [1]; rw [← l1 sK3 sK0 X1 sK3]
  have l3 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (sK3 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h43 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l1 sK3 sK0 X0 sK2]
  have l4 : ∀ X0 sK3 sK0 X1 : G, (X0 ◇ (sK3 ◇ sK0)) = (X1 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK3 sK0 X1
    conv => enter [1]; rw [l3 X0 sK3 sK0 X0]
    conv => enter [1]; rw [← l3 X1 sK3 sK0 X0]
  have l5 : ∀ sK3 sK0 X0 X1 sK2 : G, ((sK3 ◇ sK0) ◇ X0) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0 X1 sK2
    conv => enter [1]; rw [l1 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [l4 X1 sK3 sK0 sK2]
  have l6 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ sK0) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l4 sK2 sK3 sK0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l2 sK3 sK0 (sK3 ◇ sK0) X0]
  have l7 : ∀ sK2 sK3 sK0 X1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X1
    conv => enter [1]; rw [l6 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [l5 sK3 sK0 sK2 X1 sK2]
  have l8 : ∀ X0 X1 X2 sK2 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 X2 sK2 sK3 sK0
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK2 sK3 sK0 ((sK3 ◇ sK0) ◇ (X0 ◇ X1))]
  have l9 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l8 sK2 sK3 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [l0 sK2 sK3 X0]
  intro x y z w
  conv => enter [1]; rw [← l9 y z w x]
  conv => enter [1]; rw [l7 y z w x]

theorem Equation43_4512_54622_implies_Equation54345 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54345 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 sK3 sK4 : G, (X0 ◇ (sK3 ◇ sK4)) = (sK3 ◇ (X0 ◇ sK4)) := by
    intro X0 sK3 sK4
    conv => enter [1]; rw [← l0 sK3 sK4 X0]
    conv => enter [1, 2]; rw [h43 sK4 X0]
  have l2 : ∀ sK3 sK1 sK0 X1 X0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [h54622 sK3 (sK1 ◇ sK0) X1 X0]
  have l3 : ∀ X0 sK3 sK1 sK0 sK2 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK3 sK1 sK0 sK2
    conv => enter [1]; rw [h43 X0 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l2 sK3 sK1 sK0 X0 sK2]
  have l4 : ∀ X0 sK3 sK1 sK0 X1 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK3 sK1 sK0 X1
    conv => enter [1]; rw [l3 X0 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [← l3 X1 sK3 sK1 sK0 X0]
  have l5 : ∀ X0 sK3 sK1 sK0 X1 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro X0 sK3 sK1 sK0 X1
    conv => enter [1]; rw [l4 X0 sK3 sK1 sK0 X1]
    conv => enter [1]; rw [h43 X1 (sK3 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK2 sK3 sK1 sK0 X1 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK2 sK3 sK1 sK0 X1
    conv => enter [1]; rw [l5 sK2 sK3 sK1 sK0 X1]
  have l7 : ∀ X0 X1 X2 sK2 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 X2 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK2 sK3 sK1 sK0 ((sK3 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))]
  have l8 : ∀ sK2 sK3 sK1 sK0 X0 sK4 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK2 sK3 sK1 sK0 X0 sK4
    conv => enter [1]; rw [← l7 sK3 X0 sK4 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l1 sK3 X0 sK4]
  intro x y z w u
  conv => enter [1]; rw [← l8 x y w u x z]

theorem Equation43_4512_54622_implies_Equation54388 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54388 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [h43 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 sK4 sK5 : G, (X0 ◇ (sK4 ◇ sK5)) = (sK4 ◇ (X0 ◇ sK5)) := by
    intro X0 sK4 sK5
    conv => enter [1]; rw [← l1 sK4 sK5 X0]
    conv => enter [1, 2]; rw [h43 sK5 X0]
  have l3 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ sK2))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l0 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [h54622 (sK0 ◇ sK1) sK2 X1 X0]
  have l4 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X1 X0]
    conv => enter [1, 2, 2]; rw [h43 (sK0 ◇ sK1) sK2]
  have l5 : ∀ X0 sK2 sK0 sK1 sK3 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [h43 X0 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X0 sK3]
  have l6 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l5 X0 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 X1 sK2 sK0 sK1 X0]
  have l7 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [h43 X1 (sK2 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK3 sK2 sK0 sK1 X1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK3 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l7 sK3 sK2 sK0 sK1 X1]
  have l9 : ∀ X0 X1 X2 sK3 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 X2 sK3 sK2 sK0 sK1
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l8 sK3 sK2 sK0 sK1 ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1))]
  have l10 : ∀ sK3 sK2 sK0 sK1 X0 sK4 sK5 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK4 ◇ sK5)) := by
    intro sK3 sK2 sK0 sK1 X0 sK4 sK5
    conv => enter [1]; rw [← l9 sK4 X0 sK5 sK3 sK2 sK0 sK1]
    conv => enter [1]; rw [l2 sK4 X0 sK5]
  intro x y z w u v
  conv => enter [1]; rw [← l10 x w u v x y z]

theorem Equation43_4512_54622_implies_Equation54683 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54683 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [h43 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK5 sK6 X0 : G, ((sK5 ◇ sK6) ◇ X0) = (sK5 ◇ (X0 ◇ sK6)) := by
    intro sK5 sK6 X0
    conv => enter [1]; rw [← h4512 sK5 sK6 X0]
    conv => enter [1, 2]; rw [h43 sK6 X0]
  have l2 : ∀ sK1 sK2 sK0 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [← l0 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [h54622 (sK2 ◇ sK0) sK1 X1 X0]
  have l3 : ∀ sK1 sK2 sK0 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h43 (sK2 ◇ sK0) sK1]
  have l4 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l3 sK1 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0 X1 sK1]
  have l5 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l4 sK1 sK2 sK0 sK3 X0]
  have l6 : ∀ X0 X1 X2 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 X2 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l5 sK3 sK1 sK2 sK0 ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1))]
  have l7 : ∀ sK3 sK1 sK2 sK0 sK5 sK6 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK5 ◇ sK6) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 sK5 sK6 X0
    conv => enter [1]; rw [← l6 sK5 X0 sK6 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [← l1 sK5 sK6 X0]
  have l8 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ (sK5 ◇ sK6)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK4 (sK5 ◇ sK6)]
    conv => enter [1]; rw [← l7 sK3 sK1 sK2 sK0 sK5 sK6 sK4]
  intro x y z w u v r
  conv => enter [1]; rw [l8 x y z w u v r]

theorem Equation43_4512_54622_implies_Equation54312 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54312 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h54622 X0 (sK0 ◇ sK0) X1 sK0]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h54622 sK0 (sK0 ◇ sK0) X0 X1]
  have l7 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l0 sK1 sK2 X0]
    conv => enter [1]; rw [h54622 sK1 sK2 X0 X1]
  have l8 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54622 X0 X1 X2 (X3 ◇ X4)]
    conv => enter [1]; rw [← h4512 X3 X4 ((X3 ◇ X4) ◇ (X0 ◇ X1))]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54622 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ X1)]
  have l11 : ∀ X0 X1 X2 sK0 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X3 ◇ X4)) := by
    intro X0 X1 X2 sK0 X3 X4
    conv => enter [1]; rw [l8 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [l10 X3 X4 ((X3 ◇ X4) ◇ (X0 ◇ X1)) sK0]
  have l12 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X1)) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [l7 X0 sK1 sK2 X1]
    conv => enter [1]; rw [l10 X1 X1 (sK1 ◇ sK2) sK0]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l6 X0 sK0 X1]
    conv => enter [1]; rw [l10 X1 X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l15 : ∀ X0 X1 X2 sK0 X3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X3)) := by
    intro X0 X1 X2 sK0 X3
    conv => enter [1]; rw [l11 X0 X1 X2 sK0 X3 X0]
    conv => enter [1]; rw [l9 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X3 X0 sK0]
  have l16 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [l12 X0 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [l9 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1 X1 sK0]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l13 X0 sK0 X1]
    conv => enter [1]; rw [l9 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1 X1 sK0]
  have l18 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l15 X0 X1 X2 sK0 X0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0 sK0]
  have l19 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l16 X0 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0 sK0]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l17 X0 sK0 X0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0 sK0]
  have l21 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l18 X0 X1 X2 sK0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l22 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l19 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l23 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 sK0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l24 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l21 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l25 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l22 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l26 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l23 X0 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l27 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l24 X0 X1 X2 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l28 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l25 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l26 X0 sK0]
  have l30 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l28 X0 sK1 sK2 X0]
    conv => enter [1]; rw [← l28 X1 sK1 sK2 X0]
  have l31 : ∀ X0 X1 sK1 sK2 X2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) = (X2 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2 X2
    conv => enter [1]; rw [h4512 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l30 (X0 ◇ X1) sK1 sK2 X2]
  have l32 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← l31 X0 X1 sK1 sK2 sK0]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l27 sK0 sK0 (sK1 ◇ sK2) sK0]
  have l34 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [l29 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l34 x y z x]

theorem Equation43_4512_54622_implies_Equation54639 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54639 G := by
  have l0 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = ((sK3 ◇ sK0) ◇ X0) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h4512 sK0 sK3 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK3]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 X0 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l6 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [l4 sK1 X0]
    conv => enter [1]; rw [← h54622 X0 (sK1 ◇ sK1) X1 sK1]
  have l7 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ X0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 sK3 X0]
    conv => enter [1]; rw [h54622 sK0 sK3 X0 X1]
  have l8 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h54622 sK1 (sK1 ◇ sK1) X0 X1]
  have l9 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [h54622 X0 X1 X2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l10 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK1 (X0 ◇ X1)]
  have l11 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l8 X0 sK1 X1]
    conv => enter [1]; rw [l10 X1 X1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l12 : ∀ sK3 sK0 X0 sK1 X1 : G, ((sK3 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ X1)) := by
    intro sK3 sK0 X0 sK1 X1
    conv => enter [1]; rw [l7 sK3 sK0 X0 X1]
    conv => enter [1]; rw [l10 X1 X1 (sK0 ◇ sK3) sK1]
  have l13 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l6 sK1 X0 X1]
  have l14 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l11 X0 sK1 X1]
    conv => enter [1]; rw [l9 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X1 X1 sK1]
  have l15 : ∀ sK3 sK0 X0 sK1 X1 : G, ((sK3 ◇ sK0) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X1)) := by
    intro sK3 sK0 X0 sK1 X1
    conv => enter [1]; rw [l12 sK3 sK0 X0 sK1 X1]
    conv => enter [1]; rw [l9 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X1 X1 sK1]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l14 X0 sK1 X0]
    conv => enter [1]; rw [l9 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0 sK1]
  have l17 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ sK0) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1]; rw [l15 sK3 sK0 X0 sK1 sK3]
    conv => enter [1]; rw [l9 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK3 sK1]
  have l18 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l16 X0 sK1]
    conv => enter [1]; rw [l9 (sK1 ◇ sK1) (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  have l19 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ sK0) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1]; rw [l17 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [l9 (sK1 ◇ sK1) (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  have l20 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l18 X0 sK1]
    conv => enter [1]; rw [← l13 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l21 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1]; rw [l19 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [← l13 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l22 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l20 X0 sK1]
  have l23 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ sK0) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1]; rw [l21 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
  have l24 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ X0) = ((sK3 ◇ sK0) ◇ X1) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l23 sK3 sK0 X0 sK3]
    conv => enter [1]; rw [← l23 sK3 sK0 X1 sK3]
  have l25 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ sK0) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [h43 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l24 sK3 sK0 sK2 X0]
  have l26 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l25 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [l23 sK3 sK0 sK2 sK1]
  have l27 : ∀ sK2 sK3 sK0 X0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [l26 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l22 sK1 X0]
  intro x y z w
  conv => enter [1]; rw [l27 x y z w w]

theorem Equation43_4512_54622_implies_Equation54313 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54313 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 X2 X1 : G, (sK0 ◇ ((sK1 ◇ X0) ◇ X2)) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0 X2 X1
    conv => enter [1]; rw [h54622 sK0 (sK1 ◇ X0) X2 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h54622 X0 sK1 X1 sK0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h54622 X0 (sK0 ◇ sK1) X1 sK0]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
  have l6 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l3 sK0 sK1 X0 X1]
  have l7 : ∀ X1 sK0 sK1 X0 X2 : G, (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))) = (sK0 ◇ (sK1 ◇ (X0 ◇ X2))) := by
    intro X1 sK0 sK1 X0 X2
    conv => enter [1]; rw [← l2 sK0 sK1 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X2]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← l7 X1 sK0 sK1 X0 sK0]
  have l9 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l8 sK0 sK1 X1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 X1 sK0]
  have l10 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l9 sK0 sK1 X1]
  have l11 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l10 sK0 sK1 X1]
    conv => enter [1]; rw [h54622 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1 X0]
  have l12 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [← h54622 X1 X2 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X2) X0]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 X2]
  have l13 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l11 sK0 sK1 sK0 X1]
    conv => enter [1]; rw [l12 sK0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l14 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [l15 x y z x y]

theorem Equation43_4512_54622_implies_Equation54315 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54315 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l4 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l3 sK0 sK3 X0]
  have l5 : ∀ sK1 sK2 X0 X2 X1 : G, (sK1 ◇ ((sK2 ◇ X0) ◇ X2)) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0 X2 X1
    conv => enter [1]; rw [h54622 sK1 (sK2 ◇ X0) X2 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h54622 X0 sK2 X1 sK1]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [← h54622 X0 (sK1 ◇ sK2) X1 sK1]
  have l8 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l7 sK1 sK2 X0 X1]
  have l9 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l6 sK1 sK2 X0 X1]
  have l10 : ∀ X1 sK1 sK2 X0 X2 : G, (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) = (sK1 ◇ (sK2 ◇ (X0 ◇ X2))) := by
    intro X1 sK1 sK2 X0 X2
    conv => enter [1]; rw [← l5 sK1 sK2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X2]
  have l11 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← l10 X1 sK1 sK2 X0 sK1]
  have l12 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l11 sK1 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 X1 sK1]
  have l13 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l12 sK1 sK2 X1]
  have l14 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l13 sK1 sK2 X1]
    conv => enter [1]; rw [h54622 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X1 X0]
  have l15 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [← h54622 X1 X2 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X2) X0]
    conv => enter [1, 2]; rw [← l13 sK1 sK2 X2]
  have l16 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l14 sK1 sK2 sK1 X1]
    conv => enter [1]; rw [l15 sK1 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1 sK2]
  have l17 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK2 X0]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l18 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l17 sK1 sK2 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))]
  have l19 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [← l18 sK0 X0 sK3 sK1 sK2]
    conv => enter [1]; rw [l4 sK0 X0 sK3]
  intro x y z w
  conv => enter [1]; rw [← l19 x w x y z]

theorem Equation43_4512_54622_implies_Equation54636 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54636 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l3 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l4 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l3 sK0 sK3 X0]
  have l5 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0]
  have l6 : ∀ sK1 sK2 X0 X2 X1 : G, (sK1 ◇ ((sK2 ◇ X0) ◇ X2)) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0 X2 X1
    conv => enter [1]; rw [h54622 sK1 (sK2 ◇ X0) X2 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h54622 X0 sK2 X1 sK1]
  have l8 : ∀ sK1 X0 sK2 X1 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 X0 sK2 X1
    conv => enter [1, 2]; rw [← l5 sK1 X0 sK2]
    conv => enter [1]; rw [← h54622 X0 (sK1 ◇ sK2) X1 sK1]
  have l9 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [l8 sK1 X0 sK2 X1]
  have l10 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l7 sK1 sK2 X0 X1]
  have l11 : ∀ X1 sK1 sK2 X0 X2 : G, (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) = (sK1 ◇ (sK2 ◇ (X0 ◇ X2))) := by
    intro X1 sK1 sK2 X0 X2
    conv => enter [1]; rw [← l6 sK1 sK2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X2]
  have l12 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l10 sK1 sK2 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← l11 X1 sK1 sK2 X0 sK1]
  have l13 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l12 sK1 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 X1 sK1]
  have l14 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l13 sK1 sK2 X1]
  have l15 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l14 sK1 sK2 X1]
    conv => enter [1]; rw [h54622 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X1 X0]
  have l16 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [← h54622 X1 X2 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X2) X0]
    conv => enter [1, 2]; rw [← l14 sK1 sK2 X2]
  have l17 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l15 sK1 sK2 sK1 X1]
    conv => enter [1]; rw [l16 sK1 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1 sK2]
  have l18 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l17 sK1 sK2 X0]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l19 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l18 sK1 sK2 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))]
  have l20 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [← l19 sK0 X0 sK3 sK1 sK2]
    conv => enter [1]; rw [l4 sK0 X0 sK3]
  intro x y z w
  conv => enter [1]; rw [← l20 w x x y z]

theorem Equation43_4512_54622_implies_Equation54640 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54640 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l4 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK2 ◇ sK3)) X0]
  have l5 : ∀ sK2 X0 sK3 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l1 sK2 (sK2 ◇ sK3) X0]
  have l6 : ∀ sK2 sK3 X0 X2 X1 : G, (sK2 ◇ ((sK3 ◇ X0) ◇ X2)) = (X1 ◇ (X1 ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK2 sK3 X0 X2 X1
    conv => enter [1]; rw [h54622 sK2 (sK3 ◇ X0) X2 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK3 X0]
  have l7 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ ((sK2 ◇ sK3) ◇ X0)) = (X0 ◇ (sK3 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1, 2]; rw [l3 sK2 sK3 X0]
    conv => enter [1]; rw [← h54622 X0 sK3 X1 sK2]
  have l8 : ∀ sK2 X0 sK3 X1 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = (X0 ◇ ((sK2 ◇ sK3) ◇ X1)) := by
    intro sK2 X0 sK3 X1
    conv => enter [1, 2]; rw [← l5 sK2 X0 sK3]
    conv => enter [1]; rw [← h54622 X0 (sK2 ◇ sK3) X1 sK2]
  have l9 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X0) = (X0 ◇ ((sK2 ◇ sK3) ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l4 sK2 sK3 X0]
    conv => enter [1]; rw [l8 sK2 X0 sK3 X1]
  have l10 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (X0 ◇ (sK3 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [l7 sK2 sK3 X0 X1]
  have l11 : ∀ X1 sK2 sK3 X0 X2 : G, (X1 ◇ (X1 ◇ ((sK2 ◇ sK3) ◇ X0))) = (sK2 ◇ (sK3 ◇ (X0 ◇ X2))) := by
    intro X1 sK2 sK3 X0 X2
    conv => enter [1]; rw [← l6 sK2 sK3 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 sK3 X0 X2]
  have l12 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK2) = (X1 ◇ (X1 ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l10 sK2 sK3 sK2 (X0 ◇ sK2)]
    conv => enter [1]; rw [← l11 X1 sK2 sK3 X0 sK2]
  have l13 : ∀ sK2 sK3 X1 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK2) = (X1 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X1)) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l12 sK2 sK3 X1 sK2]
    conv => enter [1, 2]; rw [← l9 sK2 sK3 X1 sK2]
  have l14 : ∀ sK2 sK3 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X1 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X1)) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [l13 sK2 sK3 X1]
  have l15 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l14 sK2 sK3 X1]
    conv => enter [1]; rw [h54622 X1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) X1 X0]
  have l16 : ∀ X1 sK2 sK3 X0 X2 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 sK2 sK3 X0 X2
    conv => enter [1, 2]; rw [l14 sK2 sK3 X2]
    conv => enter [1]; rw [h54622 X1 X2 ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X2) X0]
  have l17 : ∀ sK2 sK3 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l15 sK2 sK3 sK2 X1]
    conv => enter [1]; rw [← l16 X1 sK2 sK3 sK2 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  have l18 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l17 sK2 sK3 X0]
    conv => enter [1]; rw [h43 X0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  have l19 : ∀ X0 X1 X2 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 X1 X2 sK2 sK3
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [← l18 sK2 sK3 ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1))]
  have l20 : ∀ sK2 sK3 sK1 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [← l19 sK0 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [← l2 sK1 sK0 X0]
  have l21 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l20 sK2 sK3 sK1 sK0 sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  intro x y z w u
  conv => enter [1]; rw [← l21 w u x y z]

theorem Equation43_4512_54622_implies_Equation54317 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54317 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h54622 X0 (sK1 ◇ sK1) X1 sK0]
  have l3 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X1]
    conv => enter [1]; rw [h54622 sK1 sK1 X1 X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l5 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = (X1 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l3 sK1 X0 X1]
    conv => enter [1]; rw [← l0 X1 (sK1 ◇ sK1) X1]
  have l6 : ∀ sK1 X0 sK0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [l5 sK1 X0 X1]
    conv => enter [1]; rw [← l4 sK0 sK1 X1 X1]
  have l7 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l3 sK1 sK0 sK0]
    conv => enter [1]; rw [l6 sK1 sK0 sK0 X1]
  have l8 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l7 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1))]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l3 sK1 X0 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X0]
  have l10 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l8 sK1 sK2 X0 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK2 X0]
  have l11 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l9 sK0 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [← l11 x y x z]
  conv => enter [1]; rw [← l9 x y x]

theorem Equation43_4512_54622_implies_Equation54327 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54327 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l2 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l3 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l2 sK0 sK3 X0]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK2) X0]
  have l5 : ∀ sK1 X0 sK2 X1 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK1 X0 sK2 X1
    conv => enter [1, 2]; rw [l4 X0 sK1 sK2]
    conv => enter [1]; rw [← h54622 X0 (sK2 ◇ sK2) X1 sK1]
  have l6 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ X1) = (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 X1]
    conv => enter [1]; rw [h54622 sK2 sK2 X1 X0]
  have l7 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [l5 sK1 X0 sK2 X1]
  have l8 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X0) = (X1 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l6 sK2 X0 X1]
    conv => enter [1]; rw [← l0 X1 (sK2 ◇ sK2) X1]
  have l9 : ∀ sK2 X0 sK1 X1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X1) := by
    intro sK2 X0 sK1 X1
    conv => enter [1]; rw [l8 sK2 X0 X1]
    conv => enter [1]; rw [← l7 sK1 sK2 X1 X1]
  have l10 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← l6 sK2 sK1 sK1]
    conv => enter [1]; rw [l9 sK2 sK1 sK1 X1]
  have l11 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l10 sK1 sK2 ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X1))]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l6 sK2 X0 sK1]
    conv => enter [1]; rw [h43 (sK2 ◇ sK2) X0]
  have l13 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [← l11 sK0 X0 sK3 sK1 sK2]
    conv => enter [1]; rw [l3 sK0 X0 sK3]
  have l14 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [← l12 sK1 sK2 sK1]
    conv => enter [1]; rw [l13 sK1 sK2 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l14 x w x y z]
  conv => enter [1]; rw [← l12 x w x]

theorem Equation43_4512_54622_implies_Equation54645 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54645 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK1]
  have l1 : ∀ sK1 sK0 sK4 X0 : G, ((sK1 ◇ sK0) ◇ (sK4 ◇ X0)) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 sK4 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) sK4 X0]
    conv => enter [1, 1]; rw [h43 (sK1 ◇ sK0) sK4]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l4 : ∀ X0 X1 X2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK3 ◇ sK3) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 sK3
    conv => enter [1]; rw [h54622 X0 X1 X2 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (X0 ◇ X1)]
  have l5 : ∀ sK3 X1 X0 : G, ((sK3 ◇ sK3) ◇ X1) = (X0 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X1 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 X1]
    conv => enter [1]; rw [h54622 sK3 sK3 X1 X0]
  have l6 : ∀ sK4 sK1 sK0 X1 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK4))) := by
    intro sK4 sK1 sK0 X1 X0
    conv => enter [1]; rw [← l1 sK1 sK0 sK4 X1]
    conv => enter [1]; rw [h54622 (sK1 ◇ sK0) sK4 X1 X0]
  have l7 : ∀ sK4 sK1 sK0 X1 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X1 X0
    conv => enter [1]; rw [l6 sK4 sK1 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h43 (sK1 ◇ sK0) sK4]
  have l8 : ∀ sK4 sK1 sK0 X0 sK3 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 X0 sK3
    conv => enter [1]; rw [l7 sK4 sK1 sK0 X0 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK4 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ X0 X1 X2 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 X2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l8 sK4 sK1 sK0 ((sK4 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) sK3]
  have l10 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X1) = (sK2 ◇ (X0 ◇ (X0 ◇ (sK3 ◇ sK3)))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK3) X1]
    conv => enter [1, 2]; rw [l5 sK3 X1 X0]
  have l11 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ X0) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [l5 sK3 X0 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK3 ◇ sK3)]
  have l12 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X1) = ((sK3 ◇ sK3) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l10 sK2 sK3 X1 X0]
    conv => enter [1]; rw [l4 sK2 X0 (X0 ◇ (sK3 ◇ sK3)) sK3]
  have l13 : ∀ sK2 X0 sK3 X1 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X1) := by
    intro sK2 X0 sK3 X1
    conv => enter [1]; rw [l2 sK2 X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l12 sK2 sK3 X1 X0]
  have l14 : ∀ sK2 sK3 X1 sK4 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X1) = ((sK3 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 X1 sK4 sK1 sK0
    conv => enter [1]; rw [← l13 sK2 sK2 sK3 X1]
    conv => enter [1]; rw [l9 sK2 sK2 (sK3 ◇ sK3) sK3 sK4 sK1 sK0]
  have l15 : ∀ sK3 sK2 X1 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X1) := by
    intro sK3 sK2 X1
    conv => enter [1]; rw [← l11 sK3 (sK3 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [← l14 sK2 sK3 X1 sK3 sK3 sK3]
  have l16 : ∀ sK2 sK3 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X1) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [← l5 sK3 (sK3 ◇ sK3) sK2]
    conv => enter [1]; rw [l15 sK3 sK2 X1]
  have l17 : ∀ X0 X1 X2 sK2 sK3 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro X0 X1 X2 sK2 sK3
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [← l16 sK2 sK3 ((sK2 ◇ (sK3 ◇ sK3)) ◇ (X0 ◇ X1))]
  have l18 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← l5 sK3 X0 sK2]
    conv => enter [1]; rw [h43 (sK3 ◇ sK3) X0]
  have l19 : ∀ sK2 sK3 sK1 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [← l17 sK0 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [← l3 sK1 sK0 X0]
  have l20 : ∀ sK2 sK3 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [← l18 sK2 sK3 sK2]
    conv => enter [1]; rw [l19 sK2 sK3 sK1 sK0 X0]
  have l21 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l20 sK2 sK3 sK1 sK0 sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  intro x y z w u
  conv => enter [1]; rw [← l21 w u x y z]
  conv => enter [1]; rw [← l18 w u w]

theorem Equation43_4512_54622_implies_Equation54319 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54319 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK3) X0]
  have l2 : ∀ sK2 sK0 X1 X0 : G, ((sK2 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 X1]
    conv => enter [1]; rw [h54622 sK2 sK0 X1 X0]
  have l3 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l2 sK2 sK0 X0 sK1]
  have l4 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [l3 X0 sK2 sK0 X0]
    conv => enter [1]; rw [← l3 X1 sK2 sK0 X0]
  have l5 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ X1) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [l4 X0 sK2 sK0 X1]
    conv => enter [1]; rw [h43 X1 (sK2 ◇ sK0)]
  have l6 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ X1) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l5 sK1 sK2 sK0 X1]
  have l7 : ∀ X0 X1 X2 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro X0 X1 X2 sK1 sK2 sK0
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK1 sK2 sK0 ((sK2 ◇ sK0) ◇ (X0 ◇ X1))]
  have l8 : ∀ sK1 sK2 sK0 X0 sK3 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK0 X0 sK3
    conv => enter [1]; rw [l7 sK1 sK2 sK0 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l1 sK1 X0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z x w]

theorem Equation43_4512_54622_implies_Equation54328 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54328 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK4)) X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ sK4) X0]
  have l5 : ∀ sK2 X0 sK3 sK4 X1 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (X0 ◇ ((sK3 ◇ sK4) ◇ X1)) := by
    intro sK2 X0 sK3 sK4 X1
    conv => enter [1, 2]; rw [l4 X0 sK2 sK3 sK4]
    conv => enter [1]; rw [← h54622 X0 (sK3 ◇ sK4) X1 sK2]
  have l6 : ∀ sK3 sK4 X1 X0 : G, ((sK3 ◇ sK4) ◇ X1) = (X0 ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK4 X1 X0
    conv => enter [1]; rw [← h4512 sK3 sK4 X1]
    conv => enter [1]; rw [h54622 sK3 sK4 X1 X0]
  have l7 : ∀ sK2 sK3 sK4 X0 X1 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = (X0 ◇ ((sK3 ◇ sK4) ◇ X1)) := by
    intro sK2 sK3 sK4 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [l5 sK2 X0 sK3 sK4 X1]
  have l8 : ∀ sK3 sK4 X0 X1 : G, ((sK3 ◇ sK4) ◇ X0) = (X1 ◇ ((sK3 ◇ sK4) ◇ X1)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l6 sK3 sK4 X0 X1]
    conv => enter [1]; rw [← l0 X1 (sK3 ◇ sK4) X1]
  have l9 : ∀ sK3 sK4 X0 sK2 X1 : G, ((sK3 ◇ sK4) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X1) := by
    intro sK3 sK4 X0 sK2 X1
    conv => enter [1]; rw [l8 sK3 sK4 X0 X1]
    conv => enter [1]; rw [← l7 sK2 sK3 sK4 X1 X1]
  have l10 : ∀ sK2 sK3 sK4 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X1) := by
    intro sK2 sK3 sK4 X1
    conv => enter [1]; rw [← l6 sK3 sK4 sK2 sK2]
    conv => enter [1]; rw [l9 sK3 sK4 sK2 sK2 X1]
  have l11 : ∀ X0 X1 X2 sK2 sK3 sK4 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 X1 X2 sK2 sK3 sK4
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
    conv => enter [1]; rw [← l10 sK2 sK3 sK4 ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ (X0 ◇ X1))]
  have l12 : ∀ sK2 sK3 sK4 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← l6 sK3 sK4 X0 sK2]
    conv => enter [1]; rw [h43 (sK3 ◇ sK4) X0]
  have l13 : ∀ sK2 sK3 sK4 X0 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 X0 sK1 sK0
    conv => enter [1]; rw [← l11 sK0 X0 sK1 sK2 sK3 sK4]
    conv => enter [1]; rw [l3 sK0 X0 sK1]
  have l14 : ∀ sK2 sK3 sK4 X0 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 X0 sK1 sK0
    conv => enter [1]; rw [← l12 sK2 sK3 sK4 sK2]
    conv => enter [1]; rw [l13 sK2 sK3 sK4 X0 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l14 x y z x w u]
  conv => enter [1]; rw [← l12 x w u x]

theorem Equation43_4512_54622_implies_Equation54625 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation54625 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ sK4) ◇ X0) = (sK3 ◇ (X0 ◇ sK4)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK3 sK4 X0]
    conv => enter [1, 2]; rw [h43 sK4 X0]
  have l2 : ∀ sK3 sK1 sK0 sK4 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ sK4) = ((sK3 ◇ sK4) ◇ (sK1 ◇ sK0)) := by
    intro sK3 sK1 sK0 sK4
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [← l1 sK3 sK4 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l5 : ∀ sK3 sK4 X1 X0 : G, ((sK3 ◇ sK4) ◇ X1) = (X0 ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK4 X1 X0
    conv => enter [1]; rw [← h4512 sK3 sK4 X1]
    conv => enter [1]; rw [h54622 sK3 sK4 X1 X0]
  have l6 : ∀ sK3 sK1 sK0 X1 X0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [h54622 sK3 (sK1 ◇ sK0) X1 X0]
  have l7 : ∀ sK3 sK1 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l6 sK3 sK1 sK0 X0 sK3]
    conv => enter [1]; rw [← l6 sK3 sK1 sK0 X1 sK3]
  have l8 : ∀ sK3 sK1 sK0 X0 sK4 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK3 ◇ sK4) ◇ (sK1 ◇ sK0)) := by
    intro sK3 sK1 sK0 X0 sK4
    conv => enter [1]; rw [l7 sK3 sK1 sK0 X0 sK4]
    conv => enter [1]; rw [l2 sK3 sK1 sK0 sK4]
  have l9 : ∀ X0 X1 X2 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK3 ◇ sK4) ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 X2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l8 sK3 sK1 sK0 ((sK3 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) sK4]
  have l10 : ∀ sK2 sK3 sK4 X1 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X1) = (sK2 ◇ (X0 ◇ (X0 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4 X1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK4) X1]
    conv => enter [1, 2]; rw [l5 sK3 sK4 X1 X0]
  have l11 : ∀ sK2 sK3 sK4 X1 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X1) = ((sK3 ◇ sK4) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 X1 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK3 sK4 X1 sK2]
    conv => enter [1]; rw [l9 sK2 sK2 (sK2 ◇ (sK3 ◇ sK4)) sK3 sK4 sK1 sK0]
  have l12 : ∀ sK2 sK3 sK4 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ X1) := by
    intro sK2 sK3 sK4 X1
    conv => enter [1]; rw [← l5 sK3 sK4 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l11 sK2 sK3 sK4 X1 sK2 sK2]
  have l13 : ∀ X0 X1 X2 sK2 sK3 sK4 : G, (X0 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 X1 X2 sK2 sK3 sK4
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1]; rw [← l12 sK2 sK3 sK4 ((sK2 ◇ (sK3 ◇ sK4)) ◇ (X0 ◇ X1))]
  have l14 : ∀ sK2 sK3 sK4 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← l5 sK3 sK4 X0 sK2]
    conv => enter [1]; rw [h43 (sK3 ◇ sK4) X0]
  have l15 : ∀ sK2 sK3 sK4 X0 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 X0 sK1 sK0
    conv => enter [1]; rw [← l13 sK0 X0 sK1 sK2 sK3 sK4]
    conv => enter [1]; rw [l4 sK0 X0 sK1]
  have l16 : ∀ sK2 sK3 sK4 X0 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 X0 sK1 sK0
    conv => enter [1]; rw [← l14 sK2 sK3 sK4 sK2]
    conv => enter [1]; rw [l15 sK2 sK3 sK4 X0 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l16 x y z w x u]
  conv => enter [1]; rw [← l14 w x u w]

theorem Equation43_4512_54328_implies_Equation4271 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK1 ◇ sK2)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l8 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l9 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h54328 sK0 X2 sK0 X0 X1]
    conv => enter [1]; rw [← l3 sK0 X2]
  have l10 : ∀ sK0 X0 X1 sK1 sK2 X2 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro sK0 X0 X1 sK1 sK2 X2
    conv => enter [1]; rw [← h54328 sK0 X2 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 X2]
  have l11 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h54328 sK0 X2 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l6 sK0 X2]
  have l12 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l11 sK0 X0 X1 X2]
  have l13 : ∀ sK0 X0 X1 sK1 sK2 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro sK0 X0 X1 sK1 sK2 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l10 sK0 X0 X1 sK1 sK2 X2]
  have l14 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 sK0 X0 X1 X2]
  have l15 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l12 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK1 ◇ sK2)]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l12 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l19 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l17 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l20 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l18 sK0 X0]
    conv => enter [1]; rw [l18 sK0 X1]
  have l21 : ∀ sK0 sK1 sK2 X0 X3 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X3) := by
    intro sK0 sK1 sK2 X0 X3
    conv => enter [1]; rw [← l13 sK0 sK0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l13 sK0 sK0 sK0 sK1 sK2 X3]
  have l22 : ∀ sK0 sK1 sK2 X0 X3 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X3) := by
    intro sK0 sK1 sK2 X0 X3
    conv => enter [1]; rw [← l13 sK0 sK0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l12 sK0 sK0 sK0 X3]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l22 sK0 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l16 sK0 sK0]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l23 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2 sK0]
  have l25 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) X1]
  have l26 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← l25 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l20 (sK0 ◇ (sK1 ◇ sK2)) sK0 X1]
  have l27 : ∀ sK0 X0 sK1 sK2 X3 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X3) := by
    intro sK0 X0 sK1 sK2 X3
    conv => enter [1]; rw [← l14 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l13 sK0 sK0 sK0 sK1 sK2 X3]
  have l28 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l24 sK0 sK1 sK2 sK0]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l28 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) X0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l29 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 sK0 sK0 sK0 X0]
  have l31 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l8 sK0 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X2]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 sK0]
    conv => enter [1]; rw [← l31 sK0 X0 X1 sK0]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l33 x y z]

theorem Equation43_4512_54328_implies_Equation54340 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54340 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) sK0]
  have l3 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l4 : ∀ X0 X1 X2 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 X2 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 (sK1 ◇ (sK2 ◇ sK3)) sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK3 sK0]
  have l5 : ∀ X3 X0 X1 X2 X4 X5 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X4 ◇ X5) ◇ (X3 ◇ X0)) := by
    intro X3 X0 X1 X2 X4 X5
    conv => enter [1, 2]; rw [l3 X0 X1 X2 X4 X5]
    conv => enter [1]; rw [l0 X3 X0 (X4 ◇ X5)]
  have l6 : ∀ X3 X0 X1 X2 X4 X5 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X4 ◇ (X5 ◇ (X3 ◇ X0))) := by
    intro X3 X0 X1 X2 X4 X5
    conv => enter [1]; rw [l5 X3 X0 X1 X2 X4 X5]
    conv => enter [1]; rw [← h4512 X4 X5 (X3 ◇ X0)]
  have l7 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [l3 X0 sK2 sK3 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0 sK1 (sK2 ◇ sK3)]
  have l8 : ∀ X3 X0 X1 X2 X4 sK1 sK2 sK3 sK0 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X4 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X3 X0 X1 X2 X4 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 X3 X0 X1 X2 X4 X3]
    conv => enter [1]; rw [l4 X4 X3 (X3 ◇ X0) sK1 sK2 sK3 sK0]
  have l9 : ∀ X4 sK1 sK2 sK3 sK0 X3 : G, (X4 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X3 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X4 sK1 sK2 sK3 sK0 X3
    conv => enter [1]; rw [← l4 X4 X4 (X4 ◇ X4) sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l8 X4 X4 X4 X4 X3 sK1 sK2 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [← l7 X0 sK2 sK3 sK1]
  have l11 : ∀ sK2 sK3 X0 sK1 : G, ((sK2 ◇ sK3) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) := by
    intro sK2 sK3 X0 sK1
    conv => enter [1]; rw [h43 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [← l10 sK1 sK2 sK3 X0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ sK3) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l11 sK2 sK3 sK0 sK1]
  have l13 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [← l12 sK1 sK2 sK3 sK0]
  have l14 : ∀ X0 sK2 sK3 sK0 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK2 sK3 sK0 X1
    conv => enter [1, 2]; rw [l13 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l9 X0 X0 sK2 sK3 sK0 X1]
    conv => enter [1, 2]; rw [← l13 sK2 sK3 sK0 X0]
  have l15 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l13 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [l14 sK2 sK2 sK3 sK0 X0]
  have l16 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 X0]
  have l17 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l16 sK1 sK2 sK3 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l15 sK2 sK3 sK0 (sK1 ◇ (sK2 ◇ sK3))]
  intro x y z w
  conv => enter [1]; rw [l17 x y z w]
  conv => enter [1]; rw [l13 y z w x]

theorem Equation43_4512_54328_implies_Equation54345 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54345 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ sK4) ◇ X0) = (sK3 ◇ (X0 ◇ sK4)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK3 sK4 X0]
    conv => enter [1, 2]; rw [h43 sK4 X0]
  have l2 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ sK4) X0]
  have l3 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l4 : ∀ X0 X1 X2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 X2 sK1 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  have l5 : ∀ X0 sK3 sK4 sK2 : G, (X0 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK3 sK4 sK2
    conv => enter [1]; rw [l3 X0 sK3 sK4 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0 sK2 (sK3 ◇ sK4)]
  have l6 : ∀ X0 sK3 sK4 sK1 sK0 : G, (X0 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 X0 sK3 sK4 X0 X0]
    conv => enter [1]; rw [l4 X0 X0 X0 sK1 sK0]
  have l7 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [h43 (sK2 ◇ (sK3 ◇ sK4)) X0]
    conv => enter [1]; rw [← l5 X0 sK3 sK4 sK2]
  have l8 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1, 2]; rw [l6 sK3 sK1 sK0 sK3 sK4]
    conv => enter [1]; rw [l2 sK2 sK3 sK3 sK4]
  have l9 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK3 ◇ sK4)) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l8 sK2 sK3 sK1 sK0 sK4]
    conv => enter [1]; rw [← l5 sK3 sK3 sK4 sK2]
  have l10 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK3 sK1 sK0 sK3 sK3]
    conv => enter [1]; rw [← l9 sK2 sK3 sK1 sK0 sK3]
  have l11 : ∀ sK3 sK4 X0 sK2 : G, ((sK3 ◇ sK4) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) := by
    intro sK3 sK4 X0 sK2
    conv => enter [1]; rw [h43 (sK3 ◇ sK4) X0]
    conv => enter [1]; rw [← l7 sK2 sK3 sK4 X0]
  have l12 : ∀ sK3 sK4 X0 sK2 : G, ((sK3 ◇ sK4) ◇ X0) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK4 X0 sK2
    conv => enter [1]; rw [l11 sK3 sK4 X0 sK2]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK3 ◇ sK4)) X0]
  have l13 : ∀ sK2 sK3 sK4 X0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l3 sK2 sK3 sK4 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [l2 sK2 X0 sK3 sK4]
  have l14 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ sK4) ◇ X0) = (sK3 ◇ (sK3 ◇ sK4)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l1 sK3 sK4 X0]
    conv => enter [1]; rw [l3 sK3 X0 sK4 sK3 sK4]
  have l15 : ∀ sK3 sK1 sK0 sK4 X0 : G, (sK3 ◇ (sK1 ◇ sK0)) = ((sK3 ◇ sK4) ◇ X0) := by
    intro sK3 sK1 sK0 sK4 X0
    conv => enter [1]; rw [l6 sK3 sK1 sK0 sK3 sK4]
    conv => enter [1]; rw [← l14 sK3 sK4 X0]
  have l16 : ∀ sK3 sK1 sK0 X0 sK2 sK4 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK1 sK0 X0 sK2 sK4
    conv => enter [1]; rw [l15 sK3 sK1 sK0 sK4 X0]
    conv => enter [1]; rw [l12 sK3 sK4 X0 sK2]
  have l17 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l13 sK2 sK3 sK4 sK2]
    conv => enter [1]; rw [← l16 sK3 sK1 sK0 sK2 sK2 sK4]
  intro x y z w u
  conv => enter [1]; rw [l17 x y z w u]
  conv => enter [1]; rw [l10 y w u x]

theorem Equation43_4512_54328_implies_Equation54388 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54388 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK3 sK2 sK0 sK1 X0 : G, ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK3 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK3 (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l0 X1 X2 X0]
    conv => enter [1]; rw [h43 (X1 ◇ X2) X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l5 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l6 : ∀ X0 X1 X2 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 X2 sK2 sK0 sK1
    conv => enter [1]; rw [l5 X0 X1 X2 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) sK2]
  have l7 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X4) ◇ (X0 ◇ X5)) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [l5 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [l3 X5 X0 (X3 ◇ X4)]
  have l8 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X4 ◇ (X0 ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [l7 X5 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X3 X4 (X0 ◇ X5)]
  have l9 : ∀ X0 sK4 sK5 sK3 : G, (X0 ◇ (sK4 ◇ sK5)) = (X0 ◇ (sK3 ◇ (sK4 ◇ sK5))) := by
    intro X0 sK4 sK5 sK3
    conv => enter [1]; rw [l5 X0 sK4 sK5 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 sK3 (sK4 ◇ sK5)]
  have l10 : ∀ X0 sK4 sK5 sK0 sK1 : G, (X0 ◇ (sK4 ◇ sK5)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK4 sK5 sK0 sK1
    conv => enter [1]; rw [l5 X0 sK4 sK5 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 sK0 sK1]
  have l11 : ∀ X5 X0 X1 X2 X3 sK2 sK0 sK1 : G, (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X5 X0 X1 X2 X3 sK2 sK0 sK1
    conv => enter [1]; rw [l8 X5 X0 X1 X2 X3 X5]
    conv => enter [1]; rw [l6 X3 X5 (X0 ◇ X5) sK2 sK0 sK1]
  have l12 : ∀ X3 sK2 sK0 sK1 X5 : G, (X3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X3 sK2 sK0 sK1 X5
    conv => enter [1]; rw [l6 X3 sK2 (sK0 ◇ sK1) X3 X3 X3]
    conv => enter [1]; rw [l11 X3 X3 X3 X3 X5 sK2 sK0 sK1]
  have l13 : ∀ sK3 sK4 sK5 X0 : G, ((sK3 ◇ (sK4 ◇ sK5)) ◇ X0) = (X0 ◇ (sK4 ◇ sK5)) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1]; rw [h43 (sK3 ◇ (sK4 ◇ sK5)) X0]
    conv => enter [1]; rw [← l9 X0 sK4 sK5 sK3]
  have l14 : ∀ sK0 sK1 X0 sK4 sK5 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK4 ◇ sK5)) := by
    intro sK0 sK1 X0 sK4 sK5
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l10 X0 sK0 sK1 sK4 sK5]
  have l15 : ∀ sK3 sK2 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK3 sK2 sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l12 sK3 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [← l4 (sK2 ◇ (sK0 ◇ sK1)) X0 X1]
  have l16 : ∀ sK3 sK2 sK0 sK1 X0 : G, ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l15 sK3 sK2 sK0 sK1 X0 sK3]
    conv => enter [1]; rw [l6 (sK2 ◇ (sK0 ◇ sK1)) X0 sK3 sK2 sK0 sK1]
  have l17 : ∀ sK3 sK2 sK0 sK1 X0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK3 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l12 sK3 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l16 sK3 sK2 sK0 sK1 X0]
  have l18 : ∀ sK4 sK5 X0 sK3 : G, ((sK4 ◇ sK5) ◇ X0) = ((sK3 ◇ (sK4 ◇ sK5)) ◇ X0) := by
    intro sK4 sK5 X0 sK3
    conv => enter [1]; rw [h43 (sK4 ◇ sK5) X0]
    conv => enter [1]; rw [← l13 sK3 sK4 sK5 X0]
  have l19 : ∀ sK0 sK1 X0 sK4 sK5 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK4 ◇ sK5) ◇ X0) := by
    intro sK0 sK1 X0 sK4 sK5
    conv => enter [1]; rw [l14 sK0 sK1 X0 sK4 sK5]
    conv => enter [1]; rw [h43 X0 (sK4 ◇ sK5)]
  have l20 : ∀ sK2 sK0 sK1 sK4 sK5 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK4 ◇ sK5) ◇ sK2) := by
    intro sK2 sK0 sK1 sK4 sK5
    conv => enter [1]; rw [h43 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l19 sK0 sK1 sK2 sK4 sK5]
  have l21 : ∀ sK3 sK2 sK0 sK1 sK4 sK5 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK4 ◇ sK5)) ◇ sK2) := by
    intro sK3 sK2 sK0 sK1 sK4 sK5
    conv => enter [1, 2]; rw [l20 sK2 sK0 sK1 sK4 sK5]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK5) sK2]
  have l22 : ∀ sK3 sK2 sK0 sK1 sK4 sK5 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ sK5) ◇ sK2) := by
    intro sK3 sK2 sK0 sK1 sK4 sK5
    conv => enter [1]; rw [l21 sK3 sK2 sK0 sK1 sK4 sK5]
    conv => enter [1]; rw [← l18 sK4 sK5 sK2 sK3]
  have l23 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [l20 sK2 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [← l22 sK3 sK2 sK0 sK1 sK2 sK2]
  have l24 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 X0 : G, (sK3 ◇ (sK4 ◇ sK5)) = ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l5 sK3 sK4 sK5 X0 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l2 sK3 sK2 sK0 sK1 X0]
  have l25 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK5)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l24 sK3 sK4 sK5 sK2 sK0 sK1 sK3]
    conv => enter [1]; rw [← l17 sK3 sK2 sK0 sK1 sK3]
  have l26 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK5)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l25 sK3 sK4 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [← l23 sK2 sK0 sK1 sK3]
  intro x y z w u v
  conv => enter [1]; rw [l26 x y z w u v]
  conv => enter [1]; rw [l23 w u v x]

theorem Equation43_4512_54328_implies_Equation54683 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54683 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [h43 (sK2 ◇ sK0) sK1]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l1 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l0 X1 X2 X0]
    conv => enter [1]; rw [h43 (X1 ◇ X2) X0]
  have l4 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l5 : ∀ X0 X1 X2 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 X1 X2 sK2 sK0
    conv => enter [1]; rw [l4 X0 X1 X2 sK0 sK2]
    conv => enter [1, 2]; rw [h43 sK0 sK2]
  have l6 : ∀ X0 X1 X2 sK4 sK5 sK6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK4 ◇ (sK5 ◇ sK6))) := by
    intro X0 X1 X2 sK4 sK5 sK6
    conv => enter [1]; rw [l4 X0 X1 X2 (sK5 ◇ sK6) sK4]
    conv => enter [1, 2]; rw [h43 (sK5 ◇ sK6) sK4]
  have l7 : ∀ X0 X1 X2 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 X2 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l4 X0 X1 X2 (sK1 ◇ (sK2 ◇ sK0)) sK3]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l8 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X4) ◇ (X0 ◇ X5)) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [l4 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [l3 X5 X0 (X3 ◇ X4)]
  have l9 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X4 ◇ (X0 ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [l8 X5 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X3 X4 (X0 ◇ X5)]
  have l10 : ∀ X0 sK2 sK0 sK4 sK5 sK6 : G, (X0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK4 ◇ (sK5 ◇ sK6))) := by
    intro X0 sK2 sK0 sK4 sK5 sK6
    conv => enter [1]; rw [l5 X0 sK2 sK0 X0 X0]
    conv => enter [1]; rw [l6 X0 X0 X0 sK4 sK5 sK6]
  have l11 : ∀ X5 X0 X1 X2 X3 sK3 sK1 sK2 sK0 : G, (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X5 X0 X1 X2 X3 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l9 X5 X0 X1 X2 X3 X5]
    conv => enter [1]; rw [l7 X3 X5 (X0 ◇ X5) sK3 sK1 sK2 sK0]
  have l12 : ∀ X3 sK3 sK1 sK2 sK0 X5 : G, (X3 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X5 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X3 sK3 sK1 sK2 sK0 X5
    conv => enter [1]; rw [← l7 X3 X3 (X3 ◇ X3) sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [l11 X3 X3 X3 X3 X5 sK3 sK1 sK2 sK0]
  have l13 : ∀ sK2 sK0 X0 sK4 sK5 sK6 : G, ((sK2 ◇ sK0) ◇ X0) = (X0 ◇ (sK4 ◇ (sK5 ◇ sK6))) := by
    intro sK2 sK0 X0 sK4 sK5 sK6
    conv => enter [1]; rw [h43 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [l10 X0 sK2 sK0 sK4 sK5 sK6]
  have l14 : ∀ X0 sK3 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro X0 sK3 sK1 sK2 sK0 X1
    conv => enter [1]; rw [l12 X0 sK3 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [h43 X1 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l15 : ∀ sK2 sK0 X0 sK4 sK5 sK6 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK4 ◇ (sK5 ◇ sK6)) ◇ X0) := by
    intro sK2 sK0 X0 sK4 sK5 sK6
    conv => enter [1]; rw [l13 sK2 sK0 X0 sK4 sK5 sK6]
    conv => enter [1]; rw [h43 X0 (sK4 ◇ (sK5 ◇ sK6))]
  have l16 : ∀ sK3 sK1 sK2 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro sK3 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [← l14 X1 sK3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h43 X1 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l17 : ∀ sK1 sK2 sK0 X0 sK4 sK5 sK6 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK4 ◇ (sK5 ◇ sK6)) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0 sK4 sK5 sK6
    conv => enter [1]; rw [l2 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l15 sK2 sK0 (X0 ◇ sK1) sK4 sK5 sK6]
  have l18 : ∀ sK1 sK2 sK0 X0 sK4 sK5 sK6 sK3 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK4 ◇ (sK5 ◇ sK6)) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0 sK4 sK5 sK6 sK3
    conv => enter [1]; rw [l17 sK1 sK2 sK0 X0 sK4 sK5 sK6]
    conv => enter [1]; rw [l7 (sK4 ◇ (sK5 ◇ sK6)) X0 sK1 sK3 sK1 sK2 sK0]
  have l19 : ∀ X0 X1 sK1 sK2 sK0 sK4 sK5 sK6 sK3 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK4 ◇ (sK5 ◇ sK6)) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 sK1 sK2 sK0 sK4 sK5 sK6 sK3
    conv => enter [1]; rw [l3 X0 X1 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l18 sK1 sK2 sK0 (X1 ◇ X0) sK4 sK5 sK6 sK3]
  have l20 : ∀ sK3 sK1 sK2 sK0 sK4 sK5 sK6 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK4 ◇ (sK5 ◇ sK6)) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK1 sK2 sK0 sK4 sK5 sK6
    conv => enter [1]; rw [h43 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l18 sK1 sK2 sK0 sK3 sK4 sK5 sK6 sK3]
  have l21 : ∀ sK3 sK1 sK2 sK0 X0 X1 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l20 sK3 sK1 sK2 sK0 sK3 sK3 sK3]
    conv => enter [1]; rw [← l19 X0 X1 sK1 sK2 sK0 sK3 sK3 sK3 sK3]
  have l22 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l21 sK3 sK1 sK2 sK0 X0 sK3]
  have l23 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l22 sK3 sK1 sK2 sK0 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l16 sK3 sK1 sK2 sK0 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0]
  have l24 : ∀ X0 sK5 sK6 sK3 sK1 sK2 sK0 : G, (X0 ◇ (sK5 ◇ sK6)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l4 X0 sK5 sK6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [← l23 sK3 sK1 sK2 sK0 X0]
  have l25 : ∀ sK3 sK1 sK2 sK0 X0 sK5 sK6 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK5 ◇ sK6)) := by
    intro sK3 sK1 sK2 sK0 X0 sK5 sK6
    conv => enter [1]; rw [l22 sK3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l24 X0 sK5 sK6 sK3 sK1 sK2 sK0]
  have l26 : ∀ sK3 sK1 sK2 sK0 sK5 sK6 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK5 ◇ sK6) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 sK5 sK6 X0
    conv => enter [1]; rw [l25 sK3 sK1 sK2 sK0 X0 sK5 sK6]
    conv => enter [1]; rw [h43 X0 (sK5 ◇ sK6)]
  have l27 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ (sK5 ◇ sK6)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK4 (sK5 ◇ sK6)]
    conv => enter [1]; rw [← l26 sK3 sK1 sK2 sK0 sK5 sK6 sK4]
  intro x y z w u v r
  conv => enter [1]; rw [l27 x y z w u v r]

theorem Equation43_4512_54328_implies_Equation54312 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54312 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l4 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h54328 sK0 X2 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [← l1 sK0 X2]
  have l5 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 sK0 X0 X1 X2]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 sK0 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l9 : ∀ X0 sK0 X2 X3 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X2 ◇ X3)) := by
    intro X0 sK0 X2 X3
    conv => enter [1, 2]; rw [l8 sK0 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X2 X3 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l10 : ∀ sK0 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X2 ◇ X3)) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [l9 X0 sK0 X2 X3]
  have l11 : ∀ X2 sK1 sK2 X0 X1 : G, (X2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ X1)) := by
    intro X2 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 X2 sK1 sK2]
    conv => enter [1]; rw [l3 sK1 X2 sK2 X0 X1]
  have l12 : ∀ sK0 X2 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X2 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l11 X2 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l12 x x y z]

theorem Equation43_4512_54328_implies_Equation54639 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54639 G := by
  have l0 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = ((sK3 ◇ sK0) ◇ X0) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h4512 sK0 sK3 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK3]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X2) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [← h54328 sK1 X2 (sK1 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [← l3 sK1 X2]
  have l5 : ∀ sK1 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X2) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 sK1 X0 X1 X2]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l5 sK1 sK1 sK1 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l8 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l6 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← l1 X0 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l9 : ∀ X0 sK1 X2 X3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X2 ◇ X3)) := by
    intro X0 sK1 X2 X3
    conv => enter [1, 2]; rw [l8 sK1 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X2 X3 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l10 : ∀ sK1 X0 X2 X3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X2 ◇ X3)) := by
    intro sK1 X0 X2 X3
    conv => enter [1]; rw [l7 sK1 X0]
    conv => enter [1]; rw [l9 X0 sK1 X2 X3]
  have l11 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK3 ◇ sK0) ◇ X0) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK0 X0 sK3]
    conv => enter [1]; rw [← l2 sK3 sK0 X0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [h43 (sK3 ◇ sK0) sK2]
  intro x y z w
  conv => enter [1]; rw [← l12 w x y z]

theorem Equation43_4512_54328_implies_Equation54313 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54313 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l2 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l1 X0 X1 X2 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l3 : ∀ X3 X0 X1 X2 X4 X5 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X4 ◇ X5) ◇ (X3 ◇ X0)) := by
    intro X3 X0 X1 X2 X4 X5
    conv => enter [1, 2]; rw [l1 X0 X1 X2 X4 X5]
    conv => enter [1]; rw [l0 X3 X0 (X4 ◇ X5)]
  have l4 : ∀ X3 X0 X1 X2 X4 X5 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X4 ◇ (X5 ◇ (X3 ◇ X0))) := by
    intro X3 X0 X1 X2 X4 X5
    conv => enter [1]; rw [l3 X3 X0 X1 X2 X4 X5]
    conv => enter [1]; rw [← h4512 X4 X5 (X3 ◇ X0)]
  have l5 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK0 (sK0 ◇ sK1) X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0 sK0 sK1 sK2]
  have l6 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK0 sK1 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0 sK0 sK1 sK2]
  have l7 : ∀ X3 X0 X1 X2 X4 sK0 sK1 sK2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X4 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X3 X0 X1 X2 X4 sK0 sK1 sK2
    conv => enter [1]; rw [l4 X3 X0 X1 X2 X4 X3]
    conv => enter [1]; rw [l2 X4 X3 (X3 ◇ X0) sK0 sK1 sK2]
  have l8 : ∀ X4 sK0 sK1 sK2 X3 : G, (X4 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X3 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X4 sK0 sK1 sK2 X3
    conv => enter [1]; rw [l2 X4 sK0 (sK1 ◇ sK2) X4 X4 X4]
    conv => enter [1]; rw [l7 X4 X4 X4 X4 X3 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l6 X0 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK0 sK1 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0 sK1 sK0]
  have l11 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l6 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK0 sK0 sK1 sK2 X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1 X0 sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]
  conv => enter [1]; rw [l10 x y]

theorem Equation43_4512_54328_implies_Equation54315 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54315 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l3 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l4 : ∀ X0 X1 X2 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 X2 sK3 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0 sK3]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l5 : ∀ X0 sK3 sK0 sK1 sK2 : G, (X0 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l4 X0 sK3 sK0 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK1 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l1 sK1 X0 sK2]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK1 sK2 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 X0 sK2]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1]
    conv => enter [1]; rw [← l5 sK1 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l8 x w y z]
  conv => enter [1]; rw [l6 x w x]

theorem Equation43_4512_54328_implies_Equation54636 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54636 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l2 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0]
  have l3 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l4 : ∀ sK1 sK2 X0 X1 X2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (X1 ◇ X2)) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [l3 sK1 X0 (sK1 ◇ (sK1 ◇ sK2)) X1 X2]
  have l5 : ∀ X0 X1 X2 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 X2 sK3 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0 sK3]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l6 : ∀ X0 sK3 sK0 sK1 sK2 : G, (X0 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK3 sK0 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK1 sK1 sK2 (sK3 ◇ sK0)]
  have l8 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l7 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l9 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l6 sK2 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 sK3 sK0 sK2]
  have l10 : ∀ sK2 sK3 sK0 X0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [l9 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0 X0]
  have l11 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [l10 sK2 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK1 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l2 sK1 X0 sK2]
  have l13 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK1 sK2 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l1 sK1 sK2 X0]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK1]
    conv => enter [1]; rw [← l11 sK2 sK3 sK0 sK1 sK1]
  intro x y z w
  conv => enter [1]; rw [← l14 w x y z]
  conv => enter [1]; rw [l12 w x w]

theorem Equation43_4512_54328_implies_Equation54640 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54640 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK2 ◇ sK3)) X0]
  have l2 : ∀ sK2 X0 sK3 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK3) X0]
  have l3 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l4 : ∀ X0 X1 X2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 X2 sK1 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  have l5 : ∀ X0 sK1 sK0 sK2 sK3 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l4 X0 sK1 sK0 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0 sK2 (sK2 ◇ (sK2 ◇ sK3))]
  have l6 : ∀ sK1 sK0 X0 sK2 sK3 : G, ((sK1 ◇ sK0) ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK0 X0 sK2 sK3
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l5 X0 sK1 sK0 sK2 sK3]
  have l7 : ∀ sK1 sK0 X0 sK2 sK3 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro sK1 sK0 X0 sK2 sK3
    conv => enter [1]; rw [l6 sK1 sK0 X0 sK2 sK3]
    conv => enter [1]; rw [h43 X0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  have l8 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ sK4) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [h43 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l7 sK1 sK0 sK4 sK2 sK3]
  have l9 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l3 sK2 sK2 sK3 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l2 sK2 X0 sK3]
  have l10 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l3 sK2 sK2 sK3 X0 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l1 sK2 sK3 X0]
  have l11 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK3 sK4]
    conv => enter [1]; rw [← l8 sK4 sK1 sK0 sK2 sK3]
  intro x y z w u
  conv => enter [1]; rw [← l11 w u x y z]
  conv => enter [1]; rw [l9 w u w]

theorem Equation43_4512_54328_implies_Equation54317 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54317 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l5 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l6 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ X1))) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [← h54328 sK1 X2 sK1 X0 X1]
    conv => enter [1]; rw [← l2 sK1 X2]
  have l7 : ∀ sK1 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [l6 sK1 X0 X1 X2]
  have l8 : ∀ sK1 X0 X3 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ X3) := by
    intro sK1 X0 X3
    conv => enter [1]; rw [← l7 sK1 sK1 sK1 X0]
    conv => enter [1]; rw [l7 sK1 sK1 sK1 X3]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l8 sK1 X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK1) X1]
  have l10 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l8 sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK2]
  have l11 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l8 sK1 X0 X1]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X1]
  have l12 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1, 2]; rw [← l10 sK1 sK0 sK2]
    conv => enter [1]; rw [l9 sK0 sK1 sK0 X1]
  have l13 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 X1]
  have l14 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X1]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l10 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK1) sK1]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l10 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK2]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l17 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l16 sK1 sK2 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 sK1]
  have l18 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l19 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l11 sK1 X1 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X1]
  have l20 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l19 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK1) sK2]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0 sK0]
  have l23 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ sK2) X0]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [l23 X0 sK0 sK1 sK2]
  have l25 : ∀ sK1 X1 X2 sK0 : G, (sK1 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X2 sK0
    conv => enter [1]; rw [h54328 sK1 X1 X2 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l24 sK0 sK1 sK1 sK1]
  have l26 : ∀ sK1 sK0 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X1 ◇ X2)) := by
    intro sK1 sK0 sK2 X1 X2
    conv => enter [1]; rw [l14 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l25 sK1 X1 X2 sK0]
  have l27 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X1 ◇ X2)) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l18 sK1 sK2 sK1]
    conv => enter [1]; rw [l26 sK1 sK1 sK2 X1 X2]
  have l28 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X1 ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l21 sK0 sK1 sK0]
    conv => enter [1]; rw [l27 sK1 sK0 X1 X2]
  have l29 : ∀ sK1 X0 X1 X2 sK2 : G, (sK1 ◇ (X0 ◇ X1)) = (X2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 X1 X2 sK2
    conv => enter [1]; rw [l5 sK1 X0 X1 X2 sK2]
    conv => enter [1]; rw [l4 sK1 X2 sK2]
  have l30 : ∀ sK0 sK1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 X2 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l29 sK1 sK0 sK0 X2 sK2]
  intro x y z
  conv => enter [1]; rw [← l30 x y x z]
  conv => enter [1]; rw [l22 x y x]

theorem Equation43_4512_54328_implies_Equation54327 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54327 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l3 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l2 sK0 sK3 X0]
  have l4 : ∀ sK2 X0 X1 X2 : G, (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [← h54328 sK2 X2 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK2 X2]
  have l5 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK2 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 sK2 X0 X1 X2]
  have l6 : ∀ sK2 X0 X3 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ X3) := by
    intro sK2 X0 X3
    conv => enter [1]; rw [← l5 sK2 sK2 sK2 X0]
    conv => enter [1]; rw [l5 sK2 sK2 sK2 X3]
  have l7 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ X0) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [← l5 sK2 X1 X2 X0]
    conv => enter [1]; rw [← l0 X1 X2 (sK2 ◇ sK2)]
  have l8 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l6 sK2 X0 X1]
    conv => enter [1]; rw [h43 (sK2 ◇ sK2) X1]
  have l9 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l8 sK2 X1 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ sK2) X1]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l6 sK2 (sK2 ◇ sK2) X0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l9 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l0 sK1 (sK3 ◇ sK0) (sK2 ◇ sK2)]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l11 sK1 sK2 sK1 sK1]
  have l13 : ∀ sK2 X0 X1 X2 X3 : G, ((sK2 ◇ sK2) ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK2 X0 X1 X2 X3
    conv => enter [1]; rw [l7 sK2 X0 X1 sK2]
    conv => enter [1]; rw [h54328 X1 sK2 (sK2 ◇ sK2) X2 X3]
  have l14 : ∀ sK1 sK2 X1 X2 X3 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 X1 X2 X3
    conv => enter [1]; rw [l10 sK1 sK2 sK1]
    conv => enter [1]; rw [l13 sK2 sK1 X1 X2 X3]
  have l15 : ∀ sK1 sK2 X0 X3 X4 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X3 ◇ X4)) := by
    intro sK1 sK2 X0 X3 X4
    conv => enter [1]; rw [l14 sK1 sK2 X0 sK1 sK1]
    conv => enter [1]; rw [← h54328 X0 X3 X4 sK1 sK1]
  have l16 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK0 X0 sK3]
    conv => enter [1]; rw [l3 sK0 X0 sK3]
  intro x y z w
  conv => enter [1]; rw [← l16 x w x y z]
  conv => enter [1]; rw [l12 x w]

theorem Equation43_4512_54328_implies_Equation54645 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54645 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l4 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ X0) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l6 : ∀ sK3 X0 X1 X2 : G, (sK3 ◇ (sK3 ◇ (X0 ◇ X1))) = ((sK3 ◇ sK3) ◇ X2) := by
    intro sK3 X0 X1 X2
    conv => enter [1]; rw [← h54328 sK3 X2 sK3 X0 X1]
    conv => enter [1]; rw [← l4 sK3 X2]
  have l7 : ∀ sK3 X0 X1 X2 : G, ((sK3 ◇ sK3) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK3) ◇ X2) := by
    intro sK3 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK3 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [l6 sK3 X0 X1 X2]
  have l8 : ∀ sK3 X0 X3 : G, ((sK3 ◇ sK3) ◇ X0) = ((sK3 ◇ sK3) ◇ X3) := by
    intro sK3 X0 X3
    conv => enter [1]; rw [← l7 sK3 sK3 sK3 X0]
    conv => enter [1]; rw [l7 sK3 sK3 sK3 X3]
  have l9 : ∀ sK3 X0 X1 X2 : G, ((sK3 ◇ sK3) ◇ X0) = (X1 ◇ ((sK3 ◇ sK3) ◇ X2)) := by
    intro sK3 X0 X1 X2
    conv => enter [1]; rw [← l7 sK3 X1 X2 X0]
    conv => enter [1]; rw [l5 (sK3 ◇ sK3) X1 X2]
  have l10 : ∀ sK3 X0 X1 : G, ((sK3 ◇ sK3) ◇ X0) = (X1 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [l8 sK3 X0 X1]
    conv => enter [1]; rw [h43 (sK3 ◇ sK3) X1]
  have l11 : ∀ X0 sK3 X1 : G, (X0 ◇ (sK3 ◇ sK3)) = (X1 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3 X1
    conv => enter [1]; rw [← l10 sK3 X1 X0]
    conv => enter [1]; rw [h43 (sK3 ◇ sK3) X1]
  have l12 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l11 sK2 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l8 sK3 (sK3 ◇ sK3) X0]
  have l13 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK2 sK3
    conv => enter [1, 2]; rw [l11 sK2 sK3 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [l2 sK2 (sK2 ◇ (sK3 ◇ sK3)) (sK3 ◇ sK3)]
  have l14 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l12 sK2 sK3 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))]
    conv => enter [1]; rw [← l13 sK2 sK3]
  have l15 : ∀ sK3 X0 X1 X2 X3 : G, ((sK3 ◇ sK3) ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK3 X0 X1 X2 X3
    conv => enter [1]; rw [l9 sK3 X0 X1 sK3]
    conv => enter [1]; rw [h54328 X1 (sK3 ◇ sK3) sK3 X2 X3]
  have l16 : ∀ sK2 sK3 X1 X2 X3 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK2 sK3 X1 X2 X3
    conv => enter [1]; rw [l12 sK2 sK3 sK2]
    conv => enter [1]; rw [l15 sK3 sK2 X1 X2 X3]
  have l17 : ∀ sK2 sK3 X0 X3 X4 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X3 ◇ X4)) := by
    intro sK2 sK3 X0 X3 X4
    conv => enter [1]; rw [l16 sK2 sK3 X0 sK2 sK2]
    conv => enter [1]; rw [← h54328 X0 X3 X4 sK2 sK2]
  have l18 : ∀ sK2 sK3 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [l17 sK2 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [← l3 sK1 sK0 X0]
  have l19 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l18 sK2 sK3 sK1 sK0 sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  intro x y z w u
  conv => enter [1]; rw [← l19 w u x y z]
  conv => enter [1]; rw [l14 w u]

theorem Equation43_4512_54328_implies_Equation54319 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54319 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK0) X0]
  have l3 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l4 : ∀ X3 X0 X1 X2 X4 X5 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X4 ◇ X5) ◇ (X3 ◇ X0)) := by
    intro X3 X0 X1 X2 X4 X5
    conv => enter [1, 2]; rw [l3 X0 X1 X2 X4 X5]
    conv => enter [1]; rw [l1 X3 X0 (X4 ◇ X5)]
  have l5 : ∀ X3 X0 X1 X2 X4 X5 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X4 ◇ (X5 ◇ (X3 ◇ X0))) := by
    intro X3 X0 X1 X2 X4 X5
    conv => enter [1]; rw [l4 X3 X0 X1 X2 X4 X5]
    conv => enter [1]; rw [← h4512 X4 X5 (X3 ◇ X0)]
  have l6 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [l3 X0 sK2 sK3 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0 sK1 (sK2 ◇ sK3)]
  have l7 : ∀ X3 X0 X1 X2 X4 sK2 sK0 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X4 ◇ (sK2 ◇ sK0)) := by
    intro X3 X0 X1 X2 X4 sK2 sK0
    conv => enter [1]; rw [l5 X3 X0 X1 X2 X4 X3]
    conv => enter [1]; rw [l3 X4 X3 (X3 ◇ X0) sK2 sK0]
  have l8 : ∀ X4 sK2 sK0 X3 : G, (X4 ◇ (sK2 ◇ sK0)) = (X3 ◇ (sK2 ◇ sK0)) := by
    intro X4 sK2 sK0 X3
    conv => enter [1]; rw [l3 X4 sK2 sK0 X4 (X4 ◇ X4)]
    conv => enter [1]; rw [l7 X4 X4 X4 X4 X3 sK2 sK0]
  have l9 : ∀ sK2 sK0 X0 X1 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK2 sK0 X0 X1 sK1
    conv => enter [1]; rw [← l0 X0 (sK2 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l8 X0 sK2 sK0 sK1]
  have l10 : ∀ sK2 sK0 sK1 X1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK2 sK0 sK1 X1
    conv => enter [1]; rw [l3 (sK2 ◇ sK0) sK2 sK0 sK2 X1]
    conv => enter [1]; rw [l9 sK2 sK0 sK2 X1 sK1]
  have l11 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l8 sK1 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l10 sK2 sK0 sK1 X1]
  have l12 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0 X0]
  have l13 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l13 x y z w]
  conv => enter [1]; rw [l6 x y w x]

theorem Equation43_4512_54328_implies_Equation54622 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation54622 G := by
  have l0 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l1 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l2 : ∀ sK1 sK2 sK3 X0 X1 X2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK1 ◇ (X1 ◇ X2)) := by
    intro sK1 sK2 sK3 X0 X1 X2
    conv => enter [1]; rw [l0 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l1 sK1 X0 (sK1 ◇ (sK2 ◇ sK3)) X1 X2]
  have l3 : ∀ X0 X1 X2 sK2 sK3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 X2 sK2 sK3 sK0
    conv => enter [1]; rw [l1 X0 X1 X2 (sK2 ◇ sK3) sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK3 sK0]
  have l4 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [l1 X0 sK2 sK3 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 sK1 (sK1 ◇ (sK2 ◇ sK3))]
  have l5 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [l1 X0 sK2 sK3 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 sK1 (sK2 ◇ sK3)]
  have l6 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 X0 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK1 sK1 sK2 sK3 sK0]
  have l7 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
    conv => enter [1]; rw [← l4 X0 sK2 sK3 sK1]
  have l8 : ∀ X0 sK2 sK3 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l6 sK1 sK2 sK3 X0 sK0]
  have l9 : ∀ sK2 sK3 X0 sK1 : G, ((sK2 ◇ sK3) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro sK2 sK3 X0 sK1
    conv => enter [1]; rw [h43 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 X0]
  have l10 : ∀ sK2 sK3 X0 sK1 sK0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK3 X0 sK1]
    conv => enter [1]; rw [l6 sK1 sK2 sK3 X0 sK0]
  have l11 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [l10 sK2 sK3 sK0 sK1 sK0]
  have l12 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l11 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [← l8 X0 sK2 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]
  conv => enter [1]; rw [l5 w x y w]

theorem Equation43_4512_54319_implies_Equation4271 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54319 : Equation54319 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ ((X0 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (X0 ◇ sK2) X1]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK2 X1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h54319 sK0 X0 X1 sK0]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54319 sK0 sK0 X1 X0]
    conv => enter [1]; rw [l0 sK0 sK0 X1]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54319 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l9 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X1]
    conv => enter [1]; rw [h54319 sK1 sK2 X1 X0]
  have l10 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l9 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← l5 sK1 sK2 sK1 X0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l14 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ sK2) ◇ X1) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l10 sK1 sK2 X1 sK1]
    conv => enter [1]; rw [h54319 (sK1 ◇ sK2) sK1 sK1 sK2]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l17 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK0 X0 X1]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0 X0 X1]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l17 sK0 X1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l20 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [← l18 sK0 X0 X0]
    conv => enter [1]; rw [l18 sK0 X0 X2]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ sK0) X0]
  have l22 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l14 sK1 sK2 X0]
    conv => enter [1]; rw [← l14 sK1 sK2 X1]
  have l23 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ X0) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l22 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) X1]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l21 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l22 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ sK0 X1 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X1 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l23 sK1 sK2 sK0 X1]
  intro x y z
  conv => enter [1]; rw [l25 x x y z]

theorem Equation43_4512_54319_implies_Equation54340 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54319 : Equation54319 G) : Equation54340 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK2 sK3 X0 X1 : G, (((sK2 ◇ sK3) ◇ X0) ◇ X1) = (sK2 ◇ ((X0 ◇ sK3) ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1, 1]; rw [l1 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 sK2 (X0 ◇ sK3) X1]
  have l4 : ∀ sK2 sK3 X0 X1 : G, (((sK2 ◇ sK3) ◇ X0) ◇ X1) = (sK2 ◇ (X0 ◇ (sK3 ◇ X1))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l3 sK2 sK3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK3 X1]
  have l5 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (sK3 ◇ X1))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) X0 X1]
    conv => enter [1]; rw [l4 sK2 sK3 X0 X1]
  have l6 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = (sK3 ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK3 (X0 ◇ sK0) X1]
  have l7 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = (sK3 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l6 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l8 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ X1)) = (sK3 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l7 sK3 sK0 X0 X1]
  have l9 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ ((sK2 ◇ sK3) ◇ X0)) = (sK2 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1, 2]; rw [l1 sK2 sK3 X0]
    conv => enter [1]; rw [← h54319 sK2 X0 X1 sK3]
  have l10 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ sK3) ◇ X1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ X0))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X1]
    conv => enter [1]; rw [h54319 sK2 sK3 X1 X0]
  have l11 : ∀ sK3 sK0 X1 X0 : G, ((sK3 ◇ sK0) ◇ X1) = (sK3 ◇ (sK3 ◇ (sK0 ◇ X0))) := by
    intro sK3 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X1]
    conv => enter [1]; rw [h54319 sK3 sK0 X1 X0]
  have l12 : ∀ sK3 sK0 X1 X0 : G, ((sK3 ◇ sK0) ◇ X1) = ((sK3 ◇ sK0) ◇ (sK3 ◇ X0)) := by
    intro sK3 sK0 X1 X0
    conv => enter [1]; rw [l11 sK3 sK0 X1 X0]
    conv => enter [1]; rw [← l8 sK3 sK0 sK3 X0]
  have l13 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ sK3) ◇ X1) = ((sK2 ◇ sK3) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l10 sK2 sK3 X1 X0]
    conv => enter [1]; rw [← l5 sK2 sK3 sK2 X0]
  have l14 : ∀ sK3 sK0 X1 X0 : G, ((sK3 ◇ sK0) ◇ X1) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X1 X0
    conv => enter [1]; rw [l12 sK3 sK0 X1 X0]
    conv => enter [1]; rw [← l0 sK3 X0 (sK3 ◇ sK0)]
  have l15 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ sK3) ◇ X1) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l13 sK2 sK3 X1 X0]
    conv => enter [1]; rw [← l0 sK2 X0 (sK2 ◇ sK3)]
  have l16 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ X0) = ((sK3 ◇ sK0) ◇ X1) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l14 sK3 sK0 X0 sK3]
    conv => enter [1]; rw [← l14 sK3 sK0 X1 sK3]
  have l17 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h43 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l14 sK3 sK0 X0 sK2]
  have l18 : ∀ sK3 sK2 sK0 X0 X1 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK2 sK0 X0 X1
    conv => enter [1]; rw [← l14 sK3 sK0 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← l0 X0 X1 (sK3 ◇ sK0)]
  have l19 : ∀ sK3 sK2 sK0 X1 X0 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK3 sK2 sK0 X1 X0
    conv => enter [1]; rw [← l14 sK3 sK0 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [l0 (sK3 ◇ sK0) X0 X1]
  have l20 : ∀ sK3 sK2 sK0 X1 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK2 sK0 X1
    conv => enter [1]; rw [l19 sK3 sK2 sK0 X1 sK3]
    conv => enter [1, 2]; rw [l14 sK3 sK0 sK3 sK2]
  have l21 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ ((sK3 ◇ sK0) ◇ X0)) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1, 2]; rw [l16 sK3 sK0 X0 X1]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ sK0) X1]
  have l22 : ∀ X1 sK2 sK3 sK0 : G, (X1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ sK3) ◇ (sK3 ◇ sK0))) := by
    intro X1 sK2 sK3 sK0
    conv => enter [1]; rw [← l21 sK2 sK3 sK0 X1 X1]
    conv => enter [1]; rw [← l9 sK2 sK3 (sK3 ◇ sK0) X1]
  have l23 : ∀ X1 sK2 sK3 sK0 : G, (X1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X1 sK2 sK3 sK0
    conv => enter [1]; rw [l22 X1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l18 sK3 sK2 sK0 sK2 (sK2 ◇ sK3)]
  have l24 : ∀ X0 sK3 sK0 X1 : G, (X0 ◇ (sK3 ◇ sK0)) = (X1 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK3 sK0 X1
    conv => enter [1]; rw [l17 X0 sK3 sK0 X0]
    conv => enter [1]; rw [← l17 X1 sK3 sK0 X0]
  have l25 : ∀ X0 X1 X2 sK3 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro X0 X1 X2 sK3 sK2 sK0
    conv => enter [1]; rw [h54319 X0 X1 X2 (sK3 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l17 X1 sK3 sK0 sK2]
  have l26 : ∀ X0 X1 X2 sK3 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 X2 sK3 sK2 sK0
    conv => enter [1]; rw [l25 X0 X1 X2 sK3 sK2 sK0]
    conv => enter [1, 2]; rw [← l20 sK3 sK2 sK0 X0]
  have l27 : ∀ X0 X1 X2 sK3 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 X2 sK3 sK2 sK0
    conv => enter [1]; rw [l26 X0 X1 X2 sK3 sK2 sK0]
    conv => enter [1]; rw [← l20 sK3 sK2 sK0 X0]
  have l28 : ∀ X0 X1 sK3 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) = (X2 ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 sK3 sK0 X2
    conv => enter [1]; rw [h4512 X0 X1 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l24 (X0 ◇ X1) sK3 sK0 X2]
  have l29 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [← l28 X0 X1 sK3 sK0 sK2]
  have l30 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l29 sK2 sK3 sK0 sK2 sK2]
    conv => enter [1]; rw [l27 sK2 sK2 (sK3 ◇ sK0) sK3 sK2 sK0]
  have l31 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l30 sK2 sK3 sK0]
    conv => enter [1]; rw [← l23 X0 sK2 sK3 sK0]
  have l32 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l31 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK2 ◇ (sK3 ◇ sK0))]
  have l33 : ∀ sK2 sK3 X0 sK0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 X0 sK0
    conv => enter [1]; rw [l15 sK2 sK3 X0 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← l32 sK2 sK3 sK0 (sK2 ◇ sK3)]
  have l34 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = ((sK2 ◇ sK3) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l31 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [← l33 sK2 sK3 X0 sK0]
  have l35 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l34 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ sK3) X0]
  intro x y z w
  conv => enter [1]; rw [← l35 y z w x]
  conv => enter [1]; rw [l31 y z w x]

theorem Equation43_4512_54319_implies_Equation54345 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54319 : Equation54319 G) : Equation54345 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ sK4) ◇ X0) = (sK3 ◇ (X0 ◇ sK4)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK3 sK4 X0]
    conv => enter [1, 2]; rw [h43 sK4 X0]
  have l2 : ∀ sK3 sK1 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK3 sK4 X0 X1 : G, (((sK3 ◇ sK4) ◇ X0) ◇ X1) = (sK3 ◇ ((X0 ◇ sK4) ◇ X1)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1, 1]; rw [l1 sK3 sK4 X0]
    conv => enter [1]; rw [← h4512 sK3 (X0 ◇ sK4) X1]
  have l4 : ∀ sK3 sK4 X0 X1 : G, (((sK3 ◇ sK4) ◇ X0) ◇ X1) = (sK3 ◇ (X0 ◇ (sK4 ◇ X1))) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l3 sK3 sK4 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK4 X1]
  have l5 : ∀ sK3 sK4 X0 X1 : G, ((sK3 ◇ sK4) ◇ (X0 ◇ X1)) = (sK3 ◇ (X0 ◇ (sK4 ◇ X1))) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ sK4) X0 X1]
    conv => enter [1]; rw [l4 sK3 sK4 X0 X1]
  have l6 : ∀ sK3 sK1 sK0 X0 X1 : G, (((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (sK3 ◇ ((X0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK3 (X0 ◇ (sK1 ◇ sK0)) X1]
  have l7 : ∀ sK3 sK1 sK0 X0 X1 : G, (((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (sK3 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1))) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l6 sK3 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK0) X1]
  have l8 : ∀ sK3 sK1 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK3 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1))) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l7 sK3 sK1 sK0 X0 X1]
  have l9 : ∀ sK3 sK4 X1 X0 : G, ((sK3 ◇ sK4) ◇ X1) = (sK3 ◇ (sK3 ◇ (sK4 ◇ X0))) := by
    intro sK3 sK4 X1 X0
    conv => enter [1]; rw [← h4512 sK3 sK4 X1]
    conv => enter [1]; rw [h54319 sK3 sK4 X1 X0]
  have l10 : ∀ sK3 sK1 sK0 X1 X0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X1) = (sK3 ◇ (sK3 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [h54319 sK3 (sK1 ◇ sK0) X1 X0]
  have l11 : ∀ sK3 sK1 sK0 X1 X0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X1) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ X0)) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1]; rw [l10 sK3 sK1 sK0 X1 X0]
    conv => enter [1]; rw [← l8 sK3 sK1 sK0 sK3 X0]
  have l12 : ∀ sK3 sK4 X1 X0 : G, ((sK3 ◇ sK4) ◇ X1) = ((sK3 ◇ sK4) ◇ (sK3 ◇ X0)) := by
    intro sK3 sK4 X1 X0
    conv => enter [1]; rw [l9 sK3 sK4 X1 X0]
    conv => enter [1]; rw [← l5 sK3 sK4 sK3 X0]
  have l13 : ∀ sK3 sK1 sK0 X1 X0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X1) = (sK3 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1]; rw [l11 sK3 sK1 sK0 X1 X0]
    conv => enter [1]; rw [← l0 sK3 X0 (sK3 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK3 sK4 X1 X0 : G, ((sK3 ◇ sK4) ◇ X1) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK4 X1 X0
    conv => enter [1]; rw [l12 sK3 sK4 X1 X0]
    conv => enter [1]; rw [← l0 sK3 X0 (sK3 ◇ sK4)]
  have l15 : ∀ sK3 sK1 sK0 X0 sK4 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK3 ◇ sK4) ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 X0 sK4
    conv => enter [1]; rw [l13 sK3 sK1 sK0 X0 sK4]
    conv => enter [1]; rw [h4512 sK3 sK4 (sK3 ◇ (sK1 ◇ sK0))]
  have l16 : ∀ X0 sK3 sK1 sK0 sK2 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK3 sK1 sK0 sK2
    conv => enter [1]; rw [h43 X0 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l13 sK3 sK1 sK0 X0 sK2]
  have l17 : ∀ X1 X0 sK3 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))))) := by
    intro X1 X0 sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← l0 X0 (sK3 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1, 2]; rw [l13 sK3 sK1 sK0 X1 sK2]
  have l18 : ∀ X0 X1 sK3 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l0 X0 X1 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l13 sK3 sK1 sK0 (X0 ◇ X1) sK2]
  have l19 : ∀ sK3 sK2 sK1 sK0 X0 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))))) := by
    intro sK3 sK2 sK1 sK0 X0
    conv => enter [1]; rw [l18 sK3 sK2 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [l17 sK3 X0 sK3 sK1 sK0 sK2]
  have l20 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ ((sK3 ◇ sK4) ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1, 2]; rw [← l15 sK3 sK1 sK0 X0 sK4]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ (sK1 ◇ sK0)) X0]
  have l21 : ∀ X0 sK2 sK3 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← l20 sK2 sK3 X0 sK1 sK0 X0]
    conv => enter [1]; rw [l18 sK2 (sK3 ◇ X0) sK3 sK1 sK0 sK2]
  have l22 : ∀ X0 sK3 sK1 sK0 X1 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK3 sK1 sK0 X1
    conv => enter [1]; rw [l16 X0 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [← l16 X1 sK3 sK1 sK0 X0]
  have l23 : ∀ X0 X1 X2 sK3 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 X1 X2 sK3 sK2 sK1 sK0
    conv => enter [1]; rw [h54319 X0 X1 X2 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l16 X1 sK3 sK1 sK0 sK2]
  have l24 : ∀ X0 X1 X2 sK3 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 X2 sK3 sK2 sK1 sK0
    conv => enter [1]; rw [l23 X0 X1 X2 sK3 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l19 sK3 sK2 sK1 sK0 X0]
  have l25 : ∀ X0 X1 X2 sK3 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 X2 sK3 sK2 sK1 sK0
    conv => enter [1]; rw [l24 X0 X1 X2 sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [← l19 sK3 sK2 sK1 sK0 X0]
  have l26 : ∀ X0 X1 sK3 sK1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (X2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK3 sK1 sK0 X2
    conv => enter [1]; rw [h4512 X0 X1 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l22 (X0 ◇ X1) sK3 sK1 sK0 X2]
  have l27 : ∀ sK2 sK3 sK1 sK0 X0 X1 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [← l26 X0 X1 sK3 sK1 sK0 sK2]
  have l28 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l27 sK2 sK3 sK1 sK0 sK2 sK2]
    conv => enter [1]; rw [l25 sK2 sK2 (sK3 ◇ (sK1 ◇ sK0)) sK3 sK2 sK1 sK0]
  have l29 : ∀ sK2 sK3 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [l28 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [← l21 X0 sK2 sK3 sK1 sK0]
  have l30 : ∀ sK2 sK3 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [l29 sK2 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))]
  have l31 : ∀ sK3 sK4 X0 sK2 sK1 sK0 : G, ((sK3 ◇ sK4) ◇ X0) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK4 X0 sK2 sK1 sK0
    conv => enter [1]; rw [l14 sK3 sK4 X0 (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l30 sK2 sK3 sK1 sK0 (sK3 ◇ sK4)]
  have l32 : ∀ sK2 sK3 sK1 sK0 sK4 X0 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = ((sK3 ◇ sK4) ◇ X0) := by
    intro sK2 sK3 sK1 sK0 sK4 X0
    conv => enter [1]; rw [l29 sK2 sK3 sK1 sK0 sK3]
    conv => enter [1]; rw [← l31 sK3 sK4 X0 sK2 sK1 sK0]
  have l33 : ∀ sK2 sK3 sK1 sK0 X0 sK4 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK2 sK3 sK1 sK0 X0 sK4
    conv => enter [1]; rw [l32 sK2 sK3 sK1 sK0 sK4 X0]
    conv => enter [1]; rw [h43 (sK3 ◇ sK4) X0]
  intro x y z w u
  conv => enter [1]; rw [← l33 x y w u x z]

theorem Equation43_4512_54319_implies_Equation54388 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54319 : Equation54319 G) : Equation54388 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [h43 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK3 sK4 sK5 X0 : G, ((sK3 ◇ (sK4 ◇ sK5)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK4 ◇ sK5))) := by
    intro sK3 sK4 sK5 X0
    conv => enter [1]; rw [← h4512 sK3 (sK4 ◇ sK5) X0]
    conv => enter [1, 2]; rw [h43 (sK4 ◇ sK5) X0]
  have l4 : ∀ sK4 sK5 X0 : G, ((sK4 ◇ sK5) ◇ X0) = (sK4 ◇ (X0 ◇ sK5)) := by
    intro sK4 sK5 X0
    conv => enter [1]; rw [← h4512 sK4 sK5 X0]
    conv => enter [1, 2]; rw [h43 sK5 X0]
  have l5 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l6 : ∀ sK4 sK5 X0 X1 : G, (((sK4 ◇ sK5) ◇ X0) ◇ X1) = (sK4 ◇ ((X0 ◇ sK5) ◇ X1)) := by
    intro sK4 sK5 X0 X1
    conv => enter [1, 1]; rw [l4 sK4 sK5 X0]
    conv => enter [1]; rw [← h4512 sK4 (X0 ◇ sK5) X1]
  have l7 : ∀ sK4 sK5 X0 X1 : G, (((sK4 ◇ sK5) ◇ X0) ◇ X1) = (sK4 ◇ (X0 ◇ (sK5 ◇ X1))) := by
    intro sK4 sK5 X0 X1
    conv => enter [1]; rw [l6 sK4 sK5 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK5 X1]
  have l8 : ∀ sK4 sK5 X0 X1 : G, ((sK4 ◇ sK5) ◇ (X0 ◇ X1)) = (sK4 ◇ (X0 ◇ (sK5 ◇ X1))) := by
    intro sK4 sK5 X0 X1
    conv => enter [1]; rw [h4512 (sK4 ◇ sK5) X0 X1]
    conv => enter [1]; rw [l7 sK4 sK5 X0 X1]
  have l9 : ∀ sK2 sK0 sK1 X0 X1 : G, (((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ ((X0 ◇ sK2) ◇ X1)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (X0 ◇ sK2) X1]
  have l10 : ∀ sK2 sK0 sK1 X0 X1 : G, (((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK2 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK2 X1]
  have l11 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l10 sK2 sK0 sK1 X0 X1]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l14 : ∀ sK3 sK4 sK5 X0 X1 : G, (sK3 ◇ ((sK3 ◇ (sK4 ◇ sK5)) ◇ X0)) = (sK3 ◇ (X0 ◇ X1)) := by
    intro sK3 sK4 sK5 X0 X1
    conv => enter [1, 2]; rw [l3 sK3 sK4 sK5 X0]
    conv => enter [1]; rw [← h54319 sK3 X0 X1 (sK4 ◇ sK5)]
  have l15 : ∀ sK4 sK5 X1 X0 : G, ((sK4 ◇ sK5) ◇ X1) = (sK4 ◇ (sK4 ◇ (sK5 ◇ X0))) := by
    intro sK4 sK5 X1 X0
    conv => enter [1]; rw [← h4512 sK4 sK5 X1]
    conv => enter [1]; rw [h54319 sK4 sK5 X1 X0]
  have l16 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ X0))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l1 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [h54319 (sK0 ◇ sK1) sK2 X1 X0]
  have l17 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l16 sK2 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l11 sK2 sK0 sK1 (sK0 ◇ sK1) X0]
  have l18 : ∀ sK4 sK5 X1 X0 : G, ((sK4 ◇ sK5) ◇ X1) = ((sK4 ◇ sK5) ◇ (sK4 ◇ X0)) := by
    intro sK4 sK5 X1 X0
    conv => enter [1]; rw [l15 sK4 sK5 X1 X0]
    conv => enter [1]; rw [← l8 sK4 sK5 sK4 X0]
  have l19 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l17 sK2 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK1) X0 (sK2 ◇ (sK0 ◇ sK1))]
  have l20 : ∀ sK4 sK5 X1 : G, ((sK4 ◇ sK5) ◇ X1) = ((sK4 ◇ sK5) ◇ ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5))) := by
    intro sK4 sK5 X1
    conv => enter [1]; rw [l18 sK4 sK5 X1 sK4]
    conv => enter [1]; rw [h54319 (sK4 ◇ sK5) sK4 sK4 sK5]
  have l21 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l19 sK2 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l19 sK2 sK0 sK1 X1 sK2]
  have l22 : ∀ X0 sK2 sK0 sK1 sK3 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [h43 X0 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l19 sK2 sK0 sK1 X0 sK3]
  have l23 : ∀ X0 sK2 sK0 sK1 X1 sK3 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1)) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK0 sK1 X1 sK3
    conv => enter [1]; rw [l12 X0 (sK2 ◇ (sK0 ◇ sK1)) X1]
    conv => enter [1]; rw [l19 sK2 sK0 sK1 (X0 ◇ X1) sK3]
  have l24 : ∀ X0 X1 sK2 sK0 sK1 sK3 : G, (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [l13 X0 X1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l19 sK2 sK0 sK1 (X1 ◇ X0) sK3]
  have l25 : ∀ sK0 sK1 sK3 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK3 sK2 X0
    conv => enter [1]; rw [← l23 X0 sK2 sK0 sK1 sK0 sK3]
    conv => enter [1, 2]; rw [l19 sK2 sK0 sK1 sK0 sK3]
  have l26 : ∀ sK3 sK2 sK0 sK1 X0 X1 : G, (sK3 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK2 sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l21 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l2 sK3 (sK2 ◇ (sK0 ◇ sK1)) X1]
  have l27 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 X1 : G, (sK3 ◇ ((sK3 ◇ (sK4 ◇ sK5)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l14 sK3 sK4 sK5 (sK2 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [l26 sK3 sK2 sK0 sK1 sK3 X1]
  have l28 : ∀ X1 sK3 sK2 sK0 sK1 : G, (X1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X1 sK3 sK2 sK0 sK1
    conv => enter [1]; rw [← l27 sK3 X1 X1 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [l24 sK3 (sK3 ◇ (X1 ◇ X1)) sK2 sK0 sK1 sK3]
  have l29 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l22 X0 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← l22 X1 sK2 sK0 sK1 X0]
  have l30 : ∀ X0 X1 X2 sK0 sK1 sK3 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 X1 X2 sK0 sK1 sK3 sK2
    conv => enter [1]; rw [h54319 X0 X1 X2 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l22 X1 sK2 sK0 sK1 sK3]
  have l31 : ∀ X0 X1 X2 sK0 sK1 sK3 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 X2 sK0 sK1 sK3 sK2
    conv => enter [1]; rw [l30 X0 X1 X2 sK0 sK1 sK3 sK2]
    conv => enter [1, 2]; rw [← l25 sK0 sK1 sK3 sK2 X0]
  have l32 : ∀ X0 X1 X2 sK0 sK1 sK3 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 X2 sK0 sK1 sK3 sK2
    conv => enter [1]; rw [l31 X0 X1 X2 sK0 sK1 sK3 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 sK3 sK2 X0]
  have l33 : ∀ sK3 X0 sK2 sK0 sK1 sK4 sK5 : G, (sK3 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK3 ◇ (sK4 ◇ sK5)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 X0 sK2 sK0 sK1 sK4 sK5
    conv => enter [1, 2]; rw [l29 X0 sK2 sK0 sK1 (sK4 ◇ sK5)]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK5) (sK2 ◇ (sK0 ◇ sK1))]
  have l34 : ∀ sK3 sK2 sK0 sK1 X0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l29 sK3 sK2 sK0 sK1 (sK3 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [← l33 sK3 X0 sK2 sK0 sK1 sK3 sK3]
  have l35 : ∀ sK3 sK2 sK0 sK1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1]; rw [l34 sK3 sK2 sK0 sK1 sK3]
    conv => enter [1]; rw [l32 sK3 sK3 (sK2 ◇ (sK0 ◇ sK1)) sK0 sK1 sK3 sK2]
  have l36 : ∀ sK3 sK2 sK0 sK1 X0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l35 sK3 sK2 sK0 sK1]
    conv => enter [1]; rw [← l28 X0 sK3 sK2 sK0 sK1]
  have l37 : ∀ sK4 sK5 X0 X1 : G, ((sK4 ◇ sK5) ◇ X0) = ((sK4 ◇ sK5) ◇ X1) := by
    intro sK4 sK5 X0 X1
    conv => enter [1]; rw [l20 sK4 sK5 X0]
    conv => enter [1]; rw [← l20 sK4 sK5 X1]
  have l38 : ∀ sK4 sK5 X0 X1 : G, ((sK4 ◇ sK5) ◇ X0) = (X1 ◇ (sK4 ◇ sK5)) := by
    intro sK4 sK5 X0 X1
    conv => enter [1]; rw [l37 sK4 sK5 X0 X1]
    conv => enter [1]; rw [h43 (sK4 ◇ sK5) X1]
  have l39 : ∀ sK3 sK2 sK0 sK1 sK4 sK5 X0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ sK5) ◇ X0) := by
    intro sK3 sK2 sK0 sK1 sK4 sK5 X0
    conv => enter [1]; rw [l36 sK3 sK2 sK0 sK1 (sK4 ◇ sK5)]
    conv => enter [1]; rw [l37 sK4 sK5 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
  have l40 : ∀ sK3 sK2 sK0 sK1 X1 sK4 sK5 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK4 ◇ sK5)) := by
    intro sK3 sK2 sK0 sK1 X1 sK4 sK5
    conv => enter [1]; rw [l39 sK3 sK2 sK0 sK1 sK4 sK5 sK3]
    conv => enter [1]; rw [l38 sK4 sK5 sK3 X1]
  intro x y z w u v
  conv => enter [1]; rw [← l40 x w u v x y z]

theorem Equation43_4512_54319_implies_Equation54683 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54319 : Equation54319 G) : Equation54683 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [h43 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK5 sK6 X0 : G, ((sK5 ◇ sK6) ◇ X0) = (sK5 ◇ (X0 ◇ sK6)) := by
    intro sK5 sK6 X0
    conv => enter [1]; rw [← h4512 sK5 sK6 X0]
    conv => enter [1, 2]; rw [h43 sK6 X0]
  have l4 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l5 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l1 sK1 sK2 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l6 : ∀ sK1 sK2 sK0 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = ((sK2 ◇ sK0) ◇ ((X0 ◇ sK1) ◇ X1)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1, 1]; rw [l4 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (X0 ◇ sK1) X1]
  have l7 : ∀ sK1 sK2 sK0 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l8 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l7 sK1 sK2 sK0 X0 X1]
  have l9 : ∀ sK3 sK1 sK2 sK0 X0 X1 : G, (((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) ◇ X1) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((X0 ◇ sK3) ◇ X1)) := by
    intro sK3 sK1 sK2 sK0 X0 X1
    conv => enter [1, 1]; rw [l5 sK3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK0)) (X0 ◇ sK3) X1]
  have l10 : ∀ sK3 sK1 sK2 sK0 X0 X1 : G, (((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) ◇ X1) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK3 ◇ X1))) := by
    intro sK3 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l9 sK3 sK1 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK3 X1]
  have l11 : ∀ sK3 sK1 sK2 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK3 ◇ X1))) := by
    intro sK3 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0 X1]
    conv => enter [1]; rw [l10 sK3 sK1 sK2 sK0 X0 X1]
  have l12 : ∀ sK1 sK2 sK0 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [← l0 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [h54319 (sK2 ◇ sK0) sK1 X1 X0]
  have l13 : ∀ sK3 sK1 sK2 sK0 X1 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0))) := by
    intro sK3 sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [← l1 sK1 sK2 sK0 sK3 X1]
    conv => enter [1]; rw [h54319 (sK1 ◇ (sK2 ◇ sK0)) sK3 X1 X0]
  have l14 : ∀ sK3 sK1 sK2 sK0 X1 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK3 sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [l13 sK3 sK1 sK2 sK0 X1 X0]
    conv => enter [1]; rw [← l11 sK3 sK1 sK2 sK0 (sK1 ◇ (sK2 ◇ sK0)) X0]
  have l15 : ∀ sK1 sK2 sK0 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [l12 sK1 sK2 sK0 X1 X0]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0 (sK2 ◇ sK0) X0]
  have l16 : ∀ sK3 sK1 sK2 sK0 X1 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK3 sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [l14 sK3 sK1 sK2 sK0 X1 X0]
    conv => enter [1]; rw [← l2 (sK1 ◇ (sK2 ◇ sK0)) X0 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l17 : ∀ sK1 sK2 sK0 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [l15 sK1 sK2 sK0 X1 X0]
    conv => enter [1]; rw [← l2 (sK2 ◇ sK0) X0 (sK1 ◇ (sK2 ◇ sK0))]
  have l18 : ∀ sK3 sK1 sK2 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro sK3 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l16 sK3 sK1 sK2 sK0 X0 sK3]
    conv => enter [1]; rw [← l16 sK3 sK1 sK2 sK0 X1 sK3]
  have l19 : ∀ sK3 sK1 sK2 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l18 sK3 sK1 sK2 sK0 X0 X1]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) X1]
  have l20 : ∀ X0 sK3 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK3 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← l19 sK3 sK1 sK2 sK0 X1 X0]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) X1]
  have l21 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l17 sK1 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [← l17 sK1 sK2 sK0 X1 sK1]
  have l22 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l21 sK1 sK2 sK0 sK3 X0]
  have l23 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l22 sK3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) X0]
  have l24 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l22 sK3 sK1 sK2 sK0 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l20 (sK1 ◇ (sK2 ◇ sK0)) sK3 sK1 sK2 sK0 X0]
  have l25 : ∀ X0 X1 X2 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro X0 X1 X2 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h54319 X0 X1 X2 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l23 X1 sK1 sK2 sK0 sK3]
  have l26 : ∀ X0 X1 X2 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 X2 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l25 X0 X1 X2 sK3 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l24 sK3 sK1 sK2 sK0 X0]
  have l27 : ∀ X0 X1 X2 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 X2 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l26 X0 X1 X2 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [← l24 sK3 sK1 sK2 sK0 X0]
  have l28 : ∀ sK3 sK1 sK2 sK0 sK5 sK6 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK5 ◇ sK6) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 sK5 sK6 X0
    conv => enter [1]; rw [← l27 sK5 X0 sK6 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [← l3 sK5 sK6 X0]
  have l29 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ (sK5 ◇ sK6)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK4 (sK5 ◇ sK6)]
    conv => enter [1]; rw [← l28 sK3 sK1 sK2 sK0 sK5 sK6 sK4]
  intro x y z w u v r
  conv => enter [1]; rw [l29 x y z w u v r]

end CommutativeSemigroup5
